"""Install the full pinned AFP release for Isabelle2026 and update session_roots."""
from __future__ import annotations

import argparse
import json
import re
import shutil
import tarfile
import tempfile
import urllib.request
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

from ..common import repo_path, validate_layout
from .runtime import DspConfig, hash_file

ARCHIVE_URL = "https://isa-afp.org/release/afp-2026-10-26.tar.gz"
ARCHIVE_SHA256 = "7f48e3fc3dc823a30149a90fa4a614ed53be175273971f4923debb9457fa60e4"
ARCHIVE_ROOT = "afp-2026-10-26"
DEFAULT_DESTINATION = "external/afp-2026"
DEFAULT_ARCHIVE = "itpeval/.downloads/afp-2026-10-26.tar.gz"
DEFAULT_CONFIG = "eval/configs/hol_light_to_isabelle/v2_dsp_2026.local.json"
REQUIRED_THEORIES = {"Triangle": "Angles", "Cayley_Hamilton": "Square_Matrix",
                     "Pratt_Certificate": "Pratt_Certificate"}


def atomic_json(path: Path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, prefix=path.name+"-",
                                     suffix=".tmp", encoding="utf-8", delete=False) as stream:
        temporary = Path(stream.name)
        json.dump(data, stream, indent=2, ensure_ascii=False)
        stream.write("\n")
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def download_archive(path: Path):
    """Reuse only an exact checksum match; interrupted downloads never become cache hits."""
    path = repo_path(path)
    if path.exists():
        if not path.is_file() or hash_file(path) != ARCHIVE_SHA256:
            raise ValueError("AFP cache checksum mismatch: " + str(path))
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        request = urllib.request.Request(ARCHIVE_URL, headers={"User-Agent": "ITPEval-AFP-Setup/1"})
        with urllib.request.urlopen(request, timeout=60) as source, tempfile.NamedTemporaryFile(
                dir=path.parent, prefix="afp-download-", suffix=".part", delete=False) as out:
            temporary = Path(out.name)
            shutil.copyfileobj(source, out, length=1024*1024)
        if hash_file(temporary) != ARCHIVE_SHA256:
            raise ValueError("Downloaded AFP archive does not match the pinned Isabelle2026 release")
        temporary.replace(path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def extract_sources(archive: Path, staging: Path):
    """Python 3.10-safe extraction: ordinary files/directories only, inside staging."""
    staging = repo_path(staging)
    count = 0
    with tarfile.open(archive, "r:gz") as source:
        for member in source:
            name = PurePosixPath(member.name)
            if (name.is_absolute() or ".." in name.parts or "\\" in member.name
                    or ":" in member.name or not name.parts or name.parts[0] != ARCHIVE_ROOT
                    or not (member.isdir() or member.isfile())):
                raise ValueError("Unsafe or unexpected AFP archive member: " + member.name)
            target = staging.joinpath(*name.parts[1:]).resolve()
            if not target.is_relative_to(staging.resolve()):
                raise ValueError("AFP member escapes staging directory")
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                with source.extractfile(member) as data, target.open("xb") as output:
                    shutil.copyfileobj(data, output)
                target.chmod(member.mode & 0o777)
                count += 1
    return count


def validate_sources(destination: Path):
    version = (destination / "etc/version").read_text(encoding="utf-8")
    if not re.search(r'^AFP_VERSION=["\']?2026["\']?\s*$', version, re.MULTILINE):
        raise ValueError("AFP sources do not declare AFP_VERSION=2026")
    thys = destination / "thys"
    roots = (thys / "ROOTS").read_text(encoding="utf-8").splitlines()
    entries = {line.strip() for line in roots if line.strip() and not line.lstrip().startswith("#")}
    for session, theory in REQUIRED_THEORIES.items():
        if session not in entries:
            raise ValueError("Full AFP ROOTS is missing session: " + session)
        for path in (thys / session / "ROOT", thys / session / (theory + ".thy")):
            if not path.is_file():
                raise ValueError("AFP source missing: " + str(path))
    return thys


def install(*, config_path=DEFAULT_CONFIG, destination=DEFAULT_DESTINATION, archive_path=DEFAULT_ARCHIVE):
    config_path, destination, archive = map(repo_path, (config_path, destination, archive_path))
    if config_path.is_file():
        data = json.loads(config_path.read_text(encoding="utf-8"))
        DspConfig.load(str(config_path))  # Validate before downloading or changing anything.
    else:
        example = repo_path("eval/configs/hol_light_to_isabelle/v2_dsp_2026.example.json")
        data = json.loads(example.read_text(encoding="utf-8"))
        DspConfig.load(str(example))
    if config_path == archive or config_path.is_relative_to(destination):
        raise ValueError("Configuration must be outside the AFP source directory/archive")
    manifest_path = destination / ".afp-source.json"
    if destination.exists():
        if not manifest_path.is_file():
            raise ValueError("Destination already exists without an installer manifest; choose a different --destination")
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        if manifest.get("archive_sha256") != ARCHIVE_SHA256:
            raise ValueError("Existing AFP destination is not the pinned release; choose a different --destination")
        thys = validate_sources(destination)
        print("Using existing AFP sources: " + str(destination), flush=True)
    else:
        print("Preparing full AFP archive: " + ARCHIVE_URL, flush=True)
        download_archive(archive)
        destination.parent.mkdir(parents=True, exist_ok=True)
        # The only directory move is our private staging tree to the checked
        # repository-local, absent destination. Never replace an existing checkout.
        with tempfile.TemporaryDirectory(prefix="afp-stage-", dir=destination.parent) as folder:
            staging = Path(folder) / "sources"
            staging.mkdir()
            count = extract_sources(archive, staging)
            validate_sources(staging)
            manifest = {"isabelle_version": "Isabelle2026", "archive_url": ARCHIVE_URL,
                        "archive_sha256": ARCHIVE_SHA256, "source_file_count": count,
                        "installed_at": datetime.now(timezone.utc).isoformat()}
            atomic_json(staging / ".afp-source.json", manifest)
            repo_path(staging)
            repo_path(destination)
            if destination.exists():
                raise FileExistsError("AFP destination appeared during setup; leaving it unchanged")
            staging.rename(destination)
        thys = destination / "thys"
    roots = data.get("session_roots", [])
    if thys.resolve() not in [repo_path(path) for path in roots]:
        roots = [*roots, thys.relative_to(repo_path(".")).as_posix()]
    data["session_roots"] = roots
    atomic_json(config_path, data)
    print("AFP sources ready: " + str(thys), flush=True)
    print("Updated session_roots in " + str(config_path), flush=True)
    print("This installs sources; run native lab_preflight to check Isabelle compatibility.", flush=True)
    return {"destination": str(destination), "session_roots": roots, **manifest}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root")
    parser.add_argument("--config", default=DEFAULT_CONFIG)
    parser.add_argument("--destination", default=DEFAULT_DESTINATION)
    parser.add_argument("--archive", default=DEFAULT_ARCHIVE, help="Pinned archive cache or an already downloaded copy")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    install(config_path=args.config, destination=args.destination, archive_path=args.archive)


if __name__ == "__main__":
    main()
