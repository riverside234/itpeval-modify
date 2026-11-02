"""Prepare pinned original PISA sources/stubs and optionally build its server JAR."""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import time

from ..common import repo_path, validate_layout
from .runtime import DspConfig, PACKAGE, PISA_COMMIT, RUNTIME_DIR, OwnedProcess, hash_file, source_hash


def prepare(config, *, build=False):
    root = config.root
    if not root.exists():
        root.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "clone", "https://github.com/albertqjiang/Portal-to-ISAbelle.git", str(root)], check=True)
        subprocess.run(["git", "-C", str(root), "checkout", "--detach", PISA_COMMIT], check=True)
    actual = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"], check=True, capture_output=True, text=True).stdout.strip()
    if actual != PISA_COMMIT:
        raise ValueError("Existing PISA checkout has a different revision. Preserve local changes, then check out " + PISA_COMMIT)
    expected = json.loads((PACKAGE / "upstream/pisa_sources.json").read_text(encoding="utf-8"))
    for name, digest in expected.items():
        if source_hash(root / name) != digest:
            raise ValueError("PISA source does not match the pinned revision: " + name)
    original = subprocess.run(["git", "-C", str(root), "show", PISA_COMMIT + ":build.sbt"],
                              check=True, capture_output=True, text=True).stdout
    # Upstream uses a literal {$PWD} URL. Point to the same bundled Scala-Isabelle JAR.
    old = 'from "file:{$PWD}/lib/scala-isabelle_2.13.jar"'
    new = 'from ((baseDirectory.value / "lib" / "scala-isabelle_2.13.jar").toURI.toString)'
    if old not in original:
        raise ValueError("unexpected upstream build.sbt")
    patched = original.replace(old, new)
    path = root / "build.sbt"
    if path.read_text(encoding="utf-8") not in {original, patched}:
        raise ValueError("build.sbt has unrelated edits; preserve them before preparing the pinned server")
    path.write_text(patched, encoding="utf-8")
    config.generated.mkdir(parents=True, exist_ok=True)
    subprocess.run([sys.executable, "-m", "grpc_tools.protoc", "-I", str(root / "src/main/protobuf"),
                    "--python_out=" + str(config.generated), "--grpc_python_out=" + str(config.generated),
                    str(root / "src/main/protobuf/server.proto")], check=True)
    print("Prepared original PISA sources and current Python protobuf bindings.")
    if build:
        if os.name == "nt":
            raise RuntimeError("Build PISA on the Linux lab host")
        env = config.environment()
        java = Path(shutil.which(config.java_bin) or config.java_bin).resolve()
        version = subprocess.run([str(java), "-version"], capture_output=True, text=True, check=True)
        if 'version "11.' not in version.stderr + version.stdout and 'version "11"' not in version.stderr + version.stdout:
            raise ValueError("Build original PISA with Java 11")
        env["JAVA_HOME"] = str(java.parent.parent)
        cache = repo_path(RUNTIME_DIR) / "build_cache"
        env["COURSIER_CACHE"] = str(cache / "coursier")
        env["SBT_OPTS"] = " ".join(shlex.quote(x) for x in (
            "-Dsbt.global.base=" + str(cache / "sbt"), "-Dsbt.boot.directory=" + str(cache / "boot"),
            "-Dsbt.ivy.home=" + str(cache / "ivy")))
        log = root / "pisa-build.log"
        code = OwnedProcess(["sbt", "assembly"], directory=root, env=env, log_path=log,
                            timeout_s=7200, deadline=time.monotonic()+7200).run()
        if code or not config.jar.is_file():
            raise RuntimeError("PISA assembly failed; inspect " + str(log))
        stamp = {"commit": PISA_COMMIT, "sources": expected, "jar_sha256": hash_file(config.jar),
                 "build_sbt_sha256": source_hash(path), "generated_client_sha256":
                    {name: hash_file(config.generated / name) for name in ("server_pb2.py", "server_pb2_grpc.py")}}
        (root / "pisa-build.json").write_text(json.dumps(stamp, indent=2) + "\n", encoding="utf-8")
        print("Built " + str(config.jar))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-root")
    parser.add_argument("--config", default="eval/configs/hol_light_to_isabelle/v2_dsp_2021.example.json")
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--print-env", action="store_true", help="Print only repo-local Isabelle environment exports")
    args = parser.parse_args()
    validate_layout(args.expected_root)
    config = DspConfig.load(args.config)
    if args.print_env:
        env = config.environment()
        for name in sorted(k for k in os.environ if k.startswith("ISABELLE_") or k == "BASH_ENV"):
            print("unset " + shlex.quote(name))
        for name in ("USER_HOME", "ISABELLE_IDENTIFIER", "TMPDIR", "TMP", "TEMP"):
            print("export " + name + "=" + shlex.quote(env[name]))
        return
    prepare(config, build=args.build)


if __name__ == "__main__":
    main()
