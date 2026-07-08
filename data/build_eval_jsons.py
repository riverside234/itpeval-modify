from __future__ import annotations
import json
from pathlib import Path

DATA = Path(__file__).resolve().parent   # itp-interop/data/
REPO = DATA.parent                       # itp-interop/
OUT  = REPO / "eval" / "data"

ITPS = ("hol-light", "isabelle", "lean4", "rocq")
EXT  = {"hol-light": ".ml", "isabelle": ".thy", "lean4": ".lean", "rocq": ".v"}


def _four_way_stems(dirs: dict[str, Path]) -> list[str]:
    """Return sorted stems present in all 4 ITP directories."""
    per_itp = {
        itp: {p.stem for p in d.glob(f"*{EXT[itp]}")} if d.exists() else set()
        for itp, d in dirs.items()
    }
    return sorted(per_itp["hol-light"] & per_itp["isabelle"]
                  & per_itp["lean4"] & per_itp["rocq"])


def _collect_babel_formal(mode: str, offset: int) -> tuple[list[dict], int]:
    src_dir = DATA / "babel-formal" / mode
    topics = sorted(p.stem for p in (src_dir / "lean4").glob(f"*{EXT['lean4']}"))
    rows = []
    for i, topic in enumerate(topics, start=1):
        tid = offset + i
        for itp in ITPS:
            f = src_dir / itp / (topic + EXT[itp])
            if not f.exists():
                raise FileNotFoundError(f"Missing: {f}")
            rows.append({
                "theorem_id": tid,
                "title":      topic,
                "source":     "babel-formal",
                "tier":       "a",
                "prover":     itp,
                "content":    f.read_text(),
            })
    return rows, offset + len(topics)


def _collect_hundred_theorems(mode: str, offset: int) -> tuple[list[dict], int]:
    base = DATA / "hundred-theorems" / mode
    dirs = {itp: base / itp for itp in ITPS}
    stems = _four_way_stems(dirs)
    rows = []
    for i, stem in enumerate(stems, start=1):
        tid = offset + i
        for itp in ITPS:
            f = dirs[itp] / (stem + EXT[itp])
            rows.append({
                "theorem_id": tid,
                "title":      stem,
                "source":     "hundred-theorems",
                "tier":       "b",
                "prover":     itp,
                "content":    f.read_text(),
            })
    return rows, offset + len(stems)


def _collect_minif2f(mode: str, offset: int) -> tuple[list[dict], int]:
    base = DATA / "minif2f" / mode

    itp_stems: dict[str, set[str]] = {itp: set() for itp in ITPS}
    stem_split: dict[str, str] = {}
    stem_path: dict[str, dict[str, Path]] = {}

    for itp in ITPS:
        for split in ("test", "valid"):
            d = base / itp / split
            if not d.exists():
                continue
            for p in d.glob(f"*{EXT[itp]}"):
                itp_stems[itp].add(p.stem)
                stem_split[p.stem] = split
                stem_path.setdefault(p.stem, {})[itp] = p

    common = sorted(
        itp_stems["hol-light"] & itp_stems["isabelle"]
        & itp_stems["lean4"] & itp_stems["rocq"]
    )
    rows = []
    for i, stem in enumerate(common, start=1):
        tid = offset + i
        for itp in ITPS:
            rows.append({
                "theorem_id": tid,
                "title":      stem,
                "source":     "minif2f",
                "tier":       "b",
                "split":      stem_split[stem],
                "prover":     itp,
                "content":    stem_path[stem][itp].read_text(),
            })
    return rows, offset + len(common)


def build_all() -> None:
    OUT.mkdir(parents=True, exist_ok=True)

    # stmts.json: babel-formal + hundred-theorems + minif2f (4-way intersection)
    offset = 0
    bf_s, offset = _collect_babel_formal("stmts", offset)
    ht_s, offset = _collect_hundred_theorems("stmts", offset)
    mf_s, offset = _collect_minif2f("stmts", offset)
    stmts_rows = bf_s + ht_s + mf_s
    n_stmts = offset

    (OUT / "stmts.json").write_text(json.dumps(stmts_rows, ensure_ascii=False))
    print(f"stmts.json:  {len(stmts_rows):>5} records  ({n_stmts} theorems)")

    # proofs.json: babel-formal + hundred-theorems only (4-way intersection)
    offset = 0
    bf_p, offset = _collect_babel_formal("proofs", offset)
    ht_p, offset = _collect_hundred_theorems("proofs", offset)
    proofs_rows = bf_p + ht_p
    n_proofs = offset

    (OUT / "proofs.json").write_text(json.dumps(proofs_rows, ensure_ascii=False))
    print(f"proofs.json: {len(proofs_rows):>5} records  ({n_proofs} theorems)")

    # Sanity checks
    assert len(stmts_rows) == n_stmts * len(ITPS)
    assert len(proofs_rows) == n_proofs * len(ITPS)
    assert n_stmts == 390, f"Expected 390 stmts theorems, got {n_stmts}"
    assert n_proofs == 74, f"Expected 74 proof theorems, got {n_proofs}"

    # theorem_ids must be consistent between stmts and proofs
    proof_keys = {(r["theorem_id"], r["prover"], r["title"]) for r in proofs_rows}
    stmt_keys  = {(r["theorem_id"], r["prover"], r["title"]) for r in stmts_rows}
    assert proof_keys <= stmt_keys, "Every proof record must have a corresponding stmt"

    print("All checks passed.")


if __name__ == "__main__":
    build_all()
