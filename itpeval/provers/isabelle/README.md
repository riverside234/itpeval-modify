# Isabelle adapter

Files:
- `install.sh`: downloads Isabelle into `ITPEVAL_PREFIX/isabelle` and links `isabelle` into `ITPEVAL_PREFIX/bin/isabelle`.
- `check.sh`: builds the bundled hello session.
- `hello/`: minimal session (`ROOT`) and theory (`Hello.thy`) used for the smoke test.

Overrides:
- `ITPEVAL_ISABELLE_VERSION` (default: `Isabelle2024`)
- `ITPEVAL_ISABELLE_BASE_URL` (defaults to the official `website-<version>/dist` URL)

