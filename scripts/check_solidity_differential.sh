#!/bin/sh
set -eu
# Keep the caller's Lake workspace: this script also runs from downstream repos.
verity_test_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
verity_test_venv=".lake/slice-testing-venv"
if [ ! -x "$verity_test_venv/bin/python" ]; then
    python3 -m venv "$verity_test_venv"
fi
verity_test_requirements="$verity_test_root/scripts/solidity_differential/requirements.txt"
verity_test_stamp="$verity_test_venv/.requirements.sha256"
verity_test_digest=$(python3 -c 'import hashlib, sys; print(hashlib.sha256(open(sys.argv[1], "rb").read()).hexdigest())' "$verity_test_requirements")
# Parallel mutation workers share this venv: install only when requirements change.
if [ ! -f "$verity_test_stamp" ] || [ "$(cat "$verity_test_stamp")" != "$verity_test_digest" ]; then
    "$verity_test_venv/bin/python" -m pip install --disable-pip-version-check -q -r "$verity_test_requirements"
    printf '%s\n' "$verity_test_digest" > "$verity_test_stamp"
fi
python3 "$verity_test_root/scripts/setup_solc_import.py" --output .lake/solidity-import/solc-0.8.34
python3 "$verity_test_root/scripts/setup_solc_import.py" --version 0.8.10 --output .lake/solidity-import/solc-0.8.10
exec "$verity_test_venv/bin/python" "$verity_test_root/scripts/solidity_import_differential.py" "$@"
