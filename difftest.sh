#!/usr/bin/env bash
# Extended differential test: build the extracted geofence and check its verdicts
# against an independent Python oracle over a large pseudo-random sweep.
# Requires Rocq/Coq 9, an OCaml native compiler, and python3.
# Usage:  bash difftest.sh [N]      (default N = 50000 positions)
set -euo pipefail
cd "$(dirname "$0")"

echo "[1/3] Extracting (coqc naqoura_line.v -> naqoura.ml)"
coqc naqoura_line.v

echo "[2/3] Building the differential-test runner (difftest.ml)"
ocamlopt -w -a naqoura.mli naqoura.ml difftest.ml -o difftest

echo "[3/3] Differential test vs the independent oracle"
python3 difftest.py "${1:-50000}"
