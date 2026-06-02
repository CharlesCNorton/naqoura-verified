#!/usr/bin/env bash
# Build, verify, extract, and self-test the Naqoura Line geofence.
# Requires Rocq/Coq 9 (coqc) and an OCaml native compiler (ocamlopt) on PATH;
# e.g. inside an opam switch:  eval "$(opam env)"  before running.
set -euo pipefail
cd "$(dirname "$0")"

echo "[1/4] Compiling and extracting (coqc naqoura_line.v -> naqoura.ml)"
coqc naqoura_line.v

echo "[2/4] Axiom audit (every theorem must be Closed under the global context)"
coqc audit.v 2>&1 | { ! grep -i 'axiom\|admit' ; } \
  && echo "      audit clean: no axioms, no admits"

echo "[3/4] Building extracted OCaml + self-test harness"
ocamlopt -w -a naqoura.mli naqoura.ml selftest.ml -o naqoura_selftest

echo "[4/4] Running self-test (extracted verdicts vs Coq theorems)"
./naqoura_selftest

echo "OK."
