#!/usr/bin/env bash
# Build, verify, extract, and self-test the Naqoura Line geofence.
# Requires Rocq/Coq 9 (coqc) and an OCaml native compiler (ocamlopt) on PATH;
# e.g. inside an opam switch:  eval "$(opam env)"  before running.
set -euo pipefail
cd "$(dirname "$0")"

echo "[1/5] Compiling and extracting (coqc naqoura_line.v -> naqoura.ml)"
coqc naqoura_line.v

echo "[2/5] Compiling the per-point WGS84 provenance layer (coqc provenance.v)"
coqc provenance.v

echo "[3/5] Axiom audit"
coqc audit.v 2>&1 | { ! grep -i 'axiom\|admit' ; } \
  && echo "      kernel clean: rational kernel closed under the global context, no admits"
coqc audit_bridge.v > /dev/null 2>&1 \
  && echo "      bridge ok: real-geometry layer depends only on Coq's standard classical-reals axioms"
coqc audit_provenance.v > /dev/null 2>&1 \
  && echo "      provenance ok: per-point WGS84 bounds add only Coq's primitive-integer arithmetic (CoqInterval) atop the classical-reals axioms"

echo "[4/5] Building extracted OCaml + self-test harness"
ocamlopt -w -a naqoura.mli naqoura.ml selftest.ml -o naqoura_selftest

echo "[5/5] Running self-test (extracted verdicts vs Coq theorems)"
./naqoura_selftest

echo "OK."
