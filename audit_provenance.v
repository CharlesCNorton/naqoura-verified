(* Axiom audit of the per-point WGS84 provenance layer (provenance.v).

   Each theorem depends on the standard classical real-number axioms (the same
   ones the bridge uses) together with Coq's primitive 63-bit integer arithmetic
   (PrimInt63 / Uint63Axioms), which CoqInterval uses for exact multi-precision
   interval computation.  Those primitive-integer axioms are part of Coq's
   native-arithmetic trusted base, realized by the OCaml runtime; they are not
   classical-logic axioms, and they are confined to this layer (the kernel is
   axiom-free; the bridge uses only the classical-reals axioms).  There are NO
   project-specific axioms and NO admitted lemmas.

   Run:  coqc naqoura_line.v && coqc provenance.v && coqc audit_provenance.v *)

Require Import provenance.

Print Assumptions p1_matches_wgs84_dms.
Print Assumptions p2_matches_wgs84_dms.
Print Assumptions p3_matches_wgs84_dms.
Print Assumptions p4_matches_wgs84_dms.
