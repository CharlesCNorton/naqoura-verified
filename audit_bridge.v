(* Axiom audit of the real-geometry bridge (Module Bridge in naqoura_line.v).
   These theorems interpret the rational geofence in spherical geometry over
   Coq's classical reals, so they depend on the standard real-number axioms of
   the Coq/Rocq Reals library (e.g. the completeness/total-order axioms behind
   R, sin, cos, asin, acos, sqrt).  They contain NO project-specific axioms and
   NO admitted lemmas: the only assumptions are those of the standard library.
   Run:  coqc naqoura_line.v && coqc audit_bridge.v *)

Require Import naqoura_line.

(* Q2R homomorphism and the verdict-as-real-triple-product sign agreement. *)
Print Assumptions Bridge.Q2R_dot.
Print Assumptions Bridge.verdict_real_Israeli.
Print Assumptions Bridge.verdict_real_Lebanese.

(* Cauchy-Schwarz / Gram distance bound and the kilometre clearance. *)
Print Assumptions Bridge.dot_circle_bound.
Print Assumptions Bridge.boundary_far_from_position.
Print Assumptions Bridge.karish_min_distance_km.

(* Precise geometric meaning of a committed verdict. *)
Print Assumptions Bridge.decide_Israeli_real_meaning.
Print Assumptions Bridge.decide_Lebanese_real_meaning.

(* Coq-side geodetic embedding, non-unit distance bound, per-feature kilometre
   clearances applied to the features' WGS84 unit positions. *)
Print Assumptions Bridge.ecef_unit_is_unit.
Print Assumptions Bridge.boundary_far_from_position_gen.
Print Assumptions Bridge.feature_km.
Print Assumptions Bridge.tanin_distance_km.
Print Assumptions Bridge.karish_distance_km.
Print Assumptions Bridge.karish_north_distance_km.
Print Assumptions Bridge.point1_distance_km.
Print Assumptions Bridge.qana_isr_distance_km.
Print Assumptions Bridge.qana_leb_distance_km.

(* Proximity (foot of perpendicular) and whole-boundary distance. *)
Print Assumptions Bridge.foot_on_circle.
Print Assumptions Bridge.whole_boundary_far.
Print Assumptions Bridge.karish_whole_boundary_km.

(* UNCLOS Art. 74/83 equidistance: equidistant positions are at equal
   great-circle distance from the two basepoints. *)
Print Assumptions Bridge.equidistant_real_meaning.
