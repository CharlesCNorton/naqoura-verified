(* Axiom audit of the real-geometry bridge (Module Bridge in naqoura_line.v),
   stratified by axiom weight.  Every theorem interprets the rational geofence in
   spherical geometry over Coq's classical reals, so each depends on some subset
   of the standard real-number axioms; none introduces a project-specific axiom
   and none is admitted.  The footprint is not uniform, and the split is the
   point: the operative soundness claim -- that the verdict is the real
   orientation test -- rests on strictly fewer axioms than the metric (kilometre)
   claims.  Run:  coqc naqoura_line.v && coqc audit_bridge.v

   GROUP A (orientation soundness) depends on ONLY
     ClassicalDedekindReals.sig_forall_dec
     FunctionalExtensionality.functional_extensionality_dep
   i.e. the bare machinery of Q2R and the order on R: no excluded middle, no
   sig_not_dec.  This is the legally operative layer -- which side of the line a
   position lies on. *)
Require Import naqoura_line.

Print Assumptions Bridge.Q2R_dot.
Print Assumptions Bridge.verdict_real_Israeli.
Print Assumptions Bridge.verdict_real_Lebanese.
Print Assumptions Bridge.dot_circle_bound.
Print Assumptions Bridge.decide_Israeli_real_meaning.
Print Assumptions Bridge.decide_Lebanese_real_meaning.

(* GROUP B (geodetic embedding) adds ClassicalDedekindReals.sig_not_dec (still no
   excluded middle): the sin/cos embedding produces unit vectors. *)
Print Assumptions Bridge.ecef_unit_is_unit.

(* GROUP C (metric layer) adds Classical_Prop.classic and sig_not_dec on top of
   Group A: the kilometre distance bounds, which go through acos / asin / sqrt
   and the classical real analysis those carry.  This is where, and the only
   where, excluded middle enters. *)
Print Assumptions Bridge.boundary_far_from_position.
Print Assumptions Bridge.karish_min_distance_km.
Print Assumptions Bridge.boundary_far_from_position_gen.
Print Assumptions Bridge.feature_km.
Print Assumptions Bridge.tanin_distance_km.
Print Assumptions Bridge.karish_distance_km.
Print Assumptions Bridge.karish_north_distance_km.
Print Assumptions Bridge.point1_distance_km.
Print Assumptions Bridge.qana_isr_distance_km.
Print Assumptions Bridge.qana_leb_distance_km.
Print Assumptions Bridge.foot_on_circle.
Print Assumptions Bridge.whole_boundary_far.
Print Assumptions Bridge.karish_whole_boundary_km.
Print Assumptions Bridge.equidistant_real_meaning.
