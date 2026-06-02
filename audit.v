(* Axiom audit: every theorem of naqoura_line must be closed under the global
   context (no axioms, no admits).  Run:  coqc naqoura_line.v && coqc audit.v
   Each Print Assumptions below must report "Closed under the global context". *)

Require Import naqoura_line.

(* Core decision procedure. *)
Print Assumptions decide_total.
Print Assumptions decide_Israeli_sound.
Print Assumptions decide_Lebanese_sound.
Print Assumptions decide_exclusive.
Print Assumptions decide_committed_clearance_pos.

(* Geometry, scale invariance, ordering, tiling, simplicity, generic polyline. *)
Print Assumptions meridian_eq_cross_vz.
Print Assumptions decide_scale_invariant.
Print Assumptions clearance_scale.
Print Assumptions mbl_monotone_west.
Print Assumptions bands_cover.
Print Assumptions bands_share_only_p2.
Print Assumptions bands_share_only_p3.
Print Assumptions decide_band1_indeterminate_iff.
Print Assumptions decide_poly_total.
Print Assumptions decide_poly_sound.
Print Assumptions decide_poly_is_decide.

(* Features, orientation, lines, nesting, supersession, deferred segment. *)
Print Assumptions karish_israeli.
Print Assumptions karish_north_israeli.
Print Assumptions tanin_israeli.
Print Assumptions israeli_fields_off_line.
Print Assumptions qana_straddles.
Print Assumptions qana_well_lebanese.
Print Assumptions ras_naqoura_deferred.
Print Assumptions orientation_consistent.
Print Assumptions shared_line.
Print Assumptions supersession.
Print Assumptions mbl_between_line1_and_line29.
Print Assumptions endpoint_latitude_order.
Print Assumptions cyprus_line_monotone_north.
Print Assumptions seaward_terminus_on_line.

(* Metric, robustness envelope, wrapper, agreement structure. *)
Print Assumptions nseg_norm_bounds.
Print Assumptions verdict_robust_Israeli.
Print Assumptions verdict_robust_Lebanese.
Print Assumptions clearance_exceeds_rounding_budget.
Print Assumptions karish_rounding_robust.
Print Assumptions of_ecef_scale_free.
Print Assumptions naqoura_section_2F.
