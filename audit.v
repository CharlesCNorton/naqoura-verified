(* Axiom audit of the rational kernel.  Every theorem below must report
   "Closed under the global context": the decision procedure, its certificates,
   the generic well-formedness lemmas, the feature verdicts, the robustness /
   rounding / model-error envelope, and the agreement structure contain no
   axioms and no admitted lemmas, and the geofence and clearance extract to
   runnable OCaml.  The real-geometry interpretation layer is audited
   separately in audit_bridge.v (it depends only on Coq's standard classical
   real-number axioms).  Run:  coqc naqoura_line.v && coqc audit.v *)

Require Import naqoura_line.

(* Core decision procedure. *)
Print Assumptions decide_total.
Print Assumptions decide_Israeli_sound.
Print Assumptions decide_Lebanese_sound.
Print Assumptions decide_exclusive.
Print Assumptions decide_committed_clearance_pos.

(* Boundary-data certificates (unit norm, nondegeneracy). *)
Print Assumptions boundary_points_near_unit.
Print Assumptions feature_points_near_unit.
Print Assumptions nseg_nondegenerate.

(* Geometry, scale invariance, ordering, tiling, simplicity, generic polyline. *)
Print Assumptions meridian_eq_cross_vz.
Print Assumptions decide_scale_invariant.
Print Assumptions clearance_scale.
Print Assumptions mbl_monotone_west.
Print Assumptions bands_cover.
Print Assumptions bands_share_only_p2.
Print Assumptions bands_share_only_p3.
Print Assumptions bands_meet_on_shared.
Print Assumptions mbl_is_west_chain.
Print Assumptions decide_seam_well_defined.
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

(* Metric bounds, robustness, rounding propagation, model-error envelope. *)
Print Assumptions nseg_norm_bounds.
Print Assumptions verdict_robust_Israeli.
Print Assumptions verdict_robust_Lebanese.
Print Assumptions clearance_exceeds_rounding_budget.
Print Assumptions karish_rounding_robust.
Print Assumptions dot_diff_abs_bound.
Print Assumptions rounding_propagation_within_budget.
Print Assumptions side_det_robust.
Print Assumptions karish_query_robust.
Print Assumptions point1_query_robust.
Print Assumptions committed_robust_to_model_and_rounding.

(* Wrapper and agreement structure. *)
Print Assumptions of_ecef_scale_free.
Print Assumptions naqoura_section_2F.
Print Assumptions prospect_straddle_no_unilateral.
