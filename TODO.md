All formalization items are complete. The development compiles under Rocq/Coq 9,
is closed under the global context (no axioms, no admits; see audit.v), extracts
to OCaml, and passes the extracted self-test (selftest.ml). See README.md for the
theorem inventory and wolfram/derive.wl for coordinate provenance and the
independent geodesic cross-check.

Items realized:
1. Qana/Block 9 prospect and the 31/1B well, as rational unit vectors (qana_leb, qana_isr).
2. Line 1 (Israel) seaward endpoint point1_israel; near-shore points 34, 35 not in the public record consulted.
3. Line 23 endpoint Point 23, derived exact and proved equal to MBL P4 (line23_endpoint_is_P4).
4. Line 29 anchored by the Karish field it was drawn to split (exact Point 29 was never deposited).
5. Block 9 / Block 72 straddle represented by points either side of the line (qana_straddles).
6. Cyprus-Lebanon line (points 1-6) and the deferred tripoint (cyprus_line_monotone_north, seaward_terminus_on_line).
7. Karish North and Tanin field points (karish_north, tanin).
8. Ras Naqoura land terminus and the deferred near-shore segment (ras_naqoura, ras_naqoura_deferred).
9. Generic list-based polyline with generic totality and soundness (decide_poly_total, decide_poly_sound, decide_poly_is_decide).
10. meridian / east_of / west_of track longitude ordering (meridian_eq_cross_vz, meridian_is_cross_z).
11. The three bands tile the seaward span with no gaps (bands_cover).
12. Band-edge behavior on a shared meridian (bands_share_only_p2, bands_share_only_p3).
13. Orientation consistent across all three segments (orientation_consistent).
14. Longitude strictly decreasing P1 to P4 (mbl_monotone_west).
15. The line is simple, segments interior-disjoint (bands_share_only_p2/p3).
16. The sign test needs no exact unit norm (decide_scale_invariant, clearance_scale, of_ecef_scale_free).
17. Karish North on the Israeli side (karish_north_israeli).
18. Tanin on the Israeli side (tanin_israeli).
19. The Qana prospect straddles the MBL (qana_straddles).
20. The Qana 31/1B well classified Lebanese (qana_well_lebanese).
21. Line nesting Line 1 north of Line 23 north of Line 29 (mbl_between_line1_and_line29, endpoint_latitude_order).
22. The MBL lies strictly between Line 1 and Line 29 (side test at each point's own longitude).
23. Within a band, Indeterminate only exactly on the line (decide_band1_indeterminate_iff).
24. Lebanon Annex A equals Israel Annex B (shared_line).
25. The agreed points supersede Lebanon 20-23 and Israel 34/35/1 (supersession).
26. Landward of P1 the verdict is Indeterminate (ras_naqoura_deferred, seaward_terminus_on_line).
27. Clearance linked to angular/metric distance via segment-normal bounds (nseg_norm_bounds); kilometre figures in wolfram/derive.wl.
28. Model error (sphere vs ellipsoid) handled by the relative side test and the robustness envelope.
29. Rational rounding error bounded below every committed clearance (clearance_exceeds_rounding_budget).
30. Robustness envelope: any perturbation below the clearance preserves the verdict (sign_robust_*, verdict_robust_*).
31. Front-end ECEF wrapper with the scale-free contract (of_ecef, of_ecef_scale_free).
32. OCaml test harness over Karish, Qana and boundary-adjacent points (selftest.ml).
33. Build script: coqc, extraction, OCaml build, extracted-vs-Coq self-test (build.sh).
34. The agreement structure encoded (Agreement record, naqoura_agreement).
35. Section 2F encoded as the genuine straddle (section_2F, naqoura_section_2F).
36. The agreed line recorded as the equitable delimitation (equitable_delimitation); full Article 74/83 equidistance needs coastal baselines, out of scope.
37. README written (this repo).
38. Wolfram scripts moved to wolfram/; _ck.v removed.
39. .gitignore for build artifacts and extracted OCaml.
40. LICENSE (MIT).
41. Citations (README).
42. Print Assumptions audit over all theorems (audit.v).
43. Reproducible Wolfram re-derivation and cross-check of every constant (wolfram/derive.wl).
44. Independent Wolfram geodesic recomputation of every verdict and clearance (wolfram/derive.wl).
