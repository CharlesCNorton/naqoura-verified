1. The geofence is a side-of-extended-geodesic test, not a zone-membership test: add a seaward/extent gate and a bounded-region theorem so a committed verdict entails proximity to the line, not only the side of its great circle.
2. Bound the seaward (western) extent beyond P4; the band-3 region is open-ended with the tripoint deferred.
3. Certify positions within the model+rounding budget of the line; committed_robust_to_model_and_rounding excludes the band-1 witnesses (clearance below 1e-7), so near-line positions are not robust against the spherical model.
4. Prove the ellipsoid model-error bound inside Coq rather than trusting derive.wl; Coq has only the conditional envelope plus the rational budget, while the actual spherical-vs-WGS84 determinant difference is certified only in Wolfram.
5. Thread the near-unit (1e-12) gap through the distance theorem; boundary_far_from_position assumes an exactly unit position, so the kilometre bound applies to the idealized point, not directly to the rational vector.
6. Add per-feature kilometre corollaries for Tanin, Point 1, Karish North, and the Qana points; only Karish has a Coq instance.
7. Prove a distance bound to the whole three-segment boundary (minimum over segments), not only to a single segment's great circle.
8. Replace the Line 29 proxy (line29_anchor := karish) with the actual Line 29 endpoint from the UKHO / Lebanese army study.
9. Replace the representative Qana points with sourced Block 9 / Block 72 / 31-1B coordinates if they enter the public record (the well was dry and its location was unpublished).
10. Add Israel's points 34/35 and Lebanon's points 20-22 to model the full superseded chains, and verify P4 against Decree 6433 Point 23 in the primary UN-deposited list (a scanned Arabic annex).
11. Confirm the p1-p4 DMS inputs against the primary UN MZN deposit rather than secondary compilations.
12. Prove generic tiling and coverage (west_chain implies gapless, interior-disjoint bands), generalizing the concrete bands_cover and mbl_monotone_west; this needs a longitude-transitivity lemma.
13. Prove a general landward-deferred theorem for the whole deferred region, generalizing ras_naqoura_deferred and seaward_terminus_on_line.
14. Prove a general orientation lemma that a positive triple product is the southern (lower-latitude) side, replacing the witness-based orientation_consistent.
15. Relate the agreed line to UNCLOS Articles 74/83 (equidistance and equity), beyond restating equitable_delimitation := annex_A; this needs coastal baseline points.
16. Model the operative Section 2F mechanism (Lebanon's operator develops, Israel remunerated) beyond the geometric straddle.
17. Reduce extraction trust; Coq's extraction is unverified and selftest.ml checks only eight points, so consider a verified extraction path or broader test coverage.
18. Optionally reduce the bridge's reliance on classical reals; its eight geometric theorems use excluded middle, functional extensionality, and the Dedekind-reals axioms.
19. The geodetic-to-ECEF conversion stays outside Coq (trigonometry is not in Q); only the resulting rationals are certified near-unit and the sign tests exact.
