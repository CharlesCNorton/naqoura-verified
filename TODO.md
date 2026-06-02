1. Derive the Qana / Block 9 prospect point(s) and the Qana-1 (31/1B) well location as rational unit vectors (Wolfram, within 1.3e-13 of WGS84).
2. Derive Line 1 (Israel 2011 deposit: points 34, 35, 1).
3. Derive Line 23 (Lebanon Decree 6433: points 20-23 and the full chain); OCR the scanned decree PDF via Wolfram TextRecognize since pdftoppm is unavailable.
4. Derive Line 29 (Lebanese army technical line).
5. Derive the Block 9 and Block 72 boundary polygons.
6. Derive the Lebanon-Israel-Cyprus tripoint near P4 and the Cyprus EEZ line.
7. Derive the Tanin and Karish North field points.
8. Derive the Ras Naqoura land terminus and the near-shore buoy-line points.
9. Generalize the hand-unrolled four points to a list-based polyline; reprove totality and soundness generically.
10. Prove that meridian / east_of / west_of actually track longitude ordering.
11. Prove the three longitude bands tile [lon P4, lon P1] with no gaps and no overlaps.
12. Prove band-edge behavior on a shared meridian (verdict agrees or is handled).
13. Prove the side orientation is consistent across nseg1/nseg2/nseg3 (Israel positive on each).
14. Prove monotonicity (longitude strictly decreasing P1 to P4) in Coq, not just via Wolfram.
15. Prove the line is simple (segments do not cross).
16. Prove that p1-p4 are unit vectors, or that the sign test needs no exact unit norm.
17. Prove Karish North lies on the Israeli side.
18. Prove Tanin lies on the Israeli side.
19. Prove the Qana / Block 9 prospect straddles the MBL (a committed point on each side).
20. Prove the Qana-1 well is classified Lebanese.
21. Prove the line nesting: Line 1 north of Line 23 north of Line 29.
22. Prove the agreed MBL lies strictly between Line 1 and Line 29 at sampled longitudes.
23. Strengthen totality: on the in-band seaward region the verdict is never Indeterminate except exactly on the line.
24. Prove the shared-line fact: Lebanon's Annex A points equal Israel's Annex B points.
25. Prove supersession: the agreed points replace Lebanon's 20-23 and Israel's 34/35/1.
26. Prove the deferred segment: decide returns Indeterminate landward of P1.
27. Turn clearance into an angular/metric distance (clearance = |nseg| * sin(angular distance)); derive a "kilometers inside" figure for each committed feature.
28. Bound the WGS84-versus-sphere model error and show it is below the clearance of every named feature.
29. Bound the rational-rounding error of the boundary points (about 1.3e-13) and show it never flips a committed verdict.
30. Prove the robustness envelope: any point with clearance greater than (rounding error + model error) has a verdict provably correct on the true ellipsoid.
31. Add the front-end wrapper: geodetic (degrees lat, lon) to rational unit vector with documented rounding, feeding decide.
32. Add an OCaml test harness exercising decide and clearance on Karish, Qana, and boundary-adjacent points.
33. Add a build script (coqc + extraction + ocamlfind demo) and confirm the extracted OCaml matches the Coq verdicts.
34. Encode the agreement's section structure (MBL, seaward-only scope, Prospect/Block 9 arrangement, dispute resolution) as definitions.
35. Encode Section 2F (Israel takes no deposit crossing the MBL) as a property.
36. Optionally relate the MBL to the UNCLOS Article 74/83 equidistance line (needs coastal baseline points).
37. Write the README: what is proven, the axiom-free claim, build steps, data provenance and tolerances.
38. Commit the Wolfram derivation scripts as provenance (move into a wolfram/ directory; remove _ck.v).
39. Add a .gitignore for Coq build artifacts and the extracted OCaml.
40. Add the LICENSE file (MIT is declared in the header).
41. Add citations: Exchange of Letters, Decree 6433, UN MZN notices, field and well sources.
42. Add a Print Assumptions audit over all theorems confirming closure under the global context.
43. Write one reproducible Wolfram script that re-derives and cross-checks every rational constant against true WGS84.
44. Run an independent Wolfram recomputation (geodesic distance to each segment) confirming every Coq verdict and clearance sign.
