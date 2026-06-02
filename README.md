# The Naqoura Line

*A machine-checked geofence over the 2022 Israel-Lebanon maritime boundary.*

A sound, total, extractable decision procedure that places any seaward position
on the Israeli or Lebanese side of the agreed Maritime Boundary Line (MBL), with
a certified clearance, and proves the legal geometry of the settlement: the
straddling Qana prospect, the supersession of the parties' 2011 claim lines, the
classification of the offshore gas fields, and the deferral of the near-shore
segment. The decision kernel is exact rational arithmetic, contains no axioms
and no admitted lemmas, and extracts to OCaml. A real-geometry layer then
interprets the kernel in genuine spherical geometry, proving what the rational
verdict and clearance mean: the verdict is the sign of a real scalar triple
product (a side-of-great-circle test), and a positive clearance is a real lower
bound, in kilometres, on the distance to the boundary. A third, separately
audited layer machine-checks each agreed point's rational coordinates against
the transcendental sine and cosine of its deposited degree-minute-second
position, so the boundary data itself is verified inside Coq.

**Author:** Charles C. Norton | June 2026 | License: MIT

## Background

On 27 October 2022 Israel and Lebanon settled their maritime boundary by an
Exchange of Letters mediated by the United States. The agreed MBL is four points
in the WGS84 datum joined by geodesics, deposited identically by Lebanon
(Annex A) and Israel (Annex B). The line is fixed seaward of its easternmost
point; the near-shore segment (the buoy line, landward of point P1) was left
undelimited. The settlement followed Lebanon's 2011 Line 23 (Decree 6433) on the
seaward stretch, superseding both Lebanon's points 20-23 and Israel's points
34, 35, 1, and resolved the disputed wedge between Line 1 (Israel's 2011 claim)
and Line 23. A hydrocarbon prospect (Qana/Sidon) straddles the line between
Lebanon's Block 9 and Israel's Block 72; the agreement provides for it to be
developed by Lebanon's operator with Israel remunerated, and bars Israel from
taking any deposit that crosses the line.

## Method

**Rational kernel.** The sphere is modeled in exact rational arithmetic. A
position is a vector in `Q^3` (an ECEF / unit-sphere direction). The side of the
line is the sign of a determinant: for a geodesic segment from `A` to `B`, a
position `X` is on Lebanon's (north) side when `(A x B) . X < 0` and on Israel's
(south) side when `(A x B) . X > 0`. Segment selection is by longitude band,
itself an exact rational sign test against the meridian normals. Every
classification is a finite exact rational computation, decided by `vm_compute`,
and extracts to OCaml. The default kernel reads positions as directions on a
sphere; the same machinery, fed the true WGS84 ECEF directions (the spherical
direction with `z` scaled by `1 - e^2`), gives a native ellipsoidal geofence
`decide_ellip` that agrees with it on every committed feature (see below).

The only irrational data are the boundary and feature coordinates. These are
converted from their published WGS84 geodetic positions to rational unit vectors
once, in Wolfram (`wolfram/derive.wl`), each within `1.6e-13` of the true unit
vector (sub-millimeter). The data carries Coq certificates: every point is proved
a unit vector to within `1e-12` on the squared norm (`near_unit`), and the three
segment normals are proved nondegenerate. Because the verdict is the sign
of a determinant linear in `X`, it is invariant under positive rescaling of `X`
(`decide_scale_invariant`): a consumer need only supply the correct ECEF
direction, not an exactly normalized vector.

**Real-geometry bridge.** A closing layer (Coq `Module Bridge`) embeds the
rational vectors into `R^3` via `Q2R` and proves the kernel sound against real
spherical geometry: the rational determinant has the same sign as the real
scalar triple product (`verdict_real_Israeli` / `verdict_real_Lebanese`), so the
verdict is a genuine orientation test; and, via a Cauchy-Schwarz / Gram-
determinant argument, every point of a segment's great circle is at least
`R_earth * arcsin(clearance / |n|)` away from the position
(`boundary_far_from_position`), turning a positive clearance into a kilometre
distance. This layer uses Coq's standard real-number library (the classical-reals
axioms); the kernel remains axiom-free.

**Coordinate provenance.** A separate layer (`provenance.v`) closes the one gap
the rational certificates leave open: that each stored rational really is the
embedding of its published coordinate. For all four agreed points it proves, to
within `1e-12` on every component, that the rational matches the spherical ECEF
embedding `(cos lat cos lon, cos lat sin lon, sin lat)` of the point's deposited
degrees-minutes-seconds, with the latitude and longitude given as the exact
`/360000` degree rationals of the DMS. The transcendental bound is discharged by
CoqInterval's `interval` tactic (validated interval arithmetic with a Taylor
model for sine and cosine). This pins the data to the geodetic formula inside
Coq rather than only in Wolfram; it adds Coq's primitive-integer arithmetic
(used by CoqInterval) to the trusted base, kept out of the kernel and bridge by
confinement to this file.

## What is proven

Decision procedure (kernel):

- `decide_total`, `decide_Israeli_sound`, `decide_Lebanese_sound`,
  `decide_exclusive` - the geofence is total over the seaward extent and a
  committed verdict exhibits the determining segment and sign.
- `decide_committed_clearance_pos` - a committed verdict carries a strictly
  positive clearance (the position is strictly off the line).
- `decide_scale_invariant`, `of_ecef_scale_free` - the verdict depends only on
  direction; rounding the norm cannot change it.

Boundary-data certificates (kernel):

- `boundary_points_near_unit`, `feature_points_near_unit` - every boundary and
  feature point is a unit vector to within `1e-12` on the squared norm.
- `nseg_nondegenerate` - the three segment normals are nonzero.

Geometry of the line (kernel):

- `mbl_monotone_west`, `mbl_is_west_chain` - longitude strictly decreases P1 to
  P4 (the MBL is a monotone west-chain).
- `bands_cover` - the three longitude bands tile the seaward span with no gaps.
- `bands_share_only_p2`, `bands_share_only_p3`, and the generic
  `bands_meet_on_shared` - adjacent bands meet only on a shared meridian, so the
  segments are interior-disjoint (the line is simple); the concrete facts are
  instances of the generic one.
- `decide_seam_well_defined` - on either shared meridian the verdict is the same
  from both adjacent segments (their determinants are proportional with a
  positive ratio there), so the band tie-break in `decide` is immaterial and the
  geofence is well-defined on the seams.
- `meridian_trans`, `decide_seaward_of_p4`, `decide_landward_of_p1` - the
  meridian test is transitive within a hemisphere (a 2D Lagrange identity), so a
  position seaward of P4 or landward of P1 lies in no band and is Indeterminate:
  the commitment is confined to the agreed seaward span.
- `decide_band1_indeterminate_iff` - within a band, Indeterminate holds exactly
  on the segment's great circle.
- `decide_poly_total`, `decide_poly_sound`, `decide_poly_is_decide` - the
  four-point geofence is one instance of a generic fold over an arbitrary
  east-to-west boundary list, with totality and soundness proved generically.
- `equidistant_is_bisector`, `nearer_is_halfspace`, `equidistance_trichotomy` -
  the UNCLOS Article 74/83 equidistance geometry: the locus equidistant from two
  basepoints is the perpendicular-bisector great circle (normal A - B), which
  exactly splits the "nearer-A" and "nearer-B" half-spaces; an exact rational
  test, since great-circle distance is monotone in the dot product.

Features and lines (kernel):

- `karish_israeli`, `karish_north_israeli`, `tanin_israeli`,
  `israeli_fields_off_line` - the Karish, Karish North and Tanin gas fields lie
  on the Israeli side, off the line.
- `qana_straddles`, `qana_well_lebanese`, `prospect_straddle_no_unilateral` -
  the Qana/Sidon prospect has committed points on both sides; the 31/1B well,
  drilled in Block 9, is Lebanese-side; and neither party's side contains the
  whole prospect, so a unilateral taking would cross the line (Section 2F).
- `block9_interior_lebanese`, `block9_corner_is_P3` - Lebanon's licensed Block 9
  (vertices from Decree No. 42) lies on Lebanon's side: every interior vertex is
  Lebanese and the south-eastern corner coincides with the agreed point P3, so
  the prospect straddles from Block 9 into Israel's Block 72 across that line.
- `orientation_consistent`, `positive_side_is_south`, `negative_side_is_north` -
  on every segment the Israeli side is the positive side and the Lebanese side
  the negative side; the positive side contains the geographic south pole and
  the negative side the north pole, grounding the orientation in geographic
  south rather than sample witnesses.
- `crossing_deposit_not_unilateral` - a deposit with committed points on both
  sides cannot be taken wholly by either party (Section 2F in general form); the
  Qana prospect is the instance.
- `shared_line`, `supersession`, `mbl_is_decree6433_line`,
  `israel_2011_seaward_claim_now_lebanese`, `mbl_between_line1_and_line29`,
  `endpoint_latitude_order` - the two annexes are identical; the four agreed
  points are Lebanon's Decree 6433 points 20-23, cross-checked against an
  independent embedding of the deposited coordinates to `1e-9`; Israel's whole
  seaward 2011 claim (its deposited points 1, 34, 35) lies on the Lebanese side
  of the agreed line; the line lies between Line 1 (north) and Lebanon's Line 29
  (south), each side certified.
- `cyprus_line_monotone_north`, `seaward_terminus_on_line`,
  `ras_naqoura_deferred` - the Cyprus-Lebanon line runs strictly northward; P4
  sits on the line with the tripoint deferred; the near-shore terminus is
  Indeterminate.

Robustness and rounding (kernel):

- `sign_robust_Gt`, `sign_robust_Lt`, `verdict_robust_Israeli`,
  `verdict_robust_Lebanese` - a committed verdict survives any perturbation of
  the side determinant smaller than the clearance (the error envelope).
- `dot_diff_abs_bound`, `rounding_propagation_within_budget`, `side_det_robust`,
  `karish_query_robust`, `point1_query_robust` - the side determinant is
  Lipschitz in the position; the coordinate rounding budget (1.3e-13) propagates
  to a determinant perturbation below `rounding_det_budget`, and rounding the
  query coordinates cannot flip a committed feature.
- `clearance_exceeds_rounding_budget`, `committed_robust_to_model_and_rounding` -
  every committed feature's clearance exceeds the rounding budget, and exceeds
  the combined model+rounding budget (`model_det_budget` = 1e-7), so neither the
  spherical model nor the rational rounding can flip a committed verdict.
- `nseg_norm_bounds` - tight rational upper bounds on the segment normals,
  linking the clearance to an angular (and hence kilometre) distance.

WGS84 ellipsoid, native (kernel):

- `ellip_det_identity` and the per-feature `*_ellip_sign` - the exact WGS84 ECEF
  direction of a point is its spherical direction with `z` scaled by `1 - e^2`
  (`zscale`); on the side determinant the `e^2` correction is exact (the higher
  powers vanish), and for every committed feature the spherical and ellipsoidal
  determinants share sign.
- `decide_ellip`, `decide_ellip_total`, `decide_ellip_sound`,
  `mbl_ellip_is_west_chain`, `ellipsoid_agrees_on_features` - feeding the generic
  geofence the true ECEF directions yields a total, sound, exact-rational
  decision procedure on the WGS84 ellipsoid (its boundary the central plane
  section, the great ellipse), which returns the same verdict as the spherical
  kernel on every committed feature. The longitude bands are unchanged because
  `zscale` fixes `x` and `y`. The sole residual versus the treaty's geodesic
  lines is the great-ellipse-versus-geodesic separation, on the order of tens of
  metres: transcendental, not exactly rational, and far below every clearance.
  `decide_ellip` is extracted and the self-test checks it against `decide`.

Geometric soundness (bridge, classical reals):

- `Q2R_dot`, `verdict_real_Israeli`, `verdict_real_Lebanese` - the rational
  verdict is exactly the sign of the real scalar triple product of the embedded
  vectors: a genuine orientation / side-of-great-circle test.
- `dot_circle_bound`, `boundary_far_from_position` - via a Cauchy-Schwarz / Gram
  argument, every point of a segment's great circle is at least
  `R_earth * arcsin(clearance / |n|)` from the position; a positive clearance is
  a real kilometre lower bound on the distance to the boundary.
- `decide_Israeli_real_meaning`, `decide_Lebanese_real_meaning` - the precise
  meaning of a committed verdict: it is exactly an active longitude band plus the
  correct sign of that segment's real triple product. It does not assert "X is
  in country Y's waters", only "X is south/north of that segment's great circle
  within the band".
- `boundary_far_from_position`, `boundary_far_from_position_gen`, and the
  per-feature `tanin_distance_km`, `karish_distance_km`, `karish_north_distance_km`,
  `point1_distance_km`, `qana_isr_distance_km`, `qana_leb_distance_km` - every
  point of a segment's great circle is at least `R_earth * arcsin(clearance/|n|)`
  from the position; the per-feature bounds (Tanin ~35 km, Point 1 ~16, Karish
  ~14, Karish North ~9, Qana ~5-7) apply to the features' WGS84 unit positions
  directly (the non-unit generalization removes the idealization).
- `ecef_unit_is_unit` - the geodetic-to-ECEF embedding, in Coq's own sin/cos,
  produces unit vectors.
- `equidistant_real_meaning` - an equidistant position (the rational test) is at
  equal great-circle distance from the two basepoints over the reals (equal
  `acos` of the dot products): the equidistance criterion of Articles 74/83.

Coordinate provenance (classical reals plus primitive integers):

- `p1_matches_wgs84_dms`, `p2_matches_wgs84_dms`, `p3_matches_wgs84_dms`,
  `p4_matches_wgs84_dms` - each agreed point's stored rational matches the
  spherical ECEF embedding of its deposited degrees-minutes-seconds to within
  `1e-12` on every component, the transcendental bound discharged by CoqInterval.

## Axiom status

The rational kernel contains no axioms and no admitted lemmas. `audit.v` runs
`Print Assumptions` over the kernel theorems; each reports *Closed under the
global context*. The geofence and clearance extract to runnable OCaml;
`selftest.ml` checks that the extracted verdicts match the Coq theorems, and
`difftest.ml` / `difftest.py` cross-check the extracted decision against an
independent reimplementation of the kernel over 50000 pseudo-random positions
plus structured edge cases, all on identical exact rationals.

The real-geometry bridge uses only Coq's standard real-number axioms, and
`audit_bridge.v` stratifies them by where they are actually needed. The
orientation-soundness theorems - the verdict is the sign of the real scalar
triple product (`verdict_real_Israeli` / `verdict_real_Lebanese`), the
Cauchy-Schwarz bound (`dot_circle_bound`), and the precise meaning of a
committed verdict (`decide_Israeli_real_meaning` / `decide_Lebanese_real_meaning`)
- depend on only `ClassicalDedekindReals.sig_forall_dec` and
`functional_extensionality_dep`: no excluded middle, no `sig_not_dec`. Excluded
middle (`Classical_Prop.classic`) and `sig_not_dec` enter only in the metric
layer, the kilometre distance bounds that go through `acos` / `asin` / `sqrt`.
So the operative claim - which side of the line a position lies on - rests on a
strictly smaller axiom set than the distance figures. Neither layer adds a
project-specific axiom or an admitted lemma; fully removing the classical reals
would mean reproving the metric layer over a constructive-reals library.

The coordinate-provenance layer (`provenance.v`) depends on those same
classical-reals axioms together with Coq's primitive 63-bit integer arithmetic
(`PrimInt63` / `Uint63Axioms`), which CoqInterval uses for fast exact
multi-precision computation. Those are part of Coq's native-arithmetic trusted
base, realized by the OCaml runtime, not classical-logic axioms; they appear in
no other file. `audit_provenance.v` documents this footprint. There are no
project-specific axioms and no admitted lemmas anywhere in the development.

## Data and tolerances

All coordinates are WGS84. Rational unit vectors are within `1.6e-13` of the true
unit vector, and this is certified inside Coq to `1e-12` on the squared norm. The
spherical kernel and the native ellipsoidal `decide_ellip` agree on every
committed feature, proved inside Coq (`ellipsoid_agrees_on_features`), so the
spherical idealization flips no verdict; `wolfram/derive.wl` independently
recomputes each feature's determinant on the full WGS84 ellipsoid and finds the
spherical and ellipsoidal values differ by at most `6.5e-8`, below every
clearance (smallest, Qana, is `2.1e-6`), and `committed_robust_to_model_and_rounding`
discharges the combined model and rounding envelope. The one approximation that
remains, in `decide_ellip` as in the kernel, is that a segment is the central
plane section (great ellipse) rather than the ellipsoidal geodesic; the two
separate by tens of metres over these segment lengths, far below the kilometre
clearances, but the geodesic is transcendental and so outside exact rational
arithmetic.

Kilometre clearances of the named features to the boundary (Wolfram geodesy,
matched in sign by the Coq verdicts):

| feature        | side     | clearance |
|----------------|----------|-----------|
| Tanin          | Israeli  | 35.1 km   |
| Point 1 (2011) | Lebanese | 15.9 km   |
| Karish         | Israeli  | 14.2 km   |
| Karish North   | Israeli  |  9.3 km   |
| Qana (Israel)  | Israeli  |  6.8 km   |
| Qana (Lebanon) | Lebanese |  5.4 km   |

Sourced exactly from the primary UN deposits: the four agreed MBL points, which
are Lebanon's Decree 6433 / MZN.85.2011 points 20-23 and the identical 2022
Annex A / Annex B points; Israel's superseded deposit points 1, 34, 35 (its 2011
DOALOS submission, Point 1 being the Cyprus-Israel 2010 Point 1); the
Cyprus-Lebanon 2007 line; the Ras Naqoura land terminus; and the Block 9
boundary (Lebanon's Decree No. 42, first licensing round). Sourced as
operator/region positions: Karish, Karish North, Tanin. Line 29 was never
formally deposited (the 2021 decree amending Decree 6433 was left unsigned); it
is anchored here by the Karish field it was drawn to split. The exact Qana
reservoir outline is not in the public record (the 31/1B well was a dry hole);
the prospect straddle is represented by points either side of the line within
the sourced Block 9 and the Block 72 area.

## Build

Requires Rocq/Coq 9 (`coqc`), the CoqInterval library (`coq-interval`, used by
the provenance layer), and an OCaml native compiler (`ocamlopt`).

```
coqc naqoura_line.v        # checks all proofs and extracts naqoura.ml
coqc provenance.v          # per-point WGS84 coordinate provenance (CoqInterval)
coqc audit.v               # axiom audit of the rational kernel (all closed)
coqc audit_bridge.v        # axiom footprint of the real-geometry bridge
coqc audit_provenance.v    # axiom footprint of the provenance layer
bash build.sh              # all of the above, plus the OCaml self-test
bash difftest.sh [N]       # differential test vs an independent oracle (N points)
```

`wolfram/derive.wl` (WolframScript) re-derives every rational constant from its
geodetic source and independently cross-checks every verdict, clearance, and the
ellipsoidal model error.

## Files

```
naqoura_line.v     the development: rational kernel, extraction, real bridge
provenance.v       per-point WGS84 coordinate provenance (CoqInterval)
audit.v            Print Assumptions over the rational kernel (all closed)
audit_bridge.v     Print Assumptions over the real-geometry bridge
audit_provenance.v Print Assumptions over the provenance layer
selftest.ml        OCaml harness checking extracted verdicts vs the theorems
difftest.ml        OCaml runner: extracted verdicts for positions read on stdin
difftest.py        independent oracle + differential test driver
difftest.sh        build the runner and run the differential test
build.sh           compile, audit, extract, build, self-test
wolfram/derive.wl  coordinate provenance, geodesic and ellipsoidal cross-checks
```

## Citations

- Israel-Lebanon Exchange of Letters establishing a permanent maritime boundary,
  27 October 2022 (US-mediated).
- Lebanon, Council of Ministers Decree No. 6433 (2011), defining the EEZ
  southern limit (Line 23); deposited with the UN Secretary-General, 2011.
- Agreement between Cyprus and Lebanon on the delimitation of the EEZ, 2007;
  Cyprus-Israel EEZ agreement, 2010 (Israel's Line 1 endpoint).
- UN DOALOS, deposits of charts and lists of geographical coordinates under
  UNCLOS.
- D. Meier, "Lebanon's Maritime Boundaries: Between Economic Opportunities and
  Military Confrontation," Centre for Lebanese Studies, 2013 (coordinate tables).
- Lebanese Armed Forces technical study / UK Hydrographic Office (2021) on
  Line 29.
- Energean plc and Global Energy Monitor, Karish / Karish North / Tanin field
  positions.
- TotalEnergies and the Lebanese Petroleum Administration, Block 9 and the Qana
  31/1B exploration well.
- PCA and UNCLOS (1982) for the delimitation framework (Articles 74, 83).
