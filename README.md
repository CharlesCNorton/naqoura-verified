# The Naqoura Line

*A machine-checked geofence over the 2022 Israel-Lebanon maritime boundary.*

A sound, total, extractable decision procedure that places any seaward position
on the Israeli or Lebanese side of the agreed Maritime Boundary Line (MBL), with
a certified clearance, and proves the legal geometry of the settlement: the
straddling Qana prospect, the supersession of the parties' 2011 claim lines, the
classification of the offshore gas fields, and the deferral of the near-shore
segment. The development contains no axioms and no admitted lemmas.

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

The sphere is modeled in exact rational arithmetic. A position is a vector in
`Q^3` (an ECEF / unit-sphere direction). The side of the line is the sign of a
determinant: for a geodesic segment from `A` to `B`, a position `X` is on
Lebanon's (north) side when `(A x B) . X < 0` and on Israel's (south) side when
`(A x B) . X > 0`. Segment selection is by longitude band, itself an exact
rational sign test against the meridian normals. Every classification is thus a
finite exact rational computation, decided by `vm_compute`, and extracts to
OCaml.

The only irrational data are the boundary and feature coordinates. These are
converted from their published WGS84 geodetic positions to rational unit vectors
once, in Wolfram (`wolfram/derive.wl`), each within `1.6e-13` of the true unit
vector (sub-millimeter). That script also recomputes every verdict and clearance
in this file by an independent Wolfram geodesy path (great-circle side test and
distance), as a cross-check on the Coq results.

Because the verdict is the sign of a determinant that is linear in `X`, it is
invariant under positive rescaling of `X` (`decide_scale_invariant`): a consumer
need only supply the correct ECEF direction, not an exactly normalized vector.

## What is proven

Decision procedure:

- `decide_total`, `decide_Israeli_sound`, `decide_Lebanese_sound`,
  `decide_exclusive` - the geofence is total over the seaward extent and a
  committed verdict exhibits the determining segment and sign.
- `decide_committed_clearance_pos` - a committed verdict carries a strictly
  positive clearance (the position is strictly off the line).
- `decide_scale_invariant`, `of_ecef_scale_free` - the verdict depends only on
  direction; rounding the norm cannot change it.

Geometry of the line:

- `mbl_monotone_west` - longitude strictly decreases from P1 to P4.
- `bands_cover` - the three longitude bands tile the seaward span with no gaps.
- `bands_share_only_p2`, `bands_share_only_p3` - adjacent bands meet only on a
  shared meridian, so the segments are interior-disjoint (the line is simple).
- `decide_band1_indeterminate_iff` - within a band, Indeterminate holds exactly
  on the segment's great circle.
- `decide_poly_total`, `decide_poly_sound`, `decide_poly_is_decide` - the
  hand-unrolled four-point geofence is one instance of a generic fold over an
  arbitrary east-to-west list of boundary points, with totality and soundness
  proved generically.

Features and lines:

- `karish_israeli`, `karish_north_israeli`, `tanin_israeli`,
  `israeli_fields_off_line` - the Karish, Karish North and Tanin gas fields lie
  on the Israeli side, off the line.
- `qana_straddles`, `qana_well_lebanese` - the Qana/Sidon prospect has committed
  points on both sides; the 31/1B well, drilled in Block 9, is Lebanese-side.
- `orientation_consistent` - on every segment the Israeli side is the positive
  side and the Lebanese side the negative side.
- `shared_line` - Lebanon's Annex A and Israel's Annex B points are identical.
- `supersession` - Israel's former Line 1 seaward endpoint now lies on the
  Lebanese side of the agreed line; Lebanon's Point 23 is retained as P4.
- `mbl_between_line1_and_line29`, `endpoint_latitude_order` - the agreed line
  lies strictly between Israel's Line 1 (north) and Lebanon's Line 29 (south,
  anchored by the Karish field it would have split), each side certified.
- `cyprus_line_monotone_north`, `seaward_terminus_on_line` - the Cyprus-Lebanon
  line runs strictly northward; P4 sits on the line with the trilateral
  tripoint deferred.
- `ras_naqoura_deferred` - the near-shore terminus is Indeterminate (the
  undelimited buoy line).

Robustness and structure:

- `sign_robust_Gt`, `sign_robust_Lt`, `verdict_robust_Israeli`,
  `verdict_robust_Lebanese` - a committed verdict survives any perturbation of
  the side determinant smaller than the clearance (the error envelope).
- `clearance_exceeds_rounding_budget`, `karish_rounding_robust` - every
  committed feature's clearance exceeds the rational rounding budget by orders
  of magnitude, so rounding can never flip a verdict.
- `nseg_norm_bounds` - rational upper bounds on the segment normals, linking the
  clearance to an angular (and hence kilometre) distance; the exact kilometre
  clearances are tabulated independently in `wolfram/derive.wl`.
- `naqoura_section_2F` - the agreement's Prospect arrangement (Section 2F),
  encoded as the genuine straddle of the line by the prospect.

## Axiom status

The development contains no axioms and no admitted lemmas. `audit.v` runs
`Print Assumptions` over every theorem; each reports *Closed under the global
context*. The geofence and clearance extract to runnable OCaml, and `selftest.ml`
checks that the extracted verdicts match the Coq theorems.

## Data and tolerances

All coordinates are WGS84. Rational unit vectors are within `1.6e-13` of the
true unit vector. The model is a sphere; the geodetic-to-unit embedding is
applied identically to the boundary and to every feature, so the relative side
test is preserved up to a small second-order term, which the kilometre-scale
clearances of the named fields dominate. The Qana prospect lies within a few
kilometres of the line, which is why the agreement shares it rather than
assigning it.

Sourced exactly: the four agreed MBL points; Lebanon's Point 23 (equal to P4);
Israel's Line 1 / Cyprus-Lebanon 2007 points 1-6; the Ras Naqoura land terminus.
Sourced as operator/region positions: Karish, Karish North, Tanin. Line 29 was
never formally deposited; it is anchored here by the Karish field it was drawn
to split. Israel's near-shore points 34, 35 and Lebanon's points 20-22, and the
exact Qana reservoir outline, were not in the public record consulted; the
seaward endpoints carry the disputed geometry and the prospect straddle is
represented by points either side of the line in the Block 9 / Block 72 area.

## Build

Requires Rocq/Coq 9 (`coqc`) and an OCaml native compiler (`ocamlopt`).

```
coqc naqoura_line.v        # checks all proofs and extracts naqoura.ml
coqc audit.v               # prints the axiom audit
bash build.sh              # all of the above, plus the OCaml self-test
```

`wolfram/derive.wl` (WolframScript) re-derives every rational constant from its
geodetic source and independently cross-checks every verdict and clearance.

## Files

```
naqoura_line.v     the development (definitions, theorems, extraction)
audit.v            Print Assumptions audit over every theorem
selftest.ml        OCaml harness checking extracted verdicts vs the theorems
build.sh           compile, audit, extract, build, self-test
wolfram/derive.wl  coordinate provenance and independent geodesic cross-check
TODO.md            (none remaining)
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
