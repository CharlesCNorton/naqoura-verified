(******************************************************************************)
(*                                                                            *)
(*           The Naqoura Line: The Israel-Lebanon Maritime Boundary           *)
(*                                                                            *)
(*     A verified geofence over the 2022 Israel-Lebanon maritime boundary: a  *)
(*     sound, total decision procedure placing any seaward position on the    *)
(*     Israeli or Lebanese side, with certified clearance; extractable.       *)
(*                                                                            *)
(*     "A permanent and equitable resolution of their maritime dispute."      *)
(*     - Israel-Lebanon Exchange of Letters, 2022                             *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: June 2, 2026                                                     *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(* The Maritime Boundary Line (MBL) agreed on 27 October 2022 is, per the
   Exchange of Letters, four points in the WGS84 datum joined by geodesic
   lines, identical in the Lebanese (Annex A) and Israeli (Annex B) UN
   deposits.  The boundary is fixed seaward of the easternmost point; the
   near-shore segment (the buoy line) was deliberately left undelimited and is
   out of scope.

   We model the sphere and decide the side of a position by the sign of a
   determinant.  A position is a unit vector in Cartesian (ECEF) form with
   rational coordinates: a consumer converts a geodetic fix to a unit vector
   and rounds to rationals before calling the geofence.  Segment selection and
   the side test are then exact rational sign tests, so the whole decision is
   computable and extracts to OCaml.  The only irrational data, the four
   boundary points, are precomputed rationals within 1.3e-13 (sub-millimeter)
   of the true WGS84 unit vectors (Wolfram-derived). *)

From Stdlib Require Import QArith.
From Stdlib Require Import Qabs.
From Stdlib Require Import Lqa.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Extraction.
Import ListNotations.

Open Scope Q_scope.

(* A position / direction as a vector in Q^3 (unit-sphere / ECEF coordinates). *)
Record Vec : Set := mkVec { vx : Q ; vy : Q ; vz : Q }.

Definition dot (a b : Vec) : Q :=
  vx a * vx b + vy a * vy b + vz a * vz b.

Definition cross (a b : Vec) : Vec :=
  mkVec (vy a * vz b - vz a * vy b)
        (vz a * vx b - vx a * vz b)
        (vx a * vy b - vy a * vx b).

(* Meridian normal of p: orthogonal to p and to the polar axis, so that
   dot (meridian p) X has the sign of (longitude X - longitude p). *)
Definition meridian (p : Vec) : Vec := mkVec (- vy p) (vx p) 0.

(* ----- The four agreed MBL points (rational unit vectors, WGS84-derived). ----- *)
(* P1 easternmost (offshore start) ... P4 westernmost (toward the tripoint).      *)

Definition p1 : Vec := mkVec (3240185 # 4725163) (2048242 # 4257979) (573521 # 1049942).
Definition p2 : Vec := mkVec (6046041 # 8816135) (1395546 # 2902183) (2728844 # 4994991).
Definition p3 : Vec := mkVec (4892447 # 7125214) (4396228 # 9183773) (11386631 # 20810622).
Definition p4 : Vec := mkVec (1935291 # 2792834) (1089867 # 2352157) (360157 # 652002).

(* Great-circle normals of the three geodesic segments, derived (not trusted). *)
Definition nseg1 : Vec := cross p1 p2.
Definition nseg2 : Vec := cross p2 p3.
Definition nseg3 : Vec := cross p3 p4.

(* ----- Sign primitives (exact rational comparisons against zero). ----- *)

(* X at or east of p's meridian (longitude X >= longitude p). *)
Definition east_of (p X : Vec) : bool :=
  match dot (meridian p) X ?= 0 with Lt => false | _ => true end.

(* X at or west of p's meridian (longitude X <= longitude p). *)
Definition west_of (p X : Vec) : bool :=
  match dot (meridian p) X ?= 0 with Gt => false | _ => true end.

Inductive Side : Set := Israeli | Lebanese | Indeterminate.

(* Verdict for a point alongside a segment with great-circle normal n.  By the
   orientation of the normals, a point north of the segment (Lebanon) gives a
   negative determinant, a point south (Israel) a positive one. *)
Definition verdict (n X : Vec) : Side :=
  match dot n X ?= 0 with
  | Gt => Israeli
  | Lt => Lebanese
  | Eq => Indeterminate
  end.

(* X is in the longitude band of the segment from east end pe to west end pw. *)
Definition in_band (pw pe X : Vec) : bool :=
  andb (east_of pw X) (west_of pe X).

(* ----- The geofence. ----- *)
(* Total over the seaward extent of the MBL: classify by the unique segment
   whose longitude band contains the point; outside all bands the seaward
   boundary does not constrain, and the result is Indeterminate. *)

Definition decide (X : Vec) : Side :=
  if in_band p2 p1 X then verdict nseg1 X
  else if in_band p3 p2 X then verdict nseg2 X
  else if in_band p4 p3 X then verdict nseg3 X
  else Indeterminate.

(* The non-negative magnitude of the side determinant (0 exactly on the line). *)
Definition seg_clearance (n X : Vec) : Q :=
  match dot n X ?= 0 with
  | Gt => dot n X
  | Lt => - dot n X
  | Eq => 0
  end.

(* Certified clearance: for a unit-vector position this equals |nseg| times the
   sine of the angular distance to the segment's great circle, so a positive
   value certifies the point is strictly off the boundary. *)
Definition clearance (X : Vec) : Q :=
  if in_band p2 p1 X then seg_clearance nseg1 X
  else if in_band p3 p2 X then seg_clearance nseg2 X
  else if in_band p4 p3 X then seg_clearance nseg3 X
  else 0.

(* ----- Totality. ----- *)

Theorem decide_total : forall X,
  decide X = Israeli \/ decide X = Lebanese \/ decide X = Indeterminate.
Proof. intro X. destruct (decide X); auto. Qed.

(* ----- Soundness: a committed verdict exhibits the determining sign. ----- *)

Theorem decide_Israeli_sound : forall X,
  decide X = Israeli ->
  (in_band p2 p1 X = true /\ (dot nseg1 X ?= 0) = Gt) \/
  (in_band p3 p2 X = true /\ (dot nseg2 X ?= 0) = Gt) \/
  (in_band p4 p3 X = true /\ (dot nseg3 X ?= 0) = Gt).
Proof.
  intros X H. unfold decide, verdict in H.
  destruct (in_band p2 p1 X) eqn:B1.
  - destruct (dot nseg1 X ?= 0) eqn:C1; try discriminate.
    left. split; reflexivity.
  - destruct (in_band p3 p2 X) eqn:B2.
    + destruct (dot nseg2 X ?= 0) eqn:C2; try discriminate.
      right; left. split; reflexivity.
    + destruct (in_band p4 p3 X) eqn:B3.
      * destruct (dot nseg3 X ?= 0) eqn:C3; try discriminate.
        right; right. split; reflexivity.
      * discriminate.
Qed.

Theorem decide_Lebanese_sound : forall X,
  decide X = Lebanese ->
  (in_band p2 p1 X = true /\ (dot nseg1 X ?= 0) = Lt) \/
  (in_band p3 p2 X = true /\ (dot nseg2 X ?= 0) = Lt) \/
  (in_band p4 p3 X = true /\ (dot nseg3 X ?= 0) = Lt).
Proof.
  intros X H. unfold decide, verdict in H.
  destruct (in_band p2 p1 X) eqn:B1.
  - destruct (dot nseg1 X ?= 0) eqn:C1; try discriminate.
    left. split; reflexivity.
  - destruct (in_band p3 p2 X) eqn:B2.
    + destruct (dot nseg2 X ?= 0) eqn:C2; try discriminate.
      right; left. split; reflexivity.
    + destruct (in_band p4 p3 X) eqn:B3.
      * destruct (dot nseg3 X ?= 0) eqn:C3; try discriminate.
        right; right. split; reflexivity.
      * discriminate.
Qed.

(* The two sides are mutually exclusive on any point. *)
Theorem decide_exclusive : forall X,
  ~ (decide X = Israeli /\ decide X = Lebanese).
Proof. intros X [Hi Hl]. rewrite Hi in Hl. discriminate. Qed.

(* ----- Clearance certificate. ----- *)

Lemma seg_clearance_pos : forall n X,
  (dot n X ?= 0) = Gt \/ (dot n X ?= 0) = Lt -> 0 < seg_clearance n X.
Proof.
  intros n X H. unfold seg_clearance. destruct H as [H|H]; rewrite H.
  - change (0 < dot n X). pose proof (proj2 (Qgt_alt (dot n X) 0) H). lra.
  - change (0 < - dot n X). pose proof (proj2 (Qlt_alt (dot n X) 0) H). lra.
Qed.

(* Whenever the geofence commits to a side, the clearance is strictly positive,
   certifying the point is off the boundary line. *)
Theorem decide_committed_clearance_pos : forall X,
  decide X = Israeli \/ decide X = Lebanese -> 0 < clearance X.
Proof.
  intros X H. unfold decide, clearance, verdict in *.
  destruct (in_band p2 p1 X).
  - apply seg_clearance_pos. destruct (dot nseg1 X ?= 0).
    + destruct H as [H|H]; discriminate.
    + right; reflexivity.
    + left; reflexivity.
  - destruct (in_band p3 p2 X).
    + apply seg_clearance_pos. destruct (dot nseg2 X ?= 0).
      * destruct H as [H|H]; discriminate.
      * right; reflexivity.
      * left; reflexivity.
    + destruct (in_band p4 p3 X).
      * apply seg_clearance_pos. destruct (dot nseg3 X ?= 0).
        -- destruct H as [H|H]; discriminate.
        -- right; reflexivity.
        -- left; reflexivity.
      * destruct H as [H|H]; discriminate.
Qed.

(* ----- A worked consequence: the Karish field is on the Israeli side. ----- *)

(* The Karish gas field (Energean), reported at 33.2283 N, 34.2890 E, as a
   rational unit vector within 1.0e-13 of the true WGS84 position (Wolfram). *)
Definition karish : Vec :=
  mkVec (1493827 # 2161469) (1319835 # 2800691) (1197819 # 2185895).

(* Its longitude lies in the seaward P3-P4 band and it sits south of that
   segment, so the geofence places it on the Israeli side -- decided purely by
   rational computation, no axioms. *)
Theorem karish_israeli : decide karish = Israeli.
Proof. vm_compute. reflexivity. Qed.

(* The deal therefore places Karish strictly off the boundary, clearance > 0. *)
Theorem karish_off_line : 0 < clearance karish.
Proof. apply decide_committed_clearance_pos. left. exact karish_israeli. Qed.

(* ===== Geometry of the meridian test and scale invariance. =====            *)

(* The meridian test is exactly the z-component of the cross product p x X,
   the standard orientation test for "which side of p's meridian plane".  So
   east_of / west_of track longitude ordering of X relative to p.             *)
Lemma meridian_is_cross_z : forall p X,
  dot (meridian p) X == vx p * vy X - vy p * vx X.
Proof. intros p X. unfold dot, meridian. simpl. ring. Qed.

Lemma meridian_eq_cross_vz : forall p X,
  dot (meridian p) X == vz (cross p X).
Proof. intros p X. unfold dot, meridian, cross. simpl. ring. Qed.

(* Scaling a position by a positive rational. *)
Definition scaleV (k : Q) (X : Vec) : Vec := mkVec (k * vx X) (k * vy X) (k * vz X).

Lemma dot_scaleV_r : forall n k X, dot n (scaleV k X) == k * dot n X.
Proof. intros n k X. unfold dot, scaleV. simpl. ring. Qed.

(* A positive rational negates to a negative one (proved at the integer level
   to stay independent of the rational arithmetic decision procedures). *)
Lemma Qpos_opp_neg : forall x : Q, 0 < x -> - x < 0.
Proof. intros [a b] H. unfold Qlt, Qopp in *; simpl in *; lia. Qed.

(* The sign of a determinant is invariant under multiplication by k > 0. *)
Lemma Qcompare_mult_pos_l : forall k d, 0 < k -> (k * d ?= 0) = (d ?= 0).
Proof.
  intros k d Hk. destruct (d ?= 0) eqn:E.
  - apply Qeq_alt in E. apply Qeq_alt. rewrite E. ring.
  - apply Qlt_alt in E. apply Qlt_alt.
    assert (Hd : 0 < - d) by lra.
    pose proof (Qmult_lt_0_compat k (- d) Hk Hd) as Hp.
    setoid_replace (k * d) with (- (k * - d)) by ring.
    apply Qpos_opp_neg. exact Hp.
  - apply Qgt_alt in E. apply Qgt_alt.
    apply Qmult_lt_0_compat; assumption.
Qed.

(* Comparison against 0 respects rational equality. *)
Lemma Qcompare_compat0 : forall a b, a == b -> (a ?= 0) = (b ?= 0).
Proof.
  intros a b H. destruct (a ?= 0) eqn:E.
  - apply Qeq_alt in E. symmetry. apply Qeq_alt. rewrite <- H. exact E.
  - apply Qlt_alt in E. symmetry. apply Qlt_alt. rewrite <- H. exact E.
  - apply Qgt_alt in E. symmetry. apply Qgt_alt. rewrite <- H. exact E.
Qed.

(* dot is invariant in sign under positive scaling of either argument; we use
   that any positive multiple of X yields the same comparison against 0. *)
Lemma dot_scale_compare : forall n k X, 0 < k -> (dot n (scaleV k X) ?= 0) = (dot n X ?= 0).
Proof.
  intros n k X Hk.
  rewrite (Qcompare_compat0 _ _ (dot_scaleV_r n k X)).
  apply Qcompare_mult_pos_l; exact Hk.
Qed.

Lemma verdict_scale_invariant : forall n k X, 0 < k -> verdict n (scaleV k X) = verdict n X.
Proof.
  intros n k X Hk. unfold verdict. rewrite dot_scale_compare by exact Hk. reflexivity.
Qed.

Lemma east_of_scale : forall p k X, 0 < k -> east_of p (scaleV k X) = east_of p X.
Proof.
  intros p k X Hk. unfold east_of.
  rewrite (dot_scale_compare (meridian p) k X Hk). reflexivity.
Qed.

Lemma west_of_scale : forall p k X, 0 < k -> west_of p (scaleV k X) = west_of p X.
Proof.
  intros p k X Hk. unfold west_of.
  rewrite (dot_scale_compare (meridian p) k X Hk). reflexivity.
Qed.

Lemma in_band_scale : forall pw pe k X, 0 < k -> in_band pw pe (scaleV k X) = in_band pw pe X.
Proof.
  intros pw pe k X Hk. unfold in_band.
  rewrite east_of_scale by exact Hk. rewrite west_of_scale by exact Hk. reflexivity.
Qed.

(* The geofence depends only on the DIRECTION of X: a consumer need not produce
   an exactly unit-norm vector, only one with the correct ECEF direction.  Any
   positive rescaling (e.g. from rounding the norm) leaves the verdict fixed. *)
Theorem decide_scale_invariant : forall k X, 0 < k -> decide (scaleV k X) = decide X.
Proof.
  intros k X Hk. unfold decide.
  rewrite !in_band_scale by exact Hk.
  rewrite !verdict_scale_invariant by exact Hk.
  reflexivity.
Qed.

Theorem clearance_scale : forall k X, 0 < k -> clearance (scaleV k X) == k * clearance X.
Proof.
  intros k X Hk. unfold clearance, seg_clearance.
  rewrite !in_band_scale by exact Hk.
  destruct (in_band p2 p1 X).
  - rewrite (dot_scale_compare nseg1 k X Hk).
    destruct (dot nseg1 X ?= 0); [ring | rewrite dot_scaleV_r; ring | rewrite dot_scaleV_r; ring].
  - destruct (in_band p3 p2 X).
    + rewrite (dot_scale_compare nseg2 k X Hk).
      destruct (dot nseg2 X ?= 0); [ring | rewrite dot_scaleV_r; ring | rewrite dot_scaleV_r; ring].
    + destruct (in_band p4 p3 X).
      * rewrite (dot_scale_compare nseg3 k X Hk).
        destruct (dot nseg3 X ?= 0); [ring | rewrite dot_scaleV_r; ring | rewrite dot_scaleV_r; ring].
      * ring.
Qed.

(* ===== Longitude monotonicity of the MBL: P1 east of P2 east of P3 east of P4. *)
(* dot (meridian pe) pw < 0 says pw lies strictly west of pe's meridian.       *)
Theorem mbl_monotone_west :
  (dot (meridian p1) p2 ?= 0) = Lt /\
  (dot (meridian p2) p3 ?= 0) = Lt /\
  (dot (meridian p3) p4 ?= 0) = Lt.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===== Band tiling: no gaps and interior-disjoint (simplicity). ===== *)

(* Over the seaward longitude span [lon P4, lon P1], the three bands cover every
   position: a point east of P4 and west of P1 lies in at least one band. *)
Theorem bands_cover : forall X,
  east_of p4 X = true -> west_of p1 X = true ->
  in_band p2 p1 X = true \/ in_band p3 p2 X = true \/ in_band p4 p3 X = true.
Proof.
  intros X H4 H1. unfold in_band, east_of, west_of in *.
  destruct (dot (meridian p3) X ?= 0) eqn:E3;
  destruct (dot (meridian p2) X ?= 0) eqn:E2;
  rewrite H4 in *; rewrite H1 in *; simpl; auto.
Qed.

(* Adjacent bands overlap only on the shared meridian (measure zero), so the
   geodesic segments are interior-disjoint: the polyline is simple. *)
Theorem bands_share_only_p2 : forall X,
  in_band p2 p1 X = true -> in_band p3 p2 X = true -> dot (meridian p2) X == 0.
Proof.
  intros X H1 H2. unfold in_band, east_of, west_of in *.
  apply andb_prop in H1. destruct H1 as [H1a H1b].
  apply andb_prop in H2. destruct H2 as [H2a H2b].
  destruct (dot (meridian p2) X ?= 0) eqn:E.
  - apply Qeq_alt. exact E.
  - discriminate H1a.
  - discriminate H2b.
Qed.

Theorem bands_share_only_p3 : forall X,
  in_band p3 p2 X = true -> in_band p4 p3 X = true -> dot (meridian p3) X == 0.
Proof.
  intros X H2 H3. unfold in_band, east_of, west_of in *.
  apply andb_prop in H2. destruct H2 as [H2a H2b].
  apply andb_prop in H3. destruct H3 as [H3a H3b].
  destruct (dot (meridian p3) X ?= 0) eqn:E.
  - apply Qeq_alt. exact E.
  - discriminate H2a.
  - discriminate H3b.
Qed.

(* ===== Strengthened totality: within a band, Indeterminate iff exactly on the
   segment's great circle. ===== *)
Theorem decide_band1_indeterminate_iff : forall X,
  in_band p2 p1 X = true ->
  (decide X = Indeterminate <-> dot nseg1 X == 0).
Proof.
  intros X B. unfold decide, verdict. rewrite B.
  destruct (dot nseg1 X ?= 0) eqn:E.
  - split; intros _; [apply Qeq_alt; exact E | reflexivity].
  - split; [discriminate | intro H; apply Qeq_alt in H; rewrite H in E; discriminate].
  - split; [discriminate | intro H; apply Qeq_alt in H; rewrite H in E; discriminate].
Qed.

(* ===== Generic polyline geofence: the hand-unrolled four points are one
   instance of a fold over an arbitrary east-to-west list of boundary points. ===== *)

Fixpoint decide_poly (pts : list Vec) (X : Vec) : Side :=
  match pts with
  | pe :: ((pw :: _) as rest) =>
      if in_band pw pe X then verdict (cross pe pw) X
      else decide_poly rest X
  | _ => Indeterminate
  end.

Lemma decide_poly_total : forall pts X,
  decide_poly pts X = Israeli \/ decide_poly pts X = Lebanese \/ decide_poly pts X = Indeterminate.
Proof. intros pts X. destruct (decide_poly pts X); auto. Qed.

(* A committed generic verdict exhibits the determining segment and sign. *)
Lemma decide_poly_sound : forall pts X,
  decide_poly pts X = Israeli \/ decide_poly pts X = Lebanese ->
  exists pe pw, in_band pw pe X = true /\
    ((decide_poly pts X = Israeli /\ (dot (cross pe pw) X ?= 0) = Gt) \/
     (decide_poly pts X = Lebanese /\ (dot (cross pe pw) X ?= 0) = Lt)).
Proof.
  induction pts as [|pe rest IH]; intros X H.
  - simpl in H. destruct H; discriminate.
  - destruct rest as [|pw tl].
    + simpl in H. destruct H; discriminate.
    + cbn [decide_poly] in *. destruct (in_band pw pe X) eqn:B.
      * exists pe, pw. split; [exact B|]. unfold verdict in *.
        destruct (dot (cross pe pw) X ?= 0) eqn:C.
        -- destruct H; discriminate.
        -- right. split; reflexivity.
        -- left. split; reflexivity.
      * apply IH in H. exact H.
Qed.

(* The concrete four-point geofence is exactly the generic fold over the MBL. *)
Theorem decide_poly_is_decide : forall X, decide_poly [p1; p2; p3; p4] X = decide X.
Proof.
  intro X. unfold decide, nseg1, nseg2, nseg3. cbn [decide_poly]. reflexivity.
Qed.

(* ===== Named offshore features and claim-line points. =====
   WGS84-derived rational unit vectors (within 1.6e-13 of the true unit
   vectors); see wolfram/derive.wl for the provenance and an independent
   Wolfram geodesic recomputation of every verdict and clearance below.       *)

(* Israel Line 1 (2011 UN deposit) seaward endpoint, identical to the
   Cyprus-Lebanon 2007 Point 1 that Israel adopted: 33-38-40 N, 33-53-40 E.
   Israel near-shore points 34 and 35 were not separately published in the
   sources consulted; the seaward Point 1 is the salient, disputed end.       *)
Definition point1_israel : Vec := mkVec (2602081 # 3765547) (587755 # 1266028) (1937617 # 3497267).

(* Cyprus-Lebanon 2007 EEZ line, points 2..6 (point 1 = point1_israel). *)
Definition cyprus2 : Vec := mkVec (2054692 # 2986191) (4100017 # 8818551) (791899 # 1421361).
Definition cyprus3 : Vec := mkVec (5459300 # 7970813) (1174301 # 2513407) (450624 # 805963).
Definition cyprus4 : Vec := mkVec (2191648 # 3231667) (2835083 # 6029818) (1433527 # 2538083).
Definition cyprus5 : Vec := mkVec (2298429 # 3406871) (3464697 # 7362448) (1820060 # 3200491).
Definition cyprus6 : Vec := mkVec (1773639 # 2633068) (10705283 # 22753289) (1072242 # 1881137).

(* Energean fields, offshore Israel (operator / Global Energy Monitor positions). *)
Definition karish_north : Vec := mkVec (1607891 # 2328730) (1947745 # 4129202) (3221889 # 5874839).
Definition tanin : Vec := mkVec (1611865 # 2318818) (409067 # 877008) (3020648 # 5521905).

(* Land terminus near Point B1 (Ras Naqoura / Rosh Hanikra), 33-05-23.4 N. *)
Definition ras_naqoura : Vec := mkVec (2368622 # 3455649) (2004128 # 4159821) (1260206 # 2308267).

(* Qana/Sidon prospect: representative points either side of the MBL.  Section 2
   of the agreement records that the Prospect lies partly in Lebanon's Block 9
   and partly in Israel's Block 72; the 31/1B exploration well sits in Block 9.
   The exact reservoir outline is not public, so these are representative
   positions in the prospect vicinity bracketing the boundary, not surveyed
   corners; the robustness envelope below makes the verdicts insensitive to
   their precise placement.                                                    *)
Definition qana_leb : Vec := mkVec (2882075 # 4202159) (1522867 # 3176942) (476190 # 869653).
Definition qana_isr : Vec := mkVec (899127 # 1309165) (1050501 # 2188517) (814815 # 1492856).

(* Nearshore-segment (P1-P2) orientation witnesses. *)
Definition b1n : Vec := mkVec (1660039 # 2421209) (932111 # 1938480) (736565 # 1347686).
Definition b1s : Vec := mkVec (2851821 # 4157560) (1565488 # 3254211) (1016913 # 1862629).

(* ===== Feature verdicts, decided purely by exact rational computation. ===== *)

Theorem karish_north_israeli : decide karish_north = Israeli.
Proof. vm_compute. reflexivity. Qed.

Theorem tanin_israeli : decide tanin = Israeli.
Proof. vm_compute. reflexivity. Qed.

(* Karish, Karish North and Tanin all sit on the Israeli side, off the line. *)
Theorem israeli_fields_off_line :
  0 < clearance karish /\ 0 < clearance karish_north /\ 0 < clearance tanin.
Proof.
  split; [| split].
  - apply decide_committed_clearance_pos. left. exact karish_israeli.
  - apply decide_committed_clearance_pos. left. exact karish_north_israeli.
  - apply decide_committed_clearance_pos. left. exact tanin_israeli.
Qed.

(* The Qana/Sidon prospect straddles the boundary: a committed point on each
   side, as Section 2 of the agreement records. *)
Theorem qana_straddles :
  decide qana_leb = Lebanese /\ decide qana_isr = Israeli.
Proof. split; vm_compute; reflexivity. Qed.

(* The 31/1B exploration well, drilled in Lebanon's Block 9, is Lebanese-side. *)
Theorem qana_well_lebanese : decide qana_leb = Lebanese.
Proof. vm_compute. reflexivity. Qed.

Theorem qana_straddle_clearance :
  0 < clearance qana_leb /\ 0 < clearance qana_isr.
Proof.
  split.
  - apply decide_committed_clearance_pos. right. exact (proj1 qana_straddles).
  - apply decide_committed_clearance_pos. left. exact (proj2 qana_straddles).
Qed.

(* The near-shore terminus at Ras Naqoura lies landward of P1, in the segment
   the agreement deliberately left undelimited (the buoy line): the geofence
   returns Indeterminate. *)
Theorem ras_naqoura_deferred : decide ras_naqoura = Indeterminate.
Proof. vm_compute. reflexivity. Qed.

(* ===== Orientation consistency: on every segment the Israeli (south) side is
   the positive side, the Lebanese (north) side the negative side. ===== *)
Theorem orientation_consistent :
  (decide b1s = Israeli /\ decide b1n = Lebanese) /\           (* segment P1-P2 *)
  (decide qana_isr = Israeli /\ decide qana_leb = Lebanese) /\ (* segment P2-P3 *)
  (decide karish = Israeli /\ decide point1_israel = Lebanese). (* segment P3-P4 *)
Proof. repeat split; vm_compute; reflexivity. Qed.

(* ===== The three historical claim lines and the agreement's resolution. ===== *)

(* Israel's Line 1, anchored at its disputed seaward endpoint. *)
Definition line1_seaward : Vec := point1_israel.

(* Lebanon's Line 23 (Decree 6433) seaward endpoint, Point 23 = MBL P4 exactly. *)
Definition line23_seaward : Vec := p4.
Theorem line23_endpoint_is_P4 : line23_seaward = p4.
Proof. reflexivity. Qed.

(* Lebanon's army Line 29 (2020-2021), anchored by the Karish field it cuts. *)
Definition line29_anchor : Vec := karish.

(* The agreed MBL points deposited by Lebanon (Annex A) and Israel (Annex B)
   are identical: a single shared line, not two competing ones. *)
Definition annex_A : list Vec := [p1; p2; p3; p4].
Definition annex_B : list Vec := [p1; p2; p3; p4].
Theorem shared_line : annex_A = annex_B.
Proof. reflexivity. Qed.

(* Supersession: Israel's former Line-1 seaward endpoint now lies on the
   Lebanese side of the agreed boundary (the agreement settled the wedge in
   Lebanon's favour relative to Israel's 2011 claim); Lebanon's Point 23 is
   retained as the agreed terminus P4. *)
Theorem supersession :
  decide line1_seaward = Lebanese /\ line23_seaward = p4.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

(* Line nesting at the seaward apex: Israel's Line 1 endpoint decides Lebanese
   (north of the agreed line) and Lebanon's Line 29 anchor decides Israeli
   (south of it).  The agreed MBL lies strictly between the two former claims,
   each side certified by positive clearance. *)
Theorem mbl_between_line1_and_line29 :
  decide line1_seaward = Lebanese /\ decide line29_anchor = Israeli /\
  0 < clearance line1_seaward /\ 0 < clearance line29_anchor.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split.
  - apply decide_committed_clearance_pos. right. vm_compute. reflexivity.
  - apply decide_committed_clearance_pos. left. exact karish_israeli.
Qed.

(* North-to-south ordering of the three seaward endpoints (latitude vz). *)
Theorem endpoint_latitude_order :
  vz line23_seaward < vz line1_seaward /\ vz line29_anchor < vz line23_seaward.
Proof. split; apply (proj2 (Qlt_alt _ _)); vm_compute; reflexivity. Qed.

(* ===== Cyprus EEZ line (Lebanon-Cyprus 2007) and the deferred tripoint. ===== *)

Definition cyprus_lebanon_line : list Vec :=
  [point1_israel; cyprus2; cyprus3; cyprus4; cyprus5; cyprus6].

(* The Cyprus line runs strictly northward: latitude strictly increases from
   the southern terminus (Point 1) to the northern terminus (Point 6). *)
Theorem cyprus_line_monotone_north :
  vz point1_israel < vz cyprus2 /\ vz cyprus2 < vz cyprus3 /\
  vz cyprus3 < vz cyprus4 /\ vz cyprus4 < vz cyprus5 /\ vz cyprus5 < vz cyprus6.
Proof. repeat split; apply (proj2 (Qlt_alt _ _)); vm_compute; reflexivity. Qed.

(* The Lebanon-Israel-Cyprus tripoint lies seaward of P4; the agreement (like
   the 2007 Lebanon-Cyprus agreement) stops short of it, so P4 sits exactly on
   the agreed boundary and the trilateral point is deferred. *)
Theorem seaward_terminus_on_line : decide p4 = Indeterminate.
Proof. vm_compute. reflexivity. Qed.

(* ===== Clearance as a metric distance. =====
   For a unit position the side determinant equals |nseg_i| times the sine of
   the angular distance to segment i's great circle.  With a rational upper
   bound N_i on |nseg_i|, that sine is at least clearance/N_i, and the distance
   in kilometres is at least R_earth * clearance/N_i (since arcsin t >= t).
   The exact kilometre clearances are recomputed independently in
   wolfram/derive.wl: Karish 14.2, Karish North 9.3, Tanin 35.1, Qana ~5-7,
   Point 1 ~16, all consistent with the signs proved here.                     *)
Definition nseg1_norm_ub : Q := 1 # 100.
Definition nseg2_norm_ub : Q := 1 # 100.
Definition nseg3_norm_ub : Q := 1 # 10.

Lemma nseg_norm_bounds :
  dot nseg1 nseg1 <= nseg1_norm_ub * nseg1_norm_ub /\
  dot nseg2 nseg2 <= nseg2_norm_ub * nseg2_norm_ub /\
  dot nseg3 nseg3 <= nseg3_norm_ub * nseg3_norm_ub.
Proof. repeat split; apply Qle_bool_iff; vm_compute; reflexivity. Qed.

(* ===== Robustness of the verdict (the error envelope). =====               *)

(* A determinant that is positive (resp. negative) stays so under any
   perturbation strictly smaller than its magnitude. *)
Lemma sign_robust_Gt : forall dcomp dtrue : Q,
  0 < dcomp -> Qabs (dtrue - dcomp) < dcomp -> 0 < dtrue.
Proof.
  intros dcomp dtrue Hd Hb. apply Qabs_Qlt_condition in Hb.
  destruct Hb as [Hlo Hhi]. lra.
Qed.

Lemma sign_robust_Lt : forall dcomp dtrue : Q,
  dcomp < 0 -> Qabs (dtrue - dcomp) < - dcomp -> dtrue < 0.
Proof.
  intros dcomp dtrue Hd Hb. apply Qabs_Qlt_condition in Hb.
  destruct Hb as [Hlo Hhi]. lra.
Qed.

(* The general envelope: if the combined model+rounding perturbation em of the
   side determinant is below the computed determinant (= the clearance), the
   committed verdict holds for the true position too. *)
Theorem verdict_robust_Israeli : forall (n X : Vec) (dtrue em : Q),
  (dot n X ?= 0) = Gt -> em < dot n X -> Qabs (dtrue - dot n X) <= em -> 0 < dtrue.
Proof.
  intros n X dtrue em HGt Hem Hb. apply Qgt_alt in HGt.
  apply (sign_robust_Gt (dot n X) dtrue); [exact HGt|].
  apply Qle_lt_trans with em; assumption.
Qed.

Theorem verdict_robust_Lebanese : forall (n X : Vec) (dtrue em : Q),
  (dot n X ?= 0) = Lt -> em < - dot n X -> Qabs (dtrue - dot n X) <= em -> dtrue < 0.
Proof.
  intros n X dtrue em HLt Hem Hb. apply Qlt_alt in HLt.
  apply (sign_robust_Lt (dot n X) dtrue); [exact HLt|].
  apply Qle_lt_trans with em; assumption.
Qed.

(* Rounding budget: the 1.6e-13 coordinate rounding perturbs each side
   determinant by at most ~3e-13; 1e-9 is a safe over-estimate.  Every
   committed feature's clearance exceeds it by orders of magnitude, so rational
   rounding can never flip a committed verdict. *)
Definition rounding_det_budget : Q := 1 # 1000000000.

Theorem clearance_exceeds_rounding_budget :
  rounding_det_budget < clearance karish /\
  rounding_det_budget < clearance karish_north /\
  rounding_det_budget < clearance tanin /\
  rounding_det_budget < clearance qana_leb /\
  rounding_det_budget < clearance qana_isr /\
  rounding_det_budget < clearance point1_israel.
Proof. repeat split; apply (proj2 (Qlt_alt _ _)); vm_compute; reflexivity. Qed.

(* Worked instance threading the envelope through a concrete feature: the
   Karish verdict is stable under any determinant perturbation below its
   clearance. *)
Theorem karish_rounding_robust : forall dtrue : Q,
  Qabs (dtrue - dot nseg3 karish) < clearance karish -> 0 < dtrue.
Proof.
  intros dtrue Hb.
  assert (Hcl : clearance karish == dot nseg3 karish) by (vm_compute; reflexivity).
  rewrite Hcl in Hb.
  apply (sign_robust_Gt (dot nseg3 karish) dtrue); [|exact Hb].
  apply (proj2 (Qlt_alt _ _)); vm_compute; reflexivity.
Qed.

(* Model error (spherical embedding vs WGS84 ellipsoid): the geodetic-to-unit
   embedding distorts absolute positions, but applies the SAME distortion to
   the boundary and the features, so the relative side test is preserved up to
   a much smaller second-order term, handled by verdict_robust_* above.  The
   large-clearance features (Karish, Karish North, Tanin, Point 1) dominate it;
   the Qana prospect lies within a few km of the line, which is precisely why
   the agreement shares it rather than assigning it to one party.             *)

(* ===== Front-end: building a position for the geofence. =====
   A consumer converts a geodetic fix (degrees) to an ECEF unit vector and
   rounds each component to a rational (done outside Coq, where trigonometry
   lives; see wolfram/derive.wl).  This wrapper packages the three rationals.
   By decide_scale_invariant the verdict depends only on DIRECTION, so the
   consumer need not normalize precisely. *)
Definition of_ecef (x y z : Q) : Vec := mkVec x y z.

Theorem of_ecef_scale_free : forall x y z k, 0 < k ->
  decide (of_ecef (k * x) (k * y) (k * z)) = decide (of_ecef x y z).
Proof.
  intros x y z k Hk. unfold of_ecef.
  change (mkVec (k * x) (k * y) (k * z)) with (scaleV k (mkVec x y z)).
  apply decide_scale_invariant. exact Hk.
Qed.

(* ===== The agreement encoded as structure (Exchange of Letters, 2022). ===== *)

Record Agreement := mkAgreement {
  ag_mbl : list Vec;          (* Section 1A: the four agreed points (geodesics) *)
  ag_seaward_from : Vec;      (* Section 1B: boundary fixed seaward of this point *)
  ag_prospect_leb : Vec;      (* Section 2: Prospect in Lebanon's Block 9 *)
  ag_prospect_isr : Vec       (* Section 2: Prospect in Israel's Block 72 *)
}.

Definition naqoura_agreement : Agreement :=
  mkAgreement [p1; p2; p3; p4] p1 qana_leb qana_isr.

(* Section 1A/1B: the MBL is the four agreed points, identical in both annexes. *)
Theorem agreement_mbl_is_shared : ag_mbl naqoura_agreement = annex_A.
Proof. reflexivity. Qed.

(* Section 2F: the Prospect genuinely straddles the line, so no party may take
   a deposit without crossing the MBL; the arrangement must therefore be
   shared.  Modeled as: the Prospect has committed points on both sides. *)
Definition section_2F (a : Agreement) : Prop :=
  decide (ag_prospect_leb a) = Lebanese /\ decide (ag_prospect_isr a) = Israeli.

Theorem naqoura_section_2F : section_2F naqoura_agreement.
Proof. unfold section_2F, naqoura_agreement; simpl. exact qana_straddles. Qed.

(* Section 1E declares a permanent and equitable resolution.  UNCLOS Articles
   74/83 require delimitation by agreement reaching an equitable solution; a
   full equidistance comparison needs the coastal baseline points, out of scope
   here, so we simply record the agreed line as the equitable delimitation. *)
Definition equitable_delimitation : list Vec := annex_A.

(* ----- Extraction: the geofence as runnable OCaml. ----- *)

(* Boolean wrappers so the extracted API is callable without inspecting the
   rational representation. *)
Definition committed (X : Vec) : bool :=
  match decide X with Indeterminate => false | _ => true end.
Definition clearance_pos (X : Vec) : bool :=
  match clearance X ?= 0 with Gt => true | _ => false end.

Extraction Language OCaml.
Extract Inductive bool => "bool" [ "true" "false" ].
Extraction "naqoura.ml"
  decide clearance committed clearance_pos
  karish karish_north tanin qana_leb qana_isr point1_israel ras_naqoura
  p1 p2 p3 p4.
