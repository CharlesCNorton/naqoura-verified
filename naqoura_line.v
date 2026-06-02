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
From Stdlib Require Import Lqa.
From Stdlib Require Import Extraction.

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

(* ----- Extraction: the geofence as runnable OCaml. ----- *)

Extraction Language OCaml.
Extraction "naqoura.ml" decide clearance.
