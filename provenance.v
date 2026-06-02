(* Per-point WGS84 provenance, machine-checked over the reals.

   A third, optional layer above the rational kernel (axiom-free) and the
   classical-reals bridge.  For each agreed MBL point P1..P4 it certifies that
   the stored rational components match, to within 1e-12, the spherical ECEF
   embedding (cos lat * cos lon, cos lat * sin lon, sin lat) of that point's
   deposited degrees-minutes-seconds coordinates.  The latitudes and longitudes
   are the exact /360000 rationals of the deposited DMS.  The transcendental
   bound is discharged by CoqInterval's [interval] tactic (validated interval
   arithmetic with a Taylor model for sin/cos), pinning the rational data to the
   transcendental geodetic formula inside Coq, not only in Wolfram.

   Axiom basis (audited in audit_provenance.v): the standard classical
   real-number axioms used throughout the bridge, plus Coq's primitive 63-bit
   integer arithmetic (PrimInt63 / Uint63Axioms), which CoqInterval uses for
   fast exact multi-precision computation.  The primitive-integer axioms are
   part of Coq's native-arithmetic trusted base (realized by the OCaml runtime),
   not classical-logic axioms; they are kept out of the kernel and the bridge by
   confining this layer to its own file.

   Run:  coqc naqoura_line.v && coqc provenance.v *)

Require Import naqoura_line.
From Stdlib Require Import Reals Qreals.
From Interval Require Import Tactic.
Open Scope R_scope.

(* Degrees-to-radians, and the 1e-12 component tolerance. *)
Definition deg2rad (d : R) : R := d * PI / 180.
Definition wgs84_eps : R := 1 / 1000000000000.

(* Deposited DMS of each point as exact /360000 degree rationals:
   P1 33 06 34.15 N / 35 02 58.12 E, P2 33 06 52.73 N / 35 02 13.86 E,
   P3 33 10 19.33 N / 34 52 57.24 E, P4 33 31 51.17 N / 33 46 08.78 E. *)

Theorem p1_matches_wgs84_dms :
  Rabs (Q2R (vx p1) - cos (deg2rad (11919415/360000)) * cos (deg2rad (12617812/360000))) <= wgs84_eps /\
  Rabs (Q2R (vy p1) - cos (deg2rad (11919415/360000)) * sin (deg2rad (12617812/360000))) <= wgs84_eps /\
  Rabs (Q2R (vz p1) - sin (deg2rad (11919415/360000))) <= wgs84_eps.
Proof.
  unfold wgs84_eps, deg2rad, Q2R, vx, vy, vz, p1; repeat split;
    simpl (Qnum _); simpl (Qden _); interval with (i_prec 90).
Qed.

Theorem p2_matches_wgs84_dms :
  Rabs (Q2R (vx p2) - cos (deg2rad (11921273/360000)) * cos (deg2rad (12613386/360000))) <= wgs84_eps /\
  Rabs (Q2R (vy p2) - cos (deg2rad (11921273/360000)) * sin (deg2rad (12613386/360000))) <= wgs84_eps /\
  Rabs (Q2R (vz p2) - sin (deg2rad (11921273/360000))) <= wgs84_eps.
Proof.
  unfold wgs84_eps, deg2rad, Q2R, vx, vy, vz, p2; repeat split;
    simpl (Qnum _); simpl (Qden _); interval with (i_prec 90).
Qed.

Theorem p3_matches_wgs84_dms :
  Rabs (Q2R (vx p3) - cos (deg2rad (11941933/360000)) * cos (deg2rad (12557724/360000))) <= wgs84_eps /\
  Rabs (Q2R (vy p3) - cos (deg2rad (11941933/360000)) * sin (deg2rad (12557724/360000))) <= wgs84_eps /\
  Rabs (Q2R (vz p3) - sin (deg2rad (11941933/360000))) <= wgs84_eps.
Proof.
  unfold wgs84_eps, deg2rad, Q2R, vx, vy, vz, p3; repeat split;
    simpl (Qnum _); simpl (Qden _); interval with (i_prec 90).
Qed.

Theorem p4_matches_wgs84_dms :
  Rabs (Q2R (vx p4) - cos (deg2rad (12071117/360000)) * cos (deg2rad (12156878/360000))) <= wgs84_eps /\
  Rabs (Q2R (vy p4) - cos (deg2rad (12071117/360000)) * sin (deg2rad (12156878/360000))) <= wgs84_eps /\
  Rabs (Q2R (vz p4) - sin (deg2rad (12071117/360000))) <= wgs84_eps.
Proof.
  unfold wgs84_eps, deg2rad, Q2R, vx, vy, vz, p4; repeat split;
    simpl (Qnum _); simpl (Qden _); interval with (i_prec 90).
Qed.
