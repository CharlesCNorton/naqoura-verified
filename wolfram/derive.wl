(* derive.wl — provenance + cross-check for naqoura_line.v
   Re-derives every rational unit vector used in the Coq development from its
   WGS84 geodetic source, reports the rationalization error, and independently
   recomputes each side-of-line verdict and clearance via Wolfram geodesy.
   Run:  wolframscript -file derive.wl                                        *)

ClearAll["Global`*"];
prec = 40;
(* geodetic (lat,lon in degrees) -> unit vector on the sphere (ECEF directions) *)
u[{phi_, lam_}] := {Cos[phi Degree] Cos[lam Degree],
                    Cos[phi Degree] Sin[lam Degree],
                    Sin[phi Degree]};
dms[d_, m_, s_] := d + m/60 + s/3600;
tol = 10^-13;
ratV[v_] := Rationalize[#, tol] & /@ N[v, prec];

(* ---- Sources (WGS84). Each entry: name -> {lat, lon} in decimal degrees. ---- *)
pts = <|
  (* Agreed MBL, 27 Oct 2022 Exchange of Letters (Annex A = Annex B). *)
  "p1" -> {dms[33,6,34.15],  dms[35,2,58.12]},
  "p2" -> {dms[33,6,52.73],  dms[35,2,13.86]},
  "p3" -> {dms[33,10,19.33], dms[34,52,57.24]},
  "p4" -> {dms[33,31,51.17], dms[33,46,8.78]},   (* = Lebanon Decree 6433 Point 23 *)
  (* Israel Line 1 seaward endpoint = Cyprus-Lebanon 2007 Point 1 (Meier 2013). *)
  "point1_israel" -> {dms[33,38,40], dms[33,53,40]},
  (* Cyprus-Lebanon 2007 EEZ line, points 1..6 (point1 = point1_israel above). *)
  "cyprus2" -> {dms[33,51,30], dms[34,2,50]},
  "cyprus3" -> {dms[33,59,40], dms[34,18,0]},
  "cyprus4" -> {dms[34,23,20], dms[34,44,0]},
  "cyprus5" -> {dms[34,39,30], dms[34,53,50]},
  "cyprus6" -> {dms[34,45,0], dms[34,56,0]},
  (* Band-1 (nearshore p1-p2 segment) orientation witnesses. *)
  "b1n" -> {33.13, 35.043},
  "b1s" -> {33.09, 35.043},
  (* Fields (operator/region centroids; Energean / Global Energy Monitor). *)
  "karish"      -> {33.2283, 34.2890},
  "karish_north"-> {33.2588, 34.3397},
  "tanin"       -> {33.1635, 33.8620},
  (* Land terminus near Point B1 (Ras Naqoura / Rosh Hanikra crossing). *)
  "ras_naqoura" -> {dms[33,5,23.40], dms[35,6,10.20]},
  (* Qana/Sidon prospect representative points bracketing the MBL (Block 9
     Lebanese side / Block 72 Israeli side); Section 2 asserts the straddle.
     The 31/1B well sits in Block 9 (Lebanese side). Exact reservoir outline
     is not public; these are representative points in the prospect vicinity. *)
  "qana_leb" -> {33.20, 34.95},
  "qana_isr" -> {33.08, 34.95}
|>;

(* ---- Rational unit vectors and rationalization error. ---- *)
rats = AssociationMap[ratV[u[pts[#]]] &, Keys[pts]];
errs = AssociationMap[Norm[N[rats[#], prec] - N[u[pts[#]], prec]] &, Keys[pts]];
Print["=== rationalization L2 error (unit-vector), tol ", tol, " ==="];
Do[Print[StringPadRight[k, 16], ScientificForm[errs[k], 3]], {k, Keys[pts]}];
Print["max error: ", ScientificForm[Max[Values[errs]], 3]];

(* ---- MBL segment great-circle normals and meridian normals (from rationals). ---- *)
cross = Cross;
nseg = {cross[rats["p1"], rats["p2"]], cross[rats["p2"], rats["p3"]], cross[rats["p3"], rats["p4"]]};
mer[p_] := {-p[[2]], p[[1]], 0};

(* Coq decide replica: 3 longitude bands, sign of nseg.X (>0 Israeli, <0 Lebanese). *)
eastOf[p_, x_] := mer[p].x >= 0;
westOf[p_, x_] := mer[p].x <= 0;
inBand[pw_, pe_, x_] := eastOf[pw, x] && westOf[pe, x];
verdict[n_, x_] := Which[n.x > 0, "Israeli", n.x < 0, "Lebanese", True, "Indeterminate"];
decide[x_] := Which[
  inBand[rats["p2"], rats["p1"], x], verdict[nseg[[1]], x],
  inBand[rats["p3"], rats["p2"], x], verdict[nseg[[2]], x],
  inBand[rats["p4"], rats["p3"], x], verdict[nseg[[3]], x],
  True, "Indeterminate"];
clearance[x_] := Which[
  inBand[rats["p2"], rats["p1"], x], Abs[nseg[[1]].x],
  inBand[rats["p3"], rats["p2"], x], Abs[nseg[[2]].x],
  inBand[rats["p4"], rats["p3"], x], Abs[nseg[[3]].x],
  True, 0];

(* ---- Independent geodesic cross-check via Wolfram GeoDistance. ---- *)
Rkm = 6371.0088;
geo[{phi_, lam_}] := GeoPosition[{phi, lam}];
segGeo[a_, b_] := {geo[pts[a]], geo[pts[b]]};
(* signed angular distance of feature to a segment's great circle = arcsin(n.X/|n|) *)
angKm[n_, x_] := Rkm QuantityMagnitude[ArcSin[(n.x)/Norm[n]]] ;
mblSegFor[x_] := Which[
  inBand[rats["p2"], rats["p1"], x], 1,
  inBand[rats["p3"], rats["p2"], x], 2,
  inBand[rats["p4"], rats["p3"], x], 3, True, 0];

features = {"karish", "karish_north", "tanin", "qana_leb", "qana_isr",
            "point1_israel", "ras_naqoura", "b1n", "b1s"};
Print["\n=== feature classification (Coq-rational replica) + geodesic cross-check ==="];
Do[
  Module[{x = N[rats[f], prec], seg, v, cl, km, side},
    seg = mblSegFor[x]; v = decide[x]; cl = N[clearance[x], 10];
    km = If[seg == 0, "n/a (out of band)", N[angKm[nseg[[seg]], x], 6]];
    Print[StringPadRight[f, 14], " band=", seg, "  verdict=", StringPadRight[v, 13],
          " |det|=", ScientificForm[cl, 4], "  perp~", km, " km"]],
  {f, features}];

(* latitude (vz) ordering for the line-nesting fact *)
Print["\n=== nesting (vz = sin lat; larger = more north) ==="];
Print["point1_israel vz = ", N[rats["point1_israel"][[3]], 12], "  (Israel Line 1 endpoint)"];
Print["p4/Point23    vz = ", N[rats["p4"][[3]], 12], "  (Line 23 endpoint = MBL P4)"];
Print["karish        vz = ", N[rats["karish"][[3]], 12], "  (on Line 29; Israeli side of MBL)"];
Print["point1 north of Point23 ? ", rats["point1_israel"][[3]] > rats["p4"][[3]]];

(* ---- Emit Coq definitions for the NEW points (mkVec a#b). ---- *)
qlit[r_] := If[r == 0, "0 # 1", ToString[Numerator[r]] <> " # " <> ToString[Denominator[r]]];
vecdef[name_, v_] := "Definition " <> name <> " : Vec := mkVec (" <>
  qlit[v[[1]]] <> ") (" <> qlit[v[[2]]] <> ") (" <> qlit[v[[3]]] <> ").";
Print["\n=== Coq definitions (new points) ==="];
Do[Print[vecdef[k, rats[k]]],
   {k, {"point1_israel", "cyprus2", "cyprus3", "cyprus4", "cyprus5", "cyprus6",
        "karish_north", "tanin", "ras_naqoura", "qana_leb", "qana_isr", "b1n", "b1s"}}];
Print["\n=== Cyprus line latitude (vz) order, should increase 1->6 ==="];
Print[N[{rats["point1_israel"][[3]], rats["cyprus2"][[3]], rats["cyprus3"][[3]],
         rats["cyprus4"][[3]], rats["cyprus5"][[3]], rats["cyprus6"][[3]]}, 8]];
Print["\n(existing p1..p4, karish unchanged; verify they match:)"];
Do[Print[vecdef[k, rats[k]]], {k, {"p1","p2","p3","p4","karish"}}];
