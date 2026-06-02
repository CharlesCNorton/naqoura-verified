(* Differential-test runner for the extracted geofence.  Reads positions from
   stdin, one per line as six integers "xnum xden ynum yden znum zden", builds
   the extracted rational vector, and prints "<verdict> <committed> <clearance_pos>"
   for each.  difftest.py feeds it tens of thousands of points and checks every
   line against an independent oracle.  Built by difftest.sh. *)

open Naqoura

(* OCaml int -> extracted Coq positive / Z / Q (numerators here are < 2^53). *)
let rec pos_of_int n =
  if n <= 1 then XH
  else if n land 1 = 1 then XI (pos_of_int (n asr 1))
  else XO (pos_of_int (n asr 1))

let z_of_int n =
  if n = 0 then Z0 else if n > 0 then Zpos (pos_of_int n) else Zneg (pos_of_int (- n))

let mkq n d = { qnum = z_of_int n; qden = pos_of_int d }

let string_of_side = function
  | Israeli -> "Israeli" | Lebanese -> "Lebanese" | Indeterminate -> "Indeterminate"

let () =
  try
    while true do
      let line = input_line stdin in
      if String.trim line <> "" then
        Scanf.sscanf line " %d %d %d %d %d %d"
          (fun xn xd yn yd zn zd ->
            let v = { vx = mkq xn xd; vy = mkq yn yd; vz = mkq zn zd } in
            Printf.printf "%s %b %b\n"
              (string_of_side (decide v)) (committed v) (clearance_pos v))
    done
  with End_of_file -> ()
