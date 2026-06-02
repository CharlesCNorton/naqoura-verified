(* Self-test for the extracted geofence (naqoura.ml).  Builds with the extracted
   module and checks that the runnable OCaml verdicts match the Coq theorems.
   Built and run by build.sh. *)

open Naqoura

let string_of_side = function
  | Israeli -> "Israeli"
  | Lebanese -> "Lebanese"
  | Indeterminate -> "Indeterminate"

let failures = ref 0

let check name v expected =
  let got = string_of_side (decide v) in
  let ok = got = expected in
  if not ok then incr failures;
  Printf.printf "  %-14s decide=%-13s committed=%-5b clearance_pos=%-5b  [%s]\n"
    name got (committed v) (clearance_pos v)
    (if ok then "OK" else "MISMATCH, expected " ^ expected)

let () =
  print_endline "naqoura geofence - extracted OCaml self-test";
  check "karish"        karish        "Israeli";
  check "karish_north"  karish_north  "Israeli";
  check "tanin"         tanin         "Israeli";
  check "qana_leb"      qana_leb      "Lebanese";
  check "qana_isr"      qana_isr      "Israeli";
  check "point1_israel" point1_israel "Lebanese";
  check "ras_naqoura"   ras_naqoura   "Indeterminate";
  check "p4 (on line)"  p4            "Indeterminate";
  check "b1n"           b1n           "Lebanese";
  check "b1s"           b1s           "Israeli";
  check "south_pole"    south_pole    "Israeli";
  check "north_pole"    north_pole    "Lebanese";
  check "israel_pt34"   israel_point34 "Lebanese";
  check "israel_pt35"   israel_point35 "Lebanese";
  if !failures = 0 then
    print_endline "all extracted verdicts match the Coq theorems."
  else begin
    Printf.printf "%d mismatch(es).\n" !failures; exit 1
  end
