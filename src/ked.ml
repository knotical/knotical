open Globals
open Lib
open Lib.Print

module SKW = Symkat_wrapper

module IK = SKW.ILK
module KD = Kdiff

let compare x y =
  let kat_x = Parse.expr ~msg:"First kat: " x in
  let kat_y = Parse.expr ~msg:"Second kat: " y in
  let kx = IK.expr_of_kat kat_x in
  let ky = IK.expr_of_kat kat_y in
  let () = Debug.hprint "kx: " IK.pr_expr kx in
  let () = Debug.hprint "ky: " IK.pr_expr ky in
  let kdist, time = Func.core_time (fun () ->
      KD.edit_distance (kx, ky)) in
  let pr_match (m1, m2) =
    ("fst match: " ^ (KD.pr_kelt m1)) ^ "\n" ^
    ("snd match: " ^ (KD.pr_kelt m2)) ^ "\n" in
  let () = DB.hprint "kdist: " (KD.pr_kdist KD.pr_kelt pr_match) kdist in
  let () = DB.dhprint "time: " pr_core_time time in
  ()
