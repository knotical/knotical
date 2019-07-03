open Globals
open Lib
open Lib.Func
open Lib.Basic
open Spl_syn

module I = Iast
module L = Klexer.Make(Token.Token)
module DB = Debug
module K = Kat_utils
module SK = Symkat
(* module SKW = Symkat_wrapper *)

let main () =
  try
    let _ = Printexc.record_backtrace true in
    let usage_msg =
      "\nKnotical - A Inference of \
       Trace Relational Interfaces \
       with Dual Refinement \n\n" ^
      "Usage: " ^ Sys.argv.(0) ^ " [options] <source files>\n"
    in
    let set_source_file arg = source_files := arg :: !source_files in
    let _ = Arguments.parse set_source_file usage_msg
        (Arguments.knotical_arguments_internal @
         Arguments.common_raw_arguments_internal) in
    (* Interproc *)
    if String.length !interproc_source_file != 0 then
      let _ = print_endline "Invoking Interproc ..." in
      let () = Spl.analyze_from_source !interproc_source_file in
      ()

    (* SymKAT *)
    else if String.length !symkat_x != 0 &&
            String.length !symkat_y != 0 then
      if !ked_enabled then
        Ked.compare !symkat_x !symkat_y
      else
        let _ = print_endline "Invoking SymKAT ..." in
        let res = SK.run !symkat_x !symkat_y in
        ()

    (* Knotical *)
    else if List.length !source_files != 0 then
      let iprog = Kparser.parse_one_file (List.hd !source_files) in
      if !compare_mode_enabled then
        let () = Debug.pprint ("Comparing two procedures " ^ !fst_cmp_method ^
                               " and " ^ !snd_cmp_method ^ " ...") in
        let _ = Kdiff.analyze iprog !fst_cmp_method !snd_cmp_method in
        ()
      else ()
    else ()
  with e ->
    error ("Exception: " ^ (pr_exn e) ^
           "\nBacktrace: " ^ (Printexc.get_backtrace ()))

let () =
  let _, t = time main in
  DB.rsprint [" ==> (Knotical) Time: "; Printf.sprintf "%.2f" t; " (s)\n"]
