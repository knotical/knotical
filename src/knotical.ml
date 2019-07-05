open Globals
open Lib
open Lib.Func
open Lib.Basic

module I = Iast
module L = Klexer.Make(Token.Token)
module DB = Debug
module K = Kat_utils
module SK = Symkat
module SKU = Symkat_utils

let parse_one_file (file: string): I.prog_decl =
  let () = input_file_name := file in
  let inchan =
    try open_in file
    with e -> error ("Unable to open file: " ^ file) in
  let iprog =
    try Kparser.parse_program file (Stream.of_channel inchan)
    with
    | Not_found -> error ("File not found: " ^ file)
    | End_of_file -> error ("Unable to parse file: " ^ file)
    | L.Loc.Exc_located (l, t) -> raise t in
  let () = close_in inchan in
  let () = if !print_prog_iast then (
    let program =
      "============================================\n" ^
      "=========      Parsed Program      =========\n" ^
      "============================================\n\n" ^
      (I.pr_prog ~pr_paren:true iprog) ^ "\n\n" in
    print_endline program) in

  (* let cfg_prog = I.trans_cfg_prog_decl iprog in
   * let flatten_cfg_prog = I.flatten_prog_decl cfg_prog in
   * let () = if !print_prog_iast then (
   *   let program =
   *     "=============================================\n" ^
   *     "=========      Flatten Program      =========\n" ^
   *     "=============================================\n\n" ^
   *     (String.concat "\n\n"
   *        (List.map (fun (name, stmt_lst) ->
   *             name ^ "\n\t" ^
   *             (String.concat "\n\t" (List.map I.pr_stmt stmt_lst))
   *           ) flatten_cfg_prog)) ^ "\n\n" in
   *   print_endline program) in
   * let cfg_lst = List.map (fun (name, stmt_lst) ->
   *     (name, Cfg.trans_cfg stmt_lst)) flatten_cfg_prog in
   * let () = if !print_prog_iast then (
   *   let program =
   *     "=================================\n" ^
   *     "=========      CFG      =========\n" ^
   *     "=================================\n\n" ^
   *     (String.concat "\n\n"
   *        (List.map (fun (name, cfg) ->
   *             name ^ "\n\t" ^ (Cfg.CFG.print cfg)
   *           ) cfg_lst)) ^ "\n\n" in
   *   print_endline program) in
   * let kat1s = List.map (fun (name, cfg) ->
   *     KI.kat_interp (Iface.mk_true ()) cfg) cfg_lst in *)
  iprog

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
    let _ = Arguments.parse set_source_file usage_msg in
    (* Interproc *)
    if String.length !interproc_source_file != 0 then
      let _ = print_endline "Invoking Interproc ..." in
      let spl_prog = Iproc.parse !interproc_source_file in
      let () = Frontend.analyze_and_display Format.std_formatter spl_prog in
      ()

    (* SymKAT *)
    else if String.length !symkat_x != 0 &&
            String.length !symkat_y != 0 then
      let _ = print_endline "Invoking SymKAT ..." in
      let res = SK.run !symkat_x !symkat_y in
      ()

    (* KAT Parser *)
    else if String.length !kat_source_file != 0 then
      let _ = print_endline "Parsing KAT ..." in
      let inchan =
        try open_in !kat_source_file
        with e -> error ("Unable to open file: " ^ !kat_source_file) in
      let kat_formula =
        try Kat_parser.parse_kat !kat_source_file (Stream.of_channel inchan)
        with
        | Not_found -> error ("File not found: " ^ !kat_source_file)
        | End_of_file -> error ("Unable to parse file: " ^ !kat_source_file)
        | L.Loc.Exc_located (l, t) -> raise t in
      print_endline (K.pr_kat kat_formula.K.k_expr)

    (* Knotical *)
    else
      let iprog = parse_one_file (List.hd !source_files) in
      if !compare_mode_enabled then
        let () = Debug.pprint ("Comparing two procedures " ^ !fst_cmp_method ^
                              " and " ^ !snd_cmp_method ^ " ...") in
        let _ = Kdiff.analyze iprog !fst_cmp_method !snd_cmp_method in
        ()
      else ()
  with e ->
    error ("Exception: " ^ (pr_exn e) ^
           "\nBacktrace: " ^ (Printexc.get_backtrace ()))

let () =
  let _, t = time main in
  DB.rsprint [" ==> Time: "; Printf.sprintf "%.2f" t; " (s)\n"]
