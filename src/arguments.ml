open Printf
open Globals
open Debug

let usage_msg = ref ""

let raw_arguments_release =
  [(["-h"; "-help"; "--help"], "Display list of options",
    Arg.Unit (fun () -> print_string !usage_msg))]

let common_raw_arguments_internal =
  [(["-drc"],
    "Debug by regular expression and print input, \n\
     output by chronological order",
    Arg.String (fun s ->
      debug_normal_mode := true;
      trace_function_mode := true;
      trace_function_printing_order := PrintChrono;
      trace_function_regex := s));
   (["-drd"],
    "Debug by regular expression and print input, \n\
     output by direct order",
    Arg.String (fun s ->
      debug_normal_mode := true;
      trace_function_mode := true;
      trace_function_printing_order := PrintPair;
      trace_function_regex := s));
   (["--debug"; "-d"],
    "Normal debug mode, print necessary debugging information",
    Arg.Unit (fun () ->
      trace_debug := true;
      debug_normal_mode := true;
      print_prover_stats := false;
      print_prover_option := false));
   (["--debug-deep"; "-dd"],
    "Deep debug mode, print all debugging information",
    Arg.Unit (fun () ->
      trace_debug := true;
      debug_normal_mode := true;
      debug_deep_mode := true;
      print_prover_stats := true;
      print_prover_option := true;));
   (["--debug-silence"], "Disable printing debugging information",
    Arg.Set debug_silence);
   (["-h"; "-help"; "--help"], "Display list of options",
    Arg.Unit (fun () -> ()));
  ]

(* Knotical's arguments *)
let knotical_arguments_internal =
  [(["-interproc"],
    "Source file for the interproc engine",
    Arg.String (fun s ->
      interproc_source_file := s));
   (["-kat"],
    "Source file for the kat parser",
    Arg.String (fun s ->
      kat_source_file := s));
   (["-symkat"],
    "Inputs of SymKAT",
    Arg.Tuple ([
        Arg.Set_string symkat_x;
        Arg.Set_string symkat_y ]));
   (["-ked"],
    "KAT Edit Distance",
    Arg.Tuple ([
        Arg.Set_string symkat_x;
        Arg.String (fun s ->
            ked_enabled := true;
            symkat_y := s;) ]));
   (["-cmp"],
    "Two methods to compare",
    Arg.Tuple ([
        Arg.Set_string fst_cmp_method;
        Arg.String (fun s ->
            snd_cmp_method := s;
            compare_mode_enabled := true; )
      ]));
   (["-cmpLt"],
    "Two methods to compare",
    Arg.Tuple ([
        Arg.Set_string fst_cmp_method;
        Arg.String (fun s ->
            snd_cmp_method := s;
            compare_mode_enabled := true;
            refinement_op := RLe; )
      ]));
   (["-no-rem"],
    "List of events that cannot be removed",
    Arg.String (fun s ->
        no_removed_events := String.split_on_char ',' s));
   (["-depth"], "Depth of proof search",
    Arg.Set_int rec_depth_threshold);
   (["-pi"], "Print program in intermediate language",
    Arg.Set print_prog_iast);
   (["-tex"], "Print results in LaTeX",
    Arg.Set print_tex);
  ]

(* all arguments with pretty printing *)
let mk_arguments raw_arguments =
  let arguments = List.fold_left (fun acc (keys, doc, spec) ->
    let options = List.map (fun k ->
      let ndoc = doc in
      (k, spec, " : "  ^ ndoc)) keys in
    acc @ options) [] raw_arguments in
  arguments

let parse f msg raw_arguments =
  let arguments = mk_arguments raw_arguments in
  let arg_str = arguments
                |> List.map (fun (x, y, z) -> "  " ^ x ^ z)
                |> String.concat "\n" in
  let usage = msg ^ "\n" ^ arg_str ^ "\n\n" in
  try
    let arguments = List.fold_left (fun acc (x, y, z) ->
      if (String.compare x "-h" != 0) &&
         (String.compare x "-help" != 0) &&
         (String.compare x "--help" != 0) then
        acc @ [(x, y, z)]
      else acc) [] arguments in

    let arguments = arguments @ [
      ("-h", Arg.Unit (fun () -> print_string usage),
       "Display list of options");
      ("-help", Arg.Unit (fun () -> print_string usage),
       "Display list of options");
      ("--help", Arg.Unit (fun () -> print_string usage),
       "Display list of options");] in
    Arg.parse_argv Sys.argv arguments f msg
  with
  | Arg.Bad _ ->
    let path = Sys.argv.(0) in
    let bad_arg = Sys.argv.(!Arg.current) in
    eprintf "\n%s: unknown option '%s'\n" path bad_arg;
    eprintf "%s" usage; exit 2
  | Arg.Help _ -> printf "%s" usage; exit 0
