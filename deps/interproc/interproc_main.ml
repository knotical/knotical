(** Master module *)

(* This file is part of the Interproc analyzer, released under GPL license.
   Please read the COPYING file packaged in the distribution.

   Copyright (C) Mathias Argoud, Gaël Lalire, Bertrand Jeannet 2007.
*)

open Format
open Opt

let main () =
  (* Parsing the command line *)
  Arg.parse
    Opt.speclist
      (begin fun name -> Opt.inputfilename := name end)
      "interproc <options> <inputfile>"
  ;
  (* Parsing the program *)
  let input = open_in !Opt.inputfilename in
  let lexbuf = Lexing.from_channel input in
  lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with
    Lexing.pos_fname = "file "^(!Opt.inputfilename);
  };
  let prog = Frontend.parse_lexbuf Format.err_formatter lexbuf in
  close_in input;
  
  if !debug>0 then
    printf "%sProgram with its control points:%s@.%a@."
      (!Opt.displaytags).precolorB (!Opt.displaytags).postcolor
      (PSpl_syn.print_program
	(begin fun fmt point ->
	  fprintf fmt "%s%a%s"
	  (!Opt.displaytags).precolorR
	  PSpl_syn.print_point point
	  (!Opt.displaytags).postcolor
	end))
      prog
  ;

  (* Computing solution *)
  Frontend.analyze_and_display Format.std_formatter prog;
  ()

let _ = main()
