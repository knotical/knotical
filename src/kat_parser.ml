open Token
open Camlp4
open Debug
open Globals
open Lib
open Kat_utils

module Lex = Klexer.Make(Token)
module Gram = Camlp4.Struct.Grammar.Static.Make(Lex)

(* compute the position by adding the location return by camlp4 *)
let get_pos l =
  let sp = Camlp4.PreCast.Loc.start_pos l in
  let ep = Camlp4.PreCast.Loc.stop_pos l in
  { pos_begin = sp;
    pos_end = ep; }

let kat_formula = Gram.Entry.mk "kat_formula"

EXTEND Gram
GLOBAL: kat_formula;

  kat_formula:
    [[ `EOF -> { k_defn_lst = []; k_expr = Ktrue }]];

END;;

(* parsing commands *)

let parse_kat name stream =
  try
    let katf = Gram.parse kat_formula (PreCast.Loc.mk name) stream in
    katf
  with
  | Lex.Loc.Exc_located (l, t) ->
    let pos = get_pos l in
    let filename = pos.pos_begin.Lexing.pos_fname in
    let location = pr_pos pos in
    let spos = "Location: File: " ^ filename ^ ". Line/Column: " ^ location in
    let msg = "Message: " ^ (pr_exn t) in
    error ("Syntax error!\n" ^ msg ^ "\n" ^ spos)
  | e -> raise e
