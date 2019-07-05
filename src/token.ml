open Camlp4.PreCast

type token =
  | ID of string
  | INT_LIT of int * string
  | FLOAT_LIT of float * string
  | STRING of string * string
  | TRUE | FALSE
  | NONDET
  | LT | GT | LE | GE | EQ | EQEQ | NE | COLONEQ
  | PLUS | MINUS | DIV | MULT | MOD
  | PLUS_ASSIGN | MINUS_ASSIGN | DIV_ASSIGN | MULT_ASSIGN | MOD_ASSIGN
  | AND | ANDAND | OR | OROR | NOT
  | METAAND | METAOR
  | OBRACE | CBRACE | OPAREN | CPAREN | OSQUARE | CSQUARE
  | SEMICOLON | COMMA | ARROW | DOT | DOTDOT
  | COLON | COLONCOLON
  | INT | FLOAT | BOOL | VOID
  | WHILE | CIF | CELSE
  | BREAK | CONTINUE | RETURN | GOTO | SKIP
  | ASSERT | ASSUME
  | EOF


module type KnoticalToken = Camlp4.Sig.Token with type t = token

module Token = struct
  open Format
  module Loc = Loc
  type t = token
  type token = t

  let sf = Printf.sprintf

  let to_string k = match k with
    | ID s | INT_LIT (_, s) | FLOAT_LIT (_, s) | STRING (_, s) -> s
    | FALSE -> "false" | TRUE -> "true"
    | NONDET -> "*"
    | LT -> "<" | GT -> ">" | LE -> "<=" | GE -> ">="
    | EQ -> "=" | EQEQ -> "==" | NE -> "!=" | COLONEQ -> ":="
    | PLUS -> "+" | MINUS -> "-" | MULT -> "*" | DIV -> "/" | MOD -> "%"
    | PLUS_ASSIGN -> "+=" | MINUS_ASSIGN -> "-="
    | DIV_ASSIGN -> "/=" | MULT_ASSIGN -> "*=" | MOD_ASSIGN -> "%="
    | AND -> "&" | ANDAND -> "&&" | OR -> "|" | OROR -> "||" | NOT -> "!"
    | METAAND -> "/\\" | METAOR -> "\\/"
    | OBRACE -> "{" | CBRACE -> "}"
    | OPAREN -> "(" | CPAREN -> ")"
    | OSQUARE -> "[" | CSQUARE -> "]"
    | SEMICOLON -> ";" | COMMA -> ","
    | ARROW -> "->" | DOT -> "." | DOTDOT -> ".."
    | COLON -> ":" | COLONCOLON -> "::"
    | INT -> "int" | FLOAT -> "float" | BOOL -> "bool" | VOID -> "void"
    | WHILE -> "while" | CIF -> "if" | CELSE -> "else"
    | BREAK -> "break" | CONTINUE -> "continue"
    | RETURN -> "return" | GOTO -> "goto" | SKIP -> "skip"
    | ASSERT -> "assert" | ASSUME -> "assume"
    | EOF -> "EOF"

  let print ppf x = pp_print_string ppf (to_string x)

  let match_keyword kwd _ = false

  let extract_string t = match t with
    | ID s | INT_LIT (_, s) | FLOAT_LIT (_, s) | STRING (_, s) -> s
    | _ -> ""

  module Error = struct
    type t = string
    exception E of string
    let print = pp_print_string
    let to_string x = x
  end

  module Filter = struct
    type token_filter = (t, Loc.t) Camlp4.Sig.stream_filter

    type t = {
      is_kwd : string -> bool;
      mutable filter : token_filter
    }

    let mk is_kwd =
      { is_kwd = is_kwd;
        filter = (fun s -> s) }

    let filter x = fun strm -> x.filter strm

    let define_filter x f = x.filter <- f x.filter

    let keyword_added _ _ _ = ()
    let keyword_removed _ _ = ()
  end

end

module Error = Camlp4.Struct.EmptyError
