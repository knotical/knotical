{
open Globals

open Token
(** A signature for specialized tokens. *)
module Sig = Camlp4.Sig

module Make (Token : KnoticalToken) = struct
  module Loc = Token.Loc
  module Token = Token

  open Lexing

  module Error = struct

    type t =
      | Illegal_character of char
      | Illegal_escape of string
      | Unterminated_comment
      | Unterminated_string
      | Comment_start
      | Comment_not_end
      | Literal_overflow of string

    exception E of t

    open Format

    let print ppf =
      function
      | Illegal_character c -> fprintf ppf "Illegal character (%s)" (Char.escaped c)
      | Illegal_escape s -> fprintf ppf "Illegal backslash escape in string or character (%s)" s
      | Unterminated_comment -> fprintf ppf "Comment not terminated"
      | Unterminated_string -> fprintf ppf "String literal not terminated"
      | Literal_overflow ty -> fprintf ppf "Integer literal exceeds the range of representable integers of type %s" ty
      | Comment_start -> fprintf ppf "this is the start of a comment"
      | Comment_not_end -> fprintf ppf "this is not the end of a comment"

    let to_string x =
      let b = Buffer.create 50 in
      let to_b = formatter_of_buffer b in
      let () = fprintf to_b "%a" print x in
      Buffer.contents b
  end;;

  let module M = Camlp4.ErrorHandler.Register(Error) in ()

  open Error

  type context =
    { loc        : Loc.t    ;
      in_comment : bool     ;
      lexbuf     : lexbuf   ;
      buffer     : Buffer.t }

  let default_context lb =
    { loc        = Loc.ghost ;
      in_comment = false     ;
      lexbuf     = lb        ;
      buffer     = Buffer.create 256 }

  (* To buffer string literals *)

  let store c = Buffer.add_string c.buffer (Lexing.lexeme c.lexbuf)
  let istore_char c i = Buffer.add_char c.buffer (Lexing.lexeme_char c.lexbuf i)
  let buff_contents c =
    let contents = Buffer.contents c.buffer in
    Buffer.reset c.buffer; contents

  let loc c = Loc.merge c.loc (Loc.of_lexbuf c.lexbuf)
  let is_in_comment c = c.in_comment
  let in_comment c = { (c) with in_comment = true }
  let set_start_p c = c.lexbuf.lex_start_p <- Loc.start_pos c.loc
  let move_start_p shift c =
    let p = c.lexbuf.lex_start_p in
    c.lexbuf.lex_start_p <- { (p) with pos_cnum = p.pos_cnum + shift }

  let update_loc c = { (c) with loc = Loc.of_lexbuf c.lexbuf }
  let with_curr_loc f c = f (update_loc c) c.lexbuf
  let parse_nested f c = with_curr_loc f c; set_start_p c; buff_contents c
  let shift n c = { (c) with loc = Loc.move `both n c.loc }
  let store_parse f c = store c; f c c.lexbuf
  let parse f c = f c c.lexbuf

  (* Update the current location with file name and line number. *)

  let update_loc c file line absolute chars =
    let lexbuf = c.lexbuf in
    let pos = lexbuf.lex_curr_p in
    let new_file = match file with
      | None -> pos.pos_fname
      | Some s -> s  in
    lexbuf.lex_curr_p <- { pos with
                           pos_fname = new_file;
                           pos_lnum = if absolute then line else pos.pos_lnum + line;
                           pos_bol = pos.pos_cnum - chars;
                         }

  let err error loc = raise(Loc.Exc_located(loc, Error.E error))

  let warn error loc = Format.eprintf "Warning: %a: %a@." Loc.print loc Error.print error

  let tbl_keywords = Hashtbl.create 100

  let comment_level = ref 0

  let keywords = [
    ("bool", BOOL);
    ("void", VOID);
    ("int", INT);
    ("float", FLOAT);
    ("true", TRUE);
    ("false", FALSE);
    ("while", WHILE);
    ("if", CIF);
    ("else", CELSE);
    ("goto", GOTO);
    ("skip", SKIP);
    ("continue", CONTINUE);
    ("break", BREAK);
    ("assert", ASSERT);
    ("assume", ASSUME)
  ]

  let _ = List.map (fun ((k, t): (string * token)) ->
    Hashtbl.add tbl_keywords k t) keywords
}

  let newline = ('\010' | '\013' | "\013\010")
  let blank = [' ' '\009' '\012']
  let alpha = ['a'-'z' 'A'-'Z' '\223'-'\246' '\248'-'\255' '_']
  let identchar = ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '0'-'9']
  let identseq = alpha identchar* (* A single identifier *)
  let ident = (identseq | identseq ''') ('.' identseq)* (* A {possibly} extended quantifier *)
  let locname = ident
  let not_star_symbolchar = ['$' '!' '%' '&' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~' '\\']
  let symbolchar = '*' | not_star_symbolchar
  let hexa_char = ['0'-'9' 'A'-'F' 'a'-'f']
  let decimal_literal = ['0'-'9'] ['0'-'9' '_']*
  (* let decimal_literal = ['0'-'9'] ['0'-'9']* *)
  let hex_literal = '0' ['x' 'X'] hexa_char ['0'-'9' 'A'-'F' 'a'-'f' '_']*
  let oct_literal = '0' ['o' 'O'] ['0'-'7'] ['0'-'7' '_']*
  let bin_literal = '0' ['b' 'B'] ['0'-'1'] ['0'-'1' '_']*
  let int_literal = decimal_literal | hex_literal | oct_literal | bin_literal
  let float_literal = ['0'-'9'] ['0'-'9' '_']* ('.') ['0'-'9' '_']+  (['e' 'E'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']*)?
  let frac_literal = int_literal ('/') int_literal

rule tokenizer file_name = parse
  | newline { update_loc file_name None 1 false 0; tokenizer file_name lexbuf }
  | blank+ { tokenizer file_name lexbuf }
  | (int_literal as i)
      { try  INT_LIT(int_of_string i, i)
        with Failure _ -> err (Literal_overflow "int") (Loc.of_lexbuf lexbuf) }
  | (int_literal as i) "l"
      { try  INT_LIT(int_of_string i, i) (* can try different converter if needed *)
        with Failure _ -> err (Literal_overflow "int32") (Loc.of_lexbuf lexbuf) }
  | (int_literal as i) "L"
      { try  INT_LIT(int_of_string i, i) (* can try different converter if needed *)
        with Failure _ -> err (Literal_overflow "int64") (Loc.of_lexbuf lexbuf) }
  | (int_literal as i) "n"
      { try INT_LIT(int_of_string i, i) (* can try different converter if needed *)
        with Failure _ -> err (Literal_overflow "nativeint") (Loc.of_lexbuf lexbuf) }
  | "'\\" (_ as c)
      { err (Illegal_escape (String.make 1 c)) (Loc.of_lexbuf lexbuf) }
  | "/*" { comment_level := 0; comment file_name lexbuf }
  | "//" { line_comment file_name lexbuf }
  | "/*/"
      { warn Comment_start (Loc.of_lexbuf lexbuf);
        comment_level := 0;
        comment file_name lexbuf }
  | "*/" { err Comment_not_end (Loc.of_lexbuf lexbuf) }
  | '"'
      { with_curr_loc string file_name;
        let s = buff_contents file_name in STRING (Camlp4.Struct.Token.Eval.string s, s) }
  | '&' { AND } | "&&" { ANDAND } | "/\\" { METAAND }
  | '|' { OR }  | "||" { OROR } | "\\/" { METAOR }
  | '{' { OBRACE } | '}' { CBRACE }
  | '(' { OPAREN } | ')' { CPAREN }
  | '[' { OSQUARE } | ']' { CSQUARE }
  | "->" { ARROW }
  | "." { DOT } | ".." { DOTDOT }
  | ',' { COMMA } | ';' { SEMICOLON }
  | "=" { EQ } | "==" { EQEQ } | "!=" { NE } | ":=" { COLONEQ } | "!" { NOT }
  | '<' { LT } | '>' { GT } | "<=" { LE } | ">=" { GE }
  | '+' { PLUS } | '-' { MINUS } | "*" { MULT } | '/' { DIV } | '%' { MOD }
  | "+=" { PLUS_ASSIGN } | "-=" { MINUS_ASSIGN }
  | "*=" { MULT_ASSIGN } | "/=" { DIV_ASSIGN } | "%=" { MOD_ASSIGN }
  | '*' { NONDET }
  | "B" { BOT } | "T" { TOP } | "?" { ANY }
  | ident as idstr { 
    if idstr = "_" then ID (fresh_var_anonym_name ())
    else
      try Hashtbl.find tbl_keywords idstr
      with | _ -> ID idstr }
  | eof { 
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with pos_bol  = pos.pos_bol  + 1;
                                    pos_cnum = pos.pos_cnum + 1 }; EOF }
  | '#' { EOL }
  | _ as c { err (Illegal_character c) (Loc.of_lexbuf lexbuf) }

and comment file_name = parse
  | "*/" { 
      if !comment_level = 0 then tokenizer file_name lexbuf
	    else
        let _ = comment_level := !comment_level - 1 in
      	comment file_name lexbuf }
  | "/*" { comment_level := !comment_level + 1;
	   comment file_name lexbuf }
  | newline { update_loc file_name None 1 false 0; comment file_name lexbuf }
  | _ { comment file_name lexbuf }

and line_comment file_name = parse
  | newline
  | eof { update_loc file_name None 1 false 0; tokenizer file_name lexbuf }
  | _ { line_comment file_name lexbuf }

and string c = parse
      '"'                                                       { set_start_p c }
    | '\\' newline ([' ' '\t'] * as space)
        { update_loc c None 1 false (String.length space);
          store_parse string c                                                  }
    | '\\' ['\\' '"' 'n' 't' 'b' 'r' ' ' '\'']           { store_parse string c }
    | '\\' ['0'-'9'] ['0'-'9'] ['0'-'9']                 { store_parse string c }
    | '\\' 'x' hexa_char hexa_char                       { store_parse string c }
    | '\\' (_ as x)
        { if is_in_comment c
          then store_parse string c
          else begin
            warn (Illegal_escape (String.make 1 x)) (Loc.of_lexbuf lexbuf);
            store_parse string c
          end }
    | newline
      { update_loc c None 1 false 0; store_parse string c                       }
    | eof                                     { err Unterminated_string (loc c) }
    | _                                                  { store_parse string c }


and preprocess file_name = parse
  | "import"
      {
		(* processing import *)
		let _ = rip_ws lexbuf in
		let tmp_file_name = get_file_name lexbuf in
		let f1 = String.sub tmp_file_name 1 (String.length tmp_file_name - 2) in
		let in_file = open_in f1 in
		let cont = ref true in
		let in_cont = Buffer.create 1024 in
		  while !cont do
			try
			  let line = input_line in_file in
				Buffer.add_string in_cont (line ^ "\n")
			with
			  | End_of_file -> cont := false
		  done;
		  output_string file_name (Buffer.contents in_cont);
		  preprocess file_name lexbuf
      }
  | _ as c
      { (* other character, just copy it over *)
		output_char file_name c;
		preprocess file_name lexbuf
      }
  | eof { EOF }

and rip_ws = parse
  | (' ' | '\t')+ as ws { ws }
  | _  { print_string "There must be whitespace after import directive\n"; exit (-1) }

and get_file_name = parse
  | '\"'([^ '\n' '\"'])+'\"' as fn { fn }
  | _ { print_string "file name following import must be enclosed in double quotes\n"; exit (-1) }

{
  let lexing_store s buff max =
    let rec self n s =
      if n >= max then n
      else
        match Stream.peek s with
        | Some x ->
            Stream.junk s;
            Bytes.set buff n x;
            succ n
        | _ -> n
    in
    self 0 s

  let from_context c =
    let next _ =
      let tok = with_curr_loc tokenizer c in
      let loc = Loc.of_lexbuf c.lexbuf in
      Some ((tok, loc))
    in Stream.from next

  let from_lexbuf lb =
    let c = { (default_context lb) with  loc = Loc.of_lexbuf lb}
    in from_context c

  let setup_loc lb loc =
    let start_pos = Loc.start_pos loc in
    lb.lex_abs_pos <- start_pos.pos_cnum;
    lb.lex_curr_p  <- start_pos

  let from_string loc str =
    let lb = Lexing.from_string str in
    setup_loc lb loc;
    from_lexbuf lb

  let from_stream loc strm =
    let lb = Lexing.from_function (lexing_store strm) in
    setup_loc lb loc;
    from_lexbuf lb

  let mk () loc strm = from_stream loc strm
end
}
