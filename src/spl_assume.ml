open Spl_syn
open Lib.Print
open Spl_utils

type 'k assumption = {
  assumpt_cond: bexpr;
  assumpt_symbol: 'k;
  assumpt_neg: bool;
  (* assumpt_proc: string; *)
  assumpt_pos: point list }

let pr_assumption (assumpt: 'k assumption) =
  (* assumpt.assumpt_proc ^ ":" ^ *)
  (pr_list pr_point assumpt.assumpt_pos) ^ ": " ^
  (if assumpt.assumpt_neg then "not" else "") ^
  "(" ^ (pr_bexpr assumpt.assumpt_cond) ^ ")"

let pr_assumptions (assumpts: 'k assumption list) =
  pr_list ~obrace:"{" ~cbrace:"}" pr_assumption assumpts

let char_num = ref 0

let get_incr_char () =
  let () = char_num := !char_num + 1 in
  !char_num

let reset_incr_col () =
  char_num := 0

let incr_char_point pt =
  let i = get_incr_char () in
  { pt with char = pt.char + i }

let rec assumpt_instrument_instr
  (assumpt: 'k assumption)
  (instr: instr): instr list =
  let mk_assume assumpt =
    let assume_cond =
      if assumpt.assumpt_neg then NOT assumpt.assumpt_cond
      else assumpt.assumpt_cond in
    ASSUME assume_cond in
  match instr.instruction with
  | SKIP | HALT | FAIL
  | ASSUME _ | CALL _ | ASSIGN _ -> [instr]
  | IF (c, t) ->
    if eq_bexpr c assumpt.assumpt_cond &&
       (List.exists (fun apt -> compare_point apt t.bpoint == 0)
          assumpt.assumpt_pos)
    then
      let assume_instr = {
        instruction = mk_assume assumpt;
        ipoint = incr_char_point instr.ipoint; } in
      [assume_instr; instr]
    else
      let instrumented_if = IF (c, assumpt_instrument_block assumpt t) in
      [{ instr with instruction = instrumented_if }]
  | IFELSE (c, t, e) ->
    if eq_bexpr c assumpt.assumpt_cond &&
       (List.exists (fun apt -> compare_point apt t.bpoint == 0)
          assumpt.assumpt_pos)
    then
      let assume_instr = {
        instruction = mk_assume assumpt;
        ipoint = incr_char_point instr.ipoint; } in
      [assume_instr; instr]
    else
      let instrumented_ifelse = IFELSE (c, assumpt_instrument_block assumpt t,
                                    assumpt_instrument_block assumpt e) in
      [{ instr with instruction = instrumented_ifelse }]
  | LOOP (c, b) ->
    if (* eq_bexpr c assumpt.assumpt_cond && *)
       (List.exists (fun apt -> compare_point apt b.bpoint == 0)
          assumpt.assumpt_pos)
    then
      let assume_instr = {
        instruction = mk_assume assumpt;
        ipoint = incr_char_point instr.ipoint; } in
      [assume_instr; instr]
    else
      let instrumented_loop = LOOP (c, assumpt_instrument_block assumpt b) in
      [{ instr with instruction = instrumented_loop }]

and assumpt_instrument_instrs
    (assumpt: 'k assumption)
    (instrs: instr list): instr list =
  match instrs with
  | [] -> []
  | i::is ->
    (assumpt_instrument_instr assumpt i) @
    (assumpt_instrument_instrs assumpt is)

and assumpt_instrument_block
    (assumpt: 'k assumption)
    (blk: block): block =
  if List.exists (fun apos ->
      compare_point apos blk.bpoint >= 0) assumpt.assumpt_pos
  then
    { blk with instrs = assumpt_instrument_instrs assumpt blk.instrs }
  else blk

and assumpt_instrument_proc
    (assumpt: 'k assumption)
    (proc: procedure): procedure =
  { proc with
    pcode = assumpt_instrument_block assumpt proc.pcode }

and assumpt_instrument_prog
    (assumpt: 'k assumption)
    (prog: program): program =
  { procedures = List.map (assumpt_instrument_proc assumpt)
        prog.procedures }

and assumpt_lst_instrument_prog
    (assumpts: 'k assumption list)
    (prog: program): program =
  (* let () = reset_incr_col () in *)
  List.fold_left (fun prog assumpt ->
    assumpt_instrument_prog assumpt prog) prog assumpts
