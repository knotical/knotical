include Lib.Print

module EString = Extlib.ExtString.String

exception EBool of bool
exception EInt of int
exception EFloat of float
exception EStringOpt of string option

(************************************)
(***       global variables       ***)

(* types *)
type ident = string

type refinement_direction =
  | RLe
  | REq

(* constants *)
let str_anon_name = "anon"

let str_ret_name = "res"

(* input *)
let input_file_name = ref ""
let source_files = ref ([] : string list)
let output_dir = ref "./output"
let interproc_source_file = ref ""
let kat_source_file = ref ""
let symkat_x = ref ""
let symkat_y = ref ""
let raw_kat_formula = ref ""
let ked_enabled = ref false
let fst_cmp_method = ref ""
let snd_cmp_method = ref ""
let refinement_op = ref REq
let compare_mode_enabled = ref false
let (no_removed_events: string list ref) = ref []

(* Temper *)
let compute_intersect = ref false
let use_diff_sym = ref false
let raw_kat_prop = ref ""
let file_kat_prop = ref ""

(* printing *)
let print_prover_stats = ref false
let print_prover_option = ref false
let print_prog_iast = ref false
let print_prog_cast = ref false
let print_tex = ref false

(* dump data *)

(* time out, in seconds *)

(* index counter *)
let index_var = ref 0

(* threshold *)
let rec_depth_threshold = ref (-1)  

(* generic functions *)

let fnone = fun _ -> None
let fid = fun x -> x

let dedup_gen eq xs =
  let mem x xs = List.exists (eq x) xs in
  let rec do_remove xs = match xs with
    | [] -> []
    | x::xs -> if (mem x xs) then do_remove xs else x::(do_remove xs) in
  do_remove xs

(* positions *)

type pos = {
  pos_begin : Lexing.position;
  pos_end : Lexing.position;
}

let no_lexpos = {
  Lexing.pos_fname = "";
  Lexing.pos_lnum = 0;
  Lexing.pos_bol = 0;
  Lexing.pos_cnum = 0 }

let no_pos = {
  pos_begin = no_lexpos;
  pos_end = no_lexpos;}

let pr_lexpos pos =
  (string_of_int pos.Lexing.pos_lnum) ^ ":"
  ^ (string_of_int (pos.Lexing.pos_cnum - pos.Lexing.pos_bol))

let pr_pos pos =
  (pr_lexpos pos.pos_begin) ^ "-" ^ (pr_lexpos pos.pos_end)

let pr_pos_line pos =
  string_of_int pos.pos_begin.Lexing.pos_lnum

let eq_pos p1 p2 =
  (String.equal p1.pos_begin.Lexing.pos_fname p2.pos_begin.Lexing.pos_fname)
  && (p1.pos_begin.Lexing.pos_lnum = p2.pos_begin.Lexing.pos_lnum)

(* type *)

type typ =
  | TInt
  | TBool
  | TVoid
  | TFloat
  | TVar of int              (* type variable, used for type inference *)

let eq_t t1 t2 = 
  match t1, t2 with
  | TInt, TInt -> true
  | TBool, TBool -> true
  | TVoid, TVoid -> true
  | TVar i1, TVar i2 -> i1 = i2
  | _ -> false

let pr_typ t = match t with
  | TInt -> "Int"
  | TFloat -> "Float"
  | TBool -> "Bool"
  | TVoid -> "Void"
  | TVar i -> "TVar_" ^ (string_of_int i)

let typ_of_var var = snd var

let is_int_typ t = (t = TInt)

let mem_ts t ts = List.exists (fun x -> eq_t t x) ts

let dedup_ts ts    =
  let rec dedup xs = match xs with
    | [] -> []
    | x::xs -> if (mem_ts x xs) then dedup xs else x::(dedup xs) in
  dedup ts

(* variables *)

type var = (string * typ)

let pr_var (v, t) = v

(* error printing functions *)

let get_latest_call_stack n =
  n |> Printexc.get_callstack |> Printexc.raw_backtrace_to_string

let warning msg =
  if (!Debug.debug_normal_mode || !Debug.debug_deep_mode) then
    prerr_endline ("\n!!! Warning: " ^ msg)
  else ()

let hwarning msg f x =
  let msg = msg ^ " " ^ (f x) in
  warning msg

let fhwarning (msg: string) f x =
  let msg = msg ^ " " ^ (f x) in
  let _ = warning msg in
  failwith msg

let warning_unexpected proc_id f x =
  fhwarning (proc_id ^ ": Unexpected object") f x

let error msg =
  let msg = 
    "\n!!! Error: " ^ msg ^
    "\n!!! Latest call stack:\n" ^ (get_latest_call_stack 10) in
  let _ = prerr_endline msg in
  exit 0

let herror msg f x =
  let msg = msg ^ " " ^ (f x) in
  error msg

(* naming functions *)

let fresh_var_suffix suffix =
  let _ = suffix := !suffix + 1 in
  string_of_int !suffix

let extract_var_name_prefix_suffix name =
  let prefix, suffix =
    try
      let uscore_rindex = String.rindex name '_' in
      let prefix_len = uscore_rindex in
      let prefix = String.sub name 0 prefix_len in
      let suffix_len = (String.length name) - (uscore_rindex + 1) in
      let suffix = String.sub name (uscore_rindex + 1) suffix_len in
      let suffix = int_of_string suffix in
      (prefix, suffix)
    with _ -> (name, -1) in
  prefix, suffix

let rec fresh_var_name ?(suffix=index_var) ?(sep="_") name =
  Debug.trace_1 "fresh_var_name" (pr_s, pr_s) name
    (fun () -> fresh_var_name_x ~suffix:suffix name ~sep:sep)

and fresh_var_name_x ?(suffix=index_var) ?(sep="_") name =
  let prefix, _ = extract_var_name_prefix_suffix name in
  let suffix = fresh_var_suffix suffix in
  prefix ^ sep ^ suffix

let fresh_var_new_name ?(prefix="fv") ?(suffix=index_var) ?(sep="_") () =
  let suffix = fresh_var_suffix suffix in
  prefix ^ sep ^ suffix

let fresh_var_anonym_name ?(suffix=index_var) ?(sep="_") () =
  let prefix = str_anon_name in
  let suffix = fresh_var_suffix suffix in
  prefix ^ sep ^ suffix

let fresh_var ?(suffix=index_var) ?(sfsep="_") (v: var) : var =
  let (vname, vtyp) = v in
  let nvname = fresh_var_name ~suffix:suffix ~sep:sfsep vname in
  (nvname, vtyp)

let fresh_var_of_typ ?(suffix=index_var) ?(sfsep="_") ty =
  let vname = fresh_var_new_name ~suffix:suffix ~sep:sfsep () in
  (vname, ty)

(* string functions *)

let is_empty_s s = String.compare (String.trim s) "" = 0

let eq_s s1 s2 = String.compare s1 s2 = 0

let neq_s s1 s2 = String.compare s1 s2 != 0

let count_ss s ss = ss |> List.filter (eq_s s) |> List.length

let mem_ss s ss = List.exists (fun x -> eq_s s x) ss

let subset_ss ss1 ss2 = ss1 |> List.for_all (fun s -> mem_ss s ss2)

let intersect_ss ss1 ss2 = List.filter (fun s -> mem_ss s ss2) ss1

let intersected_ss ss1 ss2 = (intersect_ss ss1 ss2 != [])

let diff_ss ss1 ss2 = List.filter (fun s -> not (mem_ss s ss2)) ss1

let eq_ss ss1 ss2 = (diff_ss ss1 ss2 = []) && (diff_ss ss2 ss1 = [])

let dedup_ss ss    =
  let rec dedup xs = match xs with
    | [] -> []
    | x::xs -> if (mem_ss x xs) then dedup xs else x::(dedup xs) in
  dedup ss

let submset_ss ss1 ss2 =
  ss1 |> dedup_ss |> List.for_all (fun s ->
    (count_ss s ss1) <= (count_ss s ss2))

let has_newline str =
  try
    let _ = Str.search_forward (Str.regexp "\n") str 0 in
    true
  with Not_found -> false

(* integer functions *)

let compare_int i1 i2 =
  if i1 < i2 then -1
  else if i1 = i2 then 0
  else 1

let mem_ints i is = List.exists (fun x -> i = x) is

let intersect_ints is1 is2 = List.filter (fun x -> mem_ints x is2) is1

let intersected_ints is1 is2 = (intersect_ints is1 is2) != []

let diff_ints is1 is2 = List.filter (fun x -> not (mem_ints x is2)) is1

let eq_ints is1 is2 = (diff_ints is1 is2 = []) && (diff_ints is2 is1 = [])

(* mode configuration *)

(* some functions *)
let raise_bool b = raise (EBool b)

let raise_int i = raise (EInt i)
