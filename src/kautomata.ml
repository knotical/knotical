open Globals
open Lib

module type State =
sig
  type t

  val eq: t -> t -> bool
  val print: t -> string
end;;

module type Symbol =
sig
  type t

  val eq: t -> t -> bool
  val print: t -> string
end;;

module Regex = functor (L: Symbol) ->
struct
  type t =
    | Pls of t * t
    | Dot of t * t
    | Str of t
    | Chr of L.t
    | Top
    | Bot

  let rec print = function
    | Pls (r, s) -> "(" ^ (print r) ^ ")+(" ^ (print s) ^ ")"
    | Dot (r, s) -> "(" ^ (print r) ^ ").(" ^ (print s) ^ ")"
    | Str r -> "(" ^ (print r) ^ ")*"
    | Chr s -> L.print s
    | Top -> "1"
    | Bot -> "0"

  let mk_pls r s =
    match r, s with
    | Bot, _ -> s
    | _, Bot -> r
    | _ -> Pls (r, s)

  let mk_dot r s =
    match r, s with
    | Top, _ -> s
    | _, Top -> r
    | Bot, _
    | _, Bot -> Bot
    | _ -> Dot (r, s)
end;;


module type Automata =
sig
  type state
  type symbol
  type t

  module type Sig_Regex =
  sig
    type t =
      | Pls of t * t
      | Dot of t * t
      | Str of t
      | Chr of symbol
      | Top
      | Bot
  
    val print: t -> string
    val mk_pls: t -> t -> t
    val mk_dot: t -> t -> t
  end;;

  module R: Sig_Regex

  val empty: t
  val init:
    ?start: state option ->
    ?accept: state list ->
    ?symbols: symbol list ->
    ?trans: (state -> symbol -> state list) -> t
  val start_state: t -> state option
  val accept_states: t -> state list
  val symbols: t -> symbol list
  val states: t -> state list

  val bfs: t -> ((state * symbol * state) -> 'a) -> 'a list

  val add_trans: t -> (state * symbol * state) -> unit
  val trans_func: t -> state -> symbol -> state list
  val trans_symbols: t -> state -> state -> symbol list

  val eq_state: state -> state -> bool
  val eq_symbol: symbol -> symbol -> bool

  val make: state option -> (state list) -> symbol list ->
    (state -> symbol -> state list) -> t

  val to_regex: t -> R.t

  val print: t -> string
  val print_state: state -> string
  val print_symbol: symbol -> string

  val get_State_module: unit -> (module State)
  val get_Symbol_module: unit -> (module Symbol)
  val get_Regex_module: unit -> (module Sig_Regex)
end;;

module Make (V: State) (E: Symbol)
  : (Automata with type state = V.t
               and type symbol = E.t) =
struct
  module type Sig_Regex =
  sig
    type t =
      | Pls of t * t
      | Dot of t * t
      | Str of t
      | Chr of E.t
      | Top
      | Bot
  
    val print: t -> string
    val mk_pls: t -> t -> t
    val mk_dot: t -> t -> t
  end;;

  module R = Regex (E)

  module H = Hashtbl.Make(
    struct
      type t = V.t
      let equal = V.eq
      let hash = Hashtbl.hash
    end)

  type state = V.t
  type symbol = E.t

  type regex = R.t

  type t = {
    start_state: state option;
    accept_states: state list;
    symbols: symbol list;
    states: state list;
    store: ((symbol * state) list) H.t;
    transition: (state -> symbol -> state list);
  }

  module S = Set.Make(
    struct
      type t = state
      let compare e f = if V.eq e f then 0 else -1
    end)

  let eq_state = V.eq

  let eq_symbol = E.eq

  let print_state = V.print

  let print_symbol = E.print

  let bfs (a: t) f =
    let rec iter acc (queue: state list) (visited: state list) trans =
      match queue with
      | [] -> acc
      | q::qs ->
        if List.mem eq_state q visited then
          iter acc qs visited trans
        else
          let transitions =
            List.map (fun s -> List.map (fun r -> (q, s, r)) (trans q s)) a.symbols
            |> List.concat in
          let n_acc = acc @ (List.map f transitions) in
          iter n_acc (qs @ (List.map Basic.thr3 transitions)) (visited @ [q]) trans
    in
    match a.start_state with
    | None -> []
    | Some p -> iter [] [p] [] a.transition

  let print (a: t): string =
    bfs a (fun (src, s, dst) ->
        (print_state src)
        ^ " (" ^ (print_symbol s) ^ ") "
        ^ (print_state dst))
    |> String.concat "\n"

  let empty = {
    start_state = None;
    accept_states = [];
    symbols = [];
    states = [];
    store = H.create 50;
    transition = fun _ _ -> [];
  }

  let init ?(start=None) ?(accept=[]) ?(symbols=[]) ?(trans=fun _ _ -> []) = {
    start_state = start;
    accept_states = accept;
    symbols = symbols;
    states = (match start with | None -> [] | Some s -> [s]) @ accept;
    store = H.create 50;
    transition = trans;
  }

  let start_state (a: t) = a.start_state

  let accept_states (a: t) = a.accept_states

  let symbols (a: t) = a.symbols

  let is_start_state (a: t) (p: state) =
    match (start_state a) with
    | None -> false
    | Some q -> eq_state p q

  let is_accept_state (a: t) (p: state) =
    List.exists (fun q -> eq_state p q) (accept_states a)

  let successors (a: t) (p: state) =
    List.map (fun s -> a.transition p s) a.symbols
    |> List.concat
    |> List.dedup eq_state

  let is_reachable (a: t) (src: state) (dst: state): bool =
    let rec helper ws s d =
      if eq_state s d then true
      else if (S.mem s ws) then false
      else
        let succs = successors a src in
        let new_ws = S.add s ws in
        List.exists (fun succ -> helper new_ws succ d) succs
    in
    helper S.empty src dst

  let dist_from_start (a: t) (dst: state): float =
    let rec helper ws s d =
      if eq_state s d then 0.0
      else if (S.mem s ws) then infinity
      else
        let succs = successors a s in
        match succs with
        | [] -> infinity
        | r::rs ->
          let new_ws = S.add s ws in
          let min_dist = List.fold_left min (helper new_ws r d) (List.map (fun r -> helper new_ws r d) rs) in
          1.0 +. min_dist
    in
    match a.start_state with
    | None -> infinity
    | Some s -> helper S.empty s dst

  let compare_state (a: t) (p: state) (q: state) =
    if (is_start_state a p) then
      if (is_start_state a q) then 0
      else -1
    else if (is_start_state a q) then 1
    else if (is_accept_state a p) then
      if (is_accept_state a q) then
        compare (dist_from_start a p) (dist_from_start a q)
      else 1
    else if (is_accept_state a q) then -1
    else compare (dist_from_start a p) (dist_from_start a q)

  let states (a: t) =
    List.dedup eq_state (bfs a (fun (src, _, dst) -> [src; dst]) |> List.concat)
    |> List.fast_sort (compare_state a)
    |> List.rev

  let trans_func (a: t) = a.transition

  let add_state (a: t) (s: state) =
    H.add a.store s []

  let add_trans (a: t) (src, symb, dst) =
    let aux () =
      try
        let src_transitions = H.find a.store src in
        H.replace a.store src (src_transitions @ [(symb, dst)])
      with Not_found ->
        H.add a.store src [(symb, dst)]
    in
    if List.exists (fun s -> V.eq s dst) (a.transition src symb) then aux ()
    else failwith "The input transition is inconsistent with the transition function"

  let trans_symbols (a: t) (src: state) (dst: state): symbol list =
    (* try
     *   H.find a.store src
     *   |> List.find_all (fun (_, d) -> eq_state d dst)
     *   |> List.map fst
     * with _ -> [] *)
   List.filter (fun sym -> List.mem eq_state dst (a.transition src sym)) a.symbols

  let make (start: state option) (accepts: state list)
    (letters: symbol list)
    (trans: state -> symbol -> state list): t =
    let aut = init ~start:start ~accept:accepts ~symbols:letters ~trans:trans in
     aut

  (* Aut2Regex *)

  type term = int * regex

  type equation = int * term list

  let base_id = -1

  let state_id = ref (-1)

  let mk_fresh_id () =
    state_id := !state_id + 1;
    !state_id

  let pr_id id = if id < 0 then "_" else "q" ^ (string_of_int id)

  let pr_term ((id, r): term): string =
    "(" ^ (R.print r) ^ ")" ^ (pr_id id)

  let pr_equation (id, ts) =
    (pr_id id) ^ " = " ^ (pr_list pr_term ts) 

  let syms_to_regex (ss: symbol list) =
    match (List.dedup eq_symbol ss) with
    | [] -> R.Bot
    | x::xs -> List.fold_left (fun r x -> R.mk_pls r (R.Chr x)) (R.Chr x) xs

  let mk_state_regular_equation (a: t) (sid, src: int * state) states: equation =
    let t = (List.map (fun (did, dst) -> (did, syms_to_regex (trans_symbols a src dst))) states)
            @ (if (is_accept_state a src) then [(base_id, R.Top)] else [(base_id, R.Bot)]) in
    (sid, t)

  let apply_Arden_rule (lhs_id, eq: equation): equation =
    let lhs_coe = List.assoc_opt lhs_id eq in
    let elim_eq =
      match lhs_coe with
      | None | Some (R.Bot) -> eq
      | Some c ->
        List.map (fun (id, r) ->
            if id == lhs_id then (id, R.Bot)
            else
              match r with
              | R.Bot -> (id, R.Bot)
              | _ -> (id, R.mk_dot (R.Str c) r)) eq
    in (lhs_id, elim_eq)

  (* Subst qj into qi *)
  let subst_equation (j, qj: equation) (i, qi: equation): equation =
    let subst_qi = List.map (fun (i, ri) ->
        if i == j then
          (i, R.mk_dot ri (List.assoc i qj))
        else
          (i, R.mk_pls ri (R.mk_dot (List.assoc j qi) (List.assoc i qj)))
      ) qi in
    let () = Debug.npprint ("subst " ^ (pr_equation (j, qj)) ^ " into " ^ (pr_equation (i, qi))) in
    let () = Debug.nhprint "res: " pr_equation (i, subst_qi) in
    (i, subst_qi)

  let solve_equation_system (eqs: equation list): equation list =
    List.fold_left (fun eqs i ->
        let qi = List.assoc i eqs in
        let n_qi = apply_Arden_rule (i, qi) in
        List.map (fun (j, qj) -> if j == i then n_qi else subst_equation n_qi (j, qj)) eqs
      ) eqs (List.map fst eqs)

  let to_regex (a: t): regex =
    match a.start_state with
    | None -> Bot
    | Some s ->
      let all_states =
        (* List.dedup eq_state (bfs a (fun (src, _, dst) -> [src; dst]) |> List.concat) *)
        states a
        |> List.map (fun s -> (mk_fresh_id (), s))
      in
      let () = Debug.nhprint "all_states: " (pr_pairs pr_id print_state) all_states in
      let start_id = List.find (fun (pid, p) -> eq_state p s) all_states |> fst in
      let regular_equations = List.map (fun (sid, s) -> mk_state_regular_equation a (sid, s) all_states) all_states in
      let () = Debug.nhprint "regular_equations: " (pr_list ~sep:"\n" pr_equation) regular_equations in
      let solved_eqs = solve_equation_system regular_equations in
      let () = Debug.nhprint "solution: " (pr_list ~sep:"\n" pr_equation) solved_eqs in
      let solution =
        solved_eqs
        |> List.find (fun (id, eq) -> id == start_id)
        |> snd
        |> List.assoc base_id in
      let () = Debug.nhprint "regex: " R.print solution in
      solution

  let get_Symbol_module () = (module E: Symbol)

  let get_State_module () = (module V: State)

  let get_Regex_module () = (module R: Sig_Regex)
end;;

module BinOps
  (A: Automata)
  (B: Automata with type symbol = A.symbol)
  : (Automata with type state = A.state * B.state
               and type symbol = A.symbol) =
  Make
    (struct
      type t = (A.state * B.state)

      let eq (p1, q1) (p2, q2) =
        (A.eq_state p1 p2) && (B.eq_state q1 q2)

      let print = pr_pair A.print_state B.print_state
    end)
    (struct
      type t = A.symbol

      let eq = A.eq_symbol

      let print = A.print_symbol
    end)
