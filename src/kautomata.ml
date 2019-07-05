module type State =
sig
  type t

  val print: t -> string
end;;

module type Symbol =
sig
  type t

  val eq: t -> t -> bool
  val print: t -> string
end;;

module type AutomataSig =
sig
  type state
  type symbol
  type t

  val empty: t
  val start_state: t -> state option
  val accept_states: t -> state list
  val add_trans: (state * symbol * state) -> t -> t
  val trans_func: t -> state -> symbol -> state list
  val print: t -> string
end;;

module Make (V: State) (E: Symbol)
  : (AutomataSig with type state = V.t and type symbol = E.t) =
struct
  type state = V.t
  type symbol = E.t
  type t = {
    start_state: state option;
    accept_states: state list;
    store: (state, (symbol * state) list) Hashtbl.t;
  }

  let empty = {
    start_state = None;
    accept_states = [];
    store = Hashtbl.create 50; }

  let start_state (a: t) = a.start_state

  let accept_states (a: t) = a.accept_states

  let trans_func (a: t) (s: state) (symb: symbol): state list =
    try
      let s_transitions = Hashtbl.find a.store s in
      List.map snd (List.filter (fun (sb, _) -> E.eq sb symb) s_transitions)
    with Not_found  -> []

  let add_trans (src, symb, dst) (a: t) =
    let () = 
      try
        let src_transitions = Hashtbl.find a.store src in
        Hashtbl.replace a.store src (src_transitions @ [(symb, dst)])
      with Not_found ->
        Hashtbl.add a.store src [(symb, dst)] in
    a

  let print (a: t): string =
    Hashtbl.fold (fun src trans s ->
        let trans_str = List.map (fun (symb, dst) ->
            (V.print src) ^ " (" ^ (E.print symb) ^ ") " ^ (V.print dst)) trans in
        s ^ "\n" ^ (String.concat "\n" trans_str)) a.store ""
end;;

