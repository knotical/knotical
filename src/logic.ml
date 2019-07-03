open Globals

type formula =
  | BVar of (var * pos)
  | BConst of (bool * pos)
  | BinRel of (bin_rel * exp * exp * pos)
  | Neg of (formula * pos)
  | Conj of (formula * formula * pos)
  | Disj of (formula * formula * pos)
  | Forall of (var * formula * pos)
  | Exists of (var * formula * pos)

and exp =
  | Var of (var * pos)
  | IConst of (int * pos)
  | Func of (func * exp list * pos)
  | BinOp of (bin_op * exp * exp * pos)

and func =
  | Max
  | Min
  | Abs

and bin_rel =
  | Lt
  | Le
  | Gt
  | Ge
  | Eq
  | Ne

and bin_op =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
