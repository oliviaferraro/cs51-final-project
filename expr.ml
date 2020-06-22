(* 
                         CS 51 Final Project
                        MiniML -- Expressions
                             Spring 2018
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | Negate ;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Div
  | Equals
  | LessThan
  | GreaterThan ;;
      
type expr =
  | Var of varid                         (* variables *)
  | Int of int                           (* integers *)
  | Float of float                       (* floats *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
 and varid = string ;;
  
(*......................................................................
  Manipulation of variable names (varids)
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars :  varidset -> varidset -> bool
   Test to see if two sets of variables have the same elements (for
   testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list : string list -> varidset
   Generate a set of variable names from a list of strings (for
   testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars : expr -> varidset
   Return a set of the variable names that are free in expression
   exp *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var a -> SS.singleton a
  | Int _ | Float _ | Bool _ -> SS.empty
  | Unop (_, b) -> free_vars b
  | Binop (_, b, c) -> SS.union (free_vars b) (free_vars c) 
  | Conditional (a, b, c) -> 
    SS.union (SS.union (free_vars a) (free_vars b)) (free_vars c)
  | Fun (a, b) -> SS.remove a (free_vars b)
  | Let (a, b, c) -> SS.remove a (SS.union (free_vars b) (free_vars c))
  | Letrec (a, b, c) -> 
    SS.union (SS.remove a (free_vars b)) (SS.remove a (free_vars c))
  | Raise -> SS.empty
  | Unassigned -> SS.empty
  | App (a, b) -> SS.union (free_vars a) (free_vars b) ;;
  
(* new_varname : unit -> varid
   Return a fresh variable, constructed with a running counter a la
   gensym. Assumes no variable names use the prefix "var". (Otherwise,
   they might accidentally be the same as a generated variable name.) *)

let inc =
  let a = ref 0 in
  fun () -> a := !a + 1 ;
  !a ;;

let new_varname () : varid =
  "var" ^ (string_of_int ((inc ()) - 1)) ;;

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst : varid -> expr -> expr -> expr
   Substitute repl for free occurrences of var_name in exp *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  let help (e : expr) : expr =
    subst var_name repl e
  in
  let free = free_vars repl in
  match exp with
  | Var a -> if a = var_name then repl else exp
  | Int _ | Float _ | Bool _ -> exp
  | Unop (a, b) -> Unop (a, help b)
  | Binop (a, b, c) -> Binop (a, help b, help c)
  | Conditional (a, b, c) -> Conditional (help a, help b, help c)
  | Fun (a, b) as f -> 
      let z = new_varname () in 
      if a = var_name then f 
      else if SS.mem a free then Fun (z, help (subst a (Var z) b))
      else Fun (a, help b)
  | Let (a, b, c) -> 
      let z = new_varname () in
      if a = var_name then Let (a, help b, c)
      else if SS.mem a free then Let (z, b, help (subst a (Var z) c))
      else Let (a, help b, help c)
  | Letrec (a, b, c) as f -> 
      let z = new_varname () in
      if a = var_name then f 
      else if SS.mem a free then Letrec (z, b, help (subst a (Var z) c))
      else Letrec (a, help b, help c)
  | Raise -> exp
  | Unassigned -> exp
  | App (a, b) -> App (help a, help b) ;;

(*......................................................................
  String representations of expressions
 *)

(* convert binops to string representation of binary operator *)
let binop_conc_string (b : binop) : string =
  match b with
  | Plus -> " + "
  | Minus -> " - "
  | Times -> " * "
  | Div -> " / "
  | Equals -> " = "
  | LessThan -> " < " 
  | GreaterThan -> " > " ;;

let unop_conc_string (u : unop) : string =
  match u with
  | Negate -> "- " ;;
    
(* exp_to_concrete_string : expr -> string
   Returns a concrete syntax string representation of the expr *)
let rec exp_to_concrete_string (exp : expr) : string =
  match exp with
  | Var a -> a
  | Int a -> string_of_int a
  | Float a -> string_of_float a
  | Bool a -> string_of_bool a
  | Unop (a, b) -> "(" ^ (unop_conc_string a) ^ (exp_to_concrete_string b) ^ ")"
  | Binop (a, b, c) -> "(" ^ (exp_to_concrete_string b) ^ (binop_conc_string a) 
    ^ (exp_to_concrete_string c) ^ ")"
  | Conditional (a, b, c) -> "if " ^ (exp_to_concrete_string a) ^ " then " ^
    (exp_to_concrete_string b) ^ " else " ^ (exp_to_concrete_string c)
  | Fun (a, b)-> "fun " ^ a ^ " -> " ^ 
    (exp_to_concrete_string b)
  | Let (a, b, c) -> "let " ^ a ^ " = " ^ (exp_to_concrete_string b) ^ " in " ^ 
    (exp_to_concrete_string c)
  | Letrec (a, b, c) -> "let rec " ^ a ^ " = " ^ (exp_to_concrete_string b) ^ 
    " in " ^ (exp_to_concrete_string c)
  | Raise -> "Exception"
  | Unassigned -> "Unassigned"
  | App (a, b) -> (exp_to_concrete_string a) ^ (exp_to_concrete_string b) ;;

let binop_abs_string (b : binop) : string =
  match b with
  | Plus -> "Binop (Plus, "
  | Minus -> "Binop (Minus, "
  | Times -> "Binop (Times, "
  | Div -> "Binop (Div, "
  | Equals -> "Binop (Equals, "
  | LessThan -> "Binop (LessThan, " 
  | GreaterThan -> "Binop (GreaterThan, " ;;

let unop_abs_string (u : unop) : string =
  match u with
  | Negate -> "Unop (Negate, " ;;

(* exp_to_abstract_string : expr -> string
   Returns a string representation of the abstract syntax of the expr *)
let rec exp_to_abstract_string (exp : expr) : string =
match exp with
  | Var a -> "Var " ^ a
  | Int a -> "Int " ^ (string_of_int a)
  | Float a -> "Float " ^ (string_of_float a)
  | Bool a -> "Bool " ^ (string_of_bool a)
  | Unop (a, b) -> (unop_abs_string a) ^ (exp_to_abstract_string b) ^ ")"
  | Binop (a, b, c) -> (binop_abs_string a) ^ (exp_to_abstract_string b) ^ 
    ", " ^ (exp_to_abstract_string c) ^ ")"
  | Conditional (a, b, c) -> "Conditional (" ^ (exp_to_abstract_string a) ^ 
    ", " ^ (exp_to_abstract_string b) ^ ", " ^ (exp_to_abstract_string c) ^ ")"
  | Fun (a, b)-> "Fun (" ^ a ^ ", " ^ (exp_to_abstract_string b) ^ ")"
  | Let (a, b, c) -> "Let (" ^ a ^ ", " ^ (exp_to_abstract_string b) ^ ", " ^ 
    (exp_to_abstract_string c) ^ ")"
  | Letrec (a, b, c) -> "Letrec (" ^ a ^ ", " ^ (exp_to_abstract_string b) ^ 
    ", " ^ (exp_to_abstract_string c) ^ ")"
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (a, b) -> "App (" ^ (exp_to_abstract_string a) ^ ", " ^ 
    (exp_to_abstract_string b) ^ ")" ;;
