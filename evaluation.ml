(* 
                         CS 51 Final Project
                         MiniML -- Evaluation
                             Spring 2018
*)

(* This module implements a small untyped ML-like language under
   various operational semantics.
 *)
    
open Expr ;;
  
(* Exception for evaluator runtime, generated by a runtime error *)
exception EvalError of string ;;
(* Exception for evaluator runtime, generated by an explicit "raise" construct *)
exception EvalException ;;


(*......................................................................
  Environments and values 
 *)

module type Env_type = sig
    type env
    type value =
      | Val of expr
      | Closure of (expr * env)
    val create : unit -> env
    val close : expr -> env -> value
    val lookup : env -> varid -> value
    val extend : env -> varid -> value ref -> env
    val env_to_string : env -> string
    val value_to_string : ?printenvp:bool -> value -> string
  end

module Env : Env_type =
  struct
    type env = (varid * value ref) list
     and value =
       | Val of expr
       | Closure of (expr * env)

    (* Creates an empty environment *)
    let create () : env = [] ;;

    (* Creates a closure from an expression and the environment it's
       defined in *)
    let close (exp : expr) (env : env) : value =
      Closure (exp, env) ;;

    (* Looks up the value of a variable in the environment *)
    let lookup (env : env) (varname : varid) : value =
      let (_, b) = List.find (fun (x, _) -> x = varname) env in
      !b ;;

    (* Returns a new environment just like env except that it maps the
       variable varid to loc *)
    let extend (env : env) (varname : varid) (loc : value ref) : env =
      match env with
      | [] -> [(varname, loc)]
      | _h :: _t -> (varname, loc) :: env ;;

    (* Returns a printable string representation of a value; the flag
       printenvp determines whether to include the environment in the
       string representation when called on a closure *)
    let rec value_to_string ?(printenvp : bool = true) (v : value) : string =
      match v with
      | Val x -> "Val " ^ (exp_to_concrete_string x)
      | Closure (x, y) -> if printenvp then "Closure (" ^ 
        (exp_to_concrete_string x) ^ ", " ^ (env_to_string y) ^ ")"
        else "Closure (" ^ (exp_to_concrete_string x) ^ ")"

    (* Returns a printable string representation of an environment *)
    and env_to_string (env : env) : string =
      env
      |> List.map 
           (fun (x, y) -> "(" ^ x ^ ", ref " ^ (value_to_string !y) ^ ")")
      |> List.fold_left ( ^ ) ("") ;;

  end
;;

(*......................................................................
  Evaluation functions

  Returns a result of type value of evaluating the expression exp
  in the environment env. We've provided an initial implementation
  for a trivial evaluator, which just converts the expression
  unchanged to a value and returns it, along with "stub code" for
  three more evaluators: a substitution model evaluator and dynamic
  and lexical environment model versions.

  Each evaluator is of type expr -> Env.env -> Env.value for
  consistency, though some of the evaluators don't need an
  environment, and some will only return values that are "bare
  values" (that is, not closures). *)

let binop_eval (b : binop) (e1 : expr) (e2 : expr) : Env.value =
  match e1, e2 with
  | Int j, Int k ->
    (match b with
    | Plus -> Env.Val (Int (j + k))
    | Minus -> Env.Val (Int (j - k))
    | Times -> Env.Val (Int (j * k))
    | Div -> Env.Val (Int (j / k))
    | Equals -> Env.Val (Bool (j = k))
    | LessThan -> Env.Val (Bool (j < k))
    | GreaterThan -> Env.Val (Bool (j > k)))
  | Float j, Float k -> 
    (match b with
    | Plus -> Env.Val (Float (j +. k))
    | Minus -> Env.Val (Float (j -. k))
    | Div -> Env.Val (Float (j /. k))
    | Times -> Env.Val (Float (j *. k))
    | Equals -> Env.Val (Bool (j = k))
    | LessThan -> Env.Val (Bool (j < k))
    | GreaterThan -> Env.Val (Bool (j > k)))
  | Bool j, Bool k -> 
    (match b with
    | Equals -> Env.Val (Bool (j = k))
    | LessThan -> Env.Val (Bool (j < k))
    | GreaterThan -> Env.Val (Bool (j > k))
    | _ -> raise(EvalError "Expression expected of type int or float"))
  | _, _ -> raise(EvalError "Expression expected of type int, float or bool");;

let unop_eval (u : unop) (e : expr) : Env.value =
  match e with
  | Int k -> 
    (match u with
    | Negate -> Env.Val (Int (~- k))) 
  | Bool k -> 
    (match u with
    | Negate -> Env.Val (Bool (not k)))
  | Float k -> 
    (match u with
    | Negate -> Env.Val (Float (~-. k)))
  | _ -> raise(EvalError "Expression expected of type int, bool, ot float");;

(* The TRIVIAL EVALUATOR, which leaves the expression to be evaluated
   essentially unchanged, just converted to a value for consistency
   with the signature of the evaluators. *)
   
let eval_t (exp : expr) (_env : Env.env) : Env.value =
  (* coerce the expr, unchanged, into a value *)
  Env.Val exp ;;

(* The SUBSTITUTION MODEL evaluator -- to be completed *)

let rec eval_s (exp : expr) (env : Env.env) : Env.value =
  let help_s (e : expr) : expr =
    match eval_s e env with
    | Env.Val b | Env.Closure (b, _) -> b
  in
  match exp with
  | Var _ -> raise(EvalError "Unbound variable")
  | Int _ | Float _ | Bool _ | Fun (_, _) -> Env.Val exp
  | Unop (a, b) -> unop_eval a (help_s b)
  | Binop (a, b, c) -> binop_eval a (help_s b) (help_s c)
  | Conditional (a, b, c) -> 
    (match help_s a with 
    | Bool x -> if x then eval_s b env else eval_s c env
    | _ -> raise(EvalError "Expression expected of type bool"))
  | Let (a, b, c) -> 
    let b1 = help_s b in
    let csub = subst a b1 c in
    eval_s csub env
  | Letrec (a, b, c) -> 
    let c1 = subst a (help_s (subst a (Letrec (a, b, Var a)) b)) c in
    eval_s (help_s c1) env 
  | Raise | Unassigned -> raise(EvalException)
  | App (a, b) -> 
    match help_s a with
    | Fun (x, y) -> eval_s (Let (x, b, y)) env
    | App (_, _) as j -> eval_s j env
    | _ -> raise(EvalError "This is not a function; it cannot be applied.") ;;

(* The DYNAMICALLY-SCOPED ENVIRONMENT MODEL evaluator -- to be
   completed *)
   
let rec eval_d (exp : expr) (env : Env.env) : Env.value =
  let help_d (e : expr) : expr =
    match eval_d e env with
    | Env.Val b | Env.Closure (b, _) -> b
  in
  match exp with
  | Var a -> Env.lookup env a
  | Int _ | Float _ | Bool _ | Fun (_, _) -> Env.Val exp
  | Unop (a, b) -> unop_eval a (help_d b)
  | Binop (a, b, c) -> binop_eval a (help_d b) (help_d c)
  | Conditional (a, b, c) ->
    (match help_d a with 
    | Bool x -> if x then eval_d b env else eval_d c env
    | _ -> raise(EvalError "Expression expected of type bool"))
  | Let (a, b, c) -> 
    let new_env = Env.extend env a (ref (eval_d b env)) in
    eval_d c new_env
  | Letrec (a, b, c) ->
    let x = ref (Env.Val Unassigned) in
    let temp_env = Env.extend env a x in
    x := eval_d b temp_env;
    eval_d c temp_env
  | Raise | Unassigned -> raise(EvalException)
  | App (a, b) -> 
    let a1, bv = help_d a, eval_d b env in
    match a1 with
    | Fun (x, y) -> 
      let new_env = Env.extend env x (ref bv) in
      eval_d y new_env
    | App (_, _) as j -> eval_d j env
    | _ -> raise(EvalError "This is not a function; it cannot be applied.") ;;
       
(* The LEXICALLY-SCOPED ENVIRONMENT MODEL evaluator -- optionally
   completed as (part of) your extension *)

let rec eval_l (exp : expr) (env : Env.env) : Env.value =
  let help_l (e : expr) : expr =
    match eval_l e env with
    | Env.Val b | Env.Closure (b, _) -> b
  in
  match exp with
  | Var a -> Env.lookup env a
  | Int _ | Float _ | Bool _ -> Env.Val exp
  | Unop (a, b) -> unop_eval a (help_l b)
  | Binop (a, b, c) -> binop_eval a (help_l b) (help_l c)
  | Conditional (a, b, c) ->
    (match help_l a with 
    | Bool x -> if x then eval_l b env else eval_l c env
    | _ -> raise(EvalError "Expression expected of type bool"))
  | Fun (_, _) -> Env.close exp env
  | Let (a, b, c) -> 
    let new_env = Env.extend env a (ref (eval_l b env)) in
    eval_l c new_env
  | Letrec (a, b, c) ->
    let x = ref (Env.Val Unassigned) in
    let temp_env = Env.extend env a x in
    x := eval_l b temp_env;
    eval_l c temp_env
  | Raise | Unassigned -> raise(EvalException)
  | App (a, b) ->
    (match eval_l a env with
    | Env.Closure (Fun (x, y), fun_env) ->
        let new_env = Env.extend fun_env x (ref (eval_l b env)) in
        eval_l y new_env 
    | Env.Val x -> 
      (match x with
      | App (_, _) as j -> eval_l j env
      | _ -> raise(EvalError 
        "This is not a function; it cannot be applied."))) ;;

(* Connecting the evaluators to the external world. The REPL in
   miniml.ml uses a call to the single function evaluate defined
   here. Initially, evaluate is the trivial evaluator eval_t. But you
   can define it to use any of the other evaluators as you proceed to
   implement them. (We will directly unit test the four evaluators
   above, not the evaluate function, so it doesn't matter how it's set
   when you submit your solution.) *)
   
let evaluate = eval_s ;;
