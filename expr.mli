(* 
                         CS 51 Final Project
                        MiniML -- Expressions
                             Spring 2018
*)

(* Abstract syntax of MiniML expressions *)

(* Unary operators *)
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

type varidset ;;

(* same_vars varids -- Test to see if two sets have the same elements
   (for testing purposes) *)
val same_vars : varidset -> varidset -> bool ;;

(* vars_of_list varids -- Generate a set of variable names from a list
   of varids (for testing purposes) *)
val vars_of_list : varid list -> varidset ;;

(* free_vars e -- Returns the set of varids corresponding to free
   variables in e *)
val free_vars : expr -> varidset

(* new_varname () -- Return a freshly minted varid *)
val new_varname : unit -> varid

(* subst x p q -- Return the expression q with p substituted for free
   occurrences of x *)
val subst : varid -> expr -> expr -> expr

(* exp_to_concrete_string e -- Return a string representation of the concrete
   syntax of the expression e *)
val exp_to_concrete_string : expr -> string

(* exp_to_abstract_string e -- Return a string representation of the
   abstract syntax of the expression e *)
val exp_to_abstract_string : expr -> string

