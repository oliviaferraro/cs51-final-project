(* TESTS!!! *)

open Evaluation ;;
open Miniml ;;
open Expr ;;

(* Static values *)
let val_list = [str_to_exp "3;;"; str_to_exp "2.3;;"; str_to_exp "true;;"; 
  str_to_exp "fun x -> (x + 4);;"]

let v, w, z = Var "v", Var "w", Var "z";;

(* Simple binop and unop operations *)
(* < and > *)
let ilst = [str_to_exp "3 < 2;;"; str_to_exp "3.3 < 3.;;"; 
  str_to_exp "0 < 2;;"; str_to_exp "0. < 2.;;"] 

let bolst = [str_to_exp "true > false;;"; str_to_exp "true < false;;"] ;;

let jlst = [str_to_exp "3 > 2;;"; str_to_exp "3.3 > 3.;;"; 
  str_to_exp "0 > (~- 3);;"; str_to_exp "0. < (~- 2.);;"] ;;

(* * and / *)
let k1, k2, k3, k4 = str_to_exp "4 + 3;;", str_to_exp "4. + 3.;;", 
  str_to_exp "0 + (~- 1);;", str_to_exp "0. + (~- 1.);;" ;;

let l1, l2, l3, l4 = str_to_exp "4 - 3;;", str_to_exp "(4. - 3.);;",
  str_to_exp "(10 - 3);;", str_to_exp "(5. - 3.);;" ;;

(* * and / *)
let mlst = [str_to_exp "4 * 3;;"; str_to_exp "4. * 3.;;";
  str_to_exp "0 * 3;;"; str_to_exp "0. * 3.;;"]

let nlst = [str_to_exp "4 / 2;;"; str_to_exp "4. / 2.;;"; 
  str_to_exp "0 / 4;;"; str_to_exp "0. / 4.;;"] ;;

(* Non-simple value expressions *)
(* App *)
let e = str_to_exp "(fun x -> (x + 3)) 6;;" ;;
let e1 = str_to_exp "(fun x -> (x + 3.4)) 6.0;;" ;;
let e3 = str_to_exp "fun x -> (x + 3);;" ;;

(* Let *)
let g = str_to_exp "let x = 5 in (x + 6);;" ;;
let g1 = str_to_exp "let x = 5. in (x + 6.8);;" ;;

(* Letrec *)
let h = str_to_exp 
  "let rec f = fun n -> if n = 0 then 1 else n * f (n-1) in f 3;;" ;;
let h1 = str_to_exp 
  "let rec f = fun n -> if n = 0. then 1. else n * f (n-(1.0)) in f 3.0;;" ;;

(* Conditional *)
let p = str_to_exp "if 3 > 4 then 6 else 7;;" ;;
let p1 = str_to_exp "if 3. = 3. then 10 else 20;;" ;;

(* Test free_vars *)
let test_free () =
  (* values *)
  assert(same_vars (free_vars k1) (vars_of_list [])) ;

  (* Unop *)
  assert(same_vars (free_vars (Unop (Negate, v))) (vars_of_list ["v"])) ;;

  (* Binop *)
  assert(same_vars (free_vars (Binop (Plus, v, w))) (vars_of_list ["v"; "w"]));
  
  (* Conditional *)
  assert(same_vars (free_vars (Conditional (z, v, w))) 
    (vars_of_list ["v"; "w"; "z"]));

  (* Fun *)
  assert(same_vars (free_vars (Fun ("v", Binop (Plus, v, z)))) 
    (vars_of_list ["z"]) && (same_vars (free_vars (Fun ("v", v))) 
    (vars_of_list [])));

  (* Let *)
  assert((same_vars (free_vars g) (vars_of_list [])) && (same_vars 
    (free_vars (Let ("v", Int 4, Binop (Plus, v, w))))
    (vars_of_list ["w"])));

  (* Letrec *)
  assert(same_vars (free_vars h) (vars_of_list []));

  (* Raise and Unassigned *)
  assert((same_vars (free_vars Raise) (vars_of_list [])) 
    && (same_vars (free_vars Unassigned) (vars_of_list [])));;

  (* App *)
  assert(same_vars (free_vars e) (vars_of_list []));;

(* Test subst *)
let test_subst () =

  (* values *)
  assert(subst "v" k1 l1 = l1);

  (* Unop *)
  assert(subst "v" (Int 3) (Unop (Negate, v)) = (Unop (Negate, Int 3)));

  (* Binop *)
  assert(subst "w" (Float 1.) (Binop (Plus, w, v)) = Binop (Plus, Float 1., v));
  
  (* Conditional *)
  assert(subst "w" (Float 1.) 
    (Conditional (Bool true, Binop (Plus, w, v), Float 3.)) = 
    (Conditional (Bool true, Binop (Plus, Float 1., v), Float 3.)));

  (* Raise and Unassigned *)
  assert((subst "v" (Int 3) (Raise) = Raise) 
    && (subst "w" (Int 3) (Unassigned) = Unassigned));

  (* App *)
  assert(subst "v" (Int 3) (App (Fun ("w", Binop (Plus, v, w)), Int 1)) =
    (App (Fun ("w", Binop (Plus, Int 3, w)), Int 1)));;

(* Test Env module *)
let test_env () =

  (* Create empty testing environment, then non-empty environment *)
  let empt, a, b = Env.create (), ref (Env.Val (Int 3)), 
    ref (Env.Val (Bool true)) in
  let two_el = Env.extend (Env.extend empt "a" a) "b" b in

  (* Close *)
  assert(Env.close e3 empt = Env.Closure (e3, empt)) ;

  (* Lookup *)
  assert((Env.lookup two_el "a" = Env.Val (Int 3)) 
    && (Env.lookup two_el "b" = Env.Val (Bool true)));

  (* Value_to_string and env_to_string *)
  assert((Env.value_to_string (Env.Val (Float 1.)) = "Val 1.")
    && (Env.value_to_string (Env.Closure (e3, empt)) = 
    "Closure (fun x -> (x + 3), )"));;

(* Test expressions that should be same for all evals *)
let test_simple f =

  (* Create empty testing environment *)
  let empt = Env.create () in

  (* Helper functions, map eval over lists appropriately *)
  let aux = List.map (fun x -> f x empt) in
  let aux2 = List.map (fun y -> Env.Val (str_to_exp y)) in

  (* Static values *)
	assert((aux val_list) = 
		(List.map (fun x -> Env.Val x) val_list)) ;
  
  (* Unop *)
  (* Negation *)
  assert((List.map (fun x -> f (Unop (Negate, x)) empt) 
    [str_to_exp "3;;"; str_to_exp "2.3;;"; str_to_exp "true;;"]) = 
    [Env.Val (Int (-3)); Env.Val (Float (-2.3)); 
    Env.Val (str_to_exp "false;;")]) ;

  (* Binop *)
	(* < and > *)
	assert((aux ilst = aux2 ["false;;"; "false;;"; "true;;"; "true;;"]) 
	  && (aux jlst = aux2 ["true;;"; "true;;"; "true;;"; "false;;"]) 
	  && (aux bolst = aux2 ["true;;"; "false;;"])) ;

  (* + and - *)
  assert((f k1 empt = Env.Val (Int 7)) && (f k2 empt = Env.Val (Float 7.))
    && (f k3 empt = Env.Val (Int (-1))) && (f k4 empt = Env.Val (Float (-1.))));
  assert((f l1 empt = Env.Val (Int 1)) && (f l2 empt = Env.Val (Float 1.))
    && (f l3 empt = Env.Val (Int 7)) && (f l4 empt = Env.Val (Float 2.)));
	
  (* * and / *)
	assert((aux mlst = aux2 ["12;;"; "12.;;"; "0;;"; "0.;;"]) 
	  && (aux nlst = aux2 ["2;;"; "2.;;"; "0;;"; "0.;;"])) ;
  
  (* More complicated expressions *)
  
  (* Conditional *)
  assert((f p empt = Env.Val (Int 7)) && (f p1 empt = Env.Val (Int 10))) ;

  (* Let *)
  assert((f g empt = Env.Val (Int 11)) 
    && (f g1 empt = Env.Val (Float 11.8)));

  (* Letrec *)
  assert((f h empt = Env.Val (Int 6)) && (f h1 empt = Env.Val (Float 6.)));

  (* App *)
  assert((f e empt = Env.Val (Int 9)) && (f e1 empt = Env.Val (Float 9.4)));;

(* Dynamic vs. Lexical *)
let test_lex () =
  (* Create example expressions for testing *)
  let dy = str_to_exp "let x = 1 in let f = (fun y -> x + y) in let x = 3 in 
    let y = 4 in f (x + y);;" in
  let dy1 = str_to_exp "let x = 1 in let f = fun y -> x in 
    let x = 2 in f 0 ;;" in
  let dy2 = str_to_exp "fun x -> (x + 3);;" in

  (* Create an empty testing environment and a Env.value ref *)
  let empt, temp = Env.create (), ref (Env.Val (Int 5)) in

  (* Create a non-empty testing environment *)
  let one_el = Env.extend empt "a" temp in
  
  (* fun *)
	(* eval_l *)
	assert(eval_l dy2 empt = Env.Closure (dy2, empt));
	assert(eval_l dy2 one_el = Env.Closure (dy2, one_el));

	(* eval_d *)
  assert(eval_d dy2 empt = Env.Val dy2);
	assert(eval_d dy2 one_el = Env.Val dy2);

  (* scoping *)
  (* eval_l *)
  assert(eval_l dy empt = Env.Val (Int 8));
  assert(eval_l dy one_el = Env.Val (Int 8));
  assert(eval_l dy1 empt = Env.Val (Int 1));
  assert(eval_l dy1 one_el = Env.Val (Int 1));

  (* eval_d *)
  assert(eval_d dy empt = Env.Val (Int 10));
  assert(eval_d dy one_el = Env.Val (Int 10));
  assert(eval_d dy1 empt = Env.Val (Int 2));
  assert(eval_d dy1 one_el = Env.Val (Int 2));;

let _ = 
  test_simple eval_s ;
  test_simple eval_d ;
  test_lex () ;
  test_free () ;
  test_subst () ;
  test_env () ;;
