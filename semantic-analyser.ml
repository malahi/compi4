(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let l_without_last l =
  List.rev (List.tl (List.rev l)) 

let rec find_element x l =
  match l with
  | [] -> -1
  | h :: t -> if x = h then 0 else 1 + find_element x t;;

let param_bound_index param_l p =
  match List.filter (fun x -> List.length (List.filter (fun y -> y = p) x) > 0) param_l with
  | [] -> (-1 , -1)
  | l ->  ((find_element (List.hd l) param_l) - 1 ,  find_element p (List.hd l))

(* --------------================= annotate_lexical_addresses ==================------------------ *)

let rec add_helper param_l expr = 
  let nested = fun () ->
  try add_const expr
  with X_syntax_error -> try add_var param_l expr 
  with X_syntax_error -> try add_if  param_l expr 
  with X_syntax_error -> try add_seq param_l expr 
  with X_syntax_error -> try add_set param_l expr 
  with X_syntax_error -> try add_lambda param_l expr 
  with X_syntax_error -> try add_def param_l expr 
  with X_syntax_error -> try add_or param_l expr 
  with X_syntax_error -> try add_lambdaopt param_l expr 
  with X_syntax_error -> try add_applic param_l expr 
  with X_syntax_error -> raise X_syntax_error in
  nested ()

and add_const = function
  | Const (x) -> Const' (x)
  | _ -> raise X_syntax_error

and add_var param_l expr =
  match expr with
  | Var(x) -> (match (param_bound_index param_l x) with
              | (-1  , -1)  -> Var'(VarFree(x))
              | (-1  , p_i) -> Var'(VarParam(x , p_i))
              | (b_i , p_i) -> Var'(VarBound(x , b_i , p_i)))
 
  | _ -> raise X_syntax_error

and add_if param_l = function
  | If(test , dit , dif) -> If'((add_helper param_l test) , (add_helper param_l dit) , (add_helper param_l dif))
  | _ -> raise X_syntax_error

and add_seq param_l = function
  | Seq(expr_l) -> Seq'(List.map (add_helper param_l) expr_l)
  | _ -> raise X_syntax_error
  
and add_lambda param_l = function
  | LambdaSimple(p_l , body) -> LambdaSimple'(p_l , (add_helper (p_l :: param_l) body))
  | _ -> raise X_syntax_error

and add_set param_l = function
  | Set(var , expr) -> Set'((add_helper param_l var) , (add_helper param_l expr))
  | _ -> raise X_syntax_error
  
and add_def param_l = function
  | Def(var , expr) -> Def'((add_helper param_l var) , (add_helper param_l expr))
  | _ -> raise X_syntax_error
  
and add_or param_l = function
  | Or(expr_l) -> Or'(List.map (add_helper param_l) expr_l)
  | _ -> raise X_syntax_error

and add_lambdaopt param_l = function
  | LambdaOpt(p_l , p_last , body) -> LambdaOpt'(p_l , p_last , (add_helper ((List.append p_l [p_last]) :: param_l) body))
  | _ -> raise X_syntax_error

and add_applic param_l = function
  | Applic(proc , p_l) -> Applic'((add_helper param_l proc) , (List.map (add_helper param_l) p_l))
  | _ -> raise X_syntax_error;;

(* -----------------===================== annotate_tail_calls ======================------------------ *)

let rec tail_calls_helper flag e = 
  match e , flag with
  | LambdaSimple'(param_l , expr_tag) , _ -> LambdaSimple'(param_l , tail_calls_helper true expr_tag)
  | LambdaOpt'(param_l , p_last , expr_tag) , _ -> LambdaOpt'(param_l , p_last , tail_calls_helper true expr_tag)
  | Set'(var , expr) , _ -> Set'(var , tail_calls_helper false expr)
  | Seq'(l) , _ -> Seq'(List.append (List.map (tail_calls_helper false) (l_without_last l)) [(tail_calls_helper flag (List.nth l ((List.length l) - 1)))])
  | Or' (l) , _ -> Or' (List.append (List.map (tail_calls_helper false) (l_without_last l)) [(tail_calls_helper flag (List.nth l ((List.length l) - 1)))])
  | Applic'(proc , p_l) , false -> Applic'  (tail_calls_helper false proc , List.map (tail_calls_helper false) p_l)
  | Applic'(proc , p_l) , true  -> ApplicTP'(tail_calls_helper false proc , List.map (tail_calls_helper false) p_l)
  | If'(test , dit , dif) , _ -> If'(tail_calls_helper false test , tail_calls_helper flag dit , tail_calls_helper flag dif)
  | Def'(var , expr) , _ -> Def'(var , tail_calls_helper false expr)
  | x , _ -> x;;

(* --------------------=========================== box_set =============================--------------------- *) 

let rec get_index var ls indx = 
  match ls with
  | [] -> -1
  | x :: cdr -> (match x = var with
                | true -> indx
                | false -> get_index var cdr (indx + 1))
   
let make_seq_set args =
    List.fold_left (fun acc arg -> List.append acc [Set'(Var'(VarParam(fst arg, snd arg)), Box'(VarParam(fst arg, snd arg)))]) [] args;;
                
              
let compare_wr w r elem =
  match elem with 
  | (1 , 1) -> (1 , 1)
  | (1 , _) -> (1 , r)
  | (_ , 1) -> (w , 1)
  | _ -> (w , r)

let rec make_exp_list_h expr = 
  match expr with
  | LambdaSimple'(param_l , expr_tag) -> [expr]
  | LambdaOpt'(param_l , p_last , expr_tag) -> [expr]
  | Seq'(l) -> List.flatten (List.map make_exp_list_h l)
  | Set'(var , expr) -> make_exp_list_h expr
  | Or' (l) -> List.flatten (List.map make_exp_list_h l)
  | If'(test , dit , dif) -> (List.append (make_exp_list_h test) (List.append (make_exp_list_h dit) (make_exp_list_h dif)))
  | Applic'(proc , p_l) -> List.append (make_exp_list_h proc) (List.flatten (List.map make_exp_list_h p_l))
  | ApplicTP'(proc , p_l) -> List.append (make_exp_list_h proc) (List.flatten (List.map make_exp_list_h p_l))
  | Def'(var , expr) -> make_exp_list_h expr
  | _ -> [];;

let make_el code =
  match code with 
  | LambdaSimple'(param_l , expr_tag) -> List.append [code] (make_exp_list_h expr_tag)
  | LambdaOpt'(param_l , p_last , expr_tag) -> List.append [code] (make_exp_list_h expr_tag)
  | _ -> [];;

let rec need_box_h arg lam_flag exp =
  match exp , lam_flag  with 
  | LambdaSimple'(param_l , expr_tag) , 0 ->  (match List.mem arg param_l with 
                                                  | false -> need_box_h arg lam_flag expr_tag 
                                                  | true -> [(0 ,0)])
  | LambdaOpt'(param_l , p_last , expr_tag) , 0 ->  (match List.mem arg (List.append param_l [p_last]) with 
                                                  | false -> need_box_h arg lam_flag expr_tag 
                                                  | true -> [(0 ,0)])
  | Seq'(l) , _ -> List.flatten (List.map (need_box_h arg lam_flag) l)
  | Set'(var , expr) , _ -> (match var with
                         | Var'(VarParam(x , _)) -> (match x = arg with
                                                    | true -> List.append [(1 , 0)] (need_box_h arg lam_flag expr)
                                                    | _ -> List.append [(0 , 0)] (need_box_h arg lam_flag expr))
                         | Var'(VarBound(x ,_ , _)) -> (match x = arg with
                                                        | true -> List.append [(1 , 0)] (need_box_h arg lam_flag expr)
                                                        | _ -> List.append [(0 , 0)] (need_box_h arg lam_flag expr))
                         | _ -> List.append [(0 ,0)] (need_box_h arg lam_flag expr))
      
  | Or' (l) , _-> List.flatten (List.map (need_box_h arg lam_flag) l)
  | If'(test , dit , dif) , _ -> (List.append (need_box_h arg lam_flag test) (List.append (need_box_h arg lam_flag dit) (need_box_h arg lam_flag dif)))
  | Applic'(proc , p_l) , _  -> List.append (need_box_h arg lam_flag proc) (List.flatten (List.map (need_box_h arg lam_flag) p_l))
  | ApplicTP'(proc , p_l) , _-> List.append (need_box_h arg lam_flag proc) (List.flatten (List.map (need_box_h arg lam_flag) p_l))
  | Var'(VarParam(x , _)) , _-> (match x = arg with
                                | true -> [(0 , 1)] 
                                | _ -> [(0 , 0)] )
  | Var'(VarBound(x ,_ , _)) , _-> (match x = arg with
                                  | true -> [(0 , 1)] 
                                  | _ -> [(0 , 0)] )
  | BoxSet'(var , expr) , _ -> need_box_h arg lam_flag expr
  | LambdaSimple'(param_l , expr_tag) , 1 ->  need_box_h arg (lam_flag + 1) expr_tag
  | LambdaOpt'(param_l , p_last , expr_tag) , 1 ->  need_box_h arg (lam_flag + 1) expr_tag
  | Def'(var , expr) , _ -> need_box_h arg lam_flag expr 
  | _ , _-> [(0 ,0)];;

let need_box ex_l arg =
  match ex_l with
  | [] ->  false
  | _ -> let wr = List.append (List.map (need_box_h arg 0) (List.tl ex_l)) [(need_box_h arg 1 (List.hd ex_l))] in
            let all_or = (List.map (fun ls -> List.fold_left (fun (w , r) wr -> compare_wr w r wr) (0 , 0) ls ) wr) in
              let one_one = List.fold_left (fun (one , zero) x -> match x with
                                                                | (1 ,1) -> (one + 1 , zero)
                                                                | (0 ,0) -> (one , zero + 1)
                                                                | _ -> (one , zero)) (0 , 0) all_or in
                let len = (List.length all_or) - 1 in
                  let value = List.fold_left (fun (w , r) wr -> compare_wr w r wr) (0 , 0) all_or in
                        match value with
                        | (1 , 1) -> (match (fst one_one) == 1 , (snd one_one) == len with
                                     | true , true -> false
                                     | _ , _ -> true) 
                        | _ -> false;;
                   
let args_to_change expr =
  let ls = make_el expr in
    match expr with
    | LambdaSimple'(param_l , expr_tag) -> List.map (fun y -> (y , (get_index y param_l 0))) (List.filter (fun x -> need_box ls x) param_l)
    | LambdaOpt'(param_l , p_last , expr_tag) -> List.map (fun y -> (y , (get_index y (List.append param_l [p_last]) 0))) (List.filter (fun x -> need_box ls x) (List.append param_l [p_last]))
    | _ -> [];;
                     
let rec change_code arg bound expr = 
  match expr , bound with
  | LambdaSimple'(param_l , expr_tag) , _ -> LambdaSimple'(param_l , change_code arg (bound + 1) expr_tag)  
  | LambdaOpt'(param_l , p_last , expr_tag) , _ -> LambdaOpt'(param_l ,  p_last ,change_code arg (bound + 1) expr_tag)
  | Var'(VarParam(var , ind)) , -1 -> (match var = arg with
                                       | true  -> BoxGet'(VarParam(var , ind)) 
                                       | false -> Var'(VarParam(var , ind)))
  | Var'(VarBound(var , b , ind)) , _ -> (match b == bound , var = arg with
                                         | true , true -> BoxGet'(VarBound(var , b, ind)) 
                                         | _ , _-> Var'(VarBound(var , b , ind)))
  | Seq'(l) , _ -> Seq'(List.map (change_code arg bound) l)
  | Set'(var , expr) , _ -> (match var , bound with
                             | Var'(VarParam(x , ind)) , -1  -> (match x = arg with
                                                                 | true -> BoxSet'(VarParam(x , ind) , change_code arg bound expr)
                                                                 |   _  -> Set'(Var'(VarParam(x , ind)) , change_code arg bound expr))
                             | Var'(VarBound(x ,b , ind)), _ -> (match x = arg , b = bound with
                                                                 | true , true -> BoxSet'(VarBound(x ,b , ind) , change_code arg bound expr)
                                                                 | _ -> Set'(Var'(VarBound(x ,b , ind)) , change_code arg bound expr))
                             | _ -> Set'(var , change_code arg bound expr))
  | Or' (l) , _ -> Or'(List.map (change_code arg bound) l)
  | If'(test , dit , dif) , _ -> If'((change_code arg bound test) , (change_code arg bound dit) , (change_code arg bound dif))
  | Applic'(proc , p_l) , _ -> Applic'((change_code arg bound proc) , (List.map (change_code arg bound) p_l))
  | ApplicTP'(proc , p_l) , _ -> ApplicTP'((change_code arg bound proc) , (List.map (change_code arg bound) p_l))
  | BoxSet'(var , expr) , _ -> BoxSet'(var , change_code arg bound expr)
  | Def'(var , expr) , _ -> change_code arg bound expr
  | x , _ -> x;;

let map_on_args lam_ls expr x =
   change_code x (-2) expr 

let make_my_box_h arg_to_change expr = 
  let lam_ls = (make_el expr) in
   List.fold_left (map_on_args lam_ls) expr arg_to_change 
     
let make_my_box expr =
  let arg_to_change = args_to_change expr in
    let new_exp = make_my_box_h (List.map (fun x -> fst x) arg_to_change) expr in
        match arg_to_change , new_exp with
        | [] , _-> new_exp
        | _  , LambdaSimple'(param_l , expr_tag)      -> LambdaSimple'(param_l , Seq'(List.append (make_seq_set arg_to_change) [expr_tag]))
        | _  , LambdaOpt'(param_l , p_last , expr_tag)-> LambdaOpt'(param_l ,  p_last , Seq'(List.append (make_seq_set arg_to_change) [expr_tag]))
        | _ , _ -> new_exp;;       

let rec box = function
  | Seq'(l) -> Seq'(List.map box l)
  | Def'(var , expr) -> Def'(var , box expr)
  | LambdaSimple'(x , y) ->  make_my_box (LambdaSimple'(x , (box y)))
  | LambdaOpt'(x , y , z) -> make_my_box (LambdaOpt'(x , y , z)) 
  | Set'(var , expr) -> Set'(var , box expr) 
  | Or' (l) -> Or'(List.map box l)
  | If'(test , dit , dif) -> If'((box test) , (box dit) , (box dif))
  | Applic'(proc , p_l) -> Applic'((box proc) , (List.map box p_l))
  | ApplicTP'(proc , p_l) -> ApplicTP'((box proc) , (List.map box p_l))
  | BoxSet'(var , expr) -> BoxSet'(var , box expr)
  | x -> x;; 

let annotate_lexical_addresses e = add_helper [] e;;

let annotate_tail_calls e = tail_calls_helper false e;;

let box_set e = box e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; 
(* struct Semantics *)
