(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)
 #use "reader.ml";;
type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let rec if_proper_list = function
  | Nil -> true
  | Pair(car , Nil) -> true
  | Pair(x , Pair(y , y2)) -> if_proper_list (Pair(y , y2))
  | Pair(car , cdr) -> false
  | _ -> false;;

let rec symbol_to_slist = function 
  | Nil -> []
  | Symbol(x) -> [x]
  | Pair(Symbol(x) , ls) -> List.append [x] (symbol_to_slist ls) 
  | _ -> raise X_syntax_error;;
  
let arg_list sexs_l = 
    let symbol_l = symbol_to_slist sexs_l in
    List.fold_left (fun acc x-> ( 
      match (ormap (fun (a) -> a = x) acc ) with
      | true  -> raise X_syntax_error
      | false -> match (ormap (fun (a) -> a = x) reserved_word_list) with
               | true  -> raise X_syntax_error
               | false -> List.append acc [x]
  )) [] symbol_l;; 

let make_list l first =
  (List.fold_right (fun acc  a-> Pair( acc , a )) l first );;
    
let get_arg ag ls =   (* ag = true returns vars, ag = false returns values *)
  List.map (fun (x) -> match x with
                      | Pair(arg , Pair(valu , Nil)) -> (match ag with
                                                         | true  -> arg
                                                         | false -> valu)
                      | _ -> raise X_syntax_error) ls;;
    
let rec flat_pairs = function
  | Pair(fs , Nil) -> [fs]
  | Pair(fs , ls)  -> fs :: (flat_pairs ls)
  | Nil -> []
  | _ -> raise X_syntax_error;; 

let rec var_to_vals = function 
  | []  -> Nil
  | a::vrls  -> Pair(Pair(a , Pair(Pair(Symbol("quote"), Pair(Symbol("whatever") , Nil)) , Nil)) , var_to_vals vrls)

let rec lr_body vars vals sexprs =
   match vars , vals with
   | [] , [] -> sexprs
   | a::vrls , b::vlls -> Pair(Pair(Symbol("set!") , Pair(a , Pair(b , Nil))) , (lr_body vrls vlls sexprs)) 
   | _ -> raise X_syntax_error
(* --------------------===================== Tag - parser ===================---------------------------------- *)
 
let rec tag_parse sexpr = 
  let nested = fun () ->
  try const_tag sexpr
  with X_syntax_error -> try var_tag sexpr
  with X_syntax_error -> try if_tag sexpr
  with X_syntax_error -> try lambda_tag sexpr
  with X_syntax_error -> try seq_begin_tag sexpr
  with X_syntax_error -> try set_tag sexpr 
  with X_syntax_error -> try def_tag sexpr
  with X_syntax_error -> try app_tag sexpr  
  with X_syntax_error -> try or_tag sexpr  
  with X_syntax_error -> try let_exp sexpr  
  with X_syntax_error -> try let_star_exp sexpr
  with X_syntax_error -> try quote_tag sexpr
  with X_syntax_error -> try and_exp sexpr
  with X_syntax_error -> try mit_exp sexpr
  with X_syntax_error -> try letrec_exp sexpr
  with X_syntax_error -> try qq_exp sexpr
  with X_syntax_error -> try cond_exp sexpr
  with X_syntax_error -> raise X_syntax_error in
  nested ()
  
and const_tag = function
  | Number(x) -> Const(Sexpr(Number(x)))
  | Bool(x) -> Const(Sexpr(Bool(x)))
  | Char(x) -> Const(Sexpr(Char(x)))
  | String(x) -> Const(Sexpr(String(x)))
  | Pair(Symbol("quote") , Pair(sexpr , Nil)) ->  Const(Sexpr(sexpr))
  | _ -> raise X_syntax_error


and var_tag = function
  | Symbol(x) -> (match (ormap (fun (a) -> a = x) reserved_word_list ) with
                  | true -> raise X_syntax_error
                  | false -> Var(x))
  | _ -> raise X_syntax_error

and if_tag = function
  | Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) -> If(tag_parse test , tag_parse dit , Const(Void))
  | Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) -> If(tag_parse test , tag_parse dit , tag_parse dif)
  | _ -> raise X_syntax_error

and lambda_tag = function
  | (Pair(Symbol("lambda") , Pair(args , sexprs))) 
                  -> (match (if_proper_list args) , sexprs with
                      | true , Pair(_ , _) -> LambdaSimple ((arg_list args), (seq_tag sexprs))
                      | false , Pair(_ , _) -> LambdaOpt (List.rev (List.tl (List.rev (arg_list args))) , (List.hd (List.rev (arg_list args))) , (seq_tag sexprs))     
                      | _ -> raise X_syntax_error)       
  | _ -> raise X_syntax_error 

and seq_begin_tag = function
  | Pair(Symbol("begin") , ls) 
                -> (match ls with
                   | Nil -> Const (Void) 
                   | Pair(car , Nil) -> tag_parse car
                   | Pair(car , cdr) -> Seq( (tag_parse car) :: (make_exp_ls cdr) ) 
                   | _ -> raise X_syntax_error)          
  | _ -> raise X_syntax_error

and seq_tag = function
  | Pair(car , ls) -> (match ls with
                      | Nil -> tag_parse car
                      | ls -> Seq( (tag_parse car) :: (make_exp_ls ls) ))   
  | sexp -> tag_parse sexp

and set_tag = function
  | Pair(Symbol("set!") , Pair( var , Pair(valu , Nil))) -> (Set((var_tag var) , (tag_parse valu))) 
  | _ -> raise X_syntax_error

and def_tag = function
  | Pair(Symbol("define") , Pair( var , Pair(valu , Nil))) -> (Def((var_tag var) , (tag_parse valu))) 
  | _ -> raise X_syntax_error 

and app_tag = function
  | Pair(car , cdr) -> Applic( tag_parse car , make_exp_ls cdr)
  | _ -> raise X_syntax_error

and make_exp_ls = function
  | Nil -> []
  | Pair(car , cdr) -> (tag_parse car) :: (make_exp_ls cdr)
  | _ -> raise X_syntax_error

and or_tag = function
  | Pair(Symbol("or") , Nil) -> Const (Sexpr (Bool false))
  | Pair(Symbol("or") , Pair(sexp , Nil)) -> tag_parse sexp
  | Pair(Symbol("or"), ls) -> Or(make_exp_ls ls)
  | _ -> raise X_syntax_error

and quote_tag = function
  | Pair (Symbol("quote"), Pair (sexp , Nil)) -> Const(Sexpr(sexp))
  | _ -> raise X_syntax_error 
(*-------------------------=============================== Macro Expansions =============================------------------------------*)

and let_exp = function
  | Pair(Symbol("let") , Pair(args , body)) 
                          -> let arg_ls = make_list (get_arg true (flat_pairs args)) Nil in
                              let lambda = Pair(Symbol("lambda") , Pair(arg_ls , body)) in
                                let values = make_list (get_arg false (flat_pairs args)) Nil in  
                                  tag_parse (Pair(lambda, values)) 
  | _ -> raise X_syntax_error

and let_star_exp = function
  | Pair(Symbol("let*") , Pair(args , body)) -> tag_parse (let_star_exp_h args body)
  | _ -> raise X_syntax_error

and let_star_exp_h args body =
  match args with
  | Nil -> (Pair(Symbol("let") , Pair(Nil, body)))
  | Pair (Pair (var, Pair(valu, Nil)), Nil) -> (Pair(Symbol("let") , Pair(Pair (Pair (var, Pair(valu, Nil)), Nil), body)))
  | Pair (Pair (var, Pair(valu, Nil)), ls)  -> (Pair(Symbol("let") , Pair(Pair (Pair (var, Pair(valu, Nil)), Nil), Pair((let_star_exp_h ls body) , Nil)))) 
  | _ -> raise X_syntax_error

and and_exp_h = function
  | Nil             -> Bool(true)
  | Pair(car , Nil) -> car 
  | Pair(car , cdr) -> Pair(Symbol("if") , Pair(car , Pair(and_exp_h cdr , Pair(Bool(false) , Nil))))  
  | _ -> raise X_syntax_error

and and_exp = function
  | Pair(Symbol("and") , cdr) -> tag_parse (and_exp_h cdr) 
  | _ -> raise X_syntax_error

and mit_exp = function
  | Pair(Symbol("define"), Pair(func , body)) 
                                -> (match func with
                                   | Pair(name , args) -> tag_parse ((Pair(Symbol("define") , Pair(name , Pair(Pair (Symbol("lambda") , Pair(args, body) ), Nil)))))
                                   | _ -> raise X_syntax_error) 
  | _ -> raise X_syntax_error
    
and letrec_exp = function
  | Pair(Symbol("letrec") , Pair(args , body)) 
                      -> (let vars = flat_pairs (make_list (get_arg true (flat_pairs args)) Nil) in
                            let values = flat_pairs (make_list (get_arg false (flat_pairs args)) Nil) in  
                              let let_s = Pair(Symbol("let") , Pair((var_to_vals vars) , (lr_body vars values body) )) in
                                tag_parse let_s)
  | _ -> raise X_syntax_error                                         


and qq_exp_h3 sexp =
  match sexp with
  | Bool(x) -> Pair (Symbol("quote") , Pair(sexp , Nil))
  | Number(x)-> Pair (Symbol("quote") , Pair(sexp , Nil))
  | Char(x) -> Pair (Symbol("quote") , Pair(sexp , Nil))
  | String(x) -> Pair (Symbol("quote") , Pair(sexp , Nil))
  | Nil       -> Pair (Symbol("quote") , Pair(sexp , Nil))
  | Symbol(x) -> Pair (Symbol("quote") , Pair(sexp , Nil))
  | Vector(x) -> Pair(Symbol("vector") , make_list (List.map (fun sex -> qq_exp_h3 sex) x) Nil )  
  (*| Pair(Symbol("quote"), Pair(sexp, Nil)) -> Pair( Symbol("quote"), Pair( Pair(Symbol("quote"), Pair(sexp, Nil)), Nil)) *)
  | Pair(Symbol("unquote") , Pair(sexp , Nil))  -> sexp           
  | Pair(car , cdr) -> (match car ,cdr  with
                        | Pair(Symbol("unquote-splicing") , Pair(sexp , Nil)) , _ ->  Pair(Symbol("append") , Pair(sexp , Pair(qq_exp_h3 cdr , Nil)))
                        | _ , Pair(Symbol("unquote-splicing") , Pair(sexp , Nil)) ->  Pair(Symbol("cons") , Pair(qq_exp_h3 car, Pair(sexp , Nil)))
                        | _ -> Pair(Symbol("cons") , Pair(qq_exp_h3 car , Pair(qq_exp_h3 cdr , Nil))))                               

and qq_exp_h = function
  | Pair (Symbol "unquote-splicing", _) -> raise X_syntax_error
  | s -> qq_exp_h3 s
              
and qq_exp = function
  | Pair (Symbol("quasiquote"), Pair (sexp , Nil)) ->  tag_parse (qq_exp_h sexp)
  | _ -> raise X_syntax_error   

and cond_exp_h = function
  | [] -> Nil
  | Pair(Symbol("else") , else_seq) :: [] -> Pair(Pair(Symbol("begin") , else_seq), Nil)
  | Pair(test , Pair(Symbol("=>"), seq)) :: ls -> (match ls with
                                                  | [] -> Pair(make_last_cond test seq , Nil)
                                                  | _  -> Pair(make_cond test seq (cond_exp_h ls) , Nil))
  | Pair(test , seq) :: ls -> Pair (Pair(Symbol("if"), Pair(test , Pair(Pair(Symbol("begin") , seq), cond_exp_h ls ))), Nil)
  | _ -> raise X_syntax_error

and cond_exp = function
  | Pair(Symbol("cond") , body) -> (let ribs = flat_pairs body in
                                    let nested_if = (cond_exp_h ribs) in
                                      match nested_if with
                                      | Pair(car , Nil) -> tag_parse car
                                      | _ -> raise X_syntax_error)
  | _ -> raise X_syntax_error
 
and make_cond test seq next = 
Pair (Symbol "let", Pair
  (Pair (Pair (Symbol "value", Pair (test, Nil)), Pair
     (Pair (Symbol "f", Pair (Pair (Symbol "lambda", Pair (Nil, seq)), Nil)), Pair
      (Pair (Symbol "rest", Pair (Pair (Symbol "lambda", Pair (Nil, next)), Nil)), Nil))), Pair
        (Pair (Symbol "if", Pair (Symbol "value", Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
          Pair (Pair (Symbol "rest", Nil), Nil)))), Nil)))

and make_last_cond test seq =
Pair (Symbol "let", Pair 
  (Pair (Pair (Symbol "value", Pair (test, Nil)), Pair
    (Pair (Symbol "f", Pair (Pair (Symbol "lambda", Pair (Nil, seq)),  Nil)), Nil)),
      Pair (Pair (Symbol "if", Pair (Symbol "value", Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)), Nil))),
            Nil)));;


let tag_parse_expression sexpr = tag_parse sexpr;;

let tag_parse_expressions sexpr = List.map tag_parse_expression sexpr ;;

end;; 
(* struct Tag_Parser *)



