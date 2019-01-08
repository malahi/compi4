(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "pc.ml";;

 exception X_not_yet_implemented;;
 exception X_this_should_not_happen;;
   
 type number =
   | Int of int
   | Float of float;;
   
 type sexpr =
   | Bool of bool
   | Nil
   | Number of number
   | Char of char
   | String of string
   | Symbol of string
   | Pair of sexpr * sexpr
   | Vector of sexpr list;;
     
   let rec sexpr_eq s1 s2 =
    match s1, s2 with
    | Bool(b1), Bool(b2) -> b1 = b2
    | Nil, Nil -> true
    | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
    | Number(Int n1), Number(Int n2) -> n1 = n2
    | Char(c1), Char(c2) -> c1 = c2
    | String(s1), String(s2) -> s1 = s2
    | Symbol(s1), Symbol(s2) -> s1 = s2
    | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
    | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
    | _ -> false;;
   
 module Reader: sig
   val read_sexpr : string -> sexpr
   val read_sexprs : string -> sexpr list
 end
 = struct
 let normalize_scheme_symbol str =
   let s = string_to_list str in
   if (andmap
   (fun ch -> (ch = (Char.lowercase_ascii ch)))
   s) then str
   else Printf.sprintf "|%s|" str;;
 

   let test a b = (
    match b with
    | '(' -> a + 1
    | ')' -> a - 1
    | '[' -> a + 1
    | ']' -> a - 1
    | _ -> a);;
  
  let rec dotsH ls =
    match ls with
    | '.' :: cdr -> 1 + dotsH cdr
    | _ -> 0;; 
  
  let rec checkLastDots ls = 
    match ls with
    | ' ' :: cdr -> checkLastDots cdr
    | '.' :: cdr -> 1 + dotsH cdr
    | _ -> 0;;
  
  let rec remove_dots ls dots = 
    match ls , dots > 0 with
    | ' ' :: cdr , _ -> remove_dots cdr dots
    | '.' :: cdr  , true-> remove_dots cdr (dots - 1)
    | cdr , _ -> List.rev cdr;;
  
  let isBalanced ls = 
    let bl = List.fold_left test 0 ls in
      let dots = checkLastDots (List.rev ls) in
    match bl , dots with
    | 0 , 3 -> remove_dots (List.rev ls) 3
    | _ , _ -> ls;;
  
  let _delimiters_ s = 
    match s with 
    | [] -> ([] , s)
    | e :: s -> 
       if ((String.contains "()[];\"#,'` ." e)  || e <= ' ') then ( [] , e::s)
       else raise PC.X_no_match;;

  let _space_ =
    PC.const (fun (c) -> c <= ' ');;
  
  let make_enclosed _l_ _p_ _r_ =
    let _enclosed_ = PC.caten (PC.caten _l_ _p_) _r_ in
    PC.pack _enclosed_ (fun ((l, p), r) -> p);;
  
  let make_spaced _p_ = 
    let _st_space_ = PC.star _space_ in
    make_enclosed _st_space_ _p_ _st_space_;;
  
 (*-----------------------------======================== Bool parser ===========================---------------------*)
 let _true_  =   (PC.caten (PC.char '#') (PC.char_ci 't'));;
 let _false_ =   (PC.caten (PC.char '#') (PC.char_ci 'f'));;
 let _bool_ =  PC.caten (PC.disj _true_ _false_) _delimiters_;;
 let bool_p = PC.pack _bool_ (fun ((e , s) , x) -> match s with
                                             | 't' | 'T' -> Bool true
                                             | 'f' | 'F' -> Bool false
                                             | _ -> raise X_this_should_not_happen);;

 (*------------------------------======================= Char parser =============================--------------------------------*)
 let _c_prefix_ = PC.caten (PC.char '#') (PC.char '\\');;
 let _vs_char_  = PC.caten (PC.pack (PC.const (fun ch -> ' ' < ch)) (fun ch -> [ch])) _delimiters_;;
 let vs_char_p  = PC.pack _vs_char_ (fun (e , d) -> Char (List.hd e));;
 
 let named_char_p =  PC.pack (PC.caten ((PC.disj_list [PC.pack (PC.word_ci "newline") (fun (s) -> Char '\n')         ; PC.pack (PC.word_ci "return")(fun (s) -> Char '\r'); 
                                                       PC.pack (PC.word_ci "page")    (fun (s) -> Char (Char.chr 12)); PC.pack (PC.word_ci "space") (fun (s) -> Char ' ' ); 
                                                       PC.pack (PC.word_ci "nul")     (fun (s) -> Char (Char.chr 0)) ; PC.pack (PC.word_ci "tab")   (fun (s) -> Char '\t')])) _delimiters_) 
                                                       (fun (sexp , del) -> sexp);; 
  
 let _hex_digit_ = PC.disj_list [(PC.range '0' '9') ; (PC.range 'a' 'f') ; (PC.range 'A' 'F')];;
 let _hex_char_  = PC.caten (PC.caten (PC.char_ci 'x') (PC.plus _hex_digit_)) _delimiters_;;
 let hex_char_p  = PC.pack _hex_char_ (fun ((e ,s) , d) -> Char (Char.chr (int_of_string (list_to_string (List.append ['0' ; 'x'] s)))));;
 
 let char_p = PC.pack ( (PC.caten (_c_prefix_) (PC.disj_list [ named_char_p ; hex_char_p ; vs_char_p ] ))) (fun (e , s) -> s) ;;
 
 (*-----------------------------===================== Integer parser =================--------------------------------------------*)
 let _hex_prefix_ = PC.word_ci "#x";;
 let _digit_      = PC.range '0' '9';;
 let _natural_    = PC.plus _digit_;;
 let _integer_    = PC.pack (PC.caten (PC.maybe (PC.disj (PC.char '+') (PC.char '-'))) _natural_) (fun (e , num) ->  match e with
                                                                                                                |  Some '-' -> ('-' :: num)
                                                                                                                | _  ->  num) ;;
 let  integer_p = PC.pack _integer_ (fun (l) ->  Number (Int (int_of_string (list_to_string l ))));;
 
 let _float_ = PC.pack (PC.caten (PC.caten _integer_  (PC.char '.'))  _natural_) (fun ((man , dot ), exp)  -> List.append man  (dot :: exp) );;                                                                                                                                                            
 let float_p = PC.pack _float_ (fun (l) ->  Number (Float (float_of_string (list_to_string l))));; 
                                          
 let _hex_natural_ = PC.plus _hex_digit_;;
 let _hex_integer_ = PC.caten (PC.caten _hex_prefix_ (PC.maybe (PC.disj (PC.char '+') (PC.char '-')))) _hex_natural_ ;;  
 let hex_integer_p = PC.pack _hex_integer_ (fun (e , s) -> match e with
                                                           | (_ , Some '-') -> Number ( Int ( -1*int_of_string (list_to_string (List.append ['0' ; 'x'] s )))) 
                                                           | (_ , _) -> Number ( Int ( int_of_string (list_to_string (List.append ['0' ; 'x'] s )))));;
 
 let _hex_float_ = PC.caten (PC.caten _hex_integer_ (PC.char '.')) _hex_natural_;;
 let hex_float_p = PC.pack _hex_float_ (fun (e , exp) -> match e with
                                                       | (((_ , Some '-'), man), _ ) -> Number (Float (-1.0*.float_of_string (list_to_string (List.append ('0' :: 'x' :: man) ('.' :: exp) )))) 
                                                       | ((_ , man), _ ) -> Number (Float (float_of_string (list_to_string (List.append ('0' :: 'x' :: man) ('.' :: exp))))));; 
let _number_ = PC.pack (PC.caten ( (PC.disj_list [float_p ; integer_p ; hex_float_p ; hex_integer_p ])) _delimiters_) (fun (e , d) -> (e));;

let caten_e_numbers n e f1 f2 = 
  Number (Float (float_of_string (String.concat "e" (List.append [(f1 n)] [(f2 e)]))));;

let make_e_numbers num exp = 
  match num , exp with
  | Number(Int(n)) , Number(Int(e)) -> caten_e_numbers n e string_of_int string_of_int
  | Number(Int(n)) , Number(Float(e)) -> caten_e_numbers n e string_of_int string_of_float
  | Number(Float(n)) , Number(Float(e)) -> caten_e_numbers n e string_of_float string_of_float
  | Number(Float(n)) , Number(Int(e)) -> caten_e_numbers n e string_of_float string_of_int
  | _ -> raise X_this_should_not_happen;;
  
let _e_first_number_ =  (PC.disj_list [float_p ; integer_p ; hex_float_p ; hex_integer_p ]);;
let _e_number_ = PC.pack (PC.caten ( (PC.caten (PC.caten _e_first_number_ (PC.char_ci 'e')) _number_)) _delimiters_ ) (fun((( num  , e ), exp ), d) -> make_e_numbers num exp);;
let number_p = PC.pack (PC.disj _e_number_ _number_) (fun (e ) -> e);;

 (*-----------------========================== Symbol parser =======================---------------------------*)
 let _symbol_char_ = PC.disj_list [(PC.range '0' '9') ; (PC.pack (PC.range_ci 'a' 'z') (fun c -> lowercase_ascii c)) ; (PC.one_of "!$^*-_=+<>?/:") ];;
 let _symbol_char_plus_ = PC.caten (PC.plus _symbol_char_) _delimiters_;;
 let symbol_p =  (PC.pack _symbol_char_plus_ (fun (l , d) -> Symbol (list_to_string l) ));;

(*-------------------========================= String parser =======================------------------------*)                                
(* <StringLiteralChar> *)
let nt_backsalsh_dq = PC.const(fun (ch) -> ch!='"' && ch!='\\');;
let _string_literal_ = PC.pack (nt_backsalsh_dq) (fun (str)->[str]);;
let string_literal_p = PC.pack _string_literal_ (fun (e)-> List.hd e);;
(* <StringMetaChar> *)
let _return_ = PC.word("\\r");;
let _newline_= PC.word("\\n");;
let _tab_ = PC.word("\\t");;
let _page_= PC.word("\\f");; 
let _backslash_ = PC.word("\\\\");;
let _double_quote_ = PC.word("\\\"");;
let _string_meta_ = PC.disj_list[_return_ ;_newline_; _tab_ ; _page_ ; _backslash_ ; _double_quote_];;
let string_meta_p = PC.pack _string_meta_ (fun (e) -> match (list_to_string e) with 
                                                          | "\\r" -> '\r'
                                                          | "\\n" -> '\n'
                                                          | "\\t" -> '\t'
                                                          | "\\f" -> '\012'
                                                          | "\\\\" -> '\\'
                                                          | "\\\"" -> '\"'
                                                          | _ -> raise X_this_should_not_happen);;
(* <StringHexChar> *)
let _hex_string_ =PC.caten (PC.caten (PC.caten (PC.char '\\') (PC.char_ci 'x')) (PC.plus _hex_digit_)) (PC.char ';');;
let string_hex_p= PC.pack _hex_string_ (fun ((((bs,x),hd)),sc)-> Char.chr (int_of_string (list_to_string (List.append ['0' ; 'x'] hd))));;
(* <StringChar> *)
let _string_char_p = PC.disj_list [string_literal_p ; string_meta_p ; string_hex_p];;
(* <String> *)
let string_p = PC.caten (PC.caten (PC.char('"'))(PC.star _string_char_p)) (PC.char '"');;
let string_p = PC.pack string_p (fun ((l,s),r)-> (String (list_to_string s)));;
 (* Comments parser *)
let _line_comm_ =  (PC.caten (PC.caten (PC.char ';') (PC.star (PC.diff PC.nt_any (PC.char '\n')))) (PC.disj (PC.nt_end_of_input) (PC.pack (PC.char '\n') (fun (e) -> [e])))) ;;
let line_comm_p = PC.pack _line_comm_ (fun (_) -> ([]));;

 (*-------------------========================= Sexpr parser =======================------------------------*)
let make_list l first =
    (List.fold_right (fun acc  a-> Pair( acc , a )) l first );;
   let a = make_list [] (Pair( Nil , Nil));; 

let rec sexp_p s =  
    let nested = PC.caten (PC.caten sexp_comment_p (make_spaced (PC.disj_list [bool_p ; char_p ; number_p ; symbol_p ; string_p ; nil_p ; list_p ; q_p ; dot_list_p ; square_dot_list_p ; square_list_p ; vector_p ; _dot_sexp_tag_ ;  _sexp_tag_ ])) ) sexp_comment_p in
      PC.pack nested (fun ((s , e) , k) -> e) s
 
and list_p        = fun (s) -> list_h_p false false s 
and square_list_p = fun (s) -> list_h_p true false  s 

and dot_list_p        = fun (s) -> dot_list_h_p false false s                 
and square_dot_list_p = fun (s) -> dot_list_h_p true false  s                  

and vector_p = fun (s) -> 
        PC.pack (PC.caten (PC.caten (make_spaced (PC.word "#("))  (PC.star sexp_p)) (make_spaced (PC.char ')')) ) (fun ((ht , sexps) , cb) -> Vector sexps) s

and sexp_comment_p = fun (s) -> 
        PC.pack ((PC.star (make_spaced (PC.disj line_comm_p _sexp_comment_) ))) (fun (_) -> []) s

and q_p = fun (s) -> ( (PC.disj_list [unquote_p() ; unquote_splicing_p() ; quasiquote_p() ; quote_p()])) s

(* ---------------------========================== three dots ==============================------------------------- *)

and sexp_tag_p s =   
    let nested = PC.caten (PC.caten sexp_comment_p (make_spaced (PC.disj_list [bool_p ; char_p ; number_p ; symbol_p ; string_p ; nil_p ; dot_list_tag_p ; square_dot_list_tag_p  ; list_tag_p ; q_p ;  square_list_tag_p ]) )) sexp_comment_p in
            PC.pack nested (fun ((s , (e )) , k) -> e) s

and list_tag_p        = fun (s) -> list_h_p false true s  
and square_list_tag_p = fun (s) -> list_h_p true  true s 

and dot_list_tag_p        = fun (s) -> dot_list_h_p false true s
and square_dot_list_tag_p = fun (s) -> dot_list_h_p true  true s                  

and _reg_list_ lp rp tag =
  match tag with
  | true  -> (PC.pack ( (PC.caten (PC.caten (make_spaced (PC.char lp)) (PC.star sexp_tag_p)) (make_spaced (PC.maybe (PC.char rp))))) (fun((e , k) , es) -> make_list k Nil))
  | false -> (PC.pack ( (PC.caten (PC.caten (make_spaced (PC.char lp)) (PC.star sexp_p)) (make_spaced (PC.char rp)))) (fun((e , k) , es) -> make_list k Nil))

and _dot_list_ lp rp tag =
  match tag with
  | true  -> (PC.pack ( ((PC.caten (PC.caten (PC.caten (PC.caten (make_spaced (PC.char lp)) (PC.plus sexp_tag_p)) ( make_spaced (PC.char '.'))) sexp_tag_p) (make_spaced (PC.maybe (PC.char rp)))))) ( fun(((( lp , sex1) , dot) , sex2) , rp) -> make_list (List.rev (List.tl (List.rev sex1))) (Pair( List.nth sex1 ((List.length sex1) - 1) , sex2))))
  | false -> (PC.pack ( ((PC.caten (PC.caten (PC.caten (PC.caten (make_spaced (PC.char lp)) (PC.plus sexp_p)) ( make_spaced (PC.char '.'))) sexp_p) (make_spaced (PC.char rp))))) ( fun(((( lp , sex1) , dot) , sex2) , rp) -> make_list (List.rev (List.tl (List.rev sex1))) (Pair( List.nth sex1 ((List.length sex1) - 1) , sex2))  ))

and list_h_p sq tag =
    match sq with
    | true    ->  _reg_list_  '[' ']' tag      (* sq  = true for '[' false for '(' *)
    | false   ->  _reg_list_  '(' ')' tag      (* tag = true for three dots CFG false for regular list CFG*)

and dot_list_h_p sq tag =
    match sq with
    | true    ->  _dot_list_ '[' ']' tag
    | false   ->  _dot_list_ '(' ')' tag
(* --------------------------------------------- end of three dots  -------------------------------------------------------- *)
and _sexp_comment_h_ s = 
        try let (e , s1) = (PC.word "#;") s in
              let (e , ss) = _sexp_comment_h_ s1 in
                match ss with
                | []  -> ([] , s1)               
                | _ -> try ((PC.pack sexp_p (fun (_) -> [] )) ss) with PC.X_no_match -> ([] , [])
        with PC.X_no_match -> ([] , s)

and _sexp_comment_ s = 
      let _ = (PC.word "#;") s in
        _sexp_comment_h_ s

and _quote_      = fun () -> PC.caten (PC.char '\'') sexp_p
and quote_p      = fun () -> PC.pack (_quote_()) (fun (q , sexp) -> Pair ( Symbol ("quote"), Pair(sexp , Nil)) )
and _quasiquote_ = fun () -> PC.caten (PC.char '`') sexp_p
and quasiquote_p = fun () -> PC.pack (_quasiquote_()) (fun (q , sexp) -> Pair ( Symbol "quasiquote", Pair(sexp , Nil)) )
and _unquote_splicing_ = fun () -> PC.caten (PC.word ",@") sexp_p
and unquote_splicing_p = fun () -> PC.pack (_unquote_splicing_()) (fun (q , sexp) -> Pair ( Symbol "unquote-splicing", Pair(sexp , Nil)) )
and _unquote_ = fun () -> PC.caten (PC.char ',') sexp_p
and unquote_p = fun () -> PC.pack (_unquote_()) (fun (q , sexp) -> Pair ( Symbol "unquote", Pair(sexp , Nil)) )

and _nil_ = fun (s) -> (PC.caten (PC.caten (PC.caten (PC.char '(') sexp_comment_p)  (PC.char ')' )) _delimiters_) s
and nil_p = fun (s) -> ( (PC.pack _nil_ (fun (e , d) -> Nil))) s

and _sexp_tag_ = fun(s) -> (PC.pack (PC.caten (PC.caten (make_spaced (PC.disj (PC.char '(') (PC.char '['))) (PC.star sexp_tag_p)) ( (PC.word "..."))) (fun((p , e) , s) -> make_list e Nil)) s
and _dot_sexp_tag_ = fun(s) -> (PC.pack (PC.caten ((( (PC.caten (PC.caten (PC.caten (make_spaced (PC.disj (PC.char '(') (PC.char '['))) (PC.plus sexp_tag_p)) ( make_spaced (PC.char '.'))) sexp_tag_p) ))) (PC.word "...") ) ( fun((((( lp , sex1) , dot) , sex2), dots) ) -> make_list (List.rev (List.tl (List.rev sex1))) (Pair( List.nth sex1 ((List.length sex1) - 1) , sex2))  )) s;;

let sexp_p_check s =
  sexp_p (isBalanced s);;

let read_sexpr string = 
  let l = string_to_list string in
      let (e , s) = (make_spaced sexp_p_check) l in
        match s with
        | [] -> e
        | _ -> raise PC.X_no_match;;
         
let read_sexprs string = 
    let (e , s) = (make_spaced sexp_comment_p) (string_to_list string) in
      match s with
      | [] -> []
      | _ -> let l = (string_to_list string) in 
              match l with 
              | [] ->  [] 
              | _  ->  let (e , s) = (make_spaced (PC.plus sexp_p_check)) l in
                      match s with
                      | [] -> e
                      | _ -> raise PC.X_no_match;;
 end;;
  (* struct Reader *)
