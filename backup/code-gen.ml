#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;; 

let lam_label_i = ref 1;;
let lam_opt_label_i = ref 1;;
let or_label_i  = ref 1;;
let if_label_i  = ref 1;;
let app_label_i  = ref 1;;

let a = ref 1;;

let getIndex i =
    let index = !i in
      i := !i + 1;
      index;;

let addToIndex = function
  | Sexpr(Number(Int(_))) -> 9 
  | Sexpr(Number(Float(_))) -> 9
  | Sexpr(Char(_)) -> 2
  | Sexpr(String(s)) -> 9 + (String.length s)
  | Sexpr(Pair (_,_)) -> 17
  | Sexpr(Bool(_)) -> 2
  | Sexpr(Symbol(_)) -> 9
  | Sexpr(Vector(x)) -> 9 + 8*(List.length x)
  | _ -> 0;;

let rec getVarTableIndex ls var =
  match ls with
  | (x , i) :: cdr  -> (match x = var with
                        | true -> i
                        | false -> getVarTableIndex cdr var)
  | [] -> -1;;

let getConstTableIndex ls value =
 let var = List.filter (fun x -> (match x with | ((v),_) -> v = value)) ls in
   match var , ls with
    | [(_,(index,_))] , _ -> index
    | _ , [] -> 0 
    | _ , _-> let (typ , (index , _)) = List.hd (List.rev ls) in 
              index + (addToIndex typ);;

let rec isContains ls value = 
  match ls with
  | ( x , _) :: cdr -> (match x = value with
                        | true  -> true
                        | false -> isContains cdr value)
  | [] -> false;;

let changeString s =
  List.map (fun c ->  (string_of_int (int_of_char c)) ) (string_to_list s);;

let rec sexprTypes ls expr = 
  match expr , (isContains ls (Sexpr(expr))) with
  | Number(Int(n)) , false  -> List.append ls [( Sexpr(expr) , ( (getConstTableIndex ls (Sexpr(expr)))  , "MAKE_LITERAL_INT("   ^ string_of_int(n) ^ ")"))]
  | Number(Float(n)) , false -> List.append ls [( Sexpr(expr) , ( (getConstTableIndex ls (Sexpr(expr)))  , "MAKE_LITERAL_FLOAT(" ^  string_of_float(n) ^ ")"))]
  | Char(c) , false -> List.append ls [(Sexpr(expr),((getConstTableIndex ls (Sexpr(expr))),"MAKE_LITERAL_CHAR(" ^ (string_of_int (int_of_char c)) ^ ")"))]
  | String(s) , false -> List.append ls [(Sexpr(expr),((getConstTableIndex ls (Sexpr(expr))) , "MAKE_LITERAL_STRING " ^ (String.concat "," (changeString s)) ^ ""))]
  | Symbol(s) , false -> let tmp_ls = (sexprTypes ls (String(s))) in
                            List.append tmp_ls [(Sexpr(expr),((getConstTableIndex tmp_ls (Sexpr(expr))) , "MAKE_LITERAL_SYMBOL( const_tbl + " ^ (string_of_int (getConstTableIndex tmp_ls (Sexpr(String(s))))) ^ ")"))]
  | Pair (car,cdr) , false -> let tmp_ls = (sexprTypes (sexprTypes ls car) cdr) in
                                      List.append tmp_ls [(Sexpr(Pair(car , cdr)) , ((getConstTableIndex tmp_ls (Sexpr(expr))) , "MAKE_LITERAL_PAIR( const_tbl + " ^ (string_of_int (getConstTableIndex tmp_ls (Sexpr(car)))) ^ "," ^ "const_tbl + " ^ (string_of_int (getConstTableIndex tmp_ls (Sexpr(cdr)))) ^ ")"))]
  | Vector (x) , false -> let tmp_ls = (List.fold_left sexprTypes ls x) in
                                      List.append tmp_ls [(Sexpr(expr) , (getConstTableIndex tmp_ls (Sexpr(expr)) , "MAKE_LITERAL_VECTOR " ^ (String.concat (",") (List.map (fun var -> "const_tbl + " ^ ((string_of_int (getConstTableIndex tmp_ls (Sexpr(var))))) ) x))))] 
  | _ -> ls;;

let rec makeConstTable ls expr =
  match expr with  
  | Const'(Sexpr(x))-> sexprTypes ls x
  | Applic' (x , y) -> List.fold_left makeConstTable (makeConstTable ls x) y
  | Def' (_ , x) -> makeConstTable ls x 
  | BoxSet'(_ , x) -> makeConstTable ls x 
  | If' (test , dit , dif) -> (makeConstTable (makeConstTable (makeConstTable ls test ) dit ) dif )
  | Seq'(exps) -> List.fold_left makeConstTable ls exps 
  | Set' (x, y) -> makeConstTable (makeConstTable ls x) y 
  | Or'(exps)-> List.fold_left makeConstTable ls exps 
  | LambdaSimple'(_ , x) -> makeConstTable ls x 
  | LambdaOpt'(_ , _ , x)-> makeConstTable ls x 
  | ApplicTP'(x , y)-> List.fold_left makeConstTable (makeConstTable ls x) y
  | _ -> ls;;


let freeVarHandler ls var =
  match var with
  | VarFree(s) -> (match (isContains ls s) with
                   | false -> List.append ls [(s , 0)]
                   | true  -> ls)
  | _ -> ls;;

let rec makeFreeVarTable_h ls expr =
  match expr with  
  | Var' (x) -> freeVarHandler ls x
  | Applic' (x, y) -> List.fold_left makeFreeVarTable_h (makeFreeVarTable_h ls x) y
  | Def' (x , y) -> makeFreeVarTable_h (makeFreeVarTable_h ls x) y 
  | Box'(x) -> freeVarHandler ls x 
  | BoxGet'(x) -> freeVarHandler ls x 
  | BoxSet'(_ , x) -> makeFreeVarTable_h ls x 
  | If' (test , dit , dif) -> (makeFreeVarTable_h (makeFreeVarTable_h (makeFreeVarTable_h ls test ) dit ) dif )
  | Seq'(exps) -> List.fold_left makeFreeVarTable_h ls exps 
  | Set' (x, y) -> makeFreeVarTable_h (makeFreeVarTable_h ls x) y 
  | Or'(exps)-> List.fold_left makeFreeVarTable_h ls exps 
  | LambdaSimple'(_ , x) -> makeFreeVarTable_h ls x 
  | LambdaOpt'(_ , _ , x)-> makeFreeVarTable_h ls x 
  | ApplicTP'(x , y)-> List.fold_left makeFreeVarTable_h (makeFreeVarTable_h ls x) y
  | _ -> ls;;

  let rec defineIndex i ls =
    match ls with
    | [] -> ls
    | (x , _) :: cdr -> (x , i) :: defineIndex (i + 8) cdr


  let makeFreeVarTable ls expr =
    let exp_ls = makeFreeVarTable_h ls expr in
      defineIndex 0 exp_ls;;


let rec makeAssmCode consts fvars lam_i e =
  match e with  
  | Const'(x) -> "mov rax , const_tbl + " ^ (string_of_int ((getConstTableIndex consts x) ) ) ^ "\n"
  | Var'(VarParam(_, minor)) -> "mov rax, qword [rbp + 8 * (4 + " ^ string_of_int(minor) ^ ")] \n"
  | Set'(Var'(VarParam(_, minor)) , eps) -> (makeAssmCode consts fvars lam_i eps) ^ 
                                            "mov qword [rbp + 8*( 4 + " ^ string_of_int(minor) ^ ")] , rax \n" ^  
                                             "mov rax, SOB_VOID_ADDRESS \n" 
  | Var'(VarBound(_, major, minor)) -> "mov rax, qword [rbp + 8*2] \n" ^
                                        "mov rax, qword [rax + 8*" ^ string_of_int(major) ^ "] \n" ^
                                        "mov rax, qword [rax + 8*" ^ string_of_int (minor) ^"] \n"
  | Set'(Var'(VarBound(_, major, minor)), eps) -> (makeAssmCode consts fvars lam_i eps) ^ "mov rbx, qword [rbp + 8*2] \n" ^ 
                                                  "mov rbx, qword [rbx + 8*" ^ string_of_int(major) ^ "] \n" ^ 
                                                  "mov qword [rbx + 8*" ^ string_of_int(minor) ^ "], rax \n" ^ 
                                                  "mov rax, SOB_VOID_ADDRESS\n" 
  | Var'(VarFree(v)) -> "mov rax, qword [fvar_tbl + " ^ (string_of_int (getVarTableIndex fvars v)) ^ "] \n"
  | Set'(Var'(VarFree(v)), eps) -> (makeAssmCode consts fvars lam_i eps) ^ 
                                   "mov qword [fvar_tbl + " ^ (string_of_int (getVarTableIndex fvars v)) ^ "], rax \n" ^
                                   "mov rax, SOB_VOID_ADDRESS \n"
  | Def'(Var'(VarFree(v)), eps) -> (makeAssmCode consts fvars lam_i eps) ^ 
                                    "mov qword [fvar_tbl + " ^ (string_of_int (getVarTableIndex fvars v)) ^ "], rax \n" ^ 
                                    "mov rax, SOB_VOID_ADDRESS \n"
  | Seq'(ls) -> List.fold_left (fun acc x -> (acc ^ (makeAssmCode consts fvars lam_i x))) "" ls
  | Or'(ls) -> let or_index = (string_of_int (getIndex a)) in
                (List.fold_left (fun acc x -> (acc ^ (makeAssmCode consts fvars lam_i x) ^ ("cmp rax, SOB_FALSE_ADDRESS \n jne orLexit" ^ or_index ^ " \n"))) "" (List.rev (List.tl (List.rev (ls))))) ^ 
                (List.fold_left (fun acc x -> (acc ^ (makeAssmCode consts fvars lam_i x) ^ ("orLexit" ^ or_index ^ ": \n") )) "" [(List.nth ls ((List.length ls) - 1))]) 
  | If'(test ,dit ,dif) -> let if_index = (string_of_int (getIndex a)) in
                              (makeAssmCode consts fvars lam_i test) ^ 
                              "cmp rax, SOB_FALSE_ADDRESS \n" ^ 
                              "je Lelse" ^ if_index ^ " \n " ^ 
                              (makeAssmCode consts fvars lam_i dit) ^ 
                              "jmp Lexit" ^ if_index ^ " \n 
                              Lelse" ^ if_index ^ ": \n" ^
                              (makeAssmCode consts fvars lam_i dif)  ^ 
                              "Lexit" ^ if_index ^ ": \n"
  | BoxGet'(v) -> (makeAssmCode consts fvars lam_i (Var'(v))) ^ 
                  "mov rax, qword [rax] \n"
  | Box'(v) -> "MALLOC rsi , 8\n" ^
               ((makeAssmCode consts fvars lam_i (Var'(v)))) ^
               "mov [rsi], rax\n" ^
               "mov rax, rsi\n"
  | BoxSet'(v , eps) -> (makeAssmCode consts fvars lam_i eps) ^ 
                        "push rax \n" ^
                        (makeAssmCode consts fvars lam_i (Var'(v))) ^ 
                        "pop qword [rax] \n" ^
                         "mov rax, SOB_VOID_ADDRESS\n"
  | Applic'(proc, args) -> let index = (string_of_int (getIndex app_label_i)) in
                           "push qword SOB_NIL_ADDRESS\n" ^
                           (List.fold_right (fun x acc-> ((acc ^ makeAssmCode consts fvars lam_i x) ^ "push rax \n")) args "") ^ 
                           "push " ^ (string_of_int (List.length args)) ^ " \n" ^
                           (makeAssmCode consts fvars lam_i proc) ^
                           "mov sil, [rax]\n" ^
                           "cmp sil, T_CLOSURE\n" ^
                           "je next" ^ index ^ "\n" ^
                           "mov rax, SOB_FALSE_ADDRESS\n" ^
                           "ret\n" ^
                           "next" ^ index ^ ":\n" ^
                           "push qword [rax + 1]\n" ^ 
                           "call [rax + 9]\n" ^
                           "add rsp, 8*1 \n" ^
                           "pop rbx\n" ^
                           "inc rbx\n" ^
                           "shl rbx, 3\n" ^
                           "add rsp, rbx\n"                     

  | LambdaSimple'(params , body) -> let label = (string_of_int (getIndex lam_label_i)) in
                                    ";------------- copy env " ^ label ^ " ----------------\n" ^
                                    "COPY_ENV " ^ (string_of_int (8*(lam_i + 1))) ^ " , " ^ (string_of_int ((lam_i + 1))) ^ "\n" ^
                                    "mov r15, r14\n" ^
                                    ";---------------- copy args " ^ label ^ " ----------------\n" ^
                                    "mov r11, qword [rbp + 8*3]\n" ^
                                    "inc r11\n" ^
                                    "mov rax, r11\n" ^
                                    "mov rdx, 8\n" ^
                                    "mul rdx\n" ^
                                    "mov r11, rax\n" ^
                                    
                                    "MALLOC r13, r11\n" ^
                                    "mov [r15], r13\n" ^
                                    "mov r10, rbp\n" ^
                                    "mov r12, 8*4\n" ^
                                    "add r10, r12\n" ^
                                     "mov r11, qword [rbp + 8*3]\n" ^
                                     "inc r11\n" ^
                                     " cmp r11, 0\n" ^
                                     " je pend" ^ label ^ "\n" ^
                                     
                                     "ploop" ^ label ^ ":\n" ^
                                     " cmp r11, 0\n" ^
                                    " je pend" ^ label ^ "\n" ^
                                    " mov r14, [r10]\n" ^
                                    " mov [r13], r14\n" ^ 
                                    " add r10, 8\n" ^
                                    " add r13, 8\n" ^
                                    " dec r11\n" ^
                                    " jmp ploop" ^ label ^ "\n" ^
                                    "pend" ^ label ^ ":\n" ^
                                    ";---------------- make closure " ^ label ^ " ----------------\n" ^
                                    "mov r12, r15\n" ^
                                    "MAKE_CLOSURE(rax , r12 , Lcode" ^ label ^ ")\n" ^
                                    "jmp " ^ "Lcont" ^ label ^ "\n" ^
                                    "Lcode" ^ label ^ ":\n" ^
                                    " push rbp\n" ^
                                    " mov rbp, rsp\n" ^
                                    " " ^ (makeAssmCode consts fvars (lam_i + 1) body) ^ "\n" ^
                                    " leave\n" ^
                                    " ret\n" ^
                                    "Lcont" ^ label ^ ":\n"
  | LambdaOpt'(params, opt , body) -> let label = (string_of_int (getIndex lam_label_i)) in
                                    ";------------- copy env " ^ label ^ " ----------------\n" ^                                  
                                    "COPY_ENV " ^ (string_of_int (8*(lam_i + 1))) ^ " , " ^ (string_of_int ((lam_i + 1))) ^ "\n" ^
                                    "mov r15, r14\n" ^
                                    ";---------------- copy args " ^ label ^ " ----------------\n" ^
                                    "mov r11, qword [rbp + 8*3]\n" ^
                                    "inc r11\n" ^
                                    "mov rax, r11\n" ^
                                    "mov rdx, 8\n" ^
                                    "mul rdx\n" ^
                                    "mov r11, rax\n" ^
                                    
                                    "MALLOC r13, r11\n" ^
                                    "mov [r15], r13\n" ^
                                    "mov r10, rbp\n" ^
                                    "mov r12, 8*4\n" ^
                                    "add r10, r12\n" ^
                                    "mov r11, qword [rbp + 8*3]\n" ^
                                    "inc r11\n" ^
                                    " cmp r11, 0\n" ^
                                    " je pend" ^ label ^ "\n" ^
                                    
                                    "ploop" ^ label ^ ":\n" ^
                                    " cmp r11, 0\n" ^
                                    " je pend" ^ label ^ "\n" ^
                                    " mov r14, [r10]\n" ^
                                    " mov [r13], r14\n" ^ 
                                    " add r10, 8\n" ^
                                    " add r13, 8\n" ^
                                    " dec r11\n" ^
                                    " jmp ploop" ^ label ^ "\n" ^
                                    "pend" ^ label ^ ":\n" ^
                                    ";---------------- make closure " ^ label ^ " ----------------\n" ^
                                    "mov r12, r15\n" ^
                                    "MAKE_CLOSURE(rax , r12 , Lcode" ^ label ^ ")\n" ^
                                    "jmp " ^ "Lcont" ^ label ^ "\n" ^
                                    "Lcode" ^ label ^ ":\n" ^
                                    " push rbp\n" ^
                                    " mov rbp, rsp\n" ^
                                    ";------ opt ----------------- \n" ^
                                    " mov r8,  [rbp + 8*3]\n" ^
                                    " mov r15, [rbp + 8*3]\n" ^
                                    " mov r10, r8\n" ^
                                    " mov r11, " ^ (string_of_int ((List.length params))) ^ "\n" ^    
                                    " sub r10, r11\n" ^
                                    " cmp r10, 0\n" ^
                                     (* "mov qword [rbp + 8*3], " ^ (string_of_int ((List.length params) + 1)) ^ "\n" ^ *)
                                    " je end_opt" ^ label ^ "\n" ^
                                    
                                    "mov qword [rbp + 8*3], " ^ (string_of_int ((List.length params) + 1)) ^ "\n" ^
                                    "mov r9, [rbp + 8*(3+r8)]\n" ^    
                                    "MAKE_PAIR(r11 , r9 , SOB_NIL_ADDRESS)\n" ^
                                    "dec r10\n" ^
                                    "make_ls" ^ label ^ ":\n" ^
                                    " cmp r10, 0\n" ^
                                    " je end_make_ls" ^ label ^ "\n" ^

                                    " dec r8\n" ^
                                    " mov r9, [rbp + 8*(3+r8)]\n" ^    
                                    " MAKE_PAIR(r12 , r9 , r11)\n" ^
                                    " mov r11, r12\n" ^
                                    " dec r10\n" ^
                                   
                                    " jmp make_ls" ^ label ^ "\n" ^
                                    " end_make_ls" ^ label ^ ":\n" ^
                                    
                                    "mov [rbp + 8*(3 + " ^ (string_of_int ((List.length params) + 1)) ^ ")] , r11\n" ^

                                    "mov r11, r15\n" ^
                                    "sub r11," ^ (string_of_int ((List.length params) + 1)) ^ "\n" ^
                                    
                                    "add rbp, 8*(5 +" ^ (string_of_int (List.length params)) ^ "  )\n" ^
                                    "SHIFT_FRAME (4+"^ (string_of_int ((List.length params) + 1)) ^") , r11\n" ^
                                    
                                    "mov rax, r11\n" ^
                                    "mov rdx, 8\n" ^
                                    "mul rdx\n" ^
                                    "add rsp, rax\n" ^
                                    "mov rbp, rsp\n" ^ 
                                    ";------ end opt ------------- \n" ^
                                    " end_opt" ^ label ^ ":\n" ^
                                    " " ^ (makeAssmCode consts fvars (lam_i + 1) body) ^ "\n" ^
                                    " leave\n" ^
                                    " ret\n" ^
                                    "Lcont" ^ label ^ ":\n"
  
  | ApplicTP'(proc , args) -> let index = (string_of_int (getIndex app_label_i)) in
                              "push qword SOB_NIL_ADDRESS\n" ^
                              (List.fold_right (fun x acc-> ((acc ^ makeAssmCode consts fvars lam_i x) ^ "push rax \n")) args "") ^ 
                              "push " ^ (string_of_int (List.length args)) ^ " \n" ^
                              (makeAssmCode consts fvars lam_i proc) ^
                              "mov sil, [rax]\n" ^
                              "cmp sil, T_CLOSURE\n" ^
                              "je t_next" ^ index ^ "\n" ^
                              "mov rax, SOB_FALSE_ADDRESS\n" ^
                              "ret\n" ^
                              "t_next" ^ index ^ ":\n" ^
                              "push qword [rax + 1]\n" ^  (*push env*)
                              "push qword [rbp + 8 * 1]\n" ^
                              "mov r10, [rbp + 8*3]\n" ^
                              "add r10, 5\n" ^
                              
                              "mov r15, qword [rbp]\n" ^

                              "SHIFT_FRAME (5 + " ^ (string_of_int (List.length args))^ ") , r10\n" ^
                              "mov rdi , rax\n" ^
                              "mov rax, r10\n" ^
                              "mov rdx, 8\n" ^
                              "mul rdx\n" ^
                              "add rsp, rax\n" ^
                              "mov rbp, rsp\n" ^
                              "mov rax, rdi\n" ^
                              
                              "CLOSURE_CODE r11 , rax\n" ^
                              "mov rbp, r15\n" ^
                              "jmp r11\n" 
                              (* "add rsp, 8*1 \n" ^
                              "pop rbx\n" ^
                              "inc rbx\n" ^
                              "shl rbx, 3\n" ^
                              "add rsp, rbx\n"  *)
  | _ -> "AAAAAA" ;;   

  let rec p ls =
    match ls with
    | (x , _) :: cdr -> x ^ " " ^ p cdr
    | _ -> "";; 


module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = 
    let ls = [(Void , (0 , "MAKE_VOID")) ; (Sexpr(Nil) , (1 , "MAKE_NIL")) ; (Sexpr(Bool(false)) , (2 , "MAKE_BOOL(0)")) ; (Sexpr(Bool(true)) , (4 , "MAKE_BOOL(1)"))] in
      List.fold_left makeConstTable ls asts;;

  let make_fvars_tbl asts = 
    let ls = 
      [( "boolean?" , 0 )    ; ( "procedure?" , 1*8 )  ; ( "symbol?" , 2*8 ) ; 
              ( "string-set!" , 0 ) ; ( "symbol->string" , 0 ); ( "integer->char" , 0 ) ; ( "set-car!" , 0 ) ; ( "set-cdr!" , 0 )] in
              List.fold_left makeFreeVarTable ls asts;;
      
  let generate consts fvars e = makeAssmCode consts fvars 0 e;;
end;;

