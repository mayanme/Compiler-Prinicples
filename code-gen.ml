#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

  let primitive_names =
    [ 
      (* Type queries  *)
      "boolean?"; "flonum?"; "rational?";
      "pair?"; "null?"; "char?"; "string?";
      "procedure?"; "symbol?";
      (* String procedures *)
      "string-length"; "string-ref"; "string-set!";
      "make-string"; "symbol->string";
      (* Type conversions *)
      "char->integer"; "integer->char"; "exact->inexact";
      (* Identity test *)
      "eq?";
      (* Arithmetic ops *)
      "+"; "*"; "/"; "="; "<";
      (* Additional rational numebr ops *)
      "numerator"; "denominator"; "gcd";
      (* you can add yours here *)
      "car"; "cdr"; "set-car!"; "set-cdr!"; "cons"; "apply"
    ]
  
  (* Collect all sexprs from ONE ast *)
  let rec collect_sexprs ast = match ast with
  | Const'(sexpr) -> [sexpr]
	| If'(test,dit,dif) -> (collect_sexprs test) @ (collect_sexprs dit) @ (collect_sexprs dif)
  | Def'(_,expr) -> (collect_sexprs expr)
  | Set'(_,expr) -> (collect_sexprs expr)
  | BoxSet'(_,expr) -> (collect_sexprs expr)
  | Or'(expr_list) -> (List.flatten (List.map collect_sexprs expr_list))
  | Seq'(expr_list) -> (List.flatten (List.map collect_sexprs expr_list))
  | LambdaSimple'(_,body) -> (collect_sexprs body)
  | LambdaOpt'(_,_,body) -> (collect_sexprs body)
  | Applic'(expr, expr_list) -> (collect_sexprs expr) @ (List.flatten (List.map collect_sexprs expr_list))
  | ApplicTP'(expr, expr_list) -> (collect_sexprs expr) @ (List.flatten (List.map collect_sexprs expr_list))
	| _ -> []

  (* Remove duplicates from list of sexprs *)
  let remove_duplicates sexpr_list =
    let accumulate_func = (fun acc_list sexpr -> if (List.mem sexpr acc_list) then acc_list else acc_list @ [sexpr]) in
    (List.fold_left accumulate_func [] sexpr_list)

  (* extends ONE const into all sub-constants - returns a list of all sub-constants in topological order *)
  (* make sure to return the constant itself at the end of the list - very important in case constant doesnt have subs *)
  let rec extend_subconstants const = match const with
	| Sexpr(Symbol(s)) -> Sexpr(String(s)) :: [const]
	| Sexpr(Pair(car,cdr)) -> (extend_subconstants (Sexpr(car))) @ (extend_subconstants (Sexpr(cdr))) @ [const]
	| _ -> [const]

  let get_const_address lst c =
    let tuple = (List.find (fun (const,(_,_)) ->  const = c) lst) in (* maybe change this to use sexpr_eq *)
    let address = (fun (_,(addr,_)) -> addr) tuple in
    "const_tbl+" ^ (string_of_int address)

  let string_to_ascii_list str =
    let chars = string_to_list str in
    let asciis = List.map Char.code chars in
    let ascii_strs = List.map (Printf.sprintf "%d") asciis in
    String.concat ", " ascii_strs

  (* Generate tuples for all types of consts, increment address everytime and catenate result to END OF tuple_list *)
  let make_const_tuple (address, tuple_list) const = match const with
  | Void -> (address + 1,tuple_list @ [(const,(address,"MAKE_VOID"))])
  | Sexpr(Nil) -> (address + 1,tuple_list @ [(const,(address,"MAKE_NIL"))])
  | Sexpr(Bool true) -> (address + 2,tuple_list @ [(const,(address,"MAKE_BOOL(1)"))])
  | Sexpr(Bool false) -> (address + 2,tuple_list @ [(const,(address,"MAKE_BOOL(0)"))])
  | Sexpr(Number(Fraction (n,d))) -> (address + 17, tuple_list @ [(const,(address,String.concat "" ["MAKE_LITERAL_RATIONAL(";(string_of_int n);",";(string_of_int d);")"]))])
  | Sexpr(Number(Float n)) -> (address + 9, tuple_list @ [(const,(address,String.concat "" ["MAKE_LITERAL_FLOAT(";(string_of_float n);")"]))])
  | Sexpr(Char ch) -> (address + 2, tuple_list @ [(const,(address,String.concat "" ["MAKE_LITERAL_CHAR(";(string_of_int(int_of_char ch));")"]))])
  | Sexpr(String(s)) -> (address + 9 + (String.length s), tuple_list @ [(const,(address, "MAKE_LITERAL_STRING " ^ (string_to_ascii_list s)))])
  | Sexpr(Symbol s) ->
    let make_symbol = String.concat "" ["MAKE_LITERAL_SYMBOL(";(get_const_address tuple_list (Sexpr(String s)));")"] in
      (address + 9, tuple_list @ [(const,(address,make_symbol))])
  | Sexpr(Pair(car,cdr)) ->
    let make_pair = String.concat "" ["MAKE_LITERAL_PAIR("; (get_const_address tuple_list (Sexpr car)); ", ";(get_const_address tuple_list (Sexpr cdr));")"] in
      (address + 17, tuple_list @ [(const, (address, make_pair))])
  
  let make_consts_tbl asts =
    let sexpr_list = (List.flatten (List.map collect_sexprs asts)) in
    let dups_removed = remove_duplicates ([Void; Sexpr Nil; Sexpr (Bool false); Sexpr (Bool true)] @ sexpr_list) in (* to make sure these sexpr are included always in the table *) 
    let subconst_extended = (List.fold_left (fun acc_list const -> acc_list @ (extend_subconstants const)) [] dups_removed) in
    let dups_removed_2 = remove_duplicates subconst_extended in
    let (adresses, final_tuple_list) = List.fold_left make_const_tuple (0, []) dups_removed_2 in
    final_tuple_list

  (* Collect all strings of free variables from ONE ast *)
  let rec collect_fvars_strings ast = match ast with
  | Var'(VarFree(s)) -> [s]  (* In the end - try to remove this and see if it's necessary *)
  | Def'(VarFree(s),expr) -> [s] @ (collect_fvars_strings expr)
  | If'(test,dit,dif) -> (collect_fvars_strings test) @ (collect_fvars_strings dit) @ (collect_fvars_strings dif)
  | Set'(_,expr) -> (collect_fvars_strings expr)
  | BoxSet'(_,expr) -> (collect_fvars_strings expr)
  | Or'(expr_list) -> (List.flatten (List.map collect_fvars_strings expr_list))
  | Seq'(expr_list) -> (List.flatten (List.map collect_fvars_strings expr_list))
  | LambdaSimple'(_,body) -> (collect_fvars_strings body)
  | LambdaOpt'(_,_,body) -> (collect_fvars_strings body)
  | Applic'(expr, expr_list) -> (collect_fvars_strings expr) @ (List.flatten (List.map collect_fvars_strings expr_list))
  | ApplicTP'(expr, expr_list) -> (collect_fvars_strings expr) @ (List.flatten (List.map collect_fvars_strings expr_list))
  | _ -> []

  let make_fvars_tbl asts =
    let fvar_strings = (List.flatten (List.map collect_fvars_strings asts)) in
    let dups_removed = primitive_names @ (remove_duplicates fvar_strings) in
    let make_fvar_pair = (fun (index, fvar_list) fvar_string -> (index + 8, fvar_list @ [(fvar_string, index)] )) in
    let (index, final_fvar_list) = (List.fold_left make_fvar_pair (0, []) dups_removed) in
    final_fvar_list
  
  (* Returns label of fvar_str in fvar_table *)
  let get_fvar_label fvar_str fvar_table =
    let (var, label) = (List.find (fun (var, label) -> var = fvar_str) fvar_table) in
    "fvar_tbl+" ^ (string_of_int label)


  let counter = ref 0
  let print = Printf.sprintf;;
  
  let rec code_gen consts fvars e env_size = match e with
  | Const'(const) -> "mov rax, " ^ (get_const_address consts const)
  | Var'(VarParam(_, minor)) -> "mov rax, qword [rbp + 8*(4+" ^ (string_of_int minor) ^ ")]"
  | Set'(VarParam(_, minor), value) -> 
      let gen_value = code_gen consts fvars value env_size in
      "" ^ gen_value ^ "\n
      mov qword [rbp + 8*(4+" ^ (string_of_int minor) ^ ")], rax\n 
      mov rax, SOB_VOID_ADDRESS"
  | Var'(VarBound(_, major, minor)) ->
      "mov rax, qword [rbp + 8*2]\n
      mov rax, qword [rax + 8*" ^ (string_of_int major) ^ "]\n
      mov rax, qword [rax + 8*" ^ (string_of_int minor) ^ "]"
  | Set'(VarBound(_, major, minor), value) ->
      let gen_value = code_gen consts fvars value env_size in
      "" ^ gen_value ^ "\n
      mov rbx, qword [rbp + 8*2]\n
      mov rbx, qword [rbx + 8*" ^ (string_of_int major) ^ "]\n
      mov qword [rbx + 8*" ^ (string_of_int minor) ^ "], rax\n
      mov rax, SOB_VOID_ADDRESS"
  | Var'(VarFree(v)) ->
      let var_label = get_fvar_label v fvars in
      "mov rax, qword [" ^ var_label ^ "]"
  | Set'(VarFree(v), value) ->
      let var_label = get_fvar_label v fvars in
      let gen_value = code_gen consts fvars value env_size in
      "" ^ gen_value ^ "\n
      mov qword [" ^ var_label ^ "], rax\n
      mov rax, SOB_VOID_ADDRESS"
  | Def'(VarFree(v), value) ->
      let var_label = get_fvar_label v fvars in
      let gen_value = code_gen consts fvars value env_size in
      ";***********Def: " ^ v ^ "**********:\n
      " ^ gen_value ^ "\n
      mov qword [" ^ var_label ^ "], rax\n
      mov rax, SOB_VOID_ADDRESS"
  | Seq'(seq) ->
      (String.concat "\n" (List.map (fun value -> (code_gen consts fvars value env_size)) seq))
  | Or'(seq) ->
      counter := !counter + 1;
      let counter_string = (string_of_int !counter) in
      let values_generated = (List.map (fun value -> (code_gen consts fvars value env_size)) seq) in
      let string_to_concat = 
        "\ncmp rax, SOB_FALSE_ADDRESS\n 
       jne Lexit" ^ counter_string ^ "\n" in
      (String.concat string_to_concat values_generated) 
       ^ "\nLexit" ^ counter_string ^ ":"
  | If'(test, dit, dif) ->
      counter := !counter + 1;
      let counter_string = (string_of_int !counter) in
      let gen_test = code_gen consts fvars test env_size in
      let gen_dit = code_gen consts fvars dit env_size in
      let gen_dif = code_gen consts fvars dif env_size in
      "" ^ gen_test ^ "
      cmp rax, SOB_FALSE_ADDRESS
      je Lelse" ^ counter_string ^ "\n"
      ^ gen_dit ^ "
      jmp Lexit" ^ counter_string ^ "
      Lelse" ^ counter_string ^ ":\n"
      ^ gen_dif ^ "
      Lexit" ^ counter_string ^ ":"
  | Box'(v) ->
      let gen_var = (code_gen consts fvars (Var'(v)) env_size) in
      "" ^ gen_var ^ "\n
      MALLOC rbx, WORD_SIZE
      mov qword [rbx], rax
      mov rax, rbx"
  | BoxGet'(v) -> 
      let gen_var = (code_gen consts fvars (Var'(v)) env_size) in
      "" ^ gen_var ^ "\n
      mov rax, qword [rax]"
  | BoxSet'(v, value) ->
      let gen_var = (code_gen consts fvars (Var'(v)) env_size) in
      let gen_value = code_gen consts fvars value env_size in
      "" ^ gen_value ^ "\n
      push rax\n"
      ^ gen_var ^ "\n
      pop qword [rax]\n
      mov rax, SOB_VOID_ADDRESS"
  | LambdaSimple'(params, body) -> 
      counter := !counter + 1;
      (gen_lambda_simple consts fvars params body env_size) 
  | LambdaOpt'(params, opt, body) -> 
      counter := !counter + 1;
      (gen_lambda_opt consts fvars params body env_size)
  | Applic'(proc, args) ->
      counter := !counter + 1;
      (gen_applic consts fvars proc args env_size)  
  | ApplicTP'(proc, args) -> 
      counter := !counter + 1;
      (gen_applic_tp consts fvars proc args env_size)
  | _ -> ""

  and gen_applic consts fvars proc args env_size =
    let counter_string = (string_of_int !counter) in
    let evaluated_reversed_args = (List.rev (List.map (fun value -> (code_gen consts fvars value env_size)) args)) in
    let push_all_args = (String.concat "" (List.map (fun argument -> argument ^ "\npush rax\n") evaluated_reversed_args)) in
    let n = (List.length args) in
    let evaluated_proc = (code_gen consts fvars proc env_size) in
    ";********APPLIC***************\n
    push SOB_NIL_ADDRESS\n"
    ^ push_all_args ^ "
    push " ^ (string_of_int n) ^ "\n" ^
    evaluated_proc ^ "\n
    TYPE rbx, rax
    cmp rbx, T_CLOSURE
    je LContinueApplic" ^ counter_string ^ "
    mov rax, 60
    syscall
    LContinueApplic" ^ counter_string ^ ":
    CLOSURE_ENV rbx, rax
    push rbx
    CLOSURE_CODE rbx, rax
    call rbx
    add rsp, 8    ; pop env
    pop rbx       ; pop number of arguments to rbx (can't be sure we returned with same number)
    shl rbx, 3    ; rbx = rbx * 8
    add rsp, rbx  ; pop arguments
    add rsp, 8    ; pop SOB_NIL_ADDRESS pushed in the beginning
    no_magic_on_stack" ^ counter_string ^ ":
    ;********END OF APPLIC***************"

    
  and gen_lambda_simple consts fvars params body env_size =
    let counter_string = (string_of_int !counter) in
    let ext_env_size = env_size + 1 in
    let gen_body = (code_gen consts fvars body ext_env_size) in
    ";********LAMBDA SIMPLE***************\n
    MALLOC rdi, " ^ (string_of_int ext_env_size) ^ "* WORD_SIZE         ; rdi = array for the extended env
    mov rbx, rdi                                                         ; backup address of beginning of array for later
    add rdi, WORD_SIZE                                                   ; move from array[0] to array[1]. rdi = destination
    mov rsi, qword [rbp + 2*WORD_SIZE]                                   ; rsi = source = env, it now points to env[0] (maybe rbp should be rsp?)
    mov rcx, " ^ (string_of_int env_size) ^ "                            ; number of iterations in the loop (size of old env array)
    
    copy_pointers_loop" ^ counter_string ^ ":
    cmp rcx, 0
    je end_of_loop" ^ counter_string ^ "
    mov r8, qword [rsi]
    mov qword [rdi], r8
    add rsi, WORD_SIZE
    add rdi, WORD_SIZE
    dec rcx
    jmp copy_pointers_loop" ^ counter_string ^ "
    
    end_of_loop" ^ counter_string ^ ":
    mov rdi, rbx                                                         ; rdi = back to ext env array[0]
    mov rsi, NUM_OF_ARGS                                                 ; rsi = number of arguments of the calling lambda
    inc rsi                                                              ; rsi ++ so we copy MAGIC as well
    shl rsi, 3                                                              ; rsi = rsi * WORD_SIZE
    MALLOC rbx, rsi                                                      ; rbx = array for the parameters of the calling lambda
    mov qword [rdi], rbx                                                 ; rdi[0] = rbx
    mov rcx, NUM_OF_ARGS                                                 ; rcx = number of arguments of the calling lambda (copy from 0 to n so we copy magic as well)
    inc rcx
    
    copy_parameters_loop" ^ counter_string ^ ":
    cmp rcx, -1
    je end_of_params_loop" ^ counter_string ^ "
    mov r8, PVAR(rcx)                                                    ; r8 = copy parameter from stack
    mov qword [rbx + rcx * WORD_SIZE], r8                                ; move parameter to the parameters array
    dec rcx
    jmp copy_parameters_loop" ^ counter_string ^ "
    
    end_of_params_loop" ^ counter_string ^ ":
    MAKE_CLOSURE(rax, rdi, Lcode" ^ counter_string ^ ")                  ; generate closure. rax = result closure, rdi = env, Lcode = lambda body code.
    jmp Lcont" ^ counter_string ^ "
    Lcode" ^ counter_string ^ ":                                         ; lambda body code
    push rbp,
    mov rbp, rsp
    " ^ gen_body ^ "
    leave
    ret
    Lcont" ^ counter_string ^ ":
    ;********END OF LAMBDA SIMPLE***************"

  and gen_lambda_opt consts fvars params body env_size =
    let counter_string = (string_of_int !counter) in
    let ext_env_size = env_size + 1 in
    let required_num_of_params = List.length params in
    let expected_num_of_params = (required_num_of_params + 1) in
    let gen_body = (code_gen consts fvars body ext_env_size) in
    ";********LAMBDA OPT***************\n
    MALLOC rdi, " ^ (string_of_int ext_env_size) ^ "* WORD_SIZE         ; rdi = array for the extended env
    mov rbx, rdi                                                         ; backup address of beginning of array for later
    add rdi, WORD_SIZE                                                   ; move from array[0] to array[1]. rdi = destination
    mov rsi, qword [rbp + 2*WORD_SIZE]                                   ; rsi = source = env, it now points to env[0] (maybe rbp should be rsp?)
    mov rcx, " ^ (string_of_int env_size) ^ "                            ; number of iterations in the loop (size of old env array)
    
    copy_pointers_loop" ^ counter_string ^ ":
    cmp rcx, 0
    je end_of_loop" ^ counter_string ^ "
    mov r8, qword [rsi]
    mov qword [rdi], r8
    add rsi, WORD_SIZE
    add rdi, WORD_SIZE
    dec rcx
    jmp copy_pointers_loop" ^ counter_string ^ "
    
    end_of_loop" ^ counter_string ^ ":
    mov rdi, rbx                                                         ; rdi = back to ext env array[0]
    mov rsi, NUM_OF_ARGS                                                 ; rsi = number of arguments of the calling lambda
    inc rsi
    shl rsi, 3                                                              ; rsi = rsi * WORD_SIZE
    MALLOC rbx, rsi                                                      ; rbx = array for the parameters of the calling lambda
    mov qword [rdi], rbx                                                 ; rdi[0] = rbx
    mov rcx, NUM_OF_ARGS                                                 ; rcx = number of arguments of the calling lambda (copy from 0 to n so we copy magic as well)
    inc rcx
    
    copy_parameters_loop" ^ counter_string ^ ":
    cmp rcx, -1
    je end_of_params_loop" ^ counter_string ^ "
    mov r8, PVAR(rcx)                                                    ; r8 = copy parameter from stack
    mov qword [rbx + rcx * WORD_SIZE], r8                                ; move parameter to the parameters array
    dec rcx
    jmp copy_parameters_loop" ^ counter_string ^ "
    
    end_of_params_loop" ^ counter_string ^ ":
    MAKE_CLOSURE(rax, rdi, Lcode" ^ counter_string ^ ")                  ; generate closure. rax = result closure, rdi = env, Lcode = lambda body code.
    jmp Lcont" ^ counter_string ^ "
    
    Lcode" ^ counter_string ^ ":                                         ; lambda body code

    ; **** TO DO ****
    ; 1. make nested pair list of optional arguments
    ; 2. put that list under magic
    ; 3. move up everything on the stack (override all the opt args we copied to the list)
    ; 4. change NUM_OF_ARGS to be expected_num_of_params
    
    mov rax, NUM_OF_ARGS_WITH_RSP
    sub rax, " ^ (string_of_int required_num_of_params) ^ "             ; rax = number of args to put in the opt list
    cmp rax, 0                                                          ; base case - only required args, no need to adjust
    je dont_do_anything" ^ counter_string ^ "
    mov rbx, NUM_OF_ARGS_WITH_RSP                                       ; rbx = n
    add rbx, 3                                                          ; rbx = n + 3
    shl rbx, 3
    add rbx, rsp                                                       ; rbx = rsp +(3+n)*WORD_SIZE -> rbx = address of MAGIC (Nil)
    mov rcx, SOB_NIL_ADDRESS                                            ; rcx = Nil, during the loop rcx will hold the address of the last pair created

    make_optional_args_list_loop" ^ counter_string ^ ":
    cmp rax, 0                                                          ; check if reached zero - we can stop the loop, this also handles base case of only required args
    je adjust_stack_cont" ^ counter_string ^ "                          ; if it is - we finished adjusting, continue to execution of lambda
    sub rbx, WORD_SIZE                                                  ; continue to next argument on the stack
    mov rdi, qword [rbx]                                                ; rdi = argument to insert to the list
    MAKE_PAIR(rsi, rdi, rcx)                                            ; rsi = address of the new pair
    mov rcx, rsi                                                        ; rcx = rsi, because rcx is supposed to hold address of last pair created
    dec rax
    jmp make_optional_args_list_loop" ^ counter_string ^ "
    
    adjust_stack_cont" ^ counter_string ^ ":
    mov rax, NUM_OF_ARGS_WITH_RSP
    dec rax
    mov PVAR_WITH_RSP(rax), rcx                                         ; move the address of the opt list to the argument under MAGIC (last argument)
    dec rax                                                                ; rax = index of argument one under opt list
    add rax, 3
    shl rax, 3
    add rax, rsp                                                       ; rax = rsp + (rax+3) * WORD_SIZE , copy to rax - address of one argument under the opt list
    mov rbx, " ^ (string_of_int required_num_of_params) ^ "             
    dec rbx                                                             ; if there are n required, we want argument n-1 (index starts at 0)
    add rbx, 3
    shl rbx, 3
    add rbx, rsp                                                         ; rbx = rsp + (rbx+3) * WORD_SIZE , copy from rbx - address of last required argument                                 
    cmp rax, rbx
    je change_num_of_args" ^ counter_string ^ "                         ; if they are equal it means there was one extra argument and we don't need to adjust
    mov rcx, " ^ (string_of_int required_num_of_params) ^ "             ; rcx = loop itertations, move up all required args
    add rcx, 3                                                          ; rcx = rcx + 3 so we move up num_of_args, env, and ret

    move_up_args_loop" ^ counter_string ^":
    cmp rcx, 0
    je update_rsp" ^ counter_string ^ "
    mov r8, qword [rbx]
    mov qword [rax], r8
    sub rax, WORD_SIZE
    sub rbx, WORD_SIZE
    dec rcx
    jmp move_up_args_loop" ^ counter_string ^"
    
    update_rsp" ^ counter_string ^ ":
    add rax, WORD_SIZE
    mov rsp, rax

    change_num_of_args" ^ counter_string ^ ":
    mov NUM_OF_ARGS_WITH_RSP, " ^ (string_of_int expected_num_of_params) ^ "
    
    dont_do_anything" ^ counter_string ^ ":
    push rbp,
    mov rbp, rsp
    " ^ gen_body ^ "
    leave
    ret
    Lcont" ^ counter_string ^ ":
    ;********END OF LAMBDA OPT***************"

  and gen_applic_tp consts fvars proc args env_size =
    let counter_string = (string_of_int !counter) in
    let evaluated_reversed_args = (List.rev (List.map (fun value -> (code_gen consts fvars value env_size)) args)) in
    let push_all_args = (String.concat "" (List.map (fun argument -> argument ^ "\npush rax\n") evaluated_reversed_args)) in
    let n = (List.length args) in
    let size_of_new_frame = n+4 in
    let evaluated_proc = (code_gen consts fvars proc env_size) in
    ";********APPLIC TP***************\n
    testC" ^ counter_string ^ ":
    push SOB_NIL_ADDRESS\n
    testB" ^ counter_string ^ ":\n"
    ^ push_all_args ^ "
    testA" ^ counter_string ^ ":
    push " ^ (string_of_int n) ^ "\n" ^
    evaluated_proc ^ "\n
    TYPE rbx, rax
    cmp rbx, T_CLOSURE
    je LContinueApplic" ^ counter_string ^ "
    mov rax, 60
    syscall
    LContinueApplic" ^ counter_string ^ ":
    CLOSURE_ENV rbx, rax
    push rbx
    CLOSURE_CODE rbx, rax

    push qword [rbp + WORD_SIZE]                          ; rbp is still old rbp (of the calling lambda) and rbp+8 is the old ret address
    mov r12, qword [rbp]                                      ; [rbp] is rbp in f -> the stack frame pointer we will return to when we return from h
    
    mov rcx, " ^ (string_of_int size_of_new_frame) ^ "    ; rcx = size of new frame
    mov rax, NUM_OF_ARGS 
    add rax, 5                                            ; rax = size of old frame
    mov r11, rax                                            ; r11 = back up for old frame size
    mov rsi, 1                                             ; rsi counts from 1 to rcx = new frame size

    copy_stack_applictp_loop" ^ counter_string ^ ":         ; this loop will run rcx times = new frame size times
    cmp rcx, 0
    je end_of_copy_stack_applictp_loop" ^ counter_string ^ "
    dec rax
    mov r9, rsi
    neg r9
    mov rdi, qword [rbp + r9*WORD_SIZE]
    mov qword [rbp + rax*WORD_SIZE], rdi
    inc rsi
    dec rcx
    jmp copy_stack_applictp_loop" ^ counter_string ^ "
    end_of_copy_stack_applictp_loop" ^ counter_string ^ ":
    
    mov rax, r11                ; restore size of old frame
    shl rax, 3
    add rsp, rax
    
    mov rbp, r12
    jmp rbx                       ; assumes rbx still holds the code of the closure
    ;********END OF APPLIC TP***************"

  let generate consts fvars e = code_gen consts fvars e 0;;
end;;