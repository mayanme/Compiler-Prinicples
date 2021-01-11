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
  | Set' of var * expr'
  | Def' of var * expr'
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
  | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
  | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
  | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
  | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
  | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
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

  let rec get_index_of_element e list index = match list with
    | [] -> -1
    | first :: rest -> if e = first then index else get_index_of_element e rest (index + 1)
  


  (* args_list is a list of lists - ordered from most inner lambda to outer *)
let rec get_var_bound_or_free e args_list major_index = match args_list with
  | [] -> VarFree(e)
  | inner_lamba :: outer_lambdas ->
    let index_of_e = get_index_of_element e inner_lamba 0 in
    if (index_of_e != -1)
    then VarBound(e, major_index, index_of_e)
    else get_var_bound_or_free e outer_lambdas (major_index + 1)

  (* args_list is a list of lists - ordered from most inner lambda to outer *)
let get_var e args_list = match args_list with
  | [] -> VarFree(e)
  | params_list :: bound_lists ->
    let index_of_e = get_index_of_element e params_list 0 in
    if (index_of_e != -1)
    then VarParam(e, index_of_e)
    else get_var_bound_or_free e bound_lists 0
  

let get_all_but_last lst = match lst with
  | [] -> []
  | _ -> 
    let reversed = List.rev lst in
    match reversed with
    | car :: cdr -> List.rev cdr
    | _ -> []

let get_last lst = match lst with
  | _ -> 
    let reversed = List.rev lst in
    match reversed with
    | car :: cdr -> car
    | _ -> raise PC.X_no_match

let rec get_lexical_rec e args_list = match e with
  | Const(expr) -> Const'(expr)
  | Var(expr) -> Var'(get_var expr args_list)
  | If(test, dit, dif) -> If'(get_lexical_rec test args_list, get_lexical_rec dit args_list, get_lexical_rec dif args_list)
  | Seq(seq) -> Seq'(List.map (fun (expr) -> (get_lexical_rec expr args_list)) seq)
  | Set(Var(v), expr) -> Set'((get_var v args_list), (get_lexical_rec expr args_list))
  | Def(Var(v), expr) -> Def'((get_var v args_list), (get_lexical_rec expr args_list))
  | Or(seq) -> Or'(List.map (fun (expr) -> (get_lexical_rec expr args_list)) seq)
  | LambdaSimple(args, body) -> LambdaSimple'(args, get_lexical_rec body (args :: args_list))
  | LambdaOpt(args, vs, body) -> LambdaOpt'(args, vs, get_lexical_rec body ((List.append args [vs]) :: args_list))
  | Applic(expr, expr_list) -> Applic'(get_lexical_rec expr args_list, (List.map (fun (expr) -> (get_lexical_rec expr args_list)) expr_list))
  | _ -> raise PC.X_no_match

let rec get_tp_applic e in_tp = match e with
  | Const'(expr) -> Const'(expr)
  | Var'(expr) -> Var'(expr)
  | If'(test, dit, dif) -> If'(get_tp_applic test false, get_tp_applic dit in_tp, get_tp_applic dif in_tp)
  | Seq'(seq) -> 
      let all_but_last = get_all_but_last seq in
      let last = get_last seq in
      Seq'(List.append (List.map (fun (expr) -> (get_tp_applic expr false)) all_but_last) [(get_tp_applic last in_tp)])
  | Set'(var, expr) -> Set'(var, (get_tp_applic expr false))
  | Def'(var, expr) -> Def'(var, (get_tp_applic expr false))
  | Or'(seq) -> 
      let all_but_last = get_all_but_last seq in
      let last = get_last seq in
      Or'(List.append (List.map (fun (expr) -> (get_tp_applic expr false)) all_but_last) [(get_tp_applic last in_tp)])
  | LambdaSimple'(args, body) -> LambdaSimple'(args, get_tp_applic body true)
  | LambdaOpt'(args, vs, body) -> LambdaOpt'(args, vs, get_tp_applic body true)
  | Applic'(expr, expr_list) -> 
    if (in_tp)
    then ApplicTP'(get_tp_applic expr false, (List.map (fun (expr) -> (get_tp_applic expr false)) expr_list))
    else Applic'(get_tp_applic expr false, (List.map (fun (expr) -> (get_tp_applic expr false)) expr_list))
  | _ -> raise PC.X_no_match


(* ----------------------- BOXING --------------------------- *)

  let generate_setbox param minor = 
    Set'(VarParam(param, minor), Box'(VarParam(param, minor)))

  let add_boxes_to_body params body = match body with
    | Seq'(seq) -> 
        let gen_setbox_func = (fun param -> generate_setbox param (get_index_of_element param params 0)) in
        Seq'((List.map gen_setbox_func params) @ seq)
    | _ -> 
        let gen_setbox_func = (fun param -> generate_setbox param (get_index_of_element param params 0)) in
        Seq'((List.map gen_setbox_func params) @ [body])

  let rec set_all_boxes e = match e with
  | Var'(var) -> (match var with
              | VarParam(_) | VarBound(_) -> BoxGet'(var)
              | VarFree(_) -> Var'(var))
  | Set'(var, exp) -> (match var with
                      | VarParam(_) | VarBound(_) -> BoxSet'(var, set_all_boxes exp)
                      | VarFree(_) -> Set'(var, set_all_boxes exp))
  | If'(test, dit, dif) -> If'(set_all_boxes test, set_all_boxes dit, set_all_boxes dif)
  | Def'(var, exp) -> Def'(var, set_all_boxes exp)
  | Seq'(seq) -> Seq'(List.map set_all_boxes seq)
  | Or'(seq) -> Or'(List.map set_all_boxes seq)
  | Applic'(proc, args) -> Applic'(set_all_boxes proc, List.map set_all_boxes args)
  | ApplicTP'(proc ,args) -> ApplicTP'(set_all_boxes proc, List.map set_all_boxes args)
  | LambdaSimple'(params, body) -> 
      let body_with_boxes = set_all_boxes body in  
      LambdaSimple'(params, add_boxes_to_body params body_with_boxes)
  | LambdaOpt'(parmas, opt, body) -> 
      let body_with_boxes = set_all_boxes body in  
      LambdaOpt'(parmas, opt, add_boxes_to_body (parmas @ [opt]) body_with_boxes) 
  | _ -> e

(* ---------------------------------------END OF BOXING --------------------------------------------- *)

let annotate_lexical_addresses e = get_lexical_rec e [];;

let annotate_tail_calls e = get_tp_applic e false;;

let box_set e = set_all_boxes e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)


