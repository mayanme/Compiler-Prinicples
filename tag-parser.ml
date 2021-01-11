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
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

(* TAG PARSER *)

(* Takes a nested Pair(String) list and returns a regular ocaml string list *)
let rec parse_lambda_arguments args_list =
  match args_list with
  | Nil -> []
  | Pair(Symbol(car), cdr) -> car :: (parse_lambda_arguments cdr)
  | _ -> []

(* Takes an improper Symbol Pair list (list that doesn't end with Nil) and returns the string inside last Symbol *)
let rec get_last_from_improper_list args_list = 
  match args_list with
  | Pair(car, cdr) -> get_last_from_improper_list cdr
  | Symbol(arg_name) -> arg_name
  | _ -> raise PC.X_no_match

(* Takes a nested Pair list of sexprs and returns a regular ocaml list of the same sexprs (will be parsed later to Expr type by the tag parser) *)
let rec flatten_list args_list = match args_list with
  | Nil -> []
  | Pair(car, cdr) -> car :: (flatten_list cdr)
  | _ -> [args_list]

(* Takes nested Pair list of (name sexpr) function arguments of let and returns nested pair list of the names *)
let rec get_lambda_args_names_as_symbols args_list = match args_list with
  | Nil -> Nil
  | Pair(Pair(Symbol(name), Pair(sexpr, Nil)), rest) -> Pair(Symbol(name), get_lambda_args_names_as_symbols rest)
  | _ -> raise PC.X_no_match

(* Takes nested Pair list of (name sexpr) function arguments of let and returns nested pair list of the sexprs *)
let rec get_lambda_args_values_as_sexpr args_list = match args_list with
  | Nil -> Nil
  | Pair(Pair(Symbol(name), Pair(sexpr, Nil)), rest) -> Pair(sexpr, get_lambda_args_values_as_sexpr rest)
  | _ -> raise PC.X_no_match

let flatten_nested_seq expr = match expr with (* if expr is of Seq type - return list of its content. Else - return it. *)
  | Seq(seq_list) -> seq_list
  | _ -> [expr]

  (*  Input: nested Pair List of ((f1 Exp1) ..... (fn Exprn)) 
      Output: nested Pair List of ((f1 'whatever) ..... (fn 'whatever))*)

let rec make_letrec_whatev_list paired_list = match paired_list with
  | Nil -> Nil
  | Pair(Pair( f_n,expr_n), rest) -> 
      let whatev_quote = Pair(Symbol("quote"), Pair(Symbol ("whatever"), Nil)) in
      Pair( Pair(f_n, Pair(whatev_quote, Nil)), make_letrec_whatev_list rest)
  | _ -> raise PC.X_no_match

let rec make_letrec_Expr_list paired_list exprs = match paired_list with
  | Nil -> let empty_let_expr = Pair(Symbol("let"),Pair(Nil,exprs)) in
      Pair(empty_let_expr,Nil)
  | Pair(Pair( f_n,expr_n), rest) -> 
      let set_expr = Pair(Symbol("set!"),Pair( f_n,expr_n)) in
      Pair( set_expr, make_letrec_Expr_list rest exprs)
  | _ -> raise PC.X_no_match

let rec append paired_list_1 paired_list_2 = match paired_list_1 with
| Nil -> paired_list_2
| Pair(car,cdr) -> Pair(car, (append cdr paired_list_2))
| _ -> raise PC.X_no_match

let rec convert_qouasiqoute exprs = match exprs with
  (* parsing inproper list *)
  |  Pair(Symbol("unquote"),Pair(sexpr1,Nil)) -> Pair(sexpr1 , Nil)
  |  Pair(Symbol("unquote-splicing"),Pair(sexpr2,Nil)) -> Pair(sexpr2,Nil)
  (* parsing proper list  *)
  | Pair(car, cdr) -> begin match car with
    | Pair(Symbol("unquote"),Pair(sexpr1,Nil)) -> Pair(Pair(Symbol("cons"),Pair(sexpr1 , (convert_qouasiqoute cdr))),Nil)
    | Pair(Symbol("unquote-splicing"),Pair(sexpr2,Nil)) -> Pair(Pair(Symbol("append"),Pair(sexpr2,(convert_qouasiqoute cdr))),Nil) 
    | _ -> Pair(Pair(Symbol("cons"),Pair(Pair(Symbol("quasiquote"),Pair(car,Nil)), (convert_qouasiqoute cdr))),Nil)
    end
  | _ -> Pair(Pair(Symbol("quote"),Pair(exprs,Nil)),Nil)

let rec element_exist_in_list element lst =
  match lst with
  | car::cdr -> element = car || element_exist_in_list element cdr
  | [] -> false

let rec dupExist lst1 lst2 =
  match lst1 with
  | car::cdr -> (element_exist_in_list car lst2) || dupExist cdr lst2
  | [] -> false

let rec rename_args_for_pset list_of_names counter = match list_of_names with
| Nil -> Nil
| Pair(Symbol(name), rest) -> Pair(Symbol(String.concat "_" [name; (string_of_int counter)]), rename_args_for_pset rest (counter+1))
| _ -> raise PC.X_no_match

let rec name_lambda_args_unique nested_list_of_names original_list =
  let renamed_args = rename_args_for_pset nested_list_of_names 1 in
  let list_of_names = parse_lambda_arguments renamed_args in (* returns ocaml list of the strings of the names *)
  if (dupExist list_of_names original_list) then (name_lambda_args_unique renamed_args original_list) else renamed_args

let rec make_sets_sequence sets_arg_names lambda_arg_names = match sets_arg_names with
| Nil -> Nil
| Pair(name1, rest1) -> (match lambda_arg_names with
                        | Nil -> Nil
                        | Pair(name2, rest2) ->
                            Pair(Pair(Symbol("set!"), Pair(name1, Pair(name2, Nil))), make_sets_sequence rest1 rest2)
                        | _ -> raise PC.X_no_match)
| _ -> raise PC.X_no_match

(* Returns true if list ends with Nil. Returns false also if nested_list is not a list *)
let rec is_proper_list nested_list = match nested_list with
| Pair(car, cdr) -> is_proper_list cdr
| Nil -> true
| _ -> false

let is_symbol sym = match sym with
| Symbol(_) -> true
| _ -> false

let get_symbol_name sym = match sym with
| Symbol(sym_name) -> sym_name
| _ -> raise PC.X_no_match

let rec const_parser sexpr = match sexpr with
| Bool(_) | Char(_) | Number(_) | String(_) -> Const(Sexpr(sexpr))
| Pair(Symbol("quote"),Pair(sexpr2, Nil)) -> Const(Sexpr(sexpr2))
| _ -> raise PC.X_no_match

and var_parser sexpr = match sexpr with
| Symbol(sym) ->
  if (List.mem sym reserved_word_list) then raise PC.X_no_match else Var(sym)
| _ -> raise PC.X_no_match

and if_parser sexpr = match sexpr with
| Pair(Symbol("if"), Pair(test, Pair(dit , Pair(dif, Nil)))) -> 
    If(tag_parser test, tag_parser dit, tag_parser dif)
| Pair(Symbol("if"), Pair(test, Pair(dit , Nil))) ->
    If(tag_parser test, tag_parser dit, Const(Void))
| _ -> raise PC.X_no_match

and lambda_parser sexpr = match sexpr with
| Pair(Symbol("lambda"), Pair(args, body_sequence)) ->
    if is_proper_list args then
      let parsed_args = parse_lambda_arguments args in
      LambdaSimple(parsed_args, implicit_sequence_parser body_sequence)
    else
      if is_symbol args then
      let arg_name = get_symbol_name args in
      LambdaOpt([], arg_name, implicit_sequence_parser body_sequence)
      else
      let mandatory_args = parse_lambda_arguments args in
      let optional_arg = get_last_from_improper_list args in
      LambdaOpt(mandatory_args, optional_arg, implicit_sequence_parser body_sequence) 
| _ -> raise PC.X_no_match

and application_parser sexpr = match sexpr with
| Pair(Pair(Symbol("lambda"), lambda_rest), func_args) ->
    let lambdaExpr = lambda_parser (Pair(Symbol("lambda"), lambda_rest)) in
    Applic(lambdaExpr, List.map tag_parser (flatten_list func_args))
| Pair(Symbol(func_name), Nil) ->
    if (List.mem func_name reserved_word_list) then raise PC.X_no_match else
    Applic(Var(func_name), [])
| Pair(Symbol(func_name), func_args) ->
    if (List.mem func_name reserved_word_list) then raise PC.X_no_match else
    Applic(Var(func_name), List.map tag_parser (flatten_list func_args))
| Pair(first, rest) ->
    Applic(tag_parser first, List.map tag_parser (flatten_list rest))
| _ -> raise PC.X_no_match

and disjunction_parser sexpr = match sexpr with
| Pair(Symbol("or"), Nil) -> Const(Sexpr(Bool false))
| Pair(Symbol("or"), Pair(expr, Nil)) -> tag_parser expr
| Pair(Symbol("or"), or_args_list) ->
    let flattened_or_args = flatten_list or_args_list in
    Or(List.map tag_parser flattened_or_args)
| _ -> raise PC.X_no_match

and definition_parser sexpr = match sexpr with
| Pair(Symbol("define"), Pair(Symbol(name), Pair(value, Nil))) ->
    if (List.mem name reserved_word_list) then raise PC.X_no_match else
    Def(Var(name), tag_parser value)
| _ -> raise PC.X_no_match

and assignment_parser sexpr = match sexpr with
| Pair(Symbol("set!"), Pair(Symbol(name), Pair(value, Nil))) ->
    Set(Var(name), tag_parser value)
| _ -> raise PC.X_no_match

and sequence_parser sexpr = match sexpr with
| Pair(Symbol("begin"), Nil) -> Const(Void)
| Pair(Symbol("begin"), Pair(value, Nil)) -> tag_parser value
| Pair(Symbol("begin"), begin_sequence) -> implicit_sequence_parser begin_sequence
| _ -> raise PC.X_no_match

and implicit_sequence_parser sexpr = match sexpr with
| Nil -> Const(Void)
| Pair(expr, Nil) -> tag_parser expr
| Pair(expr, rest) -> 
    let parsed_list = List.map tag_parser (flatten_list sexpr) in
    let flattened_sequences = List.map flatten_nested_seq parsed_list in
      Seq(List.flatten flattened_sequences)
| _ -> tag_parser sexpr

(* MACRO EXPANSIONS *)

and quasiquote_expansion sexpr = match sexpr with
  | Pair(Symbol("quasiquote"),Pair(car,Nil)) -> implicit_sequence_parser (convert_qouasiqoute car)
  | _ -> raise PC.X_no_match

and cond_expansion sexpr = match sexpr with
  | Pair(Symbol("cond"), ribs) ->
      tag_parser (expand_ribs ribs)
  | _ -> raise PC.X_no_match

and expand_ribs ribs = match ribs with
  | Nil -> Nil
  | Pair(Pair(Symbol("else"), rest), rest_ribs) -> Pair(Symbol("begin"), rest)  (* if else is last, rest_ribs is Nil. Anyway - ignore it *)
  | Pair(Pair(expr, Pair(Symbol("=>"), Pair(rest, Nil))), Nil) ->
          let value_binding = Pair(Symbol("value"), Pair(expr, Nil)) in
          let lambda_in_f = Pair(Symbol("lambda"), Pair(Nil, Pair(rest, Nil))) in
          let f_binding = Pair(Symbol("f"), Pair(lambda_in_f, Nil)) in
          let bindings_list = Pair(value_binding, Pair(f_binding, Nil)) in
          let applic_of_f_on_value = Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)) in
          let if_expression = Pair(Symbol("if"), Pair(Symbol("value"), Pair(applic_of_f_on_value, Nil))) in
            Pair(Symbol("let"), Pair(bindings_list, Pair(if_expression, Nil)))
  | Pair(Pair(expr, Pair(Symbol("=>"), exprf)), rest_ribs) ->
          let value_binding = Pair(Symbol("value"), Pair(expr, Nil)) in
          let lambda_in_f = Pair(Symbol("lambda"), Pair(Nil, exprf)) in
          let f_binding = Pair(Symbol("f"), Pair(lambda_in_f, Nil)) in
          let lambda_in_rest = Pair(Symbol("lambda"), Pair(Nil, Pair(expand_ribs rest_ribs, Nil))) in
          let rest_binding = Pair(Symbol("rest"), Pair(lambda_in_rest, Nil)) in
          let bindings_list = Pair(value_binding, Pair(f_binding, Pair(rest_binding, Nil))) in
          let applic_of_f_on_value = Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)) in
          let applic_of_rest = Pair(Symbol("rest"), Nil) in
          let if_expression = Pair(Symbol("if"), Pair(Symbol("value"), Pair(applic_of_f_on_value, Pair(applic_of_rest, Nil)))) in
            Pair(Symbol("let"), Pair(bindings_list, Pair(if_expression, Nil))) 
  | Pair(Pair(test,rest), Nil) ->
          let then_clause = Pair(Symbol("begin"), rest) in
            Pair(Symbol("if"), Pair(test, Pair(then_clause, Nil)))
  | Pair(Pair(test, rest), rest_ribs) -> 
          let then_clause = Pair(Symbol("begin"), rest) in
          let else_clause = expand_ribs rest_ribs in
            Pair(Symbol("if"), Pair(test, Pair(then_clause, Pair(else_clause, Nil))))
  | _ -> raise PC.X_no_match

and let_expansion sexpr = match sexpr with
  | Pair(Symbol("let"), Pair(args, exprs)) -> 
      let args_names = get_lambda_args_names_as_symbols args in
      let lambda_sexpr = Pair(Symbol("lambda"), Pair(args_names, exprs)) in
      tag_parser (Pair(lambda_sexpr, get_lambda_args_values_as_sexpr args))
  | _ -> raise PC.X_no_match

and let_star_expansion sexpr = match sexpr with
  | Pair(Symbol("let*"), Pair(args, exprs)) -> 
      begin
      match args with
      | Nil | Pair(_,Nil) -> tag_parser (Pair(Symbol("let"), Pair(args, exprs)))
      | Pair(arg1, rest_args) -> 
          let next_let_star = Pair(Symbol("let*"), Pair(rest_args, exprs)) in
          tag_parser (Pair(Symbol("let"), Pair(Pair(arg1,Nil) ,Pair(next_let_star,Nil))))
      | _ -> raise PC.X_no_match
      end
  | _ -> raise PC.X_no_match

and letrec_expansion sexpr = match sexpr with
  | Pair(Symbol("letrec"), Pair(args, rest_exprs)) ->
      let letrec_args = make_letrec_whatev_list args in
      let letrec_set_exprs = make_letrec_Expr_list args rest_exprs in
      let letrec_expan = Pair(Symbol("let"),Pair(letrec_args, letrec_set_exprs)) in
        tag_parser (letrec_expan)
  | _ -> raise PC.X_no_match

and and_expansion sexpr = match sexpr with
  | Pair(Symbol("and"), Nil) -> tag_parser (Bool true)
  | Pair(Symbol("and"), Pair(expr, Nil)) -> tag_parser expr
  | Pair(Symbol("and"), Pair(expr1, rest)) -> 
      let and_with_rest = Pair(Symbol("and"), rest) in
      tag_parser ( Pair(Symbol("if"), Pair(expr1, Pair(and_with_rest, Pair((Bool false), Nil)))) )
  | _ -> raise PC.X_no_match

and mit_define_expansion sexpr = match sexpr with
  | Pair(Symbol("define"), Pair(Pair(func_name, func_args_names), func_body)) ->
      let lambda_sexpr = Pair(Symbol("lambda"), Pair(func_args_names, func_body)) in
      tag_parser (Pair(Symbol("define"), Pair(func_name, Pair(lambda_sexpr, Nil))))
  | _ -> raise PC.X_no_match

and pset_expansion sexpr = match sexpr with
 | Pair(Symbol("pset!"), sets) -> 
      let sets_arg_names = get_lambda_args_names_as_symbols sets in
      let original_list = parse_lambda_arguments sets_arg_names in (* original list of names for comparison of dups *)
      let lambda_arg_names = name_lambda_args_unique sets_arg_names original_list in
      let sexpr_values = get_lambda_args_values_as_sexpr sets in
      let set_begin_sequence = make_sets_sequence sets_arg_names lambda_arg_names in
      let lambda_with_sets = Pair(Symbol("lambda"), Pair(lambda_arg_names, set_begin_sequence)) in
      tag_parser (Pair(lambda_with_sets, sexpr_values))
 | _ -> raise PC.X_no_match

and tag_parser sexpr = (PC.disj_list [  quasiquote_expansion ; cond_expansion ; let_expansion ; let_star_expansion ;
                                        letrec_expansion ; and_expansion ; mit_define_expansion ; pset_expansion ;
                                        const_parser ; var_parser ; if_parser ; lambda_parser ; application_parser ;
                                        disjunction_parser ; definition_parser ; assignment_parser ; sequence_parser]) sexpr;;

let tag_parse_expressions sexpr = List.map tag_parser sexpr;;


end;; (* struct Tag_Parser *)