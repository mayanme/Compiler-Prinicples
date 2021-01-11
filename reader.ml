
#use "pc.ml";;
open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

  
  (* Consume every char with value of whitespace or lower *)
let nt_whitespaces = PC.star (PC.range (char_of_int 0) ' ');;

let make_paired nt_left nt_right nt =
  let nt = PC.caten nt_left nt in
  let nt = PC.pack nt (fun (_, e) -> e) in
  let nt = PC.caten nt nt_right in
  let nt = PC.pack nt (fun (e, _) -> e) in
    nt;;                                        

let make_spaced nt = make_paired nt_whitespaces nt_whitespaces nt;;

let dot = PC.char '.';;

let quote = make_spaced(PC.char '\'');;

let quasiquote = make_spaced(PC.char '`');;

let unquote = make_spaced(PC.char ',');;

let digit = PC.range '0' '9';;

let hashtag = PC.char '#';;

let at = PC.char '@';;

let unquote_splicing = make_spaced(PC.caten unquote at);;

let semicolon = PC.char ';';;

let tok_lparen = make_spaced ( PC.char '(');;

let tok_rparen = make_spaced ( PC.char ')');;

let tok_addop = PC.char '+';;

let tok_subop = PC.char '-';;

let tok_mulop = make_spaced ( PC.char '*');;

let tok_divop = make_spaced ( PC.char '/');;

let tok_divop_no_space = PC.char '/';;

let spaced_dot = make_spaced ( dot );;


let low_case_characters = PC.range 'a' 'z';;

let big_case_characters = PC.range 'A' 'Z';;

let tok_sign = PC.one_of "!$^*-_=+<>?/:";;

let backslash = PC.char '\\';;

let doublequote = make_spaced ( PC.char '\"' );;

let double_quote_no_spaces = PC.char '\"' ;;

let comment_char = make_spaced ( PC.char ';' );;

let exponent = PC.char_ci 'e';;

(* checked if reached a char of endline *)
let end_of_line = PC.disj (PC.char '\n') (PC.char '\r');;

let end_of_line_parser = PC.pack end_of_line ( fun s ->
  match s with 
  | '\n' | '\r' -> []
  | _ -> raise PC.X_no_match
);;

(* Symbol *)
let symobl_char_no_dot = PC.disj_list[digit ; big_case_characters ; low_case_characters ;tok_sign];;
let symbol_char = PC.disj dot symobl_char_no_dot;;
let symbol = PC.disj_list [(PC.caten symbol_char (PC.plus symbol_char)) ; (PC.caten symobl_char_no_dot (PC.star symobl_char_no_dot))];;
let symbol_parser = PC.pack symbol (fun (ch,ch_plus) ->
  Symbol(String.lowercase_ascii (list_to_string (ch :: ch_plus)))
  );;

(* String *)
let string_meta_char = PC.caten backslash (PC.one_of_ci "tfnr\\\"") ;;
let string_meta_char_parser = PC.pack string_meta_char (fun (_, ch) -> match (lowercase_ascii ch) with
  | 'r' -> char_of_int 13
  | 'n' -> char_of_int 10
  | 't' -> char_of_int 9
  | 'f' -> char_of_int 12
  | '\\' -> char_of_int 92
  | '\"' -> char_of_int 34
  | _ -> raise PC.X_no_match
);;

let string_literal_char = PC.diff PC.nt_any (PC.disj double_quote_no_spaces backslash );;
let string_char = PC.disj string_meta_char_parser string_literal_char;;
let string_ nt = make_paired double_quote_no_spaces double_quote_no_spaces nt;;
let string_parser = PC.pack  (string_ (PC.star string_char)) (fun str-> String(list_to_string str));;

(* Number *)
let natural = PC.plus digit;;

let sub_or_add = PC.disj tok_addop tok_subop;;
let sub_or_add_parser s = match s with 
| Some('-') -> -1 
| Some('+') -> 1
| None -> 1
| _ -> raise PC.X_no_match ;;

let integer = PC.not_followed_by ( PC.caten (PC.maybe sub_or_add) natural ) (PC.diff symbol (PC.disj_list [dot ; tok_divop_no_space; exponent])) ;;
let int_of_char_list ch_l = (int_of_string (list_to_string ch_l));;
let integer_parser = PC.pack integer ( fun (s,i) -> 
  let num =  (int_of_char_list i) in 
  Number(Fraction(((sub_or_add_parser s) * num ),1))
  );;

let rec gcd a b =
  if b = 0 then a else gcd b (a mod b);;

let absolute r =
  if r < 0 then -r else r

let fraction = PC.caten (PC.caten integer tok_divop) natural;;
let fraction_parser = PC.pack fraction (fun (((s,i),div),n) -> 
  let sign = (sub_or_add_parser s) in
  let num = (int_of_char_list i) * sign in
  let n = (int_of_char_list n) in
  let gcd = gcd num n in
  let positive_gcd = absolute gcd in
  Number(Fraction(num/positive_gcd,n/positive_gcd))
);;

let _float_ = PC.caten (PC.caten integer dot) natural;;
let _float_parser = PC.pack _float_ (fun (((s,i),d),n) -> 
  let f_num = (float_of_string  (list_to_string (List.append (List.append i ['.'])  n))) in 
  Number(Float((float_of_int (sub_or_add_parser s )) *. f_num))
);;
  
let rec power n = 
  if n = 0.0 then 1.0 
  else if n > 0.0 then 10.0 *. power  (n -. 1.0)
       else  0.1 *. power (n +. 1.0);;

let scientific_notation = PC.caten ( PC.caten _float_ exponent ) integer ;;
let scientific_notation_parser = PC.pack scientific_notation ( fun (((((si,inte),d),n), e), (s,i)) ->  
  let _float_ = (float_of_string  (list_to_string (List.append (List.append inte ['.'])  n))) in
  let _float_with_sign_ = (float_of_int (sub_or_add_parser si )) *. _float_ in
  let _int_ = (int_of_char_list i)  in
  let _int_with_sign_ = ((sub_or_add_parser s) * _int_ ) in
  let ten_to_power_of_i = power (float_of_int _int_with_sign_) in
  Number(Float( _float_with_sign_ *. ten_to_power_of_i ))
);;

let scientific_notation_i = PC.caten ( PC.caten integer exponent ) integer ;;
let scientific_notation_parser_i = PC.pack scientific_notation_i ( fun (((si,inte), e), (s,i)) ->  
  let _first_int_ = (int_of_char_list inte)  in
  let _first_int_with_sign = ((sub_or_add_parser si) * _first_int_ ) in
  let _second_int_ = (int_of_char_list i)  in
  let _second_int_with_sign = ((sub_or_add_parser s) * _second_int_ ) in
  let ten_to_power_of_i = power (float_of_int _second_int_with_sign) in
  Number(Float( (float_of_int _first_int_with_sign) *. ten_to_power_of_i ))
  );;

(* Char *)
let char_prefix = PC.caten hashtag backslash;;
let named_char_words = PC.disj_list [PC.word_ci "newline" ; PC.word_ci "nul" ; PC.word_ci "page" ; PC.word_ci "return" ; PC.word_ci "space" ; PC.word_ci "tab" ];;
let named_char = PC.caten char_prefix named_char_words;;
let named_char_parser = PC.pack named_char (fun ((backslash, hashtag),word) -> 
  match (String.lowercase_ascii (list_to_string word)) with
    | "newline" -> Char('\010')
    | "nul" -> Char('\000')
    | "page" -> Char('\012')
    | "return" -> Char('\013')
    | "space" -> Char('\032')
    | "tab" -> Char('\009')
    | _ -> raise  PC.X_no_match
  );;

let is_char_greater_than_space ch = (int_of_char ch) > 32;;
let visible_simple_char = PC.caten char_prefix (PC.const is_char_greater_than_space);;
let visible_simple_char_parser = PC.pack visible_simple_char (fun ((backslash, hashtag),ch) ->
  Char(ch)
  );;

(* Bool *)
let boolean = PC.caten hashtag (PC.one_of_ci "tf");;
let boolean_parser = PC.pack boolean ( fun (h, b) ->
  match b with 
  | 't' -> Bool true;
  | 'T' -> Bool true;
  | 'f' -> Bool false;
  | 'F' -> Bool false;
  | _ -> raise PC.X_no_match
  );;


let make_list nt = make_paired tok_lparen tok_rparen nt;; 

(* List *)
let rec list_parser s = 
  (* it's either '(sexpr+) or '(sexpr+ . sexpr) , Nil is handled separately *)
  let dot_then_sexpr = PC.caten spaced_dot (sexprs_list_with_ignored sexpr_parser) in
  let lparen_then_sexpr_plus = PC.caten tok_lparen (PC.plus (sexprs_list_with_ignored sexpr_parser)) in
  let proper_or_improper = PC.caten (PC.caten lparen_then_sexpr_plus (PC.maybe dot_then_sexpr)) tok_rparen in
  PC.pack proper_or_improper (fun (((lparen, sexpr_plus), maybe_dot_then_sexpr), rparen) ->                       (* maybe_dot_then_sexpr = (dot,sexpr) *)
  let init_value = last_in_list_parser maybe_dot_then_sexpr in
  List.fold_right (fun car cdr -> Pair(car, cdr)) sexpr_plus init_value) s

  and last_in_list_parser s = match s with 
    | Some(dot,last) -> last
    | None -> Nil

  and sexpr_parser s = make_spaced ( PC.disj_list [nil_parser ; scientific_notation_parser ;scientific_notation_parser_i ; boolean_parser ; _float_parser ; fraction_parser ; integer_parser ; named_char_parser ; visible_simple_char_parser ; symbol_parser; list_parser ; string_parser ; quote_like_form  ]) s

  and char_in_line_comment s = PC.star (PC.diff PC.nt_any (PC.disj end_of_line_parser PC.nt_end_of_input)) s
  and line_comment s = PC.caten (PC.caten semicolon char_in_line_comment) (PC.disj end_of_line_parser PC.nt_end_of_input) s
  and line_comment_parser s = 
    PC.pack line_comment (fun _ -> []) s

  and remove_whitespace s = PC.pack PC.nt_whitespace (fun _ -> [] ) s

  and sexpr_comment_parser_reader s =
  PC.caten (PC.caten hashtag semicolon) (sexprs_list_with_ignored sexpr_parser) s

  and sexpr_comment_parser s = 
    PC.pack sexpr_comment_parser_reader ( fun _ ->  [] ) s

  and ignored s = PC.star (PC.disj_list [ line_comment_parser ; sexpr_comment_parser ; remove_whitespace ]) s
  and sexprs_list_with_ignored nt s = 
    let sexpr_comment = make_paired ignored ignored nt  in
     PC.pack sexpr_comment (fun (d) -> d ) s
     
  (* Nil *)
  and nil_parser s =
    (PC.disj nil_parser_line_comment nil_parser_sexpr_comment) s

  and nil_parser_line_comment s = 
  let comments_with_whitespaces  = make_spaced (PC.maybe line_comment)  in
  let nil = make_paired tok_lparen tok_rparen comments_with_whitespaces   in
  PC.pack nil (fun _ -> Nil) s

  and nil_parser_sexpr_comment s = 
  let sexpr_comment = make_spaced (PC.maybe sexpr_comment_parser_reader) in
  let nil = make_paired tok_lparen tok_rparen sexpr_comment  in
  PC.pack nil (fun _ -> Nil) s

  (* Quoted forms *)
  and quote_like_form s = PC.disj_list [quote_parser; quasiquote_parser; unquote_parser; unquote_splicing_parser ] s

  and quote_parser s = 
    let quoted_expr = PC.caten quote sexpr_parser in
    PC.pack quoted_expr ( fun (sign, sexpr) -> 
      Pair(Symbol("quote"),Pair(sexpr, Nil))) s

  and quasiquote_parser s = 
    let quasiquoted_expr = PC.caten quasiquote sexpr_parser in
    PC.pack quasiquoted_expr ( fun (sign, sexpr) -> 
      Pair(Symbol("quasiquote"),Pair(sexpr, Nil))) s
  
  and unquote_parser s = 
    let unquoted_expr = PC.caten unquote sexpr_parser in
    PC.pack unquoted_expr ( fun (sign, sexpr) -> 
      Pair(Symbol("unquote"),Pair(sexpr, Nil))) s
  
  and unquote_splicing_parser s = 
    let unquote_spliced_expr = PC.caten unquote_splicing sexpr_parser in
    PC.pack unquote_spliced_expr ( fun (sign, sexpr) -> 
      Pair(Symbol("unquote-splicing"),Pair(sexpr, Nil))) s ;;

let rec get_sexprs_list s =
  if s = [] then []
  else let (car,cdr) = sexprs_list_with_ignored sexpr_parser s in  
    car :: (get_sexprs_list cdr);;

let read_sexprs string = get_sexprs_list (string_to_list string);;  
end;; (* struct Reader *)


(* 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s s) s)) s)) s)) s)) s)) s)) s)) s)) s)) s)) s)) s)) s)) s)) s)) s)) s)) s)) s)) 'mary 'had 'a 'little 'lambda)


((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s 
((lambda s s) s)) s)) s)) s)) s)) 'mary 'had 'a 'little 'lambda) *)

    (* let nt = caten (caten tok_lparen (star (sexprs_list_with_ignored sexpr_parser))) tok_rparen in
    let nt = PC.pack nt (fun ((l,exp_list),r) -> List.fold_right (fun a b -> Pair(a,b)) exp_list Nil ) in
      nt s

    and improper_list s =
    let nt = pack (PC.caten tok_lparen (PC.plus (sexprs_list_with_ignored sexpr_parser))) (fun (l,exp) -> exp) in
    let nt = pack (caten nt (char '.')) (fun (exp1,dot) -> exp1) in
    let nt = pack (caten nt (sexprs_list_with_ignored sexpr_parser)) (fun (exp1,exp2) -> (exp1,exp2)) in
    let nt = pack (caten nt tok_rparen) (fun ((exp1,exp2),r) -> (exp1,exp2)) in
    let nt = pack nt (fun (exp1,exp2) -> List.fold_right (fun a b -> Pair(a,b)) exp1 exp2) in
    nt s *)