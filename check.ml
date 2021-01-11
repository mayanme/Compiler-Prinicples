#use "code-gen.ml";;

let string_to_asts s = List.map Semantics.run_semantics
(Tag_Parser.tag_parse_expressions
   (Reader.read_sexprs s)) in

let file_to_string f =
   let ic = open_in f in
   let s = really_input_string ic (in_channel_length ic) in
   close_in ic;
   s in

let code =  (file_to_string "stdlib.scm")  in

(* generate asts for all the code *)
let asts = string_to_asts "
((lambda (a b c) ((lambda (a b c d) b) a (a 0 1) c c)) (lambda (a b) (+ a b)) 2 3)
" in

(* generate the constants table *)
let consts_tbl = Code_Gen.make_consts_tbl asts in

(* generate the fvars table *)
 let fvars_tbl = Code_Gen.make_fvars_tbl asts in 
 asts;;

  (* merge everything into a single large string and print it out *)
let a = Printf.sprintf ("Hello****************************************%d") 8;;
let b = 5;;
a;;

