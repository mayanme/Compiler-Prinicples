#use "semantic-analyser.ml"

let string_to_asts s = List.map Semantics.run_semantics
(Tag_Parser.tag_parse_expressions
   (Reader.read_sexprs s))

string_to_asts "(define letrec_example
(letrec ((x 1)
        (y 2))
        (+ x y))
)";;