

type 'a linear_implicative_type =
    | Atom of 'a
    | Arrow of 'a linear_implicative_type * 'a linear_implicative_type


type ('a, 'c) vocabulary =
    { atomic_types: 'a;
    constant: 'c;
    typing_fun: 'c -> 'a linear_implicative_type}

type 'c linear_lambda_term =
    | Constant of 'c
    | App of ('c linear_lambda_term * 'c linear_lambda_term)
    | Var of string
    | Abs of string * 'c linear_lambda_term

type ('a, 'c, 'b, 'd) lexicon =
    { type_translate: 'a -> 'b linear_implicative_type;
    lambda_translate: 'c -> 'd linear_lambda_term}

type ('a, 'c, 'b, 'd) acg = {
    abstract_voc: ('a, 'c) vocabulary;
    object_voc: ('b, 'd) vocabulary;
    lexicon: ('a, 'c, 'b, 'd) lexicon;
    s: 'a}
