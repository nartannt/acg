type 'a linear_implicative_type =
    | Atom of 'a
    | Arrow of 'a linear_implicative_type * 'a linear_implicative_type
    | Var of int

type 'c lambda_term =
   | Constant of 'c
   | App of ('c lambda_term * 'c lambda_term)
   | Var of int
   | Abs of int * 'c lambda_term

val normalised_term: 'a lambda_term -> 'a lambda_term
val linear_lambda_term: 'a lambda_term -> bool

val infer_term_type: 'a lambda_term -> ('a -> 'a linear_implicative_type) -> ('a linear_implicative_type) option
val types_compatible: 'a linear_implicative_type -> 'a linear_implicative_type -> bool
val type_check: 'a lambda_term -> 'a linear_implicative_type -> ('a -> 'a linear_implicative_type) -> bool
