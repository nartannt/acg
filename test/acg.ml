open Acg

(*tests for linear_lambda_term, which tests whether a well formed lambda term is linear *)
(*for constants*)
let constant_term = Constant ""
let () = assert (linear_lambda_term constant_term = true)

(*single variables*)
let var_term = Var 0
let () = assert (linear_lambda_term var_term = true)

(*applications*)
let app_term_ok = App (constant_term, var_term)
let () = assert (linear_lambda_term app_term_ok = true)

let app_term_err = App (var_term, var_term)
let () = assert (linear_lambda_term app_term_err = false)

let var_term_2 = Var 1
let app_term_ok_2 = App (var_term_2, var_term)
let () = assert (linear_lambda_term app_term_ok_2 = true)

(*lambda abstractions*)
let abs_term_ok = Abs (0, app_term_ok)
let () = assert (linear_lambda_term abs_term_ok = true)

let abs_term_ok_2 = Abs (0, app_term_ok_2)
let () = assert (linear_lambda_term abs_term_ok_2 = true)

let abs_term_err = Abs (0, app_term_err)
let () = assert (linear_lambda_term abs_term_err = false)

(*tests for substitute var, which substitutes a variable in a lambda term by another term*)

(*constants*)
let constant_term_2 = Constant "le pipi est stocké dans les couilles"
let () = assert (constant_term = (substitute_var constant_term 0 constant_term_2))

(*variables*)
let () = assert (constant_term_2 = (substitute_var var_term 0 constant_term_2))
let () = assert (Var 1 = (substitute_var var_term_2 0 constant_term_2))
let () = assert (constant_term_2 = (substitute_var var_term_2 1 constant_term_2))

(*applications*)
let () = assert (app_term_ok = (substitute_var app_term_ok 1 constant_term_2))
let () = assert (app_term_ok = (substitute_var app_term_ok_2 1 constant_term))

(*abstraction*)
let () = assert (abs_term_ok = (substitute_var abs_term_ok 1 constant_term_2))
let () = assert (abs_term_ok = (substitute_var abs_term_ok 0 constant_term_2))
let () = assert (Abs(0, App (constant_term_2, Var 0)) = (substitute_var abs_term_ok_2 1 constant_term_2))
