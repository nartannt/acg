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
let () = assert (constant_term = substitute_var constant_term 0 constant_term_2)

(*variables*)
let () = assert (constant_term_2 = substitute_var var_term 0 constant_term_2)
let () = assert (Var 1 = substitute_var var_term_2 0 constant_term_2)
let () = assert (constant_term_2 = substitute_var var_term_2 1 constant_term_2)

(*applications*)
let () = assert (app_term_ok = substitute_var app_term_ok 1 constant_term_2)
let () = assert (app_term_ok = substitute_var app_term_ok_2 1 constant_term)

(*abstraction*)
let () = assert (abs_term_ok = substitute_var abs_term_ok 1 constant_term_2)
let () = assert (abs_term_ok = substitute_var abs_term_ok 0 constant_term_2)

let () =
  assert (
    Abs (0, App (constant_term_2, Var 0))
    = substitute_var abs_term_ok_2 1 constant_term_2)

(*tests for normalisation of lambda terms*)
(*lambda terms that are already normalised*)
let () = assert (constant_term = normalised_term constant_term)
let () = assert (var_term = normalised_term var_term)
let () = assert (app_term_ok = normalised_term app_term_ok)

(*lambdas terms that have beta-redexes*)
let redex_term = App (abs_term_ok, constant_term_2)
let double_redex_term = App (abs_term_ok, App (abs_term_ok, constant_term_2))
let constant_app = App (constant_term, constant_term_2)
let () = assert (constant_app = normalised_term redex_term)

let () =
  assert (App (constant_term, constant_app) = normalised_term double_redex_term)

let () =
  assert (
    App (constant_app, App (constant_term, constant_app))
    = normalised_term (App (redex_term, double_redex_term)))


(*big section for testing some of the functions used in the unification algorithm*)

(*testing substitute_in_type*)
let type_1 = Arrow(Var 1, Atom 0)
let type_2 = Atom 1
let () = assert (Arrow (Atom 1, Atom 0) = substitute_in_type type_1 (Var 1) type_2)

let type_1 = Arrow(Var 1, Var 1)
let type_2 = Atom 1
let () = assert (Arrow (Atom 1, Atom 1) = substitute_in_type type_1 (Var 1) type_2)

let type_1 = Arrow(Var 1, Var 1)
let type_2 = Arrow (Atom 0, Var 1)
let () = assert (Arrow (type_2, type_2) = substitute_in_type type_1 (Var 1) type_2)

let type_1 = Arrow(Var 1, Var 1)
let type_2 = Arrow (Atom 0, Var 1)
(*this test should work no matter what type_1 and type_2 are*)
let () = assert (type_2 = substitute_in_type type_1 type_1 type_2)

(*wasn't very thourough with these tests but it will do for now*)


(*tests for infer_term_type*)
let constant_type n = Atom n

let infer_type (term: 'a lambda_term) = infer_term_type term constant_type

(*constants*)
let term_1 = Constant 0
let type_1 = Atom 0
let () = assert (infer_type term_1 = Some(type_1))

(*variables*)
let term_1 = Var 1515
let type_res = infer_type term_1
let () =
    match type_res with
        | Some (Var _) -> assert true
        | _ -> assert false

(*lambda abstractions*)
let constant_type_abs n = match n with
    | 0 -> Arrow (Atom 0, Atom 1)
    | 1 -> Arrow (Arrow (Atom 0, Atom 1), Atom 2)
    | _ -> Atom n
let term_1 = Abs (0, App(Constant 0, Var 0))
let type_1 = Arrow (Atom 0, Atom 1)
let () = assert (infer_term_type term_1 constant_type_abs= Some(type_1))

let term_1 = Abs (0, Var 0)
let () = match infer_type term_1 with
    | Some(Arrow(Var a, Var b)) when a = b -> assert true
    | _ -> assert false

let term_1 = Abs (0, Var 1)
let () = match infer_type term_1 with
    | Some (Arrow (Var a, Var b)) when a != b -> assert true
    | _ -> assert false

let term_1 = Abs (0, App(Constant 0, Var 0))
let type_1 = Arrow (Atom 0, Atom 1)
let term_2 = Abs (1, App(term_1, Var 1))
let term_3 = Abs (2, App(term_2, Var 2))
let () = assert (infer_term_type term_3 constant_type_abs = Some (type_1))


(*don't have an idea for other interesting small tests for lambda abstractions*)

(*applications*)
let term_1 = App (Constant 1, Constant 0)
let type_1 = Atom 2
let () = assert (infer_term_type term_1 constant_type_abs = Some(type_1))

let term_1 = App (Constant 0, Constant 0)
let () = assert (infer_term_type term_1 constant_type_abs = None)

(*similarly don't have more ideas right now for other interesting tests*)
(*bigger tests would be nice*)



