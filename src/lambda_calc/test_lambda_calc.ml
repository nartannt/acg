open Lambda_calc_module

(*tests for substitute var, which substitutes a variable in a lambda term by another term*)
let constant_term_1 = Constant "peepee poopoo"
let constant_term_2 = Constant "le pipi est stocké dans les couilles"

let var_term_1 = App (constant_term_1, BVar 2)
let var_term_2 = BVar 3
let app_term_1 = App(constant_term_1, constant_term_2)

let abs_term_1 = Abs(BVar 2)
let abs_term_2 = Abs(BVar 1)
let abs_term_3 = Abs(constant_term_2)

(*constants and free variables*)
let () = assert (constant_term_1 = substitute_bounded_var constant_term_1 1515  constant_term_2)

(*variables and applications*)
let () = assert (app_term_1 = substitute_bounded_var var_term_1 2 constant_term_2)
let () = assert (var_term_1 = substitute_bounded_var var_term_1 1 constant_term_2)
let () = assert (constant_term_2 = substitute_bounded_var var_term_2 3 constant_term_2)

(*abstraction*)
let () = assert (abs_term_2 = substitute_bounded_var abs_term_2 1 constant_term_2)
let () = assert (abs_term_2 = substitute_bounded_var abs_term_2 2 constant_term_2)

let () = assert (abs_term_3 = substitute_bounded_var abs_term_1 1 constant_term_2)


(*would be nice if we had more tests, and bigger tests, will add if bugs are found*)

(*tests for normalisation of lambda terms*)
(*lambda terms that are already normalised*)
let () = assert (constant_term_1 = normalised_term constant_term_1)
let () = assert (var_term_1 = normalised_term var_term_1)

(*lambdas terms that have beta-redexes*)
let beta_redex_1 = App(Abs (BVar 0), constant_term_1)
let beta_redex_2 = App(Abs(App(constant_term_1, BVar 0)), constant_term_2)

let nested_redex_1 = App(Abs(App(constant_term_1, BVar 0)), beta_redex_2)

let created_redex_1 = App ( Abs(App(BVar 0, constant_term_2)), Abs(BVar 0))
let created_redex_2 = App( App(Abs( Abs (BVar 0)), constant_term_1), constant_term_2)

let created_redex_3 = Abs(App(constant_term_1, App(constant_term_2, BVar 0)))
let res_1 = (App(constant_term_1, App(constant_term_2, Abs(BVar 0))))

let () = assert (beta_eq constant_term_1 beta_redex_1)
let () = assert (beta_eq app_term_1 beta_redex_2)

let () = assert (beta_eq (App(constant_term_1, app_term_1)) nested_redex_1)

let () = assert (beta_eq created_redex_1 constant_term_2)
let () = assert (beta_eq created_redex_2 constant_term_2)

let () = assert (beta_eq (App(created_redex_3, Abs(BVar 0))) (res_1) )

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


(*tests for infer_term_type*)
let constant_type n = Atom n
let infer_type (term: 'a lambda_term) = infer_term_type term constant_type

(*constants*)
let term_1 = Constant 0
let type_1 = Atom 0
let () = assert (infer_type term_1 = Some(type_1))

(*variables*)
let term_1 = FVar "1515"
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
let term_1 = Abs (App(Constant 0, BVar 0))
let type_1 = Arrow (Atom 0, Atom 1)

                
let () = assert (infer_term_type term_1 constant_type_abs = Some(type_1))

let term_1 = Abs (BVar 0)
let () = match infer_type term_1 with
    | Some(Arrow(Var a, Var b)) when a = b -> assert true
    | _ -> assert false

let term_1 = Abs (BVar 1)
let () = match infer_type term_1 with
    | Some (Arrow (Var a, Var b)) when a != b -> assert true
    | _ -> assert false

let term_1 = Abs (App(Constant 0, BVar 0)) (*Atom 0 -> Atom 1*)
let type_1 = Arrow (Atom 0, Atom 1)
let term_2 = Abs ( App(term_1, BVar 0)) (* Atom 0 -> Atom 1 *) 
let term_3 = Abs ( App(term_2, BVar 0)) (* Atom 0 -> Atom 1 *)

let () = assert (infer_term_type term_3 constant_type_abs = Some (type_1))


(*don't have an idea for other interesting small tests for lambda abstractions*)

(*applications*)
let term_1 = App (Constant 1, Constant 0)
let type_1 = Atom 2
let () = assert (infer_term_type term_1 constant_type_abs = Some(type_1))

let term_1 = App (Constant 0, Constant 0)
let () = assert (infer_term_type term_1 constant_type_abs = None)

let constant_abs_test n = match n with
    | 2 -> Arrow (Atom 1, Arrow (Atom 1, Atom 1515))
    | n -> Atom n

let non_lin_term = App(Abs( App (App(Constant 2, BVar 0), BVar 0)), Constant 1)
let () = assert (infer_term_type non_lin_term constant_abs_test = Some(Atom 1515))

let non_lin_term_2 = App(Abs(App (App(Constant 2, BVar 0), BVar 0)), BVar 2)
let () = assert (infer_term_type non_lin_term_2 constant_abs_test = Some(Atom 1515))

(*
(*tests type check to allow lambda terms to be typed with more general types*)
let test_term = Constant 1
let constant_type = fun n -> Atom n
let () = assert (type_check test_term (Var 0) constant_type)

let (test_type: string linear_implicative_type) = Atom "ay"
let (test_term: int lambda_term) = Constant 1
let dummy_type_fun = fun n -> if n = 0 then Atom "ay" else Atom "ay"
let () = assert (type_check test_term test_type dummy_type_fun()*)

