(* TODO go through code rename, comment and document*)
(* TODO check that comparisons of lambda terms checks for alpha-equivalence*)
(* TODO when assuming that a lambda term is linear, use predicat assert at beginning of function*)
(* TODO Rename Var to Var_type or something to that effect*)
(* DOING use De Bruijn indexes *)

(*linear implicative types*)
type 'a linear_implicative_type =
  | Atom of 'a
  | Arrow of 'a linear_implicative_type * 'a linear_implicative_type
  | Var of int
    

(* using De Bruijn indices for bounded variables (BVar) that are therefore represented by int
 * using strings for free variables (FVar) will be using strings, seems most appropriate*)
type 'c lambda_term =
  | Constant of 'c
  | App of ('c lambda_term * 'c lambda_term)
  | Abs  of 'c lambda_term
  | FVar of string
  (* /!\ the De Bruijn indices will start at 0, lambda x. x will be written as lambda. 0*)
  | BVar of int 

(*returns true if and only if the terms are alpha equivalent*)
(* i believe that a simple equality would work*)
let rec alpha_eq term_1 term_2 =
    match term_1, term_2 with
        | Constant c1, Constant c2 -> c1 = c2
        | App(t1_left, t1_right), App(t2_left, t2_right) -> (alpha_eq t1_left t2_left) && (alpha_eq t1_right t2_right)
        | Abs sub_term_1, Abs sub_term_2 -> alpha_eq sub_term_1 sub_term_2
        | FVar var_name_1, FVar var_name_2 -> var_name_1 = var_name_2
        | BVar var_id_1, BVar var_id_2 -> var_id_1 = var_id_2
        | _ -> false

(*raises the indices of the free BVars in the given term by raise_amount *)
let raise_free_vars term raise_amount = 
    let rec raise_free cutoff_depth = function
        | Constant c -> Constant c
        | App (lt, rt) -> App(raise_free cutoff_depth lt, raise_free cutoff_depth rt)
        | FVar var_name -> FVar var_name
        | BVar var_id when var_id >= cutoff_depth -> BVar (var_id + raise_amount)
        | BVar var_id -> BVar var_id
        | Abs sub_term -> Abs (raise_free (cutoff_depth + 1) sub_term)
    in raise_free 0 term

(* given a lambda term, will replace all the instanceas of a variable bounded at a higher (given) level but locally free by the new_term*)
let rec substitute_bounded_var term var_level new_term =
    (*this feels like it could be handled better i don't want it to be able to fail quitely*)
    if var_level < 0 then failwith "invalid argument var_level must be a positive integer"
    else
    match term with
    | Constant c -> Constant c
    | App(t_left, t_right) ->
        App(substitute_bounded_var t_left var_level new_term,
            substitute_bounded_var t_right var_level new_term)
    | FVar var_name -> FVar var_name
    | BVar var_id when var_id = var_level -> new_term
    | BVar var_id -> BVar var_id
    | Abs (sub_term) -> Abs( substitute_bounded_var sub_term (var_level + 1) (raise_free_vars new_term 1))


let rec print_term = function
    | Constant _ -> print_string "constant"
    | FVar var_name -> print_string ("(free variable: " ^ var_name ^ ")")
    | BVar var_id -> print_string ("(var: " ^ (string_of_int var_id) ^ ")")
    | App (lt, rt) -> print_string "App(";
                      print_term lt;
                      print_string ", ";
                      print_term rt;
                      print_string ")"
    |Abs st -> print_string "Abs(";
               print_term st;
               print_string ")"

(*checks whether a term is in normal head form*)
let rec check_normalised = function
    | Constant _ -> true
    | BVar _ -> true
    | FVar _ -> true
    | Abs t -> check_normalised t
    | App (l, r) ->
            begin
            match l with
                | App _ -> false
                | _ -> (check_normalised l) && (check_normalised r)
            end

(*given a lambda term, applies all possible beta_reductions to that term, since the terms
 * are supposed to be linear linear reduction strategy doesn't matter, if i'm not mistaken*)
let rec pre_normalised_term = function
  | Constant c -> Constant c
  | BVar var_id -> BVar var_id
  | FVar var_name -> FVar var_name
  | Abs sub_term -> Abs (pre_normalised_term sub_term)
  | App (left_term, right_term) -> (
      let pre_normalised_left_term = pre_normalised_term left_term in
      let pre_normalised_right_term = pre_normalised_term right_term in
      match pre_normalised_left_term with
      (* beta reduction *)
      | Abs sub_term ->
        let reduction_res = substitute_bounded_var sub_term 0 pre_normalised_right_term in
        pre_normalised_term reduction_res
      | _ ->
          App (pre_normalised_left_term, pre_normalised_right_term))

  (*for an explanation on the the whole normalisation thing*)
(*http://www.lsv.fr/~goubault/Lambda/strategies-step-by-step_compressed.pdf*)

(*given a term that is not a lambda abstraction will return a list of its arguments as understood
 * in the definition of normal head form*)
let rec extract_arg_list = function
    | Constant c -> [Constant c]
    | BVar var_id -> [BVar var_id]
    | FVar var_name -> [FVar var_name]
    | Abs t -> [Abs t]
    (*the order is very important*)
    | App (l, r) -> (extract_arg_list l) @ (extract_arg_list r)

(*takes as argument the list of "arguments" given by extract_arg_list and returns a series of
 * applications compatible with normal head form*)
let rec normalised_arguments = function
    | [] -> failwith "invalid argument"
    | [h] -> h
    | h1::t -> App(h1, normalised_arguments t)

let normalised_term term =
    let rec final_normalised_term = function
        | Constant c -> Constant c
        | BVar var_id -> BVar var_id
        | FVar var_name -> FVar var_name
        | Abs t -> Abs (final_normalised_term t)
        | App (l, r) ->
                let n_l = final_normalised_term l in
                let n_r = final_normalised_term r in
                let arg_list = extract_arg_list (App(n_l, n_r)) in
                normalised_arguments arg_list
    in final_normalised_term (pre_normalised_term term)


let rec print_type (li_type: int linear_implicative_type) = match li_type with
    | Atom n -> print_string ("Atom(" ^ (string_of_int n) ^ ")")
    | Arrow(ltype, rtype) -> print_type ltype; print_string " -> "; print_type rtype
    | Var var_id -> print_string ("Var(" ^ string_of_int var_id ^ ")")


let beta_eq term_1 term_2 =
    let n_term_1 = normalised_term term_1 in
    let n_term_2 = normalised_term term_2 in
    (*nice little invariant that leaves us feeling a bit safer*)
    assert (check_normalised n_term_1);
    assert (check_normalised n_term_2);
    alpha_eq (n_term_1) (n_term_2)

(* given a variable id will return the associated variable name in the given list*)
let rec retrieve_var_name var_id = function
    | [] -> None
    | (id, var_name)::_ when id = var_id -> Some var_name
    | _::t -> retrieve_var_name var_id t

    (*given a list of associations of bvars to variable ids will return the same list with all vars below a certain lambda depth removed*)
let rec remove_bvars_cutoff cutoff_depth = function
    | [] -> []
    | (depth, _)::t when depth > cutoff_depth -> remove_bvars_cutoff cutoff_depth t
    | h::t -> h::(remove_bvars_cutoff cutoff_depth t)

  (* find the most general type for a given lambda term and give the appropriate type equations*)
  (* type_eq will contain pairs that represent equality constraints on types*)
  (* the lambda_depth is for the bounded variables and represents how deep we are in the term abstratction-wise*)
  (* can detect some typing errors, will return none then *)
  (*unique_id is used to generate unique identifiers for the type variables*)
    (*this function is an absolute mess, fixing it first then refactoring*)
let rec infer_type_eq term constant_type lambda_depth fvar_rec bvar_rec unique_id = match term with
    | Constant c -> Some (constant_type c, [], fvar_rec, bvar_rec, unique_id)
    | FVar var_name ->
            let new_fvar_rec, fvar_type = 
                match retrieve_var_name var_name fvar_rec with
                    | None -> (var_name, unique_id)::fvar_rec, Var unique_id
                    | Some type_var_id -> fvar_rec, Var type_var_id
            in
            Some (fvar_type, [], new_fvar_rec, bvar_rec, unique_id+1)
    | BVar var_id -> 
            let new_bvar_rec, bvar_type =
                match retrieve_var_name (lambda_depth - var_id - 1) bvar_rec with
                    | None -> (lambda_depth - var_id - 1, unique_id)::bvar_rec, Var unique_id
                    | Some type_var_id -> bvar_rec, Var type_var_id
            in
            Some (bvar_type, [], fvar_rec, new_bvar_rec, unique_id+1)
    | Abs sub_term -> 
        begin
            let new_bvar_rec = (lambda_depth, unique_id)::bvar_rec in
            match infer_type_eq sub_term constant_type (lambda_depth + 1) fvar_rec new_bvar_rec (unique_id+1) with
                | None -> None
                | Some (type_res, type_eq, new_fvar_rec, bvar_rec_res, new_unique_id) ->
                        Some (Arrow(Var unique_id, type_res), type_eq, new_fvar_rec, bvar_rec_res, new_unique_id)
        end
    | App (left_term, right_term) -> 
            let res_right_term = infer_type_eq right_term constant_type lambda_depth fvar_rec bvar_rec unique_id in
            match res_right_term with
                | None -> None
                | Some (right_type, right_type_eq, fvar_rec_right, bvar_rec_right, unique_id_right) ->
                    let cutoff_bvar_rec = remove_bvars_cutoff lambda_depth bvar_rec_right in
                    let res_left_term = infer_type_eq left_term constant_type lambda_depth fvar_rec_right cutoff_bvar_rec unique_id_right in
                begin
                match res_left_term with
                    | None -> None
                    | Some (Arrow(arg_type, res_type), left_type_eq, fvar_rec_left, bvar_rec_left, unique_id_left) ->
                        let new_type_eq = (arg_type, right_type)::right_type_eq@left_type_eq in
                        Some(res_type, new_type_eq, fvar_rec_left, bvar_rec_left, unique_id_left) 
                    | _ -> None
                end

let get_type_eq term constant_type =
    match infer_type_eq term constant_type 0 [] [] 0 with
        | None -> None
        | Some (type_res, type_eq, _, _, _) ->
                Some(type_res, type_eq)

(*given a type and a substitution, will return the type with the appropriate substitutions having taken place*)
let rec substitute_in_type type_to_change type_to_replace replacement_type =
    if type_to_change = type_to_replace then 
        replacement_type
    else
        match type_to_change with
            | Atom c -> Atom c
            | Var var_id -> Var var_id
            | Arrow (left_type, right_type) ->
                    let new_left_type = substitute_in_type left_type type_to_replace replacement_type in
                    let new_right_type = substitute_in_type right_type type_to_replace replacement_type in
                    Arrow (new_left_type, new_right_type)


(*given a list of type equations and a substitution, will substitute the approriate terms in all the equations*)
let simplify_eq type_eq type_to_replace replacement_type =
    List.map (fun (a, b) ->
        ((substitute_in_type a type_to_replace replacement_type), (substitute_in_type b type_to_replace replacement_type))) type_eq

(*given a type variable will check whether it appears in a type *)
let rec appears_in type_var_id type_to_check = match type_to_check with
    | Atom _ -> false
    | Var var_id when type_var_id = var_id -> true
    | Var _ -> false
    | Arrow (left, right) -> (appears_in type_var_id left) || (appears_in type_var_id right)

    (* given a list of type substitutions and two types will add the substitution to the list
    and apply the new substitution to all the the types in the substitution list*)
let rec add_substitution substitution type_to_change new_type = match substitution with
    | [] -> [(type_to_change, new_type)]
    | (to_change, replacement)::t ->
            let new_to_change = substitute_in_type to_change type_to_change new_type in
            let new_replacement = substitute_in_type replacement type_to_change new_type in
            (new_to_change, new_replacement)::(add_substitution t type_to_change new_type)

    (*when given a type equation, will return all type equation that can be deduced*)
    (* will return false if the given type equation cannot be unified*)
let rec extract_eq (type_1: 'a linear_implicative_type) (type_2: 'a linear_implicative_type) = match type_1, type_2 with
    | Atom a, Atom b when a = b -> [], true
    | Atom a, Atom b when a != b -> [], false
    (*not necessary but needed for compiler*)
    | Atom _, Atom _ -> [], false
    | Var var_id, type_term -> [(((Var var_id):'a linear_implicative_type), type_term)], true
    | type_term, Var var_id -> [(Var var_id, type_term)], true
    | Atom _, Arrow _ -> [], false
    | Arrow _, Atom _ -> [], false
    | Arrow (left_1, right_1), Arrow (left_2, right_2) ->
            let res_1, ok_1 = extract_eq left_1 left_2 in
            let res_2, ok_2 = extract_eq right_1 right_2 in
            res_1@res_2, ok_1 && ok_2


(*simplifies the type equations by successive rewriting*)
(*will return None if unification fails*)
(*the substitutions is a list of pairs where the left term is to be replaced by the right one*)
let rec unify_eq (type_eq: ('a linear_implicative_type * 'a linear_implicative_type) list)  substitution = match type_eq with
    (*Base case*)
    | [] -> Some (substitution)
    (*Trivial*)
    | (type_1, type_2)::t when type_1 = type_2 -> unify_eq t substitution
    (*Bind*)
    | (Var var_id, new_type) :: t when not (appears_in var_id new_type) ->
            unify_eq (simplify_eq t (Var var_id) new_type) (add_substitution substitution (Var var_id) new_type)
    | (new_type, Var var_id) :: t when not (appears_in var_id new_type) ->
            unify_eq (simplify_eq t (Var var_id) new_type) (add_substitution substitution (Var var_id) new_type)
    (*Check*)
    | (Var var_id, new_type) :: _ when appears_in var_id new_type -> None
    | (new_type, Var var_id) :: _ when appears_in var_id new_type -> None
    (*Dec and Dec fail*) 
    | (type_1, type_2):: t ->
            let eq_res, ok = extract_eq type_1 type_2 in
            if ok then
                unify_eq (eq_res@t) substitution
            else None

(*given a linear lambda term (should work with any lambda terms) returns the most general type that can be infered, if it cannot be typed then None is returned*)
let infer_term_type (term: 'a lambda_term) (constant_type: 'a  -> 'b linear_implicative_type) =
    begin
    match get_type_eq term constant_type with
    | None -> None
    | Some (tmp_type, type_eq) ->
        begin
        match unify_eq type_eq [] with
            | Some substitutions ->
                    Some (List.fold_left 
                        (fun type_to_change (type_to_replace, replacement_type) ->
                            substitute_in_type type_to_change type_to_replace replacement_type ) tmp_type substitutions)
            | None -> None
        end
    end

    (*checks that the given types can be unified *)
let types_compatible type_1 type_2 =
    let type_eq, reducible_candidate = extract_eq type_1 type_2 in
    if reducible_candidate then
        match unify_eq type_eq [] with
            | Some _ -> true
            | None -> false
    else
        false


  (*check that the given lambda term can be typed with the target type*)
let type_check term test_type constant_type = 
    match infer_term_type term constant_type with
        | Some(infered_type) ->
                types_compatible infered_type test_type
        | None -> false
