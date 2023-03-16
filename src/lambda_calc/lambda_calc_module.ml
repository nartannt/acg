(* TODO go through code rename, comment and document*)
(* TODO check that comparisons of lambda terms checks for alpha-equivalence*)
(* TODO when assuming that a lambda term is linear, use predicat assert at beginning of function*)

(*linear implicative types*)
type 'a linear_implicative_type =
  | Atom of 'a
  | Arrow of 'a linear_implicative_type * 'a linear_implicative_type
  | Var of int
    

(*first draft as stand in for a simply typed linear lambda calculus*)
(*using string as variables names poses lots of problems that will be ignored for as long as possible*)
(*could it be possible to enforce linearity of the lambda terms by construction ? possibly, probably not*)
type 'c lambda_term =
  | Constant of 'c
  | App of ('c lambda_term * 'c lambda_term)
  | Var of int
  | Abs of int * 'c lambda_term

(*returns true if and only if the terms are alpha equivalent*)
let alpha_eq term_1 term_2 = 
    let rec lambda_compare t1 t2 abs_var_rec = 
        begin
        match t1, t2 with
        | Constant c1, Constant c2 -> c1 = c2
        | Var var_id_1, Var var_id_2 -> var_id_1 = abs_var_rec var_id_2
        | App (left_1, right_1), App (left_2, right_2) -> (lambda_compare left_1 left_2 abs_var_rec) && (lambda_compare right_1 right_2 abs_var_rec)
        (*i'm not sure that a function is the best way to do this, most likely not*)
        | Abs (var_id_1, sub_term_1), Abs(var_id_2, sub_term_2) -> lambda_compare sub_term_1 sub_term_2 (fun x -> if x = var_id_2 then var_id_1 else abs_var_rec x)
        | _ -> false
        end
    in lambda_compare term_1 term_2 (fun _ -> -1)


(*this function checks whether a given well formed lambda term is linear or not*)
let linear_lambda_term lambda_term =
  let rec linear_check term free_vars =
    match term with
    | Constant _ -> (true, free_vars)
    (*should make special case to return false and end there if any returns false*)
    | App (left, right) ->
        let well_formed_left, free_vars_l = linear_check left free_vars in
        let well_formed_right, free_vars_r = linear_check right free_vars_l in
        (well_formed_left && well_formed_right, free_vars_r)
    | Var var_id ->
        if List.mem var_id free_vars then (false, [])
        else (true, var_id :: free_vars)
    | Abs (var_id, term) ->
        let free_vars_abs = List.filter (fun x -> x != var_id) free_vars in
        linear_check term free_vars_abs
  in
  fst (linear_check lambda_term [])


(*substitutes all occurences of a var in the given term by the substitute term
 * will only substitute if the variable is free in the term, otherwise, returns the same term*)
let rec substitute_var term var_id new_term =
  match term with
  | Constant c -> Constant c
  | App (t_left, t_right) ->
      App(substitute_var t_left var_id new_term,
          substitute_var t_right var_id new_term)
  | Var id when var_id = id -> new_term
  | Var id -> Var id
  | Abs (id, sub_term) when id = var_id -> Abs (id, sub_term)
  | Abs (id, sub_term) -> Abs (id, substitute_var sub_term var_id new_term)

(*given a linear lambda term, returns a normalised form of that term, since it's linear reduction strategy doesn't matter, i think*)
let rec normalised_term = function
  | Constant c -> Constant c
  | Var var_id -> Var var_id
  | Abs (var_id, sub_term) -> Abs (var_id, normalised_term sub_term)
  | App (left_term, right_term) -> (
      match left_term with
      (* beta reduction *)
      | Abs (var_id, sub_term) ->
          let normalised_left_term = normalised_term sub_term in
          let normalised_right_term = normalised_term right_term in
          substitute_var normalised_left_term var_id normalised_right_term
      | _ ->
          let normalised_left_term = normalised_term left_term in
          let normalised_right_term = normalised_term right_term in
          App (normalised_left_term, normalised_right_term))

  (* find the most general type for a given lambda term and give the appropriate type equations*)
  (* type_eq will contain pairs that represent equality constraints on types*)
  (* the returned type corresponds to that of the given term, it is as generic as possible, the equations add further constraints*)
  (* can detect some typing errors, will return none then *)
let rec infer_type_eq (term: 'a lambda_term) (constant_type: 'a -> 'b linear_implicative_type) = match term with
    | Constant c -> Some (constant_type c, [])
    (* quick way to associate a variable and its type variable easily, unsure it's the best way to do this*)
    (* note that the returned Var var_id is a type variable and is the type associated with the term Var var_id*)
    (* the nice thing with this approach is that it guarantees that all instances of a variable will have the same type*)
    | Var var_id -> Some (Var var_id, [])
    | Abs (var_id, sub_term) -> 
            begin
            match infer_type_eq sub_term constant_type with
            | None -> None
            | Some (type_res, new_type_eq) ->
                Some (Arrow(Var var_id, type_res), new_type_eq)
            end
    | App (left_term, right_term) -> 
            begin
            match infer_type_eq right_term constant_type with
            | None -> None
            | Some (right_type, right_type_eq) ->
                begin
                match infer_type_eq left_term constant_type with
                | None -> None
                | Some (left_type, left_type_eq) -> 
                    begin
                    match left_type with
                        | Arrow (arg_type, res_type) -> Some(res_type, (arg_type, right_type)::right_type_eq@left_type_eq)
                        | _ -> None
                    end
                end
            end

(*given a type and a substitution, will return the type with the appropriate substitutions having taken place*)
let rec substitute_in_type type_to_change type_to_replace replacement_type =
    if type_to_change = type_to_replace then replacement_type
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

(*given a type variable will check whether it appears free in anothe type, that is whether it appears at all given we have no quantifiers *)
let rec free_in type_var_id type_to_check = match type_to_check with
    | Atom _ -> false
    | Var var_id when type_var_id = var_id -> true
    | Var _ -> false
    | Arrow (left, right) -> (free_in type_var_id left) || (free_in type_var_id right)

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
    | (Var var_id, new_type) :: t when not (free_in var_id new_type) ->
            unify_eq (simplify_eq t (Var var_id) new_type) (add_substitution substitution (Var var_id) new_type)
    | (new_type, Var var_id) :: t when not (free_in var_id new_type) ->
            unify_eq (simplify_eq t (Var var_id) new_type) (add_substitution substitution (Var var_id) new_type)
    (*Check*)
    | (Var var_id, new_type) :: _ when free_in var_id new_type-> None
    | (new_type, Var var_id) :: _ when free_in var_id new_type -> None
    (*Dec and Dec fail*) 
    | (type_1, type_2):: t ->
            let eq_res, ok = extract_eq type_1 type_2 in
            if ok then
                unify_eq (eq_res@t) substitution
            else None

            (*given a linear lambda term (should work with any lambda terms) returns the most general type that can be infered, if it cannot be typed then None is returned*)
let infer_term_type (term: 'a lambda_term) (constant_type: 'a  -> 'b linear_implicative_type) =
    begin
    match infer_type_eq term constant_type with
    | None -> None
    | Some (tmp_type, type_eq) ->
        begin
        match unify_eq type_eq [] with
            | Some substitutions -> Some (List.fold_left (fun type_to_change (type_to_replace, replacement_type) -> substitute_in_type type_to_change type_to_replace replacement_type ) tmp_type substitutions)
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
        | Some(infered_type) -> types_compatible infered_type test_type
        | None -> false
