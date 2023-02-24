(*linear implicative types*)
type 'a linear_implicative_type =
  | Atom of 'a
  | Arrow of 'a linear_implicative_type * 'a linear_implicative_type
  | Var of int
    

(*vocabulary or higher order signature*)
type ('a, 'c) vocabulary = {
  atomic_types : 'a;
  constant : 'c;
  typing_fun : 'c -> 'a linear_implicative_type;
}

(*first draft as stand in for a simply typed linear lambda calculus*)
(*using string as variables names poses lots of problems that will be ignored for as long as possible*)
(*could it be possible to enforce linearity of the lambda terms by construction ? possibly, probably not*)
type 'c lambda_term =
  | Constant of 'c
  | App of ('c lambda_term * 'c lambda_term)
  | Var of int
  | Abs of int * 'c lambda_term

(*lexicon between two vocabularies*)
type ('a, 'c, 'b, 'd) lexicon = {
  type_translate : 'a -> 'b linear_implicative_type;
  lambda_translate : 'c -> 'd lambda_term;
}

(*abstract categorial grammar*)
type ('a, 'c, 'b, 'd) acg = {
  abstract_voc : ('a, 'c) vocabulary;
  object_voc : ('b, 'd) vocabulary;
  lexicon : ('a, 'c, 'b, 'd) lexicon;
  s : 'a;
}

(*this function checks whether a given well formed lambda term is linear or not*)
let linear_lambda_term lambda_term =
  let rec linear_check term free_vars =
    match term with
    | Constant _ -> (true, free_vars)
    (*should make special case to return false and end there if any returns false*)
    | App (l, r) ->
        let wf_l, free_vars_l = linear_check l free_vars in
        let wf_r, free_vars_r = linear_check r free_vars_l in
        (wf_l && wf_r, free_vars_r)
    | Var var_name ->
        if List.mem var_name free_vars then (false, [])
        else (true, var_name :: free_vars)
    | Abs (var_name, term) ->
        let free_vars_abs = List.filter (fun x -> x != var_name) free_vars in
        linear_check term free_vars_abs
  in
  fst (linear_check lambda_term [])

(*substitutes the var in the given term byt the substitute term
 * will only substitute if the variable is free in the term, otherwise, returns the same term*)
let rec substitute_var term var_id substitute_term =
  match term with
  | Constant c -> Constant c
  | App (t_left, t_right) ->
      App
        ( substitute_var t_left var_id substitute_term,
          substitute_var t_right var_id substitute_term )
  | Var id when var_id = id -> substitute_term
  | Var id -> Var id
  | Abs (id, sub_term) when id = var_id -> Abs (id, sub_term)
  | Abs (id, sub_term) ->
      Abs (id, substitute_var sub_term var_id substitute_term)

(*given a linear lambda term, returns a normalised form of that term, since it's linear reduction strategy doesn't matter*)
let rec normalised_term = function
  | Constant c -> Constant c
  | Var var_id -> Var var_id
  | Abs (var_id, sub_term) -> Abs (var_id, normalised_term sub_term)
  | App (left_term, right_term) -> (
      match left_term with
      | Abs (var_id, sub_term) ->
          let normalised_left_term = normalised_term sub_term in
          let normalised_right_term = normalised_term right_term in
          substitute_var normalised_left_term var_id normalised_right_term
      | _ ->
          let normalised_left_term = normalised_term left_term in
          let normalised_right_term = normalised_term right_term in
          App (normalised_left_term, normalised_right_term))

  (*find the most general type for a given lambda term and give the appropriate type equations*)
  (* type_eq will contain pairs that represent equality constraints on types*)
let rec infer_type_eq term type_eq (constant_type: 'a lambda_term -> 'a linear_implicative_type) = match term with
    | Constant c -> constant_type c, type_eq
    | Var var_id -> Var var_id, type_eq (*pretty useful to be able to associate a variable and its type variable easily, doesn't seem very clean though*)
    | Abs (var_id, sub_term) -> 
            let type_res, new_type_eq = infer_type_eq sub_term type_eq constant_type in
            Arrow(Var var_id, type_res), new_type_eq
    | App (left_term, right_term) -> 
            let right_type, right_type_eq = infer_type_eq right_term type_eq constant_type in
            let left_type, left_type_eq = infer_type_eq left_term type_eq constant_type in
            match left_type with
                (*this handling of type_eq is egregioulsy inefficient but right now i only want something correct*)
                | Arrow (arg_type, res_type) -> res_type, (arg_type, right_type)::right_type_eq@left_type_eq@type_eq
                | _ -> failwith "The term is not well formed my friend"

(*given a type and a substitution, will return the type with the appropriate substitutions having taken place*)
let rec substitute_in_type type_to_change type_to_replace replacement_type =
    (*not sure how caml handles equality*)
    if type_to_change = type_to_replace then replacement_type
    else
        match type_to_change with
            | Atom c -> Atom c
            | Var var_id -> Var var_id
            | Arrow (left_type, right_type) ->
                    let new_left_type = substitute_in_type left_type type_to_replace replacement_type in
                    let new_right_type = substitute_in_type right_type type_to_replace replacement_type in
                    Arrow (new_left_type, new_right_type)


(*given a list of type equations and a substitution, will substitute the approriate terms in the equations*)
let simplify_eq type_eq type_to_replace replacement_type = List.map (fun (a, b) -> ((substitute_in_type a type_to_replace replacement_type), (substitute_in_type b type_to_replace replacement_type))) type_eq

(*given a type variable will check whether it appears free in anothe type, that is whether is appears in our case*)
let rec free_in type_var_id type_to_check = match type_to_check with
    | Atom _ -> false
    | Var var_id when type_var_id = var_id -> true
    | Var _ -> false
    | Arrow (left, right) -> (free_in type_var_id left) || (free_in type_var_id right)

let rec add_substitution substitution type_to_change new_type = match substitution with
    | [] -> [(type_to_change, new_type)]
    | (to_change, replacement)::t ->
            let new_to_change = substitute_in_type to_change type_to_change new_type in
            let new_replacement = substitute_in_type replacement type_to_change new_type in
            (new_to_change, new_replacement)::(add_substitution t type_to_change new_type)

            (*when given an equation between two types, will extract all equations that can be extracted*)
let rec extract_eq (type_1: 'a linear_implicative_type) (type_2: 'a linear_implicative_type) = match type_1, type_2 with
    | Atom a, Atom b when a = b -> [], true
    | Atom a, Atom b when a != b -> [], false
    (*not necessary but needed for compiler, could replace the one above, probably should*)
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
(*will return None when unification fails*)
let rec unify_eq (type_eq: ('a linear_implicative_type * 'a linear_implicative_type) list)  substitution = match type_eq with
    (*Base case*)
    | [] -> Some (substitution)
    (*Trivial*)
    | (type_1, type_2)::t when type_1 = type_2 -> unify_eq t substitution
    (*Bind*)
    | (Var var_id, sub_type) :: t when not (free_in var_id sub_type) ->
            unify_eq (simplify_eq t (Var var_id) sub_type) (add_substitution substitution (Var var_id) sub_type)
    | (sub_type, Var var_id) :: t when not (free_in var_id sub_type) ->
            unify_eq (simplify_eq t (Var var_id) sub_type) (add_substitution substitution (Var var_id) sub_type)
    (*Check*)
    | (Var var_id, sub_type) :: _ when free_in var_id sub_type -> None
    | (sub_type, Var var_id) :: _ when free_in var_id sub_type -> None
    (*Dec and Dec fail*) 
    | (type_1, type_2):: t ->
            let eq_res, ok = extract_eq type_1 type_2 in
            if ok then
                unify_eq (eq_res@t) substitution
            else None

let infer_term_type term constant_type =
    let tmp_type, type_eq = infer_type_eq term [] constant_type in
    let substitutions_opt = unify_eq type_eq [] in
    match substitutions_opt with
        | Some substitutions -> Some (List.fold_left (fun type_to_change (type_to_replace, replacement_type) -> substitute_in_type type_to_change type_to_replace replacement_type ) tmp_type substitutions)

        | None -> None

  (*check that the given lambda term can be typed with the target type*)
let rec type_check term target_type constant_type (context: int -> 'a linear_implicative_type) = match term with
    | Constant c -> target_type = constant_type c
    | Var var_id ->
        begin
        match context var_id with
            | Var _ -> true
            | _ -> target_type = context var_id
        end
    | Abs (var_id, sub_term) ->
            (match target_type with
                | Arrow (left_type, right_type) -> type_check sub_term right_type constant_type (fun x -> if x = var_id then left_type else context x)
                | _ -> false)
    | App (left_term, right_term) ->
            let right_type_opt = infer_term_type right_term constant_type in
            let left_type_opt = infer_term_type left_term constant_type in
            begin
            match left_type_opt, right_type_opt with
                | Some (Arrow (arg_type, res_type)), Some(right_type) ->
                        let _, compatible = extract_eq arg_type right_type in
                        compatible && target_type = res_type
                | _ -> false
            end
