
(*linear implicative types*)
type 'a linear_implicative_type =
    | Atom of 'a
    | Arrow of 'a linear_implicative_type * 'a linear_implicative_type


(*vocabulary or higher order signature*)
type ('a, 'c) vocabulary =
    { atomic_types: 'a;
    constant: 'c;
    typing_fun: 'c -> 'a linear_implicative_type}

(*first draft as stand in for a simply typed linear lambda calculus*)
(*using string as variables names poses lots of problems that will be ignored for as long as possible*)
(*could it be possible to enforce linearity of the lambda terms by construction ? possibly, probably not*)
type 'c lambda_term =
    | Constant of 'c
    | App of ('c lambda_term * 'c lambda_term)
    | Var of int
    | Abs of int * 'c lambda_term

(*lexicon between two vocabularies*)
type ('a, 'c, 'b, 'd) lexicon =
    { type_translate: 'a -> 'b linear_implicative_type;
    lambda_translate: 'c -> 'd lambda_term}

(*abstract categorial grammar*)
type ('a, 'c, 'b, 'd) acg = {
    abstract_voc: ('a, 'c) vocabulary;
    object_voc: ('b, 'd) vocabulary;
    lexicon: ('a, 'c, 'b, 'd) lexicon;
    s: 'a}

(*this function checks whether a given well formed lambda term is linear or not*)
let linear_lambda_term lambda_term = 
    let rec linear_check term free_vars = match term with
        | Constant _ -> (true, free_vars)
        (*should make special case to return false and end there if any returns false*)
        | App (l, r) -> let wf_l, free_vars_l = linear_check l free_vars in
                        let wf_r, free_vars_r = linear_check r free_vars_l in
                        (wf_l && wf_r, free_vars_r)
        | Var var_name -> if List.mem var_name free_vars then false, []
                          else true, var_name::free_vars
        | Abs (var_name, term) ->
                let free_vars_abs = List.filter (fun x -> x != var_name) free_vars in
                linear_check term free_vars_abs
    in fst (linear_check lambda_term [])

(*substitutes the var in the given term byt the substitute term
 * will only substitute if the variable is free in the term, otherwise, returns the same term*)
let rec substitute_var term var_id substitute_term = match term with
    | Constant c -> Constant c
    | App (t_left, t_right) ->
            App (substitute_var t_left var_id substitute_term, substitute_var t_right var_id substitute_term)
    | Var id when var_id = id -> substitute_term
    | Var id -> Var id
    | Abs (id, sub_term) when id = var_id -> Abs (id, sub_term)
    | Abs (id, sub_term) -> Abs (id, substitute_var sub_term var_id substitute_term)



(*let normalised_lambda_term term = function
    | Constant c -> Constant c
    | Var var_id -> Var var_id
    | Abs (var_id, sub_term) -> Abs (var_id, normalised_lambda_term sub_term)
    | App (left_term, right_term) -> 
            match left_term with
                | Abs (var_id, sub_term) -> *)


(*given a function to type constants and a context (that types the free variables in a term)
 * this function check if the given type can be derived from the lambda term passed as input*)
(*let rec type_check term term_type type_constant context = match term with
    | Constant c -> term_type = type_constant c
    | Var var_id -> term_type = context var_id
    | Abs (var_id, sub_term) ->
            match term_type with
                | Arrow (type_left, type_right) ->
                        let new_context = fun id -> if id = var_id then type_left else context id in
                        type_check sub_term type_right type_constant new_context
                | _ -> false
    | App (term_left, term_right) ->  
            let left_type = ? in
            check term_left Arrow (left_type, term_type) &&
            check term_right term_type*)
