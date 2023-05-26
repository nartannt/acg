open Lambda_calc

(*this whole section is beat for beat a translation of the orignal 2001 paper by de Groote*)
(*will add references and all that other stuff when i can be bothered or when the project will start taking proper form*)

type ('a, 'b) vocabulary = {
    type_constants: 'a list;
    lambda_constants: 'b list;
    (*this list represents a function from the constants of type 'c to 'a types*)
    constant_typing_list: ('b * 'a linear_implicative_type) list}

(*given a list of pairs will return a function*)
let rec list_to_fun (l: ('a * 'b) list) (elem: 'a) = match l with
    (*i don't like this solution for the fail case but implementing an option would 
     * prevent this function from being used as the constant typing function
     * we could rewrite some of the lambda_calc module but it would feel clunky to have to handle
     * the options everywhere*)
    | [] -> failwith "the given element is not part the input's list domain"
    | (h, res)::_ when elem  = h-> res
    | _::t -> list_to_fun t elem

(*might not be the best name*)
(* returns the homomorphic extension of f : 'a -> 'b lambda_term*)
(* term could be (should be?) anonymous but adding type annotation seemed to make things clearer*)
let rec homomorphic_extension_lamba (g: 'a -> 'b lambda_term) (term: 'a lambda_term) = match term with
    | Constant c -> g c
    | BVar var_id -> BVar var_id
    | FVar var_name -> FVar var_name
    | Abs ( sub_term) -> Abs ( homomorphic_extension_lamba g sub_term)
    | App (left_term, right_term) -> App (homomorphic_extension_lamba g left_term, homomorphic_extension_lamba g right_term)

    (*same thing but for linear implicative types*)
let rec homomorphic_extension_types (f: 'a -> 'b linear_implicative_type) = function
    | Atom a -> f a
    | Var var_id -> Var var_id
    | Arrow (left_type, right_type) -> Arrow(homomorphic_extension_types f left_type, homomorphic_extension_types f right_type)

type ('a, 'b, 'c, 'd) lexicon = {
    type_translate_list: ('a * 'c linear_implicative_type) list;
    term_translate_list: ('b * 'd lambda_term) list}

type ('a, 'b, 'c, 'd) abstract_categorial_grammar = {
    abstract_vocabulary: ('a, 'b) vocabulary;
    object_vocabulary: ('c, 'd) vocabulary;
    lexicon: ('a, 'b, 'c, 'd) lexicon;
    distinguished_type: 'a linear_implicative_type}

(*the lambda calc module does all the work for us for this one*)
let in_abstract_lang term acg =
    let s = acg.distinguished_type in
    type_check term s (list_to_fun acg.abstract_vocabulary.constant_typing_list)

(*given the list representation of a function and an element of the domain, looks for all corresponding elements of the codomain*)
(*when the function is between lambda terms *)
let rec list_antecedents (element: 'b lambda_term) (list_fun: ('a * 'b lambda_term) list) = match list_fun with
    | [] -> []
    | (a, b)::t when beta_eq b element -> (Constant a)::(list_antecedents element t)
    | (_, _)::t -> list_antecedents element t 


    (*will give all possible applications that could have been derived from two lists of antecedents*)
let rec generate_pairs list_left list_right = match list_left, list_right with
    | [], _ -> []
    | _, [] -> []
    | left_term::t, _ ->
            let res_head = List.map (fun right_term -> App(left_term, right_term)) list_right in
            res_head @ (generate_pairs t list_right)


(*need to match a term with potential antecedents*)
(* naive method, for each subterm of the object term, compare it against
 * the list of images in the list, the inefficiency is probably not too bad*)
(* improved method would make sure that we don't test the same sub-terms multiple times*)

(*this function is making me uneasy, because proving it to be correct would probably be a nightmare
  this implies the function is probably wrong, additionally this is a doubly exponential function (hopefully not the case in practice)*)
(* we will consider normalised terms the whole way through*)
(*takes in an object term and attempts to find all of its antecedents by the function represented by the term_translate list*)
let rec match_object_term (object_term: 'd lambda_term) (term_translate_list: ('b * 'd lambda_term) list) =
    (*base case, the term is part of the domain*)
    let (antecedents: ('b lambda_term) list) = list_antecedents (normalised_term object_term) term_translate_list in
    let sub_antecedents = match normalised_term object_term with
        | Constant _ -> []
        | BVar var_id -> [BVar var_id]
        | FVar var_name -> [FVar var_name]
        | Abs (sub_term) ->
                let sub_term_antecedants = match_object_term sub_term term_translate_list in
                List.map (fun term -> Abs(term)) sub_term_antecedants
        | App (left_term, right_term) ->
                let antecedents_left = match_object_term left_term term_translate_list in
                let antecedents_right = match_object_term right_term term_translate_list in
                (*this part makes it obvious that interweaving type checking and finding antecedants is a good idea performance-wise*)
                (*will stick with naïve implementation until performance demands it (if i'm lucky it won't happen until i start dealing with large semantics and lexicons)*)

                (*cause of double exponentialyness*)
                let res = generate_pairs antecedents_left antecedents_right in
                (*print_term (App(left_term, right_term));
                print_string "\n";
                print_int (List.length res);
                print_string " -> app res\n";*)
                res
    in
    print_term (normalised_term object_term);
    print_string " term len: ";
    print_int (List.length (antecedents @ sub_antecedents));
    print_string "\n";
    antecedents @ sub_antecedents


(*putting everything together*)
let in_object_lang (term: 'd lambda_term) (acg: ('a, 'b, 'c, 'd) abstract_categorial_grammar) =
    let s = acg.distinguished_type in
    let antecedents = match_object_term term acg.lexicon.term_translate_list in
    let g = homomorphic_extension_lamba (list_to_fun acg.lexicon.term_translate_list) in
    (*because i do not trust match_object_term*)
    let _ = List.map (fun antecedent -> assert (g antecedent = term)) antecedents in
    let (constant_type_fun: 'b -> 'a linear_implicative_type) = list_to_fun acg.abstract_vocabulary.constant_typing_list in
    List.exists (fun _term_antecedent -> (type_check _term_antecedent s constant_type_fun)) antecedents
