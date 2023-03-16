open Lambda_calc


(*this whole section is beat for beat a translation of the orignal 2001 paper by de Groote*)
(*can you believe this was published the same year i was born*)
(*will add references and all that other stuff when i can be bothered or when the project will start taking proper form*)

type ('a, 'c) vocabulary = {
    type_constants: ('a linear_implicative_type) list;
    lambda_constants: 'c list;
    constant_typing: 'c -> 'a linear_implicative_type}

(*might not be the best name*)
(* returns the homomorphic extension of f : 'a -> 'b lambda_term*)
(* term could be (should be?) anonymous but adding type annotation seemed to make things clearer*)
let rec homomorphic_extension_lamba (g: 'a -> 'b lambda_term) (term: 'a lambda_term) = match term with
    | Constant c -> g c
    | Var var_id -> Var var_id
    | Abs (var_id, sub_term) -> Abs (var_id, homomorphic_extension_lamba g sub_term)
    | App (left_term, right_term) -> App (homomorphic_extension_lamba g left_term, homomorphic_extension_lamba g right_term)

    (*same thing but for linear implicative types*)
let rec homomorphic_extension_types (f: 'a -> 'b linear_implicative_type) = function
    | Atom a -> f a
    | Var var_id -> Var var_id
    | Arrow (left_type, right_type) -> Arrow(homomorphic_extension_types f left_type, homomorphic_extension_types f right_type)

type ('a, 'b, 'c, 'd) lexicon = {
    type_translate: 'a -> 'b linear_implicative_type;
    term_translate: 'c -> 'd lambda_term}

type ('a, 'b, 'c, 'd) abstract_categorial_grammar = {
    abstract_vocabulary: ('a, 'c) vocabulary;
    object_vocabulary: ('b, 'd) vocabulary;
    lexicon: ('a, 'b, 'c, 'd) lexicon;
    distinguished_type: 'a linear_implicative_type}

(*the lambda module does all the work for us for this one*)
let is_abstract_term term acg =
    let s = acg.distinguished_type in
    type_check term s acg.abstract_vocabulary.constant_typing

(*this one however will not be easy*)

(*first idea to approach the pb:
    - find all antecedants of the term by g -- the difficult part
        * unify constants with the codomain of g
        * is unification necessary, it could be sufficient to simply match them and test by applying g
        * if successful great
        * if not try to unify successively bigger parts of the the term with the codomain of g
        * this will terminate because eventually you attempt to match the whole term

        * fancy stuff to gain performance
            # keep a list of sub-terms we attempted to match so we don't have to recalculate them
            # a clever use type tests at key moments in the previous algorithm could help with pruning the possibilities
    - check if any of them are of type s -- the trivial part*)
