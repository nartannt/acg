include Acg_module
(*using the examples from the 2001 OC for tests*)
type grammatical_types =
    | N
    | NP
    | S


type grammtical_constants = 
    | J
    | S_re
    | S_dicto
    | A
    | U

(*let voc_1 = {
    type_constants= [N; NP; S];
    lambda_constants= [J; S_re; S_dicto; A; U];
    constant_typing_list= 
        [(J, Atom NP);
        (S_re, Arrow(Atom NP, Arrow(Atom NP, Atom S)));
        (S_dicto, Arrow(Atom NP, Arrow(Atom NP, Atom S)));
        (A, Arrow(Atom N, Atom NP));
        (U, Atom N)]
} *)
