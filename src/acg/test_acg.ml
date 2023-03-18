include Acg_module
include Lambda_calc
(*using the examples from the 2001 OC for tests*)

type grammatical_type =
    | N
    | NP
    | S


type grammatical_constant = 
    | J
    | S_re
    | S_dicto
    | A
    | U

type str_type =
    | Str 

type str_constant =
    | String of string
    | Concat

let _voc_1 = {
    type_constants= [N; NP; S];
    lambda_constants= [J; S_re; S_dicto; A; U];
    constant_typing_list= 
        [(J, Atom NP);
        (S_re, Arrow(Atom NP, Arrow(Atom NP, Atom S)));
        (S_dicto, Arrow(Atom NP, Arrow(Atom NP, Atom S)));
        (A, Arrow(Atom N, Atom NP));
        (U, Atom N)]
} 

let _voc_2 = {
    type_constants= [Str];
    lambda_constants= [String "John"; String "seeks"; String "a"; String "unicorn"];
    constant_typing_list= [
        (String "John", Atom Str);
        (String "seeks", Atom Str);
        (String "a", Atom Str);
        (String "unicorn", Atom Str);
        (Concat, Arrow(Atom Str, Arrow (Atom Str, Atom Str)))]
}

(*let lexicon = {
    type_translate_list = [
        (N, Atom Str);
        (NP, Atom Str);
        (S, Atom Str)];
    term_translate_list = [
        (J, Constant (String "John"));
        (U, Constant (String "unicorn"));
        (A, Abs(0, App(App (Constant Concat, Constant (String "a")), Var 0)));
        (S_re,Abs(0,Abs(1,App(App(App(Constant Concat,App(Constant Concat,Var 0)),Constant (String "seeks")), Var 1))));
        (S_dicto, Abs(0,Abs(1,App(App(App(Constant Concat,App(Constant Concat,Var 0)),Constant (String "seeks")), Var 1))))
    ]}

let () = assert (List.mem (Constant J) (match_object_term (Constant (String "John")) lexicon.term_translate_list ))*)
