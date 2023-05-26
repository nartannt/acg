include Acg_module
open Lambda_calc_extension
open Lambda_calc
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


type str_constant =
    | String of string

let voc_1 = {
    type_constants= [N; NP; S];
    lambda_constants= [J; S_re; S_dicto; A; U];
    constant_typing_list= 
        [(J, Atom NP);
        (S_re, Arrow(Atom NP, Arrow(Atom NP, Atom S)));
        (S_dicto, Arrow(Atom NP, Arrow(Atom NP, Atom S)));
        (A, Arrow(Atom N, Atom NP));
        (U, Atom N)]
} 

let voc_2 = {
    type_constants= [Star];
    lambda_constants= [String "John"; String "seeks"; String "a"; String "unicorn"];
    constant_typing_list= [
        (String "John", string_type);
        (String "seeks", string_type);
        (String "a", string_type);
        (String "unicorn", string_type);]
}

let cnst str = Constant (String str)

let lexicon = {
    type_translate_list = [
        (N, string_type);
        (NP, string_type);
        (S, string_type)];
    term_translate_list = [
        (J,  cnst "John");
        (U, cnst "unicorn");
        (A, Abs ((cnst "a") ++ (BVar 0)) );
        (S_re, Abs ( Abs ( (BVar 0) ++ (cnst "seeks") ++ (BVar 1)  )));
        (S_dicto, Abs ( Abs ( (BVar 0) ++ (cnst "seeks") ++ (BVar 1)  )));
    ]}


let _acg = {
    abstract_vocabulary= voc_1;
    object_vocabulary= voc_2;
    lexicon= lexicon;
    distinguished_type= Atom S;
}




let () = assert (List.mem (Constant U) (list_antecedents (cnst "unicorn") lexicon.term_translate_list ))
let () = assert (List.mem (Constant U) (match_object_term (cnst "unicorn") lexicon.term_translate_list))

let () = assert (not (List.mem (BVar 0) (list_antecedents (BVar 0) lexicon.term_translate_list)))

let a_term = Abs( (cnst "a") ++ (BVar 0)) 
let () = assert (List.mem  (Constant A) (list_antecedents (a_term) lexicon.term_translate_list))
let () = assert (List.mem  (Constant A) (match_object_term (a_term) lexicon.term_translate_list))

let () = print_string "np\n"


let np = App(Constant A, Constant U)
let a_unicorn_str = (cnst "a") ++ (cnst "unicorn")

let () = print_string "\n\n\n  ---  HERE  --- \n\n\n"


let () = assert (beta_eq (a_unicorn_str) (App(Abs((cnst "a") ++ (BVar 0)), (cnst "unicorn"))))
let f = (homomorphic_extension_lamba (list_to_fun lexicon.term_translate_list))

let () = assert ( beta_eq (f np) (a_unicorn_str))

(*let res_2 = match_object_term (Abs((cnst "a") ++ (BVar 0))) lexicon.term_translate_list
let res_3 = match_object_term (cnst "unicorn") lexicon.term_translate_list*)

let res = match_object_term a_unicorn_str lexicon.term_translate_list

let () = print_int (List.length res);
         print_string " -> final antecedents\n"
let () = assert (List.mem np res)




(*
let sentence = (cnst "John") ++ (cnst "seeks") ++ (cnst "a") ++ (cnst "unicorn")
let () = assert (in_object_lang sentence acg)*)
