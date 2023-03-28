(* TODO maybe eventually turn this into a functor *)
(* will need to be functor for two modules, one defining some sort of lambda caclulus
 * and the other one defining the extension of lambda calculus*)
open Lambda_calc


(* implementing strings in lc should not be the job of this module but it's hard to see what i need
 * before trying*)
type pre_string = Star

(* this is how we will represent strings) *)
let string_type = Arrow(Atom Star, Atom Star)

(* given two terms encoding strings, will return the term encoding their concatenation*)
(* will probably have to switch to DeBrujn notation unless i want things to become a nightmare*)
(*let concat str_1 str_2 = 
    Constant "come back once DeBrujn is done"*)
