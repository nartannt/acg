(* TODO maybe eventually turn this into a functor *)
(* will need to be functor for two modules, one defining some sort of lambda caclulus
 * and the other one defining the extension of lambda calculus*)
open Lambda_calc


(* implementing strings in lc should not be the job of this module but it's hard to see what i need
 * before trying*)
type pre_string = Star

(* this is how we will represent strings) *)
let string_type = Arrow(Atom Star, Atom Star)

(* the empty string*)
let epsilon = Abs (BVar 0)

(* given two terms encoding strings, will return the term encoding their concatenation*)
let (++) str_1 str_2 = 
    let t_1 =
    (App(App(
        Abs(Abs(Abs(
            App(BVar 2, App(BVar 1, BVar 0))))) , str_1), str_2)) in
    (*learned hard way that attempting to substitute manually causes problems
     with free BVars getting caught in the wrong abstraction*)
    t_1
