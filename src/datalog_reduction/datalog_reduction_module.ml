open Lambda_calc

module SInt = Set.Make(Int)

(* given a typable lambda term, will return a boolean if it is almost linear
 * an almost linear lambda term is one in for all subterms, if a variable occurs free more than once
 * it has an atomic type *)
(* might have an issue with terms where such a variable could be typed multiple ways *)
let almost_linear_term = function | _ -> true


type node =
    | Node of int

type 'a hyperedge =
    | Hyperedge of ('a lambda_term * int list)

let rec type_atomic_card linear_type = match linear_type with
    | Atom _ -> 1
    | Arrow (left, right) -> type_atomic_card left + type_atomic_card right
    | Var _ -> failwith "contains a type variable, the number of occurences of atomic types cannot be evaluated"


    (* returns a list from n to 1 in increasing order *)
let num_list n =
    let rec desc_list n = 
        if n = 1 then [1]
        else n::(desc_list(n-1))
    in List.rev (desc_list n)
    

type 'a hypergraph = 'a hyperedge list

(* given a hypergraph will return a set of all its external nodes in increasing order *)
let extract_node_list hypergraph =
    let extract_nodes_edge hyperedge node_set =
        let Hyperedge (_, node_list) = hyperedge in
        List.fold_left (fun x y -> SInt.add y x) node_set node_list
    in
    let node_set = 
        List.fold_left 
            (fun set edge -> SInt.union (extract_nodes_edge edge SInt.empty) set) SInt.empty hypergraph in
    SInt.elements node_set


(* this does a full search for every single node, not efficient, would be better to sort
 * and then look for them, however, can't be bothered and the number of nodes shouldn't go beyond
 * a few hundred (and that would probably be pushing it) *)
let rec corresponding_node old_nodes new_nodes search_node = match old_nodes, new_nodes with
    | old_hd::_ , new_hd::_ when old_hd = search_node -> new_hd
    | _::old_tl, _::new_tl -> corresponding_node old_tl new_tl search_node
    | [], _ -> failwith "node not in given list"
    | _, [] -> failwith "new nodes list too incomplete"


(* given a hypergraph and a list of nodes, will replace all the nodes in the hypergraph
 * by the corresponding node in the list, correspondance here meaning that the first (smallest)  node in the list
 * will replace the first (smallest) node in the graph ...*)
let replace_nodes ext_nodes hypergraph =
    let g_ext_nodes = extract_node_list hypergraph in
    let replace_nodes_edges edge =
        let Hyperedge (label, node_list) = edge in
        let new_list = List.map (corresponding_node ext_nodes g_ext_nodes) node_list in
        label, new_list
    in
    List.map replace_nodes_edges hypergraph
    
(*returns the last n elements of list l (in order), if l contains less than n elements, l is returned *)
let rec last_elements l n =
    if n < 0 then failwith "invalid argument, a list cannot have less than 0 elements"
    else
    if List.length l <= n then l
    else 
        match l with 
            | [] -> failwith "could return [] but this shouldn't happen anyways"
            | _::tl -> last_elements tl n



(*should possibly be in lambda_calc*)
(*given a lambda term, returns a list of all its free variables*)
let free_vars_in term = 
    let rec free_vars lambda_depth = function
        | BVar var_id when var_id >= lambda_depth -> [term]
        | BVar _ -> []
        | FVar _ -> [term]
        | Constant _ -> []
        | Abs sub_term -> free_vars (lambda_depth + 1) sub_term
        (* will not filter out duplicates *)
        | App (left, right) -> (free_vars lambda_depth left) @ (free_vars lambda_depth right)
    in
    free_vars 0 term

(* given two terms under the same nb of lambda abstractions
 * returns a list of free variables that they have in common *)
let common_free_vars term_1 term_2 =
    let free_vars_1 = free_vars_in term_1 in
    let free_vars_2 = free_vars_in term_2 in
    (* easyest way to remove duplicates from lists *)
    List.sort_uniq (fun _ _ -> 0) (free_vars_1 @ free_vars_2)


(*given a hyperedge list, will return a pair of hyperedge lists, one whose label are in the label_list
 * and one whose labels aren't *)
let rec seperate_edges edge_list label_list = match edge_list with
    | [] -> [], []
    | hd::tl when List.mem (fst hd) label_list ->
            let not_in_list, in_list = seperate_edges tl label_list in
            not_in_list, (hd::in_list)
    | hd::tl -> 
            let not_in_list, in_list = seperate_edges tl label_list in
            (hd::not_in_list, in_list)


(* given two hypergraphs with the same external nodes, will return the fusion of both *)
(* the hypergraphs must be derived from an application whose terms will be passed to the funciton*)
let fuse_hypergraphs hg_1 hg_2 term_1 term_2 =
    let common_free_vars = common_free_vars term_1 term_2 in
    let not_in_list_1, _in_list_1 = seperate_edges hg_1 common_free_vars in
    let not_in_list_2, _in_list_2 = seperate_edges hg_2 common_free_vars in
    let _unchanged_edges = not_in_list_1 @ not_in_list_2 in
    []

    


 (* given an almost linear term and its type, returns the associated hypergraph*)
let rec hypergraph_of_term term term_type = match term with
    | Constant _ | FVar _ | BVar _ -> [Hyperedge (term, num_list (type_atomic_card term_type))]
    | App (left, right) ->
            let left_type, right_type = match term_type with
                | Arrow (lt, rt) -> lt, rt
                | _ -> failwith "fucked up the typing of this term"
            in
            let left_hyperg = hypergraph_of_term left left_type in
            let left_hyperg_nodes = extract_node_list left_hyperg in
            
            let right_hyperg = hypergraph_of_term right right_type in
            let right_hyperg_nodes = extract_node_list right_hyperg in

            assert (List.length left_hyperg_nodes = type_atomic_card left_type);
            assert (List.length right_hyperg_nodes = type_atomic_card right_type);

            let num_right_nodes = type_atomic_card right_type in

            let last_left_nodes = last_elements left_hyperg_nodes num_right_nodes in 
            
            let _new_right_hyperg = replace_nodes last_left_nodes right_hyperg in

            (*still need to fuse the graphs*)
            []

    | _ -> []
