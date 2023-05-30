open Lambda_calc

module SInt = Set.Make(Int)

(* given a typable lambda term, will return a boolean if it is almost linear
 * an almost linear lambda term is one in for all subterms, if a variable occurs free more than once
 * it has an atomic type *)
(* might have an issue with terms where such a variable could be typed multiple ways *)
let almost_linear_term = function | _ -> true


(* the secong int represents the node's id, it is used to identify the node and must therefore be unique *)
(* the first int is used to mark the node as external if it is greater than 0, then this number will mark
 * the external node's place, if the node is not external, it will be 0*)
type node =
    | Node of int * int

(* the lambda term is the label of the hyperedge, the node list represents the nodes
 * that the edge is incident on, the order of that list is important *)
type 'a hyperedge =
    | Hyperedge of 'a lambda_term * node list

type 'a hypergraph =
    | Hypergraph of 'a hyperedge list


(* a coyple of utility functions*)

(* calculates the number of occurences of atomic type in a linear implicative type *)
let rec type_atomic_card linear_type = match linear_type with
    | Atom _ -> 1
    | Arrow (left, right) -> type_atomic_card left + type_atomic_card right
    | Var _ -> failwith "contains a type variable, the number of occurences of atomic types cannot be evaluated"


(* returns a list from 1 to n in increasing order *)
let num_list n =
    let rec desc_list n = 
        if n = 1 then [1]
        else n::(desc_list(n-1))
    in List.rev (desc_list n)

(*returns the last n elements of list l (in order), if l contains less than n elements, l is returned *)
(* preserves order *)
let rec last_elements l n =
    if n < 0 then failwith "invalid argument, a list cannot have less than 0 elements"
    else
    if List.length l <= n then l
    else 
        match l with 
            | [] -> failwith "could return [] but this shouldn't happen anyways"
            | _::tl -> last_elements tl n

(* returns true iff the given node is external*)
let is_external node =
    let Node(ext, _) = node in
    ext != 0

(* returns a list of all external nodes (in order) of a hyperedge *)
let hyperedge_ext_nodes hyperedge =
    let Hyperedge (_, node_list) = hyperedge in
    List.filter is_external node_list

(*given a hypergraph, will return the last n external nodes of the hypergraph, in increasing order
 * if n is greater than the number of external nodes, all external nodes are returned *)
let last_ext_nodes n hypergraph =
    let Hypergraph edge_list = hypergraph in
    let external_nodes = hyperedge_ext_nodes edge_list in
    last_elements external_nodes n

     

(* given two hypergraphs of terms forming an application, will return the resulting hypergraph*)
let fuse_app_hypergraphs left_hyperg right_hyperg =
    let Hypergraph hedge_list_right = right_hyperg in
    let Hypergraph hedge_list_left = left_hyperg in

    let ext_nodes_right = last_ext_nodes
    (*find last external nodes of left*)
    (*rename all nodes of right in order to avoid node_id collisions*)
    (*for each external node in right, rename it to the corresponding node in left*)
    (*identify the edges shared by free variables in right and left as well as the nodes they are incident on*)

    (*placeholder result*)
    Hypergraph []

(* failed attempt, might be able to recycle some stuff*)
(*type node =
    | Node of int

type 'a hyperedge =
    | Hyperedge of ('a lambda_term * int list)

    

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
(* given two node lists and a node, will return the node in the new_nodes list that corresponds to its
 * position in the old_nodes list*)
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
        Hyperedge (label, new_list)
    in
    List.map replace_nodes_edges hypergraph
    



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

(*removes duplicates from a list*)
let rec remove_duplicates = function 
    | [] -> []
    | hd::tl when List.mem hd tl -> remove_duplicates tl
    | hd::tl -> hd::(remove_duplicates tl)

(* given two terms under the same nb of lambda abstractions
 * returns a list of free variables that they have in common *)
let common_free_vars term_1 term_2 =
    let free_vars_1 = free_vars_in term_1 in
    let free_vars_2 = free_vars_in term_2 in
    remove_duplicates (free_vars_1 @ free_vars_2)

(* given a list of hyperedges, will return the first one found with the given label*)
let rec edge_from_label hyperedge_list label = match hyperedge_list with
    (* yes bc all i want to do rn is have to handle options yipee*)
    | [] -> None
    | hd::_ when fst hd = label -> Some(snd hd)
    | _::tl -> edge_from_label tl label


(* given a hyperedge and a hypegraph, will identify the hyperedge with the one (if there is one)
 * in the hypergraph, assumes that the labels are of terms under the same lambda abstraction *)
(* assumes that no two edges are labeled by the same term in the hyergraph *)
let rec identify_edge hyperedge hypergraph =
    let Hyperedge hedge = hyperedge in
    match hypergraph with
    | [] -> []
    | (Hyperedge hd) :: tl when fst hd = fst hedge ->
            let new_node_list = remove_duplicates ((snd hd)@(snd hedge)) in
            (* we can return because it is assumed no other edge will have the same label*)
            (Hyperedge (fst hd, new_node_list))::tl
    | (Hyperedge hd) :: tl -> (Hyperedge hd) :: (identify_edge hyperedge tl)

    

(* given two hypergraphs at the same lambda abstraction level
 * will identify the edges that have the same label*)
let fuse_hypergraphs hypergraph_1 hypergraph_2 =
    List.fold_left (fun graph edge -> identify_edge edge graph) hypergraph_1 hypergraph_2 
    
    
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
            
            let new_right_hyperg = replace_nodes last_left_nodes right_hyperg in

            fuse_hypergraphs new_right_hyperg left_hyperg

    | _ -> []*)
