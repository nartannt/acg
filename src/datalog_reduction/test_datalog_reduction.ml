open Datalog_reduction_module
open Lambda_calc_module


let normalise_node_ranks hypergraph =
    let ext_nodes = last_ext_nodes (-1) hypergraph in
    
    let generate_new_nodes ext_node_list =
        let rec renumber_ranks curr_rank node_list = match node_list with
            | [] -> []
            | Node(_, node_id)::tl ->
                    Node(curr_rank+1, node_id)::(renumber_ranks (curr_rank+1) tl)
        in
        renumber_ranks 0 ext_node_list
    in

    let new_nodes = generate_new_nodes ext_nodes in

    identify_nodes ext_nodes new_nodes hypergraph
        

(*assuming that the ranks have been normalised*)
(* whilst this function only guarantees that the given edges are incident on external nodes of the
 * same rank*)
let test_hyperedges he_1 he_2 =
    (*print_string "begin hyperedge comparison\n";*)
    let Hyperedge(label_1, node_list_1) = he_1 in
    print_term label_1;
    (match label_1 with | Constant c -> print_string (" " ^ c^"\n"); | _ -> (););
    let Hyperedge(label_2, node_list_2) = he_2 in

    let rec ext_nodes_eq nl_1 nl_2 = match nl_1, nl_2 with
        | [], [] -> true
        | hd_1::tl_1, hd_2::tl_2 ->
                let res_tl = ext_nodes_eq tl_1 tl_2 in
                let Node(ext_1, _) = hd_1 in
                let Node(ext_2, _) = hd_2 in
                (*print_int ext_2;
                print_string "\n";*)
                (*if ext_1 != ext_2 then print_string "nodes not equal when they should\n";*)
                (ext_1 = ext_2) && res_tl
        | _ -> failwith "the hyperedges are incident on a different number of nodes"
    in
    
    (*print_string "perhaps the labels have a pb\n";*)
    if not (alpha_eq label_1 label_2) then print_string "labels aren't equal\n";

    (*print_term label_1;
    print_string "\n";
    print_term label_2;
    print_string "\n";*)

    (*begin
    match label_1, label_2 with
        | Constant c1, Constant c2 -> print_string ("c1: " ^ c1 ^ ", c2: " ^ c2 ^ "\n");
        | _ -> ();
    end;*)

    (alpha_eq label_1 label_2) && (ext_nodes_eq node_list_1 node_list_2)

(*simply applies previous function to all edges*)
(*requires that the edges be sorted according to their labels*)
let test_hypergraphs hg_1 hg_2 =
    let Hypergraph edge_list_1 = normalise_node_ranks hg_1 in
    let Hypergraph edge_list_2 = normalise_node_ranks hg_2 in

    List.iter print_edge edge_list_1;

    (*print_string "list length: ";
    print_int (List.length edge_list_1);
    print_string "\n";*)
    
    let has_label label edge =
        let Hyperedge(edge_label, _) = edge in
        label = edge_label
    in

    (* will return a permutation of el_1 such that the label of its nodes correspond to those of el_2*)
    let rec match_edges_labels el_1 el_2 = match el_2 with
        | [] -> []
        | Hyperedge(label_2, _)::tl ->
                let corresponding_edge = List.find (fun e -> has_label label_2 e) el_1 in
                corresponding_edge :: (match_edges_labels el_1 tl)
    in

    let rec _print_labels l = match l with
        | [] -> ()
        | Hyperedge(label, _)::tl ->
            print_string "label: ";
            print_term label;
            print_string "\n";
            _print_labels tl
    in


    let matching_edge_list_1 = match_edges_labels edge_list_1 edge_list_2 in
    
    (*_print_labels edge_list_2;
    print_string "--- \n";
    _print_labels matching_edge_list_1;*)
    
    (*print_string "so far so good\n";*)

    List.fold_left2 (fun b e1 e2 -> b && (test_hyperedges e1 e2)) true edge_list_2 matching_edge_list_1


(*building terms*)
let aterm_1 = Datalog_reduction_module.Abs (
    (App (((BVar (0, Arrow (Atom 0, Atom 1)) ), Constant ("a", Atom 0)), Atom 1)),
    Arrow(Arrow(Atom 0, Atom 1), Atom 1))

let x1_aterm = Datalog_reduction_module.App(
    (Constant ("X1", Arrow(Arrow(Atom "e", Atom "e"), Atom "t")), BVar (1, Atom "e")),
    Arrow(Atom "e", Atom "t"))

let x2_aterm = Datalog_reduction_module.App(
    (Constant ("X2", Arrow(Arrow(Atom "e", Atom "e"), Atom "t")), BVar (1, Atom "e")),
    Arrow(Atom "e", Atom "t"))

let _x1_hgraph = Hypergraph [
    Hyperedge (Constant "X1", [Node(1, 1); Node(2, 2); Node(0, 3)]);
    Hyperedge (BVar 1, [Node(0, 3)])
    ]

let _x2_hgraph = Hypergraph [
    Hyperedge (Constant "X2", [Node(1, 1); Node(2, 2); Node(0, 3)]);
    Hyperedge (BVar 1, [Node(0, 3)])
    ]

let x1_app = Datalog_reduction_module.App(
    (x1_aterm, BVar (0, Atom "e")),
    (Atom "t"))

let x2_app = Datalog_reduction_module.App(
    (* TODO have multiple occurences of the same free var in a term (if it is of atomic type obviously) *)
    (* the bug associated with that should have been fixed but a test still needs to be written*)
    (x2_aterm, BVar (0, Atom "e")),
    (Atom "t"))

let and_const = Datalog_reduction_module.Constant ("land", Arrow(Arrow(Atom "t", Atom "t"), Atom "t"))

let and_app = Datalog_reduction_module.App(
    (App((and_const, x1_app), Arrow(Atom "t", Atom "t" )), x2_app),
    (Atom "t"))

let and_abs = Datalog_reduction_module.Abs(
    Abs(and_app, Arrow(Atom "e", Atom "t")), Arrow(Arrow (Atom "e", Atom "e"), Atom "t"))

let and_abs_hg = Hypergraph [
    Hyperedge (Constant "land", [Node(1, 1); Node(0, 2); Node(0, 3)]);
    Hyperedge (Constant "X1", [Node(0, 3); Node(2, 4); Node(3, 5)]);
    Hyperedge (Constant "X2", [Node(0, 2); Node(2, 4); Node(3, 5)]);
    Hyperedge (BVar 0, [Node(2, 4)]);
    Hyperedge (BVar 1, [Node(3, 5)])]


let () =
    let _hg_x1 = hypergraph_of_term x1_aterm in
    (*assert (test_hypergraphs hg_x1 x1_hgraph);*)
    let hg_and_abs = hypergraph_of_term and_abs in
    assert (test_hypergraphs hg_and_abs and_abs_hg)

let () =
    let hg_1 = hypergraph_of_term aterm_1 in
    let hg_2 = hypergraph_of_term aterm_1 in
    assert (test_hypergraphs hg_1 hg_2)
 
