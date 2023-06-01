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
    let Hyperedge(label_1, node_list_1) = he_1 in
    let Hyperedge(label_2, node_list_2) = he_2 in

    let rec ext_nodes_eq nl_1 nl_2 = match nl_1, nl_2 with
        | [], [] -> true
        | hd_1::tl_1, hd_2::tl_2 ->
                let res_tl = ext_nodes_eq tl_1 tl_2 in
                let Node(ext_1, _) = hd_1 in
                let Node(ext_2, _) = hd_2 in
                (ext_1 = ext_2) && res_tl
        | _ -> failwith "the hyperedges are incident on a different number of nodes"
    in

    (label_1 = label_2) && (ext_nodes_eq node_list_1 node_list_2)

(*simply applies previous function to all edges*)
(*requires that the edges be sorted according to their labels*)
let test_hypergraphs hg_1 hg_2 =
    let Hypergraph edge_list_1 = normalise_node_ranks hg_1 in
    let Hypergraph edge_list_2 = normalise_node_ranks hg_2 in

    let has_label label edge =
        let Hyperedge(edge_label, _) = edge in
        label = edge_label
    in

    let rec match_edges_labels el_1 el_2 = match el_1 with
        | [] -> []
        | Hyperedge(label_1, _)::tl ->
                let corresponding_edge = List.find (fun e -> has_label label_1 e) el_2 in
                corresponding_edge :: (match_edges_labels tl el_2)
    in

    let matching_edge_list_2 = match_edges_labels edge_list_1 edge_list_2 in

    List.fold_left2 (fun b e1 e2 -> b && (test_hyperedges e1 e2)) true edge_list_1 matching_edge_list_2


(*building terms*)
let aterm_1 = Datalog_reduction_module.Abs (
    (App (((BVar (0, Arrow (Atom 0, Atom 1)) ), Constant ("a", Atom 0)), Atom 1)),
    Arrow(Arrow(Atom 0, Atom 1), Atom 1))

let () =
    let hg_1 = hypergraph_of_term aterm_1 in
    let hg_2 = hypergraph_of_term aterm_1 in
    assert (test_hypergraphs hg_1 hg_2)
 
