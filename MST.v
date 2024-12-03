Require Export MST.Graphs.
Require Export MST.Edges.
Require Export MST.Vertices.
Require Export MST.Trees.

Section Weighted.

Inductive WeightedArc : Set := 
    WA_ends : nat -> Vertex -> Vertex -> WeightedArc.

Definition WA_set := U_set WeightedArc.

Definition WA_empty := Empty WeightedArc.

Definition WA_union := Union WeightedArc.

Definition WA_included := Included WeightedArc.

(* Could generalize the existing definitions polymorphically with weighted arcs, but this avoids breaking anything *)
(* Also may need to reprove some theorems provided *)

Inductive WE_set (n : nat) (x y : Vertex) : WA_set :=
    | WE_right : WE_set n x y (WA_ends n x y)
    | WE_left : WE_set n x y (WA_ends n y x).

Inductive WeightedGraph : V_set -> WA_set -> Set := 
    | WG_empty : WeightedGraph V_empty WA_empty 
    | WG_vertex : forall (v : V_set) (wa : WA_set) (d : WeightedGraph v wa) (x : Vertex), 
        ~ v x -> WeightedGraph (V_union (V_single x) v) wa
    | WG_edge :
      forall (v : V_set) (wa : WA_set) (d : WeightedGraph v wa) (x y : Vertex) (n : nat),
      v x ->
      v y ->
      x <> y ->
      ~ wa (WA_ends n x y) -> ~ wa (WA_ends n y x) -> WeightedGraph v (WA_union (WE_set n x y) wa)
    | WG_eq :
        forall (v v' : V_set) (wa wa' : WA_set),
        v = v' -> wa = wa' -> WeightedGraph v wa -> WeightedGraph v' wa'.

Inductive WeightedTree : V_set -> WA_set -> Set := 
    | WT_root : forall r : Vertex, WeightedTree (V_single r) WA_empty
    (* A leaf node is the union between an existing tree and a single node l, with a single arc connecting *)
    | WT_leaf : forall (v : V_set) (wa : WA_set) (t : WeightedTree v wa) (l x : Vertex) (n : nat), 
        v x -> ~ v l -> WeightedTree (V_union (V_single l) v) (WA_union (WE_set n x l) wa)
    | WT_eq : forall (v v' : V_set) (wa wa' : WA_set), 
        v = v' -> wa = wa' -> WeightedTree v wa -> WeightedTree v' wa'.

(* A subgraph contains a subset of the edges of a graph G. TODO: is this definition correct? *)
Definition is_subgraph (V V' : V_set) (E E' : WA_set) (T : WeightedGraph V' E') (G : WeightedGraph V E) : Prop := 
    WA_included E' E.

Definition is_subgraph_tree (V V' : V_set) (E E' : WA_set) (T : WeightedTree V' E') (G : WeightedGraph V E) : Prop := 
    WA_included E' E.

(* A spanning graph contains all vertices of G *)
Definition is_spanning (V V' : V_set) (E E' : WA_set) (T : WeightedGraph V' E') (G : WeightedGraph V E) : Prop := 
    (V' = V) /\ (is_subgraph V V' E E' T G).

Definition is_spanning_tree (V V' : V_set) (E E' : WA_set) (T : WeightedTree V' E') (G : WeightedGraph V E) : Prop := 
    (V' = V) /\ (is_subgraph_tree V V' E E' T G).

(* Function that gets the total edge weight of a tree *)
Fixpoint total_tree_EW (V : V_set) (WA : WA_set) (T : WeightedTree V WA) : nat := 
    match T with 
    | WT_root r => 0 
    | WT_leaf V' WA' T' l x n _ _ => n + total_tree_EW V' WA' T'
    | WT_eq V' _ WA' _ _ _ T' => total_tree_EW V' WA' T'
    end.

Definition root: WeightedTree (V_single (index 1)) (WA_empty) := 
    WT_root (index 1).

(* Need this to show that vertex 2 is NOT in the vertex set {vertex 1} *)
Definition ex_not_in : ~ (V_single (index 1)) (index 2).
Proof. Admitted. 
Definition root1leaf :=
    WT_leaf (V_single (index 1)) (WA_empty) root (index 2) (index 1) 5 (V_in_single (index 1)) (ex_not_in).

Example test1: total_tree_EW (V_union (V_single (index 2)) (V_single (index 1))) 
                      (WA_union (WE_set 5 (index 1) (index 2)) WA_empty) 
                      root1leaf = 5.
Proof. reflexivity. Qed.

(* A tree is a MST of a graph if out of possible subsets of edges, T is a spanning tree that has weight 
<= all other spanning trees. 

TODO: might be cleaner if we provide a inductive definition for SpanningTree.
*)
Definition is_MST (V V' : V_set) (WA WA': WA_set) (T : WeightedTree V' WA') (G : WeightedGraph V WA) : Prop := 
    is_spanning_tree V V' WA WA' T G -> forall WA'' : WA_set, WA_included WA'' WA -> forall T' : WeightedTree V' WA'', is_spanning_tree V V' WA WA'' T' G -> total_tree_EW V' WA' T <= total_tree_EW V' WA'' T'.
End Weighted.
