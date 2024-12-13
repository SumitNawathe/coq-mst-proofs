Require Export MST.Graphs.
Require Export MST.Edges.
Require Export MST.Vertices.
Require Export MST.Trees.
Require Export MST.Connected.
Require Export MST.Sets.
Require Export MST.Cuts.
Require Export MST.CustomNotations.

Definition is_subgraph (V V' : V_set) (E E' : A_set) (T : Graph V' E') (G : Graph V E) : Prop := 
    V_included V' V /\ A_included E' E.

Definition is_subtree {V V' : V_set} {E E' : A_set} (T : Tree V' E') (G : Graph V E) : Prop := 
    V_included V' V /\ A_included E' E.

Definition is_spanning_tree {V V' : V_set} {E E' : A_set} (T : Tree V' E') (G : Graph V E) : Prop := 
    (V' = V) /\ (is_subtree T G).

Theorem connected_prop :
	forall {V E} (G: Graph V E), V <> V_empty ->
	(forall x y, V x -> V y -> {vl : V_list &  {el : E_list &  Walk V E x y vl el}}) ->
	Connected V E.
Proof. Admitted.

Fixpoint st_weight {V : V_set} {E : A_set} (T : Tree V E) (f: (A_set -> nat)) : nat :=
	match T with
	| T_root _ => 0
	| T_leaf _ _ T x y _ _ => f (E_set x y) + (st_weight T f)
	| T_eq V _ A _ _ _ T => (st_weight T f)
	end.

Definition is_MST (f : A_set -> nat) {V : V_set} {E E_T : A_set} (T : Tree V E_T) (G : Graph V E) :=
	is_subtree T G -> forall E_T' (T': Tree V E_T'), is_subtree T' G -> st_weight T f <= st_weight T' f.

(*
Definition nontrivial_cut {V : V_set} {E : A_set} (G: Graph V E) (A : V_set) : Prop :=
	A ⊂ V /\ ~ trivial_cut G A.
*)

(* 
Lemma MST_exists : forall (V : V_set) (E : A_set) (f : A_set -> nat) (G : Connected V E), exists (E_T : A_set) (T: Tree V E_T), is_MST f T G.
Proof. Admitted.
*)

(* Definition edge_crossing_cut {V : V_set} {E : A_set} (G : Graph V E) (A : V_set) (x y: Vertex) : Prop :=
	nontrivial_cut G A -> E (A_ends x y) /\ A x /\ ~ A y. *)

(* Definition prim_invar1 {V E} (G : Graph V E) {V' E'} (T : Tree V' E') w *)

(* Exchange argument *)
Lemma join_connected {V1 V2 : V_set} {E1 E2 : A_set} (G1 : Connected V1 E1) (G2 : Connected V2 E2) (x y : Vertex):
	V1 x -> V2 y -> Connected (V_union V1 V2) (A_union (E_set x y) (A_union E1 E2)).
Proof. Admitted.

Lemma join_cycle_free {V1 V2 : V_set} {E1 E2 : A_set} (G1 : Acyclic V1 E1) (G2 : Acyclic V2 E2) (u v : Vertex) : 
	V_inter V1 V2 = V_empty -> V1 u -> V2 v -> Acyclic (V_union V1 V2) (A_union (E_set u v) (A_union E1 E2)).
Proof. Admitted.

Lemma join_trees {V1 V2 : V_set} {E1 E2 : A_set} (T1 : Tree V1 E1) (T2 : Tree V2 E2) (u v : Vertex) : 
	V_inter V1 V2 = V_empty -> V1 u -> V2 v -> Tree (V_union V1 V2) (A_union (E_set u v) (A_union E1 E2)).
Proof. Admitted.

Lemma split_tree :
	forall {V E} (T: Tree V E) x y, A_included (E_set x y) E ->
	exists V1 V2 E1 E2 (T1 : Tree V1 E1) (T2 : Tree V2 E2),
	V_union V1 V2 = V /\ A_union E1 E2 = (E \ (E_set x y)) /\ V1 x /\ V2 y.
Proof. Admitted.

Lemma tree_has_edge_crossing_cut :
	forall {V E} (G : Graph V E) (T: Tree V E) (f: A_set -> nat) A,
	nontrivial_cut G A -> exists x y, edge_crossing_cut G A x y.
Proof. Admitted.

Lemma tree_edge_crossing_cut_unique :
	forall {V E} (G : Graph V E) (T: Tree V E) (f: A_set -> nat) A, nontrivial_cut G A ->
	forall x y u v, edge_crossing_cut G A x y -> edge_crossing_cut G A u v ->
	(x ~~ y) = (u ~~ v).
Proof. Admitted.

(* Assume edge weights are unique *)
Definition light_edge {V E} (G: Graph V E) A x y (w : A_set -> nat) :=
	edge_crossing_cut G A x y /\ (forall u v, edge_crossing_cut G A u v -> w (E_set x y) < w (E_set u v)).

Definition is_subset_MST {V V_T: V_set} {E E_T: A_set} (w : A_set -> nat) (T : Tree V_T E_T) (G : Graph V E) :=
	exists E_MST (MST : Tree V E_MST), is_MST w MST G /\ A_included E_T E_MST /\ V_included V_T V.

Theorem light_edge_is_safe :
	forall {V E} (G: Graph V E) (C: Connected V E) {V' E'} (T : Tree V' E') x y w,
	is_subset_MST w T G -> light_edge G V' x y w ->
	{ T' : Tree (V_union (V_single y) V') (A_union (E_set x y) E') & is_subset_MST w T' G }.
Proof. Admitted.

Theorem prim_ends :
	forall {V E} (G: Graph V E) (C: Connected V E) {E'} (T : Tree V E') w,
	is_subset_MST w T G -> is_MST w T G.
Proof. intros. unfold is_MST. intros.





(* 
Approach 1:
- join trees
- split trees

Approach 2:
- show that m=n-1 and connected -> tree
- show that walk between any two points -> connected (1/2 done)
 *)




