Require Export MST.Graphs.
Require Export MST.Edges.
Require Export MST.Vertices.
Require Export MST.Trees.
Require Export MST.Connected.
Require Export MST.Sets.

Definition is_subgraph (V V' : V_set) (E E' : A_set) (T : Graph V' E') (G : Graph V E) : Prop := 
    V_included V' V /\ A_included E' E.

Definition is_subtree {V V' : V_set} {E E' : A_set} (T : Tree V' E') (G : Graph V E) : Prop := 
    V_included V' V /\ A_included E' E.

Definition is_spanning_tree {V V' : V_set} {E E' : A_set} (T : Tree V' E') (G : Graph V E) : Prop := 
    (V' = V) /\ (is_subtree T G).

(* Really inconvienent to have types for paths, walks, connected graphs, cycles etc. Define propositional statements instead. *)
(* Also, need lemmas that show equivalence between propositions and types. *)

Definition is_connected {V : V_set} {E : A_set} (G : Graph V E) := 
	forall (x y : Vertex), V x -> V y -> x <> y -> (Path V E x y (GV_list V E G) (GE_list V E G)).

Lemma connected_if : forall (V : V_set) (E : A_set) (G : Graph V E), is_connected G -> Connected V E. 
Proof. Admitted.

Lemma connected_onlyif : forall (V : V_set) (E : A_set) (G : Graph V E), Connected V E -> is_connected G.
Proof. Admitted.

Fixpoint st_weight {V : V_set} {E : A_set} (T : Tree V E) (f: (A_set -> nat)) : nat :=
	match T with
	| T_root _ => 0
	| T_leaf _ _ T x y _ _ => f (E_set x y) + (st_weight T f)
	| T_eq V _ A _ _ _ T => (st_weight T f)
	end.

Definition is_MST (f : A_set -> nat) {V : V_set} {E E_T : A_set} (T : Tree V E_T) (G : Graph V E) :=
	is_subtree T G -> forall E_T' (T': Tree V E_T'), is_subtree T' G -> st_weight T f <= st_weight T' f.

(* Really inconvienent to have types for paths, walks, connected graphs, cycles etc. Define propositional statements instead. *)

Lemma MST_exists : forall (V : V_set) (E : A_set) (f : A_set -> nat) (G : Connected V E), exists (E_T : A_set) (T: Tree V E_T), is_MST f T G.
Proof.

(* Algorithm: subgraph starts with one node. Every iteration, add a node maintaining that 
A is a subgraph of a MST, and A stays a tree. *)

Definition is_subset_MST {V : V_set} {A E E_T: A_set} (f : A_set -> nat) (G : Graph V E) :=
	exists (T : Tree V E_T), is_MST f T G /\ A_included A E_T.








