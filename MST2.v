Require Export MST.Graphs.
Require Export MST.Edges.
Require Export MST.Vertices.
Require Export MST.Trees.
Require Export MST.Connected.
Require Export MST.Sets.



Definition is_subgraph {V V' : V_set} {E E' : A_set} (G' : Graph V' E') (G : Graph V E) : Prop := 
    V_included V' V /\ A_included E' E.

Definition is_subtree {V V' : V_set} {E E' : A_set} (T : Tree V' E') (G : Graph V E) : Prop := 
    V_included V' V /\ A_included E' E.

Lemma is_subtree_implies_is_subgraph :
	forall V V' E E' (T : Tree V' E') (G' : Graph V' E') (G : Graph V E),
	is_subtree T G -> is_subgraph G' G.
Proof.
	intros. inversion H as [HV HE].
	unfold is_subgraph. split; trivial.
Qed.



Definition is_spanning {V V' : V_set} {E E' : A_set} (G' : Graph V' E') (G : Graph V E) : Prop := 
    (V' = V) /\ (is_subgraph G' G).

Definition is_spanning_tree (V V' : V_set) (E E' : A_set) (T : Tree V' E') (G : Graph V E) : Prop := 
    (V' = V) /\ (is_subtree T G).



(* Lemma weight_functions_good : forall V E (T: Tree V E) (f: (A_set -> nat)) x y, f (E_set x y) = f (E_set y x).
Proof.
	intros. apply f_equal. apply E_set_eq.
Qed. *)
Fixpoint st_weight {V : V_set} {E : A_set} (T : Tree V E) (f: (A_set -> nat)) : nat :=
	match T with
	| T_root _ => 0
	| T_leaf _ _ T x y _ _ => f (E_set x y) + (st_weight T f)
	| T_eq V _ A _ _ _ T => (st_weight T f)
	end.


Definition nontrivial_cut {V : V_set} {E : A_set} (G : Graph V E) (A : V_set) : Prop :=
	V_included A V /\ (exists x, A x) /\ (exists y, V y /\ ~ A y).

Definition edge_crossing_cut {V : V_set} {E : A_set} (G : Graph V E) (A : V_set) (x y: Vertex) : Prop :=
	nontrivial_cut G A -> E (A_ends x y) /\ A x /\ ~ A y.

(* TODO: needed? note, Vertex is not a finite type *)
Axiom Vset_dec : forall (V: V_set) (x: Vertex), {V x} + {~ V x}.

Lemma connected_graph_has_edge_crossing_cut :
	forall V E (G: Graph V E), Connected V E ->
	forall A, nontrivial_cut G A ->
	exists u v, edge_crossing_cut G A u v.
Proof.
	intros V E G H_connected A H_A_cut.
	(* Since A nontrivial, get vertex x in A and y not in A *)
	destruct H_A_cut as [H_VA [[x H_Ax] [y [H_Vy H_not_Ay]]]].
	apply H_VA in H_Ax as H_Vx.
	(* Get path between these vertices *)
	specialize (Connected_path V E H_connected x y H_Vx H_Vy) as [vl [el H_path]].
	generalize dependent el. generalize dependent y. generalize dependent x.
	induction vl as [|h t]; intros; inversion H_path; subst; clear H_path.
	- (* path is nil -> x = y, but x in A and y not in A -> contradiction *)
	   contradiction.
	- (* case analysis: does edge x--h cross the cut *)
	  case (Vset_dec A h); intros H_Ah.
	  + apply H_VA in H_Ah as H_Vh.
	  	apply (IHt h H_Ah H_Vh y H_Vy H_not_Ay el0 H1).
		+ exists x. exists h.
			unfold edge_crossing_cut; intros H_A_nontrivial. split; try split; assumption.
Qed.









Section MST2.

Variable f: Vertex -> nat.




