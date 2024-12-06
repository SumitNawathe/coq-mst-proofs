Require Export MST.Graphs.
Require Export MST.Edges.
Require Export MST.Vertices.
Require Export MST.Trees.
Require Export MST.Connected.
Require Export MST.Sets.
Require Export Coq.Init.Specif.



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



Lemma included_in_empty_means_empty : forall T (A: U_set T), Included T A (Empty T) -> A = Empty T.
Proof.
	intros T A H_AT. apply U_set_eq. intros x; split; intros H; [auto | inversion H].
Qed.

Lemma self_includes_self : forall T (A : U_set T), Included T A A.
Proof.
	intros. unfold Included. auto.
Qed.

Lemma set_minus_point_still_included :
	forall T (A : U_set T) (x : T), Included T (Differ T A (Single T x)) A.
Proof.
	intros. unfold Included. intros y H_differ.
	inversion H_differ; subst; clear H_differ. assumption.
Qed.

Lemma included_trans :
	forall T A B C, Included T A B -> Included T B C -> Included T A C.
Proof.
	intros T A B C H_AB H_BC. unfold Included. intros. auto.
Qed.

Lemma not_Single_not_equal :
	forall T x y, ~ Single T x y -> x <> y.
Proof.
	intros. unfold not; intros H_xy.
	rewrite H_xy in H. apply H. constructor.
Qed.




(* Axiom Vset_dec : forall (V: V_set) (x: Vertex), {V x} + {~ V x}. *)
Lemma vertex_subset_decideable :
	forall V E (G: Graph V E) A, V_included A V -> forall x, {A x} + {~ A x}.
Proof.
	Admitted.

Lemma being_part_of_graph_means_enumerable :
	forall V E (G : Graph V E), V_enumerable V.
Proof.
	intros. induction G.
	- unfold V_enumerable. unfold U_enumerable.
		apply exist with (x := nil). intros x H. inversion H.
	- inversion IHG as [vl Hvl].
		exists (x::vl). intros y Hy.
		case (V_eq_dec y x); intros H_xy.
		+ rewrite H_xy. unfold In; left; reflexivity.
		+ assert (H_Vy : v y). {
				unfold V_union in Hy. destruct Hy; subst.
				- inversion H; subst; clear H. contradiction.
				- assumption.
			}
			 apply (Hvl y) in H_Vy.
			 unfold In; right. apply H_Vy.
	- assumption.
	- subst; assumption.
Qed.


Lemma enumerable_means_equiv_list :
	forall T A, U_enumerable T A -> exists l, forall x, In x l <-> A x.
Proof.
	intros T A H_Aenum.
	inversion H_Aenum as [l Hl].
	generalize dependent A. induction l as [|h t Ht]; intros.
	- exists nil; split.
		+ intros H; inversion H.
		+ intros H_Ax. auto.
	- 


(* Lemma included_in_enumerable_means_enumerable :
	forall T A B, U_enumerable T A -> Included T B A -> U_enumerable T B.
Proof.
	intros T A B H_Aenum H_BA. unfold U_enumerable.
	inversion H_Aenum as [Avl HAvl].
	generalize dependent B. generalize dependent A. induction Avl as [|h t]; intros.
	- exists nil. intros x HBx. auto.
	-  *)
	


(* Lemma enumerable_means_can_be_graph :
	forall V, V_enumerable V -> Graph V A_empty.
Proof.
	intros. induction H as [vl Hvl].
	induction vl as [|h t].
	- assert (H_V_empty : V = V_empty). {
			apply V_set_eq. split; intros Hx.
			- apply Hvl in Hx. inversion Hx.
			- inversion Hx.
		}
		rewrite H_V_empty. constructor.
	- 


	intros. inversion H as [vl Hvl].
	generalize dependent V. induction vl as [|h t]; intros.
	- assert (H_V_empty : V = V_empty). {
			apply V_set_eq. split; intros Hx.
			- apply Hvl in Hx. inversion Hx.
			- inversion Hx.
		}
		rewrite H_V_empty. constructor.
	- eapply G_vertex. *)


(* Alternate proof strategy: prove the following, then use the fact that any
V_set that's part of a graph is decideable *)
(* Lemma cut_induces_isolated_graph :
	forall V E (G : Graph V E) A, V_included A V -> Graph A A_empty.
Proof.
	intros V E G. induction G; intros.
	- (* A subset of empty set -> A is empty *)
		apply included_in_empty_means_empty in H. rewrite H. constructor.
	- (* case of adding vertex x: apply IH to A - {x} *)
		specialize IHG with (A := V_differ A (V_single x)) as IHG'.
		assert (H_A_minus_x_in_V : V_included (V_differ A (V_single x)) v). {
			unfold V_included. unfold Included. intros y Hy.
			unfold V_differ in Hy. inversion Hy; subst; clear Hy.
			unfold V_single in H1. apply not_Single_not_equal in H1.
			unfold V_included in H. unfold Included in H.
			specialize (H y) as Hy. apply Hy in H0; clear Hy.
			unfold V_union in H0. inversion H0; subst; clear H0.
			- inversion H2. contradiction.
			- assumption.
		}
		apply IHG' in H_A_minus_x_in_V as H_graph_diff.



	- apply (G_minus_vertex (V_union (V_single x) v) A_empty) with (x := x).
		+ assert (H_V_includes_V : V_included v v) by apply self_includes_self.
			assert (H_graph_V_Aempty : Graph v A_empty). { apply IHG. assumption. }
			constructor; assumption.
		+ unfold V_union. constructor. unfold V_single. constructor.
		+ intros y H'. inversion H'.
		+  *)



Definition nontrivial_cut {V : V_set} {E : A_set} (G : Graph V E) (A : V_set) : Prop :=
	V_included A V /\ (exists x, A x) /\ (exists y, V y /\ ~ A y).

(* Lemma trivial_cut_all_or_none :
	forall V E (G : Graph V E) (A : V_set),
	~ nontrivial_cut G A -> A = V \/ A = V_empty.
Proof.
	intros.
	unfold nontrivial_cut in H.
	
	destruct (V_eq_dec A V_empty). *)

Definition edge_crossing_cut {V : V_set} {E : A_set} (G : Graph V E) (A : V_set) (x y: Vertex) : Prop :=
	nontrivial_cut G A -> E (A_ends x y) /\ A x /\ ~ A y.


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
	  (* case (Vset_dec A h); intros H_Ah. *)
		case (vertex_subset_decideable V E G A H_VA h); intros H_Ah.
	  + apply H_VA in H_Ah as H_Vh.
	  	apply (IHt h H_Ah H_Vh y H_Vy H_not_Ay el0 H1).
		+ exists x. exists h.
			unfold edge_crossing_cut; intros H_A_nontrivial.
			split; try split; assumption.
Qed.



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

Definition MST (f : A_set -> nat) {V : V_set} {E E_T : A_set} (T : Tree V E_T) (G : Graph V E) :=
	is_subtree T G -> forall E_T' (T': Tree V E_T'), is_subtree T' G -> st_weight T f <= st_weight T' f.



Theorem graph_cut_theorem :
	forall V E (G: Graph V E) A, nontrivial_cut G A ->
	forall (f: A_set -> nat) x y, edge_crossing_cut G A x y ->
	(forall x' y', edge_crossing_cut G A x' y' -> f (E_set x y) < f (E_set x' y')) ->
	forall (T : Tree V E), MST f T G -> E (A_ends x y).
Proof.
	intros V E G A H_A_nontriv f x y H_xy_cross_A B_xy_smallest T H_T_MST.

