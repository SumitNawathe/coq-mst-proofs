Require Export Coq.Init.Specif.
Require Export MST.Graphs.
Require Export MST.Edges.
Require Export MST.Vertices.
Require Export MST.Trees.
Require Export MST.Connected.
Require Export MST.Sets.
Require Export MST.CustomNotations.
Require Export MST.Logic.
Require Export MST.SetLogic.

Open Scope uset_scope.


(* Useful theorems on sets *)

Lemma subset_empty_is_empty : forall {T} (A: U_set T), A ⊆ ∅ -> A = ∅.
Proof.
	intros T A H_AT. apply U_set_eq. intros x; split; intros H; [auto | inversion H].
Qed.

Lemma self_inclusion : forall T (A : U_set T), A ⊆ A.
Proof. intros. unfold Included. auto. Qed.

Lemma set_minus_point_still_included :
	forall T (A : U_set T) (x : T), (A\⟨x⟩) ⊆ A.
Proof.
	intros. unfold Included. intros y H_differ.
	inversion H_differ; subst; clear H_differ. assumption.
Qed.

Lemma included_trans :
	forall T (A B C: U_set T), A ⊆ B -> B ⊆ C -> A ⊆ C.
Proof. intros T A B C H_AB H_BC. unfold Included. intros. auto. Qed.

Lemma not_Single_not_equal :
	forall (T : Set) (x y : T), y ∉ ⟨x⟩ -> x <> y.
Proof.
	intros. unfold not; intros H_xy.
	rewrite H_xy in H. apply H. constructor.
Qed.



(* Subgraph/subtree definitions *)

Definition is_subgraph {V V' : V_set} {E E' : A_set} (G' : Graph V' E') (G : Graph V E) : Prop := 
    V' ⊆ V /\ E' ⊆ E.

Definition is_subtree {V V' : V_set} {E E' : A_set} (T : Tree V' E') (G : Graph V E) : Prop := 
    V' ⊆ V /\ E' ⊆ E.

Lemma is_subtree_implies_is_subgraph :
	forall V V' E E' (T : Tree V' E') (G' : Graph V' E') (G : Graph V E),
	is_subtree T G -> is_subgraph G' G.
Proof.
	intros. inversion H as [HV HE].
	unfold is_subgraph. split; trivial.
Qed.



(* Spanning definitions *)

Definition is_spanning {V V' : V_set} {E E' : A_set} (G' : Graph V' E') (G : Graph V E) : Prop := 
  (V' = V) /\ (is_subgraph G' G).

Definition is_spanning_tree (V V' : V_set) (E E' : A_set) (T : Tree V' E') (G : Graph V E) : Prop := 
  (V' = V) /\ (is_subtree T G).



(* Unrelated lemma (can probably be removed) *)

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



(* Nontrivial cut definition *)

Definition trivial_cut {V : V_set} {E : A_set} (G: Graph V E) (A : V_set) : Prop :=
	A = V \/ A = ∅.

Definition nontrivial_cut {V : V_set} {E : A_set} (G: Graph V E) (A : V_set) : Prop :=
	A ⊆ V /\ ~ trivial_cut G A.

Lemma nontrivial_cut_point_inside :
	forall V E (G: Graph V E) A,
	nontrivial_cut G A -> {x & x ∈ A}.
Proof.
	intros.
	inversion H as [H_AV H_A_nontriv].
	unfold not in H_A_nontriv. unfold trivial_cut in H_A_nontriv.
	case (set_eq_dec A (∅)); intros H_A1; try solve [exfalso; apply H_A_nontriv; auto].
	apply (not_empty_iff_exists) in H_A1. assumption.
Qed.

Lemma nontrivial_cut_point_outside :
	forall V E (G: Graph V E) A,
	nontrivial_cut G A -> {y & y ∈ V & y ∉ A}.
Proof.
	intros.
	inversion H as [H_AV H_A_nontriv].
	unfold not in H_A_nontriv. unfold trivial_cut in H_A_nontriv.
	case (set_eq_dec A V); intros H_A2; try solve [exfalso; apply H_A_nontriv; auto].
	specialize (subset_but_not_equal _ _ _ H_AV H_A2) as H'. assumption.
Qed.

Lemma points_nontrivial_cut :
	forall V E (G: Graph V E) A x y,
	A ⊆ V -> x ∈ A -> y ∈ V -> y ∉ A -> nontrivial_cut G A.
Proof.
	intros V E G A x y H_AV H_Ax H_Vy H_not_Ay.
	split; try solve [assumption].
	intros H_Atriv. destruct H_Atriv as [H_A1 | H_A2]; subst; contradiction.
Qed.



(* Finding edges crossing cut *)

Definition edge_crossing_cut {V : V_set} {E : A_set} (G : Graph V E) (A : V_set) (x y: Vertex) : Prop :=
	nontrivial_cut G A -> E (A_ends x y) /\ A x /\ ~ A y.

Lemma connected_graph_has_edge_crossing_cut :
	forall V E (G: Graph V E), Connected V E ->
	forall A, nontrivial_cut G A ->
	exists u v, edge_crossing_cut G A u v.
Proof.
	intros V E G H_connected A H_A_cut.
	(* Since A nontrivial, get vertex x in A and y not in A *)
	destruct (nontrivial_cut_point_inside V E G A H_A_cut) as [x H_Ax].
	destruct (nontrivial_cut_point_outside V E G A H_A_cut) as [y H_Vy H_not_Ay].
	destruct H_A_cut as [H_VA H_A_nontriv].
	apply H_VA in H_Ax as H_Vx.
	(* Get path between these vertices *)
	specialize (Connected_path V E H_connected x y H_Vx H_Vy) as [vl [el H_path]].
	generalize dependent el. generalize dependent y. generalize dependent x.
	induction vl as [|h t]; intros; inversion H_path; subst; clear H_path.
	- (* path is nil -> x = y, but x in A and y not in A -> contradiction *)
	   contradiction.
	- (* case analysis: does edge x--h cross the cut *)
	  (* case (Vset_dec A h); intros H_Ah. *)
	  	case (decideability (h ∈ A)); intros H_Ah.
	  + apply H_VA in H_Ah as H_Vh.
	  	apply (IHt h H_Ah H_Vh y H_Vy H_not_Ay el0 H1).
		+ exists x. exists h.
			unfold edge_crossing_cut; intros H_A_nontrivial.
			split; try split; assumption.
Qed.

Lemma find_crossing_edge_on_walk :
    forall {V E} (G: Graph V E) A x z vl el,
    nontrivial_cut G A -> x ∈ A -> z ∉ A -> Walk V E x z vl el ->
    exists u v, edge_crossing_cut G A u v /\
		exists vl1 el1 vl2 el2 (walk1 : Walk V E x u vl1 el1) (walk2 : Walk V E v z vl2 el2), True.
Proof.
	intros V E G A x z vl. generalize dependent z. generalize dependent x.
	induction vl as [|h t]; intros x z el H_A_nontrivial H_Ax H_nAz H_walk;
	inversion H_walk; subst; try solve [contradiction].
	case (decideability (h ∈ A)); [intros H_Ah | intros H_nAh].
	- (* h ∈ A -> cross in later part of walk *)
		specialize (IHt h z el0 H_A_nontrivial H_Ah H_nAz H1) as H.
		inversion H as [u [v [H_cross [vl1 [el1 [vl2 [el2 [H_walk1 H_walk2]]]]]]]].
		exists u. exists v. split; try solve [assumption].
		exists (h::vl1). exists ((x ~~ h)::el1). exists vl2. exists el2.
		split; try solve [simpl; apply f_equal; assumption].
		+ constructor 2; try solve [assumption].
		+ assumption.
	- (* h ∉ A -> x -- h is the cross *)
		exists x. exists h. split.
		+ constructor.
			* assumption.
			* split; assumption.
		+ exists nil. exists nil. exists t. exists el0. split.
			* constructor. assumption.
			* exists H1. trivial.
Qed.



Lemma tree_has_edge_crossing_cut :
	forall {V GE E} (G : Graph V GE) (T: Tree V E) A, nontrivial_cut G A ->
	{x: Vertex & {y: Vertex & (x -- y) ∈ E /\ edge_crossing_cut G A x y}}.
Proof.
	intros.
	specialize (Tree_isa_connected _ _ T) as Tcon.
	(* apply (nontrivial_cut_points) in H.
	destruct H as [H_AV [H_Ax H_Ay]]. *)
Admitted.







Lemma tree_edge_crossing_cut_unique :
	forall {V GE E} (G : Graph V GE) (T: Tree V E) A, nontrivial_cut G A ->
	forall x y u v, edge_crossing_cut G A x y -> edge_crossing_cut G A u v ->
	x = u /\ y = v.
Proof. Admitted.