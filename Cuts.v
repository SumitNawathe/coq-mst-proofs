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

Lemma subset_empty_is_empty : forall {T} (A: U_set T), A ⊂ ∅ -> A = ∅.
Proof.
	intros T A H_AT. apply U_set_eq. intros x; split; intros H; [auto | inversion H].
Qed.

Lemma self_inclusion : forall T (A : U_set T), A ⊂ A.
Proof. intros. unfold Included. auto. Qed.

Lemma set_minus_point_still_included :
	forall T (A : U_set T) (x : T), (A\⟨x⟩) ⊂ A.
Proof.
	intros. unfold Included. intros y H_differ.
	inversion H_differ; subst; clear H_differ. assumption.
Qed.

Lemma included_trans :
	forall T (A B C: U_set T), A ⊂ B -> B ⊂ C -> A ⊂ C.
Proof. intros T A B C H_AB H_BC. unfold Included. intros. auto. Qed.

Lemma not_Single_not_equal :
	forall (T : Set) (x y : T), y ∉ ⟨x⟩ -> x <> y.
Proof.
	intros. unfold not; intros H_xy.
	rewrite H_xy in H. apply H. constructor.
Qed.



(* Decideability axioms *)

Axiom decideable : forall P, {P} + {~P}.

Lemma vertex_subset_decideable :
	forall V E (G: Graph V E) A, A ⊂ V -> forall x, {x ∈ A} + {x ∉ A}.
Proof.
	intros. destruct (decideable (x ∈ A)); auto.
Qed.

Lemma pbc : forall P, (~P -> False) -> P.
Proof.
	intros. destruct (decideable P); solve [assumption | contradiction].
Qed.

Ltac proof_by_contradiction := apply pbc; match goal with
	| [ |- ~ (exists x, ?P x) -> False ] => idtac
end.

Lemma not_exists_elem : forall U (A: U_set U),
	~ (exists x, x ∈ A) -> (forall x, x ∉ A).
Proof.
	intros; intros H_Ax. apply H. exists x. assumption.
Qed.

(* Lemma is_empty_dec : forall T (A: U_set U), {A = ∅} + {A <> ∅}. *)



(* Subgraph/subtree definitions *)

Definition is_subgraph {V V' : V_set} {E E' : A_set} (G' : Graph V' E') (G : Graph V E) : Prop := 
    V' ⊂ V /\ E' ⊂ E.

Definition is_subtree {V V' : V_set} {E E' : A_set} (T : Tree V' E') (G : Graph V E) : Prop := 
    V' ⊂ V /\ E' ⊂ E.

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
	A ⊂ V /\ ~ trivial_cut G A.

Lemma nontrivial_cut_points :
	forall V E (G: Graph V E) A,
	nontrivial_cut G A <-> A ⊂ V /\ (exists x, x ∈ A) /\ (exists y, y ∈ V /\ y ∉ A).
Proof.
	intros. split; intros H.
	- inversion H as [H_AV H_A_nontriv].
		unfold not in H_A_nontriv. unfold trivial_cut in H_A_nontriv.
		split; [solve [assumption] | split].
		+ proof_by_contradiction. intros H_contra. apply H_contra.
			destruct (decideable (A = ∅)); try solve [exfalso; auto].
			exfalso. apply H_A_nontriv. auto.
			apply not_empty_iff_exists in n as [x H_Ax].
			exfalso. apply H_contra. exists x. assumption.
		+ destruct (decideable (A = V)); try solve [exfalso; auto].
			apply subset_but_not_equal; assumption.
	- destruct H as [H_AV [H1 H2]]. unfold nontrivial_cut. split; try solve [assumption].
		intros H_Gtriv. inversion H_Gtriv; subst; [destruct H2 | destruct H1]; intuition.
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
	apply nontrivial_cut_points in H_A_cut.
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

Lemma find_crossing_edge_on_walk :
    forall {V E} (G: Graph V E) A x z vl el,
    nontrivial_cut G A -> x ∈ A -> z ∉ A -> Walk V E x z vl el ->
    exists u v, edge_crossing_cut G A u v /\ exists vl1 el1 vl2 el2, (Walk V E x u vl1 el1 /|\ Walk V E v z vl2 el2).
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
			* assumption.
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
	Abort.

