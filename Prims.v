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
	is_subtree T G /\ forall E_T' (T': Tree V E_T'), is_subtree T' G -> st_weight T f <= st_weight T' f.

(*
Definition nontrivial_cut {V : V_set} {E : A_set} (G: Graph V E) (A : V_set) : Prop :=
	A ⊆ V /\ ~ trivial_cut G A.
*)
 
Lemma MST_exists : forall (V : V_set) (E : A_set) (f : A_set -> nat) (G : Graph V E) (C : Connected V E), exists (E_T : A_set) (T: Tree V E_T), is_MST f T G.
Proof. Admitted.

(* Edge weight unique -> unique MST *)

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
	V1 ∩ V2 = ∅ /\ V1 ∪ V2 = V /\ A_union E1 E2 = (E \ (E_set x y)) /\ V1 x /\ V2 y.
Proof. Admitted.

Lemma tree_has_edge_crossing_cut :
	forall {V GE E} (G : Graph V GE) (T: Tree V E) A, nontrivial_cut G A ->
	{x: Vertex & {y: Vertex & (x -- y) ∈ E /\ edge_crossing_cut G A x y}}.
Proof. Admitted.

Lemma tree_edge_crossing_cut_unique :
	forall {V GE E} (G : Graph V GE) (T: Tree V E) A, nontrivial_cut G A ->
	forall x y u v, edge_crossing_cut G A x y -> edge_crossing_cut G A u v ->
	x = u /\ y = v.
Proof. Admitted.

(* Assume edge weights are unique *)
Definition light_edge {V E} (G: Graph V E) A x y (w : A_set -> nat) :=
	edge_crossing_cut G A x y /\
	(forall u v, edge_crossing_cut G A u v -> w (E_set x y) < w (E_set u v)).

Definition is_subset_MST {V V_T: V_set} {E E_T: A_set} (w : A_set -> nat)
	(T : Tree V_T E_T) (G : Graph V E) :=
	{E_MST : A_set & {MST : Tree V E_MST & 
	is_MST w MST G /\ A_included E_T E_MST /\ V_included V_T V}}.

Lemma union_included1 :
	forall {T} {A B C : U_set T}, A ∪ B ⊆ C -> A ⊆ C.
Proof. intros. intros a Ha. apply H. left. assumption. Qed.

Lemma union_included2 :
	forall {T} {A B C : U_set T}, A ∪ B ⊆ C -> B ⊆ C.
Proof. intros. intros a Ha. apply H. right. assumption. Qed.

Lemma tree_empty_edge_zero_weight : 
  forall {V} (T : Tree V A_empty) w, st_weight T w <= 0.
Proof.
    intros. remember A_empty as A.
    unfold st_weight. induction T.
    - reflexivity.
    - assert (H' : A_union (E_set n f) a <> A_empty). {
        apply U_set_diff. exists (n -- f). split; [repeat constructor | intros H; inversion H].
        }
        contradiction.
    - subst. apply IHT. reflexivity.
Qed.

Lemma tree_subset_weight_bound : 
	forall {V V' E E'} (T : Tree V E) (T': Tree V' E') w,
	A_included E E' -> st_weight T w <= st_weight T' w.
Proof. intros V V' E E' T. generalize dependent E'. generalize dependent V'. induction T'; intros.
	+ simpl. apply subset_empty_is_empty with (A := E) in H. subst. apply tree_empty_edge_zero_weight.

(* T_leaf *)
	+ simpl. specialize IHT' with (w := w). 
	(* We know A_included E (A_union (E_set n f) a) *)
	assert (H_E_in_union_a : A_included E a). admit. apply IHT' in H_E_in_union_a. lia.
	+ simpl. specialize IHT' with (w := w); subst. apply IHT' in H. lia.
Admitted.

Theorem light_edge_is_safe :
	forall {V E} (G: Graph V E) (C: Connected V E) {V' E'} (T : Tree V' E') x y w,
	V' <> V -> is_subset_MST w T G -> light_edge G V' x y w ->
	{T' : Tree (⟨y⟩ ∪ V') ((E_set x y) ∪ E') & is_subset_MST w T' G}.
Proof.
	intros V E G C V' E' T x y w H_V'_neq_V H_T_sMST H_xy_light.
	(* obtain the MST guarenteed by is_subset_MST *)
	destruct H_T_sMST as [E_MST [MST [H_MST [H_ET_EMST H_V'_sub_V]]]].
	assert (H_MST' : is_MST w MST G) by assumption.
	destruct H_MST as [H_MST_subtree H_MST_weight_cond].
	unfold V_included in *. unfold A_included in *.
	(* obtain the edge crossing cut *)
	destruct H_xy_light as [H_xy_crossing H_xy_light].
	assert (H_xy_crossing' : edge_crossing_cut G V' x y) by assumption.
	unfold edge_crossing_cut in H_xy_crossing.
	assert (H_V'_nontriv : nontrivial_cut G V'). {
		apply nontrivial_cut_points. clear H_xy_crossing'.
		split; [apply H_V'_sub_V | split].
		- induction T.
			+ exists r. constructor.
			+ exists f. repeat constructor.
			+ subst. exact (IHT H_V'_neq_V H_ET_EMST H_V'_sub_V H_xy_crossing H_xy_light).
		- apply (subset_but_not_equal _ _ _ H_V'_sub_V H_V'_neq_V).
	}
	destruct (H_xy_crossing H_V'_nontriv) as [H_EMST_xy [H_V'x H_nV'y]]; clear H_xy_crossing.
	(* tree MST has edge crossing cut *)
	destruct (tree_has_edge_crossing_cut G MST V' H_V'_nontriv) as [u [v [H_EMST_uv H_uv_crossing]]].
	assert (H_uv_crossing' : edge_crossing_cut G V' u v) by assumption.
	unfold edge_crossing_cut in H_uv_crossing.
	destruct (H_uv_crossing H_V'_nontriv) as [H_E_uv [H_V'u H_nV'v]]; clear H_uv_crossing.
	(* is (x -- y) in MST or not? *)
	specialize (Tree_isa_graph V E_MST MST) as G_MST.
	case (G_a_dec _ _ G_MST (x -- y)); intros H_xy_MST.
	{
		(* easy case: (x -- y) in MST => by uniqueness, equals (u -- v) *)
		destruct (tree_edge_crossing_cut_unique G MST V' H_V'_nontriv _ _ _ _
				H_xy_crossing' H_uv_crossing'); subst.
		(* extend T to T' by adding u -- v *)
		specialize (T_leaf V' E' T v u H_V'u H_nV'v) as T'.
		exists T'. unfold is_subset_MST. exists E_MST. exists MST.
		split; [assumption | split].
		- unfold A_included; unfold A_union. intros a Ha. inversion Ha.
			+ subst. inversion H.
				* assumption.
				* apply (G_non_directed _ _ G_MST). assumption.
			+ subst. apply H_ET_EMST. assumption.
		- unfold V_included; unfold V_union. intros a Ha. inversion Ha.
			+ subst. inversion H; subst a.
				apply (G_ina_inv2 _ _ G _ _ H_E_uv).
			+ apply H_V'_sub_V. assumption.
	}
	(* hard case: (x -- y) not in MST *)
	(* plan: exchange argument to make new tree, show it has smaller weight *)
	exfalso.
	assert (H_EMST_uv' : A_included (E_set u v) E_MST). {
		intros a Ha. inversion Ha.
		- assumption.
		- apply (G_non_directed _ _ G_MST). assumption.
	}
	destruct (split_tree MST u v H_EMST_uv') as
			[V1 [V2 [E1 [E2 [T1 [T2 [H_V1V2_cap [H_V1V2_cup [H_VE1E2 [H_V1_u H_V2_v]]]]]]]]]].
	unfold A_union in *; unfold A_included in *.
	(* must show that x and y lie on either side of the split *)
	assert (H_V1_x : x ∈ V1) by admit.
	assert (H_V2_y : y ∈ V2) by admit.
	(* use x -- y to join the trees *)
	specialize (join_trees T1 T2 x y H_V1V2_cap H_V1_x H_V2_y) as T_new.
	unfold V_union in *; unfold A_union in *.
	rewrite H_V1V2_cup in T_new.
	(* show that T_new has smaller weight *)
	assert (H_MSTw_better : E_MST = E_set u v ∪ (E1 ∪ E2)). {
		apply U_set_eq. intros a. split; intros Ha.
		- case (A_eq_dec a (u -- v)); intros H_a_uv; try solve [subst; left; constructor].
			case (A_eq_dec a (v -- u)); intros H_a_vu; try solve [subst; left; constructor].
			right. rewrite H_VE1E2. apply In_differ.
			+ assumption.
			+ intros H_uva. inversion H_uva; symmetry in H; contradiction.
		- case (A_eq_dec a (u -- v)); intros H_a_uv; try solve [subst; assumption].
			case (A_eq_dec a (v -- u)); intros H_a_vu; try solve [subst; apply (G_non_directed _ _ G_MST); assumption].
			inversion Ha; subst.
			+ inversion H; symmetry in H0; contradiction.
			+ rewrite H_VE1E2 in H. inversion H. assumption.
	}
	subst E_MST.
	specialize (split_tree_weight_lemma MST T1 T2 w) as H_w1.
	specialize (split_tree_weight_lemma T_new T1 T2 w) as H_w2.
	assert (H_T_new_smaller : st_weight T_new w < st_weight MST w). {
		rewrite H_w1. rewrite H_w2.
		specialize (H_xy_light u v H_uv_crossing') as H_w_ineq.
		lia.
	}
	(* show that T_new is subtree of G *)
	assert (H_Tnew_subtree : is_subtree T_new G). {
		unfold is_subtree. split; try solve [apply self_inclusion].
		destruct H_MST_subtree as [_ H_MST_Eincl]. unfold A_included in *.
		intros a Ha. inversion Ha.
		- subst. inversion H; subst.
			+ assumption.
			+ apply (G_non_directed _ _ G). assumption.
		- subst. apply (union_included2 H_MST_Eincl). assumption.
	}
	(* derive contradiction *)
	specialize (H_MST_weight_cond _ T_new H_Tnew_subtree) as H_Tnew_bigger.
	lia.
Admitted.


Lemma split_tree_weight_lemma :
	forall V V1 E1 V2 E2 x y
	(T: Tree V (E_set x y ∪ (E1 ∪ E2))) (T1 : Tree V1 E1) (T2: Tree V2 E2) w,
	st_weight T w = st_weight T1 w + st_weight T2 w + w (E_set x y).
Proof. Admitted.




Lemma tree_empty_edge_zero_weight : 
  forall {V} (T : Tree V A_empty) w, st_weight T w <= 0.
Proof.
    intros. remember A_empty as A.
    unfold st_weight. induction T.
    - reflexivity.
    - assert (H' : A_union (E_set n f) a <> A_empty). {
        apply U_set_diff. exists (n -- f). split; [repeat constructor | intros H; inversion H].
        }
        contradiction.
    - subst. apply IHT. reflexivity.
Qed.

Lemma tree_subset_weight_bound : 
	forall {V V' E E'} (T : Tree V E) (T': Tree V' E') w,
	A_included E E' -> st_weight T w <= st_weight T' w.
Proof. intros V V' E E' T. generalize dependent E'. generalize dependent V'. induction T'; intros.
	+ simpl. apply subset_empty_is_empty with (A := E) in H. subst. apply tree_empty_edge_zero_weight.

(* T_leaf *)
	+ simpl. specialize IHT' with (w := w). 
	(* We know A_included E (A_union (E_set n f) a) *)
	assert (H_E_in_union_a : A_included E a). admit. apply IHT' in H_E_in_union_a. lia.
	+ simpl. specialize IHT' with (w := w); subst. apply IHT' in H. lia.
Admitted.


Theorem prim_ends :
	forall {V E} (G: Graph V E) (C: Connected V E) {E'} (T : Tree V E') w,
	is_subset_MST w T G -> is_MST w T G.
Proof. intros. unfold is_subset_MST in H. 

(* Show T is a subtree of G *)
destruct H as [E_MST [MST [H_MST_is_MST [E'_incl V_incl]]]]. inversion H_MST_is_MST. unfold is_MST. split.
- unfold is_subtree. split.
	+ apply V_incl.
	+ unfold is_subtree in H. inversion H. apply included_trans with (A := E') (B := E_MST) (C := E).
		* apply E'_incl.
		* apply H2.

(* Show T is an MST *)
-  intros. 
specialize (H0 E_T' T' H1) as H_MST_weight. 
specialize (tree_subset_weight_bound T MST w) as H_T_weight_bound. 
apply H_T_weight_bound in E'_incl. lia. 
Qed.





(* 
Approach 1:
- join trees
- split trees

Approach 2:
- show that m=n-1 and connected -> tree
- show that walk between any two points -> connected (1/2 done)
 *)




