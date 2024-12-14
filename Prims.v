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
  forall {V} (T : Tree V A_empty) w, st_weight T w = 0.
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
Proof.
	intros V V' E E' T T'. generalize dependent T. generalize dependent E. generalize dependent V.
	induction T'; intros.
	- fold (st_weight T w). 
		assert (HE : E = A_empty) by apply (subset_empty_is_empty _ H). subst.
		specialize (tree_empty_edge_zero_weight T w) as H'. lia.
	- unfold A_included in *. simpl.
		specialize (Tree_isa_graph V E T) as G_T.
		case (G_a_dec _ _ G_T (n -- f)); intros H_nf.
		+ admit.
		+ assert (HE : E ⊆ a). {
				intros x Hx. destruct (H x Hx) as [H' | H'].
				- inversion H0.
					+ subst. contradiction.
					+ subst. exfalso. apply H_nf. apply (G_non_directed _ _ G_T). assumption.
				- assumption.
			}
			specialize (IHT' _ _ T w HE) as H'. lia.
	- simpl. subst. apply IHT'. assumption.
Admitted.


Lemma split_tree_weight_lemma :
	forall {V1 E1 V2 E2 x y}
	(T: Tree (V1 ∪ V2) (E_set x y ∪ (E1 ∪ E2))) (T1 : Tree V1 E1) (T2: Tree V2 E2) w,
	x ∈ V1 -> y ∈ V2 -> V1 ∩ V2 = ∅ -> st_weight T w = st_weight T1 w + st_weight T2 w + w (E_set x y).
Proof.
	intros V1 E1 V2 E2 x y T T1 T2 w H_V1x H_V2y H_V1V2.
	remember (V1 ∪ V2) as V. remember (E_set x y ∪ (E1 ∪ E2)) as E.
	generalize dependent T2. generalize dependent E2. generalize dependent V2.
	generalize dependent T1. generalize dependent E1. generalize dependent V1.
	generalize dependent y. generalize dependent x.
	induction T; intros.
	- assert (HeqE' : A_empty <> E_set x y ∪ (E1 ∪ E2)). {
			apply U_set_diff_commut. apply U_set_diff.
			exists (x -- y). split; [repeat constructor | intros H; inversion H].
		}
		contradiction.
	- simpl. unfold V_union in *; unfold A_union in *.
		assert (Hn : n ∈ (V1 ∪ V2)) by admit.
		assert (Hf : f ∈ (V1 ∪ V2)) by admit.

		(* case (E_set n f) = (E_set x y). *)
		(* n and f are in V1 and V2 (or reverse) *)
		(* -> (n--f) not in E1 or E2 -> E1 ∪ E2 = a -> ok *)

		(* case (E_set n f) <> (E_set x y) *)
		(* case (n -- f) in E1 -> n and f in V1 *)
Admitted.

(* Lemma split_tree_weight_lemma :
	forall {V1 E1 V2 E2 x y}
	(T: Tree (V1 ∪ V2) (E_set x y ∪ (E1 ∪ E2))) (T1 : Tree V1 E1) (T2: Tree V2 E2) w,
	x ∈ V1 -> y ∈ V2 -> st_weight T w = st_weight T1 w + st_weight T2 w + w (E_set x y).
Proof.
	intros V1 E1 V2 E2 x y T T1 T2 w H_V1x H_V2y.
	remember (V1 ∪ V2) as V. remember (E_set x y ∪ (E1 ∪ E2)) as E.
	generalize dependent T2. generalize dependent E2. generalize dependent V2.
	generalize dependent T1. generalize dependent E1. generalize dependent V1.
	induction T; intros.
	- assert (HeqE' : A_empty <> E_set x y ∪ (E1 ∪ E2)). {
			apply U_set_diff_commut. apply U_set_diff.
			exists (x -- y). split; [repeat constructor | intros H; inversion H].
		}
		contradiction.
	- simpl. *)

(* Lemma split_tree_weight_lemma :
	forall {V V1 E1 V2 E2 x y}
	(T: Tree V (E_set x y ∪ (E1 ∪ E2))) (T1 : Tree V1 E1) (T2: Tree V2 E2) w,
	st_weight T w = st_weight T1 w + st_weight T2 w + w (E_set x y).
Proof.
	intros V V1 E1 V2 E2 x y T T1 T2.
	remember (E_set x y ∪ (E1 ∪ E2)) as E.
	generalize dependent T2. generalize dependent E2. generalize dependent V2.
	generalize dependent T1. generalize dependent E1. generalize dependent V1.
	induction T; intros.
	- assert (HeqE' : A_empty <> E_set x y ∪ (E1 ∪ E2)). {
			apply U_set_diff_commut. apply U_set_diff.
			exists (x -- y). split; [repeat constructor | intros H; inversion H].
		}
		contradiction.
	- simpl. *)


Lemma lift_walk :
	forall {V E x y vl el V' E'}, V ⊆ V' -> E ⊆ E' -> Walk V E x y vl el -> Walk V' E' x y vl el.
Proof.
	intros. induction H1.
	- constructor. apply H. assumption.
	- constructor.
		+ assumption.
		+ apply H. assumption.
		+ apply H0. assumption.
Qed.




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
	assert (H_V1_x : x ∈ V1). {
		case (V_eq_dec x u); intros H_xu.
		{ subst; assumption. }
		apply pbc; intros H_nV1_x.
		assert (H_V2_x : x ∈ V2) by admit.
		(* walk from v --> x *)
		specialize (Tree_isa_connected _ _ T2) as C2.
		destruct (Connected_walk _ _ C2 x v H_V2_x H_V2_v) as [wvl_xv [wel_xv walk_xv]].
		(* squeeze to path, then relax back to walk *)
		specialize (Walk_to_path _ _ _ _ _ _ walk_xv) as [pvl_xv [pel_xv path_xv]].
		specialize (Path_isa_trail _ _ _ _ _ _ path_xv) as trail_xv.
		specialize (Trail_isa_walk _ _ _ _ _ _ trail_xv) as walk_xv'. clear trail_xv.
		(* lift walk_xv to MST *)
		assert (H_V1V2_sub_V : V1 ∪ V2 ⊆ V). {
			subst. apply self_inclusion.
		}
		assert (H_V2_V : V2 ⊆ V) by apply (union_included2 H_V1V2_sub_V).
		assert (H_E2_sub_EMST : E2 ⊆ E_MST). {
			intros a Ha.
			case (A_eq_dec a (u -- v)); intros H_a_uv;
				try solve [subst; assumption].
			case (A_eq_dec a (v -- u)); intros H_a_vu;
				try solve [subst; apply (G_non_directed _ _ G_MST); assumption].
			specialize (U_eq_set _ _ _ H_VE1E2 a) as H'.
			assert (H_a_E1E2 : (E1 ∪ E2) a) by (right; assumption).
			apply H' in H_a_E1E2. inversion H_a_E1E2. assumption.
		}
		specialize (lift_walk H_V2_V H_E2_sub_EMST walk_xv') as walk_xv''.
		(* walk from x --> u *)
		specialize (Tree_isa_connected _ _ T) as CV'.
		destruct (Connected_walk _ _ CV' u x H_V'u H_V'x) as [wvl_ux [wel_ux walk_ux]].
		(* squeeze to path, then relax back to walk *)
		specialize (Walk_to_path _ _ _ _ _ _ walk_ux) as [pvl_ux [pel_ux path_ux]].
		specialize (Path_isa_trail _ _ _ _ _ _ path_ux) as trail_ux.
		specialize (Trail_isa_walk _ _ _ _ _ _ trail_ux) as walk_ux'. clear trail_ux.
		(* lift walk_ux to MST *)
		specialize (lift_walk H_V'_sub_V H_ET_EMST walk_ux') as walk_ux''.
		(* join to get walk from v --> x --> u *)
		specialize (Walk_append _ _ u x v _ _ _ _ walk_ux'' walk_xv'') as walk_uv.
		(* make it a path from v --> u, using the improved version *)
		destruct (Walk_to_path' _ _ _ _ _ _ walk_uv) as [pvl [pel path_uv] p_vl_cond].
		(* extend using v -- u to make a cycle *)
		assert (H_EMST_vu : E_MST (v -- u)) by (apply (G_non_directed _ _ G_MST); assumption).
		assert (H_Vv : V v) by apply (G_ina_inv1 _ _ G_MST _ _ H_EMST_vu).
		assert (H_vnu : v <> u) by (intros H_vu; subst; contradiction).
		assert (H_u_not_in_pvl : ~ In u pvl). {
			intros H_u_pvl. apply p_vl_cond in H_u_pvl.
			destruct (in_app_or _ _ _ H_u_pvl) as [H_u_wvl_ux | H_u_wvl_xv].
			- assert (H_xu' : u = x) by apply (P_when_cycle _ _ _ _ _ _ path_ux H_u_wvl_ux).
				symmetry in H_xu'. contradiction.
			- assert (H_V2u : u ∈ V2) by apply (P_invl_inv _ _ _ _ _ _ path_xv _ H_u_wvl_xv).
				assert (H_V1V2_cap' : V1 ∩ V2 <> ∅). {
					apply U_set_diff. exists u. split.
					- split; assumption.
					- intros H. inversion H.
				}
				contradiction.
		}
		assert (H_vrefl : In v pvl -> v = v) by (intros; reflexivity).
		assert (H_no_vu_in_pel : forall u0, In u0 pel -> ~ E_eq u0 (v ~~ u)) by admit.
		(* TODO: need similar extension as for vl to solve ^ *)
		specialize (P_step V E_MST v u v pvl pel path_uv H_Vv
			H_EMST_vu H_vnu H_u_not_in_pvl H_vrefl H_no_vu_in_pel) as p_cyc.
		(* cycle in tree -> contradiction *)
		assert (cyc: Cycle _ _ _ _ _ _ p_cyc) by constructor.
		specialize (Tree_isa_acyclic _ _ MST) as A_MST.
		specialize (Acyclic_no_cycle _ _ A_MST _ _ _ _ p_cyc cyc); intros Hvl.
		discriminate.
	}
	assert (H_V2_y : y ∈ V2) by admit. (* Mostly the same as the H_V1_x by symmetry *)
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

Theorem prim_ends :
	forall {V E} (G: Graph V E) (C: Connected V E) {E'} (T : Tree V E') w,
	is_subset_MST w T G -> is_MST w T G.
Proof. intros V E G C E' T w H. unfold is_subset_MST in H. 

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




