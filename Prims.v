Require Export MST.Graphs.
Require Export MST.Edges.
Require Export MST.Vertices.
Require Export MST.Trees.
Require Export MST.Connected.
Require Export MST.Sets.
Require Export MST.Cuts.
Require Export MST.CustomNotations.
Require Export MST.OrderSizeLemmas. 
Require Export MST.CycleLemmas.
Require Export MST.Weights.
Require Export MST.ImprovedPaths.

Definition is_MST (f : A_set -> nat) {V : V_set} {E E_T : A_set} (T : Tree V E_T) (G : Graph V E) :=
	is_spanning_tree T G /\ forall E_T' (T': Tree V E_T'), is_spanning_tree T' G -> st_weight T f <= st_weight T' f.


Theorem connected_prop :
	forall {V E} (G: Graph V E), V <> ∅ ->
	(forall x y, x ∈ V -> y ∈ V -> {vl : V_list &  {el : E_list &  Walk V E x y vl el}}) ->
	Connected V E.
Proof. Admitted.

Theorem connected_vert_not_empty :
	forall {V E} (G: Connected V E), V <> ∅.
Proof.
	intros V E G. induction G.
	- apply U_set_diff. exists x. split.
		+ constructor.
		+ intros H. inversion H.
	- apply U_set_diff. exists y. split.
		+ left. constructor.
		+ intros H. inversion H.
	- assumption.
	- subst. assumption.
Qed.

(* Exchange argument *)
Lemma join_connected :
	forall {V1 V2 : V_set} {E1 E2 : A_set} (G1 : Connected V1 E1) (G2 : Connected V2 E2) (x y : Vertex),
	V1 x -> V2 y -> Connected (V_union V1 V2) (A_union (E_set x y) (A_union E1 E2)).
Proof.
	intros V1 V2 E1 E2 G1 G2 x y H_V1x H_V2y.
	(* idea: use the connected_prop ^^ to get a walk between any two points *)
	(* cases on which sides the two points are on; use xy if needed *)
	(* use the axiom set_in_dec to do case analysis on which side each of the two points are *)
	(* for instance, set_in_dec u V1 will get 2 cases, u \in V1 and u \not\in V1 *)
	(* for the latter, use u in V_union V1 V2 to get u in V2 *)
	(* 4 cases; 2 are easy by being in the same connected *)
	(* for the other two, walk from one to x and the other two y, then join the walks *)
	(* there is a Walk_append lemma somewhere already *)
Admitted.


Lemma join_cycle_free :
	forall {V1 V2 : V_set} {E1 E2 : A_set} (G1 : Acyclic V1 E1) (G2 : Acyclic V2 E2) (u v : Vertex),
	V_inter V1 V2 = V_empty -> V1 u -> V2 v -> Acyclic (V_union V1 V2) (A_union (E_set u v) (A_union E1 E2)).
Proof. Admitted.


Lemma join_trees:
	forall {V1 V2 : V_set} {E1 E2 : A_set} (T1 : Tree V1 E1) (T2 : Tree V2 E2) (u v : Vertex),
	V_inter V1 V2 = V_empty -> V1 u -> V2 v -> Tree (V_union V1 V2) (A_union (E_set u v) (A_union E1 E2)).
Proof.
	intros.

	specialize (Tree_isa_connected _ _ T1) as C1.
	specialize (Tree_isa_connected _ _ T2) as C2.
	specialize (join_connected C1 C2 u v H0 H1) as C.

	specialize (Tree_isa_acyclic _ _ T1) as A1.
	specialize (Tree_isa_acyclic _ _ T2) as A2.
	specialize (join_cycle_free A1 A2 u v H H0 H1) as A.

	apply (Acyclic_connected_isa_tree _ _ A C).
Qed.


Lemma split_tree :
	forall {V E} (T: Tree V E) x y, A_included (E_set x y) E ->
	exists V1 V2 E1 E2 (T1 : Tree V1 E1) (T2 : Tree V2 E2),
	V1 ∩ V2 = ∅ /\ V1 ∪ V2 = V /\ A_union E1 E2 = (E \ (E_set x y)) /\ V1 x /\ V2 y.
Proof. Admitted.

(* Assume edge weights are unique *)
Definition light_edge {V E} (G: Graph V E) A x y (w : A_set -> nat) :=
	edge_crossing_cut G A x y /\
	(forall u v, edge_crossing_cut G A u v -> w (E_set x y) < w (E_set u v)).

Definition is_subset_MST {V V_T: V_set} {E E_T: A_set} (w : A_set -> nat)
	(T : Tree V_T E_T) (G : Graph V E) :=
	{E_MST : A_set & {MST : Tree V E_MST & 
	is_MST w MST G /\ A_included E_T E_MST /\ V_included V_T V}}.

Lemma tree_Vempty_contra : 
	forall {V E} (T: Tree V E), V = V_empty -> False.
Proof.
	intros. induction T.
	- subst.
		assert (H1 : V_single r <> V_empty). {
			apply U_set_diff. exists r. split.
			- constructor.
			- intros H'. inversion H'.
		}
		contradiction.
	- subst.
		assert (H3 : V_union (V_single f) v <> V_empty). {
			apply U_set_diff. exists f. split.
			- constructor. constructor.
			- intros H'. inversion H'.
		}
		contradiction.
	- apply IHT. subst. reflexivity.
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
		split; try solve [assumption].
		intros H_V'triv. destruct H_V'triv as [H_V'1 | H_V'2].
		- contradiction.
		- apply (tree_Vempty_contra T H_V'2).
	}
	destruct (H_xy_crossing H_V'_nontriv) as [H_EMST_xy [H_V'x H_nV'y]]; clear H_xy_crossing.
	(* tree MST has an xy path *)
	specialize (Tree_isa_connected _ _ MST) as C_MST.
	assert (H_Vx : V x) by apply (G_ina_inv1 _ _ G _ _ H_EMST_xy).
	assert (H_Vy : V y) by apply (G_ina_inv2 _ _ G _ _ H_EMST_xy).
	destruct (Connected_walk _ _ C_MST x y H_Vx H_Vy) as [og_xy_vl_w [og_xy_el_w og_xy_walk]].
	specialize (Walk_to_path _ _ _ _ _ _ og_xy_walk) as [og_xy_pvl [og_xy_pel og_xy_path]].
	clear og_xy_walk.
	(* this path must have an edge crossing the cut *)
	specialize (Tree_isa_graph _ _ MST) as G_MST.
	specialize (nontrivial_cut_transfer G G_MST V' H_V'_nontriv) as H_V'_nontriv_transfer.
	(* destruct (find_crossing_edge_on_path G_MST V' _ _ _ _ H_V'_nontriv_transfer H_V'x H_nV'y og_xy_path)
			as [u [v [H_uv_crossing H_uv_in_og_xy_el] [xu_vl [xu_el [vy_vl [vy_el og_xy_vl_equiv og_xy_el_equiv]]]]]]. *)
	destruct (find_last_crossing_edge_on_path G_MST V' _ _ _ _ H_V'_nontriv_transfer H_V'x H_nV'y og_xy_path)
				as [u [v [H_uv_crossing H_uv_in_og_xy_el] [xu_vl [xu_el [vy_vl [vy_el
				[xu_path [vy_path og_xy_vl_equiv og_xy_el_equiv]]]]]]]].
	assert (H_uv_crossing' : edge_crossing_cut G V' u v). {
		unfold edge_crossing_cut; intros H_V'_nontriv_again.
		unfold edge_crossing_cut in H_uv_crossing.
		destruct (H_uv_crossing H_V'_nontriv_again) as [H_EMST_uv H_V'_uv].
		split; try solve [assumption].
		destruct H_MST_subtree. destruct H0. apply H1. assumption.
	}
	assert (H_uv_crossing'' : edge_crossing_cut G V' u v) by assumption.
	unfold edge_crossing_cut in H_uv_crossing.
	destruct (H_uv_crossing H_V'_nontriv) as [H_EMST_uv [H_V'u H_nV'v]]; clear H_uv_crossing.
	assert (H_E_uv : E (u -- v)). {
		unfold edge_crossing_cut in H_uv_crossing'.
		destruct (H_uv_crossing' H_V'_nontriv) as [H_EMST_uv' H_V'_uv].
		destruct H_MST_subtree. destruct H0. apply H1. assumption.
	}
	(* is (x -- y) in MST or not? *)
	case (G_a_dec _ _ G_MST (x -- y)); intros H_xy_MST.
	{
		(* easy case: (x -- y) in MST *)
		(* use path uniqueness in trees to show that (x -- y) = (x --> u -- v --> y) *)
		(* then (x -- y) = (u -- v) *)
		assert (H_xy_uv_eq : x = u /\ y = v). {
			(* construct the path from x -- y by the edge *)
			specialize (P_null V E_MST y H_Vy) as Pyy.
			assert (H_x_neq_y : x <> y) by (intros H_x_eq_y; subst; contradiction).
			assert (H_y_notin_nil : ~ In y nil) by (intros H; contradiction).
			assert (H_bad : In x nil -> x = y) by (intros H; inversion H).
			assert (H_worse : forall u, In u nil -> ~ E_eq u (x~~y)) by (intros r H; inversion H).
			specialize (P_step V E_MST x y y nil nil Pyy H_Vx H_xy_MST H_x_neq_y H_y_notin_nil H_bad H_worse) as P_xy'.
			(* use path uniqueness in tree *)
			specialize (Tree_isa_acyclic _ _ MST) as A_MST.
			destruct (path_uniq_in_acyclic _ _ A_MST _ _ _ _ _ _ P_xy' og_xy_path) as [vl_eq el_eq].
			subst. simpl in *. rewrite <- el_eq in H_uv_in_og_xy_el.
			inversion H_uv_in_og_xy_el; try solve [contradiction].
			inversion H; subst; split; reflexivity.
		}
		destruct H_xy_uv_eq; subst.
		(* extend T to T' by adding u -- v *)
		specialize (T_leaf V' E' T v u H_V'u H_nV'v) as T'.
		exists T'. unfold is_subset_MST. exists E_MST. exists MST.
		split; [assumption | split].
		- unfold A_included; unfold A_union. intros a Ha. inversion Ha.
			+ subst. inversion H; try solve [assumption].
				apply (G_non_directed _ _ G_MST). assumption.
			+ subst. apply H_ET_EMST. assumption.
		- unfold V_included; unfold V_union. intros a Ha. inversion Ha.
			+ subst. inversion H; subst a. apply (G_ina_inv2 _ _ G _ _ H_E_uv).
			+ apply H_V'_sub_V. assumption.
	}
	(* hard case: (x -- y) not in MST *)
	(* plan: exchange argument to make new tree, show it has smaller weight *)
	exfalso.
	assert (H_EMST_uv' : A_included (E_set u v) E_MST). {
		intros a Ha. inversion Ha; try solve [assumption].
		apply (G_non_directed _ _ G_MST). assumption.
	}
	destruct (split_tree MST u v H_EMST_uv') as
			[V1 [V2 [E1 [E2 [T1 [T2 [H_V1V2_cap [H_V1V2_cup [H_VE1E2 [H_V1_u H_V2_v]]]]]]]]]].
	unfold A_union in *; unfold A_included in *.
	(* some useful lemmas about the split *)
	assert (H_notV1_V2 : forall n, V n -> ~ V1 n -> V2 n). {
		intros n H_Vn H_not_V1n.
		specialize (Tree_isa_graph _ _ T1) as G1.
		specialize (Tree_isa_graph _ _ T2) as G2.
		rewrite <- H_V1V2_cup in H_Vn.
		specialize (Union_dec _ V1 V2 n (G_v_dec _ _ G1 n) (G_v_dec _ _ G2 n) H_Vn) as H'.
		destruct H'; solve [contradiction | assumption].
	}
	assert (H_notV2_V1 : forall n, V n -> ~ V2 n -> V1 n). {
		intros n H_Vn H_not_V1n.
		specialize (Tree_isa_graph _ _ T1) as G1.
		specialize (Tree_isa_graph _ _ T2) as G2.
		rewrite <- H_V1V2_cup in H_Vn.
		specialize (Union_dec _ V1 V2 n (G_v_dec _ _ G1 n) (G_v_dec _ _ G2 n) H_Vn) as H'.
		destruct H'; solve [assumption | contradiction].
	}
	assert (H_V1V2_sub_V : V1 ∪ V2 ⊆ V) by (subst; apply self_inclusion).
	(* must show that x and y lie on either side of the split *)
	assert (H_V1_x : x ∈ V1). {
		case (V_eq_dec x u); intros H_xu.
		{ subst; assumption. }
		apply pbc; intros H_nV1_x.
		assert (H_V2_x : x ∈ V2). {
			apply H_notV1_V2; [apply H_V'_sub_V; assumption | assumption].
		}
		(* walk from v --> x *)
		specialize (Tree_isa_connected _ _ T2) as C2.
		destruct (Connected_walk _ _ C2 x v H_V2_x H_V2_v) as [wvl_xv [wel_xv walk_xv]].
		(* squeeze to path, then relax back to walk *)
		specialize (Walk_to_path _ _ _ _ _ _ walk_xv) as [pvl_xv [pel_xv path_xv]].
		specialize (Path_isa_trail _ _ _ _ _ _ path_xv) as trail_xv.
		specialize (Trail_isa_walk _ _ _ _ _ _ trail_xv) as walk_xv'. clear trail_xv.
		(* lift walk_xv to MST *)
		assert (H_V2_V : V2 ⊆ V) by apply (union_included2 H_V1V2_sub_V).
		assert (H_E2_sub_EMST : E2 ⊆ E_MST). {
			intros a Ha.
			case (A_eq_dec a (u -- v)); intros H_a_uv; try solve [subst; assumption].
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
		(* make it a path from v --> u, using the improved lemma *)
		destruct (Walk_to_path'' _ _ _ _ _ _ walk_uv) as [pvl [pel path_uv path_el_cond] p_vl_cond].
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
		assert (H_no_vu_in_pel : forall u0, In u0 pel -> ~ E_eq u0 (v ~~ u)). {
			intros e He_pel He_vu. apply path_el_cond in He_pel.
			destruct (in_app_or _ _ _ He_pel) as [He1 | He2].
			- specialize (Tree_isa_graph _ _ T) as G'.
				inversion He_vu; subst; specialize (P_inel_ina _ _ _ _ _ _ path_ux _ _ He1) as H'.
				+ specialize (G_ina_inv1 _ _ G' _ _ H') as H_V'v. contradiction.
				+ specialize (G_ina_inv2 _ _ G' _ _ H') as H_V'v. contradiction.
			- specialize (Tree_isa_graph _ _ T2) as G2.
				inversion He_vu; subst; specialize (P_inel_ina _ _ _ _ _ _ path_xv _ _ He2) as H'.
				+ specialize (G_ina_inv2 _ _ G2 _ _ H') as H_V2v.
					assert (H_contra : V1 ∩ V2 <> ∅). {
						apply U_set_diff. exists u. split.
						- split; assumption.
						- intros H. inversion H.
					}
					contradiction.
				+ specialize (G_ina_inv1 _ _ G2 _ _ H') as H_V2v.
					assert (H_contra : V1 ∩ V2 <> ∅). {
						apply U_set_diff. exists u. split.
						- split; assumption.
						- intros H. inversion H.
					}
					contradiction.
		}
		specialize (P_step V E_MST v u v pvl pel path_uv H_Vv
			H_EMST_vu H_vnu H_u_not_in_pvl H_vrefl H_no_vu_in_pel) as p_cyc.
		(* cycle in tree -> contradiction *)
		assert (cyc: Cycle _ _ _ _ _ _ p_cyc) by constructor.
		specialize (Tree_isa_acyclic _ _ MST) as A_MST.
		specialize (Acyclic_no_cycle _ _ A_MST _ _ _ _ p_cyc cyc); intros Hvl.
		discriminate.
	}
	assert (H_V2_y : y ∈ V2). {
		case (V_eq_dec y v); intros H_yv.
		{ subst; assumption. }
		apply pbc; intros H_nV2_y.
		assert (H_V1_y : y ∈ V1). {
			apply H_notV2_V1.
			- apply (G_ina_inv2 _ _ G _ _ H_EMST_xy).
			- assumption.
		}
		(* walk from u --> y *)
		specialize (Tree_isa_connected _ _ T1) as C1.
		destruct (Connected_walk _ _ C1 y u H_V1_y H_V1_u) as [wvl_yu [wel_yu walk_yu]].
		(* squeeze to path, then relax back to walk *)
		specialize (Walk_to_path _ _ _ _ _ _ walk_yu) as [pvl_yu [pel_yu path_yu]].
		specialize (Path_isa_trail _ _ _ _ _ _ path_yu) as trail_yu.
		specialize (Trail_isa_walk _ _ _ _ _ _ trail_yu) as walk_yu'. clear trail_yu.
		(* lift walk_yu to MST *)
		assert (H_V1_V : V1 ⊆ V) by apply (union_included1 H_V1V2_sub_V).
		assert (H_E1_sub_EMST : E1 ⊆ E_MST). {
			intros a Ha.
			case (A_eq_dec a (u -- v)); intros H_a_uv;
				try solve [subst; assumption].
			case (A_eq_dec a (v -- u)); intros H_a_vu;
				try solve [subst; apply (G_non_directed _ _ G_MST); assumption].
			specialize (U_eq_set _ _ _ H_VE1E2 a) as H'.
			assert (H_a_E1E2 : (E1 ∪ E2) a) by (left; assumption).
			apply H' in H_a_E1E2. inversion H_a_E1E2. assumption.
		}
		specialize (lift_walk H_V1_V H_E1_sub_EMST walk_yu') as walk_yu''.
		(* take the original walk from y --> v, relax to walk, lift to MST,  *)
		specialize (Path_isa_trail _ _ _ _ _ _ vy_path) as trail_vy.
		specialize (Trail_isa_walk _ _ _ _ _ _ trail_vy) as walk_vy'. clear trail_vy.
		assert (H_diff_included : (V\V') ⊆ V). {
			intros a Ha. inversion Ha. assumption.
		}
		assert (EMST_sub_self : E_MST ⊆ E_MST) by apply self_inclusion.
		specialize (lift_walk H_diff_included EMST_sub_self walk_vy') as walk_vy''.
		(* join to get walk from u --> y --> v *)
		specialize (Walk_append _ _ v y u _ _ _ _ walk_vy'' walk_yu'') as walk_vu.
		(* make it a path from v --> u, using the improved lemma *)
		destruct (Walk_to_path'' _ _ _ _ _ _ walk_vu) as [pvl [pel path_vu path_el_cond] p_vl_cond].
		(* extend using v -- u to make a cycle *)
		assert (H_Vu : V u) by apply (G_ina_inv1 _ _ G_MST _ _ H_EMST_uv).
		assert (H_unv : u <> v) by (intros H_uv; subst; contradiction).
		assert (H_v_not_in_pvl : ~ In v pvl). {
			intros H_v_pvl. apply p_vl_cond in H_v_pvl.
			destruct (in_app_or _ _ _ H_v_pvl) as [H_v_wvl_vy | H_v_wvl_yu].
			- assert (H_vy' : v = y) by apply (P_when_cycle _ _ _ _ _ _ vy_path H_v_wvl_vy).
				symmetry in H_vy'. contradiction.
			- assert (H_V1v : v ∈ V1) by apply (P_invl_inv _ _ _ _ _ _ path_yu _ H_v_wvl_yu).
				assert (H_V1V2_cap' : V1 ∩ V2 <> ∅). {
					apply U_set_diff. exists v. split.
					- split; assumption.
					- intros H. inversion H.
				}
				contradiction.
		}
		assert (H_urefl : In u pvl -> u = u) by (intros; reflexivity).
		assert (H_no_uv_in_pel : forall u0, In u0 pel -> ~ E_eq u0 (u ~~ v)). {
			intros e He_pel He_uv. apply path_el_cond in He_pel.
			destruct (in_app_or _ _ _ He_pel) as [He1 | He2].
			- inversion He_uv; subst.
				+ specialize (P_inel_inv1 _ _ _ _ _ _ vy_path u v He1) as H'.
					inversion H'; subst. contradiction.
				+ specialize (P_inel_inv2 _ _ _ _ _ _ vy_path v u He1) as H'.
					inversion H'; subst. contradiction.
			- specialize (Tree_isa_graph _ _ T1) as G1.
				inversion He_uv; subst; specialize (P_inel_ina _ _ _ _ _ _ path_yu _ _ He2) as H'.
				+ specialize (G_ina_inv2 _ _ G1 _ _ H') as H_V2y.
					assert (H_contra : V1 ∩ V2 <> ∅). {
						apply U_set_diff. exists v. split.
						- split; assumption.
						- intros H. inversion H.
					}
					contradiction.
				+ specialize (G_ina_inv1 _ _ G1 _ _ H') as H_V1u.
					assert (H_contra : V1 ∩ V2 <> ∅). {
						apply U_set_diff. exists v. split.
						- split; assumption.
						- intros H. inversion H.
					}
					contradiction.
		}
		specialize (P_step V E_MST u v u pvl pel path_vu H_Vu
			H_EMST_uv H_unv H_v_not_in_pvl H_urefl H_no_uv_in_pel) as p_cyc.
		(* cycle in tree -> contradiction *)
		assert (cyc: Cycle _ _ _ _ _ _ p_cyc) by constructor.
		specialize (Tree_isa_acyclic _ _ MST) as A_MST.
		specialize (Acyclic_no_cycle _ _ A_MST _ _ _ _ p_cyc cyc); intros Hvl.
		discriminate.
	}
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
	symmetry in H_V1V2_cup.
	specialize (split_tree_weight_lemma' MST T1 T2 w H_V1V2_cup H_MSTw_better H_V1_u H_V2_v H_V1V2_cap) as H_w1.
	remember (E_set x y ∪ (E1 ∪ E2)) as E_new eqn:H_Enew.
	specialize (split_tree_weight_lemma' T_new T1 T2 w H_V1V2_cup H_Enew H_V1_x H_V2_y H_V1V2_cap) as H_w2.
	assert (H_T_new_smaller : st_weight T_new w < st_weight MST w). {
		rewrite H_w1. rewrite H_w2.
		specialize (H_xy_light u v H_uv_crossing') as H_w_ineq.
		lia.
	}
	(* show that T_new is subtree of G *)
	assert (H_Tnew_subtree : is_spanning_tree T_new G). {
		unfold is_spanning_tree. split; try solve [reflexivity].
		unfold is_subtree. split; try solve [apply self_inclusion].
		destruct H_MST_subtree as [_ [_ H_MST_Eincl]]. unfold A_included in *.
		intros a Ha. subst. inversion Ha.
		- subst. inversion H; subst.
			+ assumption.
			+ apply (G_non_directed _ _ G). assumption.
		- subst. apply (union_included2 H_MST_Eincl). assumption.
	}
	(* derive contradiction *)
	specialize (H_MST_weight_cond _ T_new H_Tnew_subtree) as H_Tnew_bigger.
	lia.
Qed.

Theorem prim_ends :
	forall {V E} (G: Graph V E) (C: Connected V E) {E'} (T : Tree V E') w,
	is_subset_MST w T G -> is_MST w T G.
Proof. intros V E G C E' T w H. unfold is_subset_MST in H. 

(* Show T is a subtree of G *)
destruct H as [E_MST [MST [H_MST_is_MST [E'_incl V_incl]]]]. inversion H_MST_is_MST. unfold is_MST. split.
- unfold is_subtree. split.
	+ reflexivity.
	+ unfold is_subtree in H. inversion H. unfold is_subtree. split. apply V_incl. 
	apply included_trans with (A := E') (B := E_MST) (C := E).
		* apply E'_incl.
		* apply H2.

(* Show T is an MST *)
-  intros. 
specialize (H0 E_T' T' H1) as H_MST_weight. 
specialize (tree_subset_weight_bound T MST w) as H_T_weight_bound. 
apply H_T_weight_bound in E'_incl. lia. 
Qed.


