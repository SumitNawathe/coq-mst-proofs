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

Fixpoint st_weight {V : V_set} {E : A_set} (T : Tree V E) (f: (A_set -> nat)) : nat :=
	match T with
	| T_root _ => 0
	| T_leaf _ _ T x y _ _ => f (E_set x y) + (st_weight T f)
	| T_eq V _ A _ _ _ T => (st_weight T f)
	end.
 
(* The weight of edges in a list *)
Fixpoint elist_weight (E : E_list) (f : (A_set -> nat)) : nat := 
	match E with 
	| nil => 0 
	| (E_ends x y) :: t => f (E_set x y) + elist_weight t f
	end.  

Lemma st_weight_elist_weight_equiv : forall {V} {E} (T : Tree V E) (w : A_set -> nat), 
	st_weight T w = elist_weight (TE_list T) w.
Proof. 
	intros V E T w. induction T.
	- reflexivity.
	- simpl. specialize (E_set_eq n f) as H_E_set_equiv. 
	assert (H_w_equiv : w (E_set f n) = w (E_set n f)). {
		rewrite -> H_E_set_equiv. reflexivity. 
	} 
	rewrite -> H_w_equiv.
	rewrite -> IHT. reflexivity. 
	- simpl. apply IHT.
Qed.


Definition is_MST (f : A_set -> nat) {V : V_set} {E E_T : A_set} (T : Tree V E_T) (G : Graph V E) :=
	is_spanning_tree T G /\ forall E_T' (T': Tree V E_T'), is_spanning_tree T' G -> st_weight T f <= st_weight T' f.

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

Lemma extract_union : forall (E' a: A_set) (n f : Vertex),
	A_included (A_union (E_set n f) a) E' -> A_included a E' /\ E' (A_ends n f) /\ E' (A_ends f n).
Proof. 
	intros. 
	specialize (A_included_union a (E_set n f) ) as H_incl_union. 
	specialize (A_included_union (E_set n f) a) as H_n_f_incl_union. 
	split. 
		+ apply included_trans with (A := (a)) (B := (A_union (E_set n f) a)) (C := E'). 
			- specialize (A_union_commut a (E_set n f)) as H_union_commut.
			rewrite -> H_union_commut in H_incl_union. 
			apply H_incl_union. 
			- apply H. 
		+ split. 
			apply included_trans with (A := (E_set n f)) (B := (A_union (E_set n f) a)) (C := E'). 
				* specialize (A_union_commut a (E_set n f)) as H_union_commut. apply H_n_f_incl_union. 
				* apply H.
				* apply E_right. 
				* apply included_trans with (A := (E_set n f)) (B := (A_union (E_set n f) a)) (C := E'). apply H_n_f_incl_union. apply H.
				apply E_left. 
Qed. 

(* subset of edges implies subset of list of edges *)
Lemma tree_edge_subset_implies_list_subset : 
	forall {V V' E E'} (T : Tree V E) (T' : Tree V' E'), 
	A_included E E' -> forall e, E_in e (TE_list T) -> E_in e (TE_list T').
Proof. 
	intros V V' E E' T T'. intros H_E_subset. induction T.

	(* T is a root *) 
	- intros H_e_in_T. simpl. contradiction. 

	(* T is a leaf *)
	- intros e H_e_in_T. unfold TE_list in H_e_in_T. fold (TE_list T) in H_e_in_T. 
	
	specialize (extract_union E' a n f) as H_included. 
	
	specialize (H_included H_E_subset).
	destruct H_included as [H_a_incl H_n_f_incl]. 
	specialize (IHT H_a_incl) as H_e_gen. 
	unfold E_in in H_e_in_T. generalize dependent H_e_in_T.
	case (E_eq_dec e (n ~~ f)). intros.
	
	(* if (n,f) in E', then (n,f) in TE_list T' *) 
	inversion e0; subst. 
	apply (E_in_tree_list n f T'). apply H_n_f_incl. 

	(* if (f,n) in E', then (f,n) in TE_list T'*)
	apply (E_in_tree_list f n T'). destruct H_n_f_incl. apply H0.

	(* if e ~= (n,f), then (n,f) in E, by IH this means it is in TE_list T' *)
	intros. fold (E_in) in H_e_in_T. specialize (IHT H_a_incl). apply IHT with (e := e) in H_e_in_T. apply H_e_in_T.

	(* T is equal to another tree *)
	- subst. specialize (IHT H_E_subset). intros. simpl in H. apply IHT with (e := e). apply H. 
Qed. 

(* A version of NoDup using E_in instead of In. *)
Inductive ENoDup : list Edge -> Prop := 
	| ENoDup_nil : ENoDup nil 
	| ENoDup_cons : forall x El, ~ E_in x El -> ENoDup El -> ENoDup (x :: El). 

(* the list of edges in a tree is distinct *)
Lemma elist_no_dup : 
	forall {V E} (T : Tree V E), 
	ENoDup (TE_list T).
Proof. intros. induction T. 
	- simpl. constructor. 

	- simpl. constructor. 
	+ unfold not. intros. 

	assert (H_nf_contra : E_in (n ~~ f) (TE_list T) -> v n /\ v f). 
	{
		split. 
		- apply v0. 
		- specialize (E_in_tree_iff_list n f T) as H_in_tree_iff. 
		destruct H_in_tree_iff. 
		apply H1 in H.
		destruct H; 
		specialize (Tree_isa_graph v a T) as H_t_is_g; 
		specialize (G_ina_inv2 v a H_t_is_g n f) as H_nf_in_t;
		specialize (G_non_directed v a H_t_is_g f n) as H_e_refl.
			+ apply H_nf_in_t in H. apply H. 
			+ apply H_e_refl in H. apply H_nf_in_t in H. contradiction. 
	}
	apply H_nf_contra in H. destruct H. contradiction. 
	+ apply IHT. 
	- simpl. apply IHT. 
Qed. 

(* Remove an edge from a list of edges *)
Fixpoint remove_edge (e : Edge) (l : list Edge) : list Edge := 
	match l with 
	| nil => nil 
	| x :: t => if E_eq_dec e x then remove_edge e t else x :: (remove_edge e t)
	end. 

(* If we have a edge list with no duplicates, an edge will not show up after being removed *)
Lemma removed_edge_not_in_list : 
    forall (e : Edge) (l : list Edge), 
    ~ E_in e (remove_edge e l).
Proof.
    intros e l. generalize dependent e.
    induction l as [|h T]; intros e H.
    - inversion H.
    - simpl in H. generalize dependent H.
        case (E_eq_dec e h); intros H_eh H.
        + subst. apply (IHT e). assumption.
        + simpl in H. generalize dependent H.
            case (E_eq_dec e h); intros H_eh' H.
            * contradiction.
            * apply (IHT e). assumption.
Qed.

Lemma extract_from_enodup_list : 
	forall (e : Edge) (l : list Edge), 
	ENoDup l -> E_in e l -> exists (l' : list Edge), 
	(forall (y : Edge), E_in y l -> (y = e \/ E_in y l')) /\ ENoDup l'. 
Proof. 

	(* the y = e case -> ~E_in y l'*)
	intros. exists (remove_edge e l). split.  
	- unfold E_in. 

	Admitted. 
(*
	intros. generalize dependent e. induction l.  
	(* e is in an empty list, contra *)
	- intros. unfold E_in in H0. contradiction. 
	- inversion H; subst. intros. 

	specialize (IHl H3).

	(* get all edges besides e *)
	exists (remove_edge (e) (l)). split. 
		+  intros. unfold iff. split. 
			* admit. 
			* intros. destruct H1. 
				-- rewrite <- H1 in H0. apply H0. 
				-- unfold E_in in H1. generalize dependent H1. case (E_eq_dec y a); fold E_in. 
					++ 
					++ intros. fold E_in. unfold  

Admitted. 
*)

Lemma edge_list_lemma : 
	forall (l1 l2 : E_list) (w: (A_set -> nat)), 
	ENoDup l1 -> ENoDup l2 -> 
	(forall x, E_in x l1 -> E_in x l2) -> 
	elist_weight l1 w <= elist_weight l2 w.
Proof. 
	intros l1. induction l1; intros. 

	- simpl. lia. 
	- simpl. 
		inversion H; subst. 
		assert (H_a_in_l2 : E_in a l2). {
			apply H1. unfold E_in. case (E_eq_dec a a). 
			+ intros. apply I. 
			+ intros. specialize (E_refl a). intros. contradiction. 
		}

		destruct (extract_from_enodup_list a l2 H0 H_a_in_l2) as [l2' [l2'_prop l2'_nodup]].
  		destruct a eqn:H_a. subst.      

		assert (H' : w (E_set v v0) + elist_weight l2' w = elist_weight l2 w). admit. 

		rewrite <- H'. 

		assert (Hx : forall x, E_in x l1 -> E_in x l2'). {
            intros x Hx.

            assert (H_x_in_l2 : E_in x (l2)). {
                apply H1. unfold E_in. case (E_eq_dec x (v ~~ v0)).
					- intros. apply I. 
					- intros. fold E_in. apply Hx.  
            }

			apply (l2'_prop x) in H_x_in_l2. destruct H_x_in_l2. 
			- subst. contradiction.
			- apply H2. 
        }

		specialize (IHl1 l2' w H5 l2'_nodup Hx) as H_special. lia.

Admitted.  

Lemma tree_subset_weight_bound : 
	forall {V V' E E'} (T : Tree V E) (T': Tree V' E') w,
	A_included E E' -> st_weight T w <= st_weight T' w.
Proof.
	intros. specialize (tree_edge_subset_implies_list_subset T T') as H_elist_subset.
	specialize (H_elist_subset H).
	specialize (elist_no_dup T) as H_nodup_t.
	specialize (elist_no_dup T') as H_nodup_t'. 
	specialize (edge_list_lemma (TE_list T) (TE_list T') w H_nodup_t H_nodup_t') as H_Elist_lemma.
	specialize (H_Elist_lemma H_elist_subset). 
	
	rewrite -> st_weight_elist_weight_equiv. 
	rewrite -> st_weight_elist_weight_equiv.

	apply H_Elist_lemma. 
Qed. 

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
		(* ... why is this a contradiction? its not? *)
Admitted.


Lemma split_tree_weight_lemma' :
	forall {V E V1 E1 V2 E2 x y}
	(T: Tree V E) (T1 : Tree V1 E1) (T2: Tree V2 E2) w,
	V = (V1 ∪ V2) -> E = (E_set x y ∪ (E1 ∪ E2)) ->
	x ∈ V1 -> y ∈ V2 -> V1 ∩ V2 = ∅ ->
	st_weight T w = st_weight T1 w + st_weight T2 w + w (E_set x y).
Proof.
	intros. subst. apply (split_tree_weight_lemma T T1 T2 w H1 H2 H3).
Qed.


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



Lemma P_inel_inv1 :
	forall V E (x y : Vertex) (vl : V_list) (el : E_list),
	Path V E x y vl el ->
	forall x' y' : Vertex, In (E_ends x' y') el -> V x'.
Proof.
	intros V E x y vl el p; elim p; intros.
	inversion H.

	inversion H0.
	inversion H1.
	subst.
	assumption.
	apply (H _ y'). assumption.
Qed.


Lemma P_inel_inv2 :
	forall V E (x y : Vertex) (vl : V_list) (el : E_list),
	Path V E x y vl el ->
	forall x' y' : Vertex, In (E_ends x' y') el -> V y'.
Proof.
	intros V E x y vl el p; elim p; intros.
	inversion H.

	inversion H0.
	inversion H1.
	subst.
	clear H1. clear H0.
	inversion p0; subst; try solve [assumption].
	apply (H x' _). assumption.
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
		intros n H_Vn H_not_V1n. apply pbc; intros H_not_V2n.
		assert (H_contra : V1 ∪ V2 <> V). {
			apply U_set_diff_commut. apply U_set_diff. exists n. split; try solve [assumption].
			intros H. inversion H; contradiction.
		}
		contradiction.
	}
	assert (H_notV2_V1 : forall n, V n -> ~ V2 n -> V1 n). {
		intros n HVn H_not_V2n. apply pbc; intros H_not_V1n.
		assert (H_contra : V1 ∪ V2 <> V). {
			apply U_set_diff_commut. apply U_set_diff. exists n. split; try solve [assumption].
			intros H. inversion H; contradiction.
		}
		contradiction.
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