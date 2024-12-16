Require Export Coq.Init.Specif.
Require Export MST.Graphs.
Require Export MST.Edges.
Require Export MST.Vertices.
Require Export MST.Trees.
Require Export MST.Connected.
Require Export MST.Sets.
Require Export MST.CustomNotations.
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

Definition is_spanning_tree {V V' : V_set} {E E' : A_set} (T : Tree V' E') (G : Graph V E) : Prop := 
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
	{u & {v & edge_crossing_cut G A u v}}.
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
	  	case (set_in_dec h A); intros H_Ah.
	  + apply H_VA in H_Ah as H_Vh.
	  	apply (IHt h H_Ah H_Vh y H_Vy H_not_Ay el0 H1).
		+ exists x. exists h.
			unfold edge_crossing_cut; intros H_A_nontrivial.
			split; try split; assumption.
Qed.

Lemma find_crossing_edge_on_walk :
    forall {V E} (G: Graph V E) A x z vl el,
    nontrivial_cut G A -> x ∈ A -> z ∉ A -> Walk V E x z vl el ->
		{u & {v & edge_crossing_cut G A u v &
		{vl1 & {el1 & {vl2 & {el2 & Walk V E x u vl1 el1 & Walk V E v z vl2 el2}}}}}}.
Proof.
	intros V E G A x z vl. generalize dependent z. generalize dependent x.
	induction vl as [|h t]; intros x z el H_A_nontrivial H_Ax H_nAz H_walk;
	inversion H_walk; subst; try solve [contradiction].
	case (set_in_dec h A); [intros H_Ah | intros H_nAh].
	- (* h ∈ A -> cross in later part of walk *)
		specialize (IHt h z el0 H_A_nontrivial H_Ah H_nAz H1) as H.
		inversion H as [u [v H_cross [vl1 [el1 [vl2 [el2 H_walk1 H_walk2]]]]]].
		exists u. exists v; try solve [assumption].
		exists (h::vl1). exists ((x ~~ h)::el1).
		exists vl2. exists el2; try solve [simpl; f_equal; assumption].
		constructor 2; solve [assumption].
	- (* h ∉ A -> x -- h is the cross *)
		exists x. exists h.
		+ constructor.
			* assumption.
			* split; assumption.
		+ exists nil. exists nil. exists t. exists el0.
			* constructor. assumption.
			* assumption.
Qed.

Lemma find_crossing_edge_on_walk' :
    forall {V E} (G: Graph V E) A x z vl el,
    nontrivial_cut G A -> x ∈ A -> z ∉ A -> Walk V E x z vl el ->
		{u & {v & (edge_crossing_cut G A u v /\ In (u~~v) el) &
		{vl1 & {el1 & {vl2 & {el2 & Walk V E x u vl1 el1 & Walk V E v z vl2 el2}}}}}}.
Proof.
	intros V E G A x z vl. generalize dependent z. generalize dependent x.
	induction vl as [|h t]; intros x z el H_A_nontrivial H_Ax H_nAz H_walk;
	inversion H_walk; subst; try solve [contradiction].
	case (set_in_dec h A); [intros H_Ah | intros H_nAh].
	- (* h ∈ A -> cross in later part of walk *)
		specialize (IHt h z el0 H_A_nontrivial H_Ah H_nAz H1) as H.
		inversion H as [u [v H_cross [vl1 [el1 [vl2 [el2 H_walk1 H_walk2]]]]]].
		exists u. exists v.
		+ destruct H_cross. split.
			* assumption.
			* apply in_cons. assumption.
		+	exists (h::vl1). exists ((x ~~ h)::el1).
			exists vl2. exists el2; try solve [simpl; f_equal; assumption].
			constructor 2; solve [assumption].
	- (* h ∉ A -> x -- h is the cross *)
		exists x. exists h.
		+ split.
			* constructor.
				-- assumption.
				-- split; assumption.
			* left. reflexivity.
		+ exists nil. exists nil. exists t. exists el0.
			* constructor. assumption.
			* assumption.
Qed.

Lemma find_crossing_edge_on_path :
	forall {V E} (G: Graph V E) A x z vl el,
	nontrivial_cut G A -> x ∈ A -> z ∉ A -> Path V E x z vl el ->
	{u & {v & (edge_crossing_cut G A u v /\ In (u~~v) el) &
	{vl1 & {el1 & {vl2 & {el2 & vl = vl1 ++ v :: vl2 & el = el1 ++ el2}}}}}}.
Proof.
	intros V E G A x z vl. generalize dependent z. generalize dependent x.
	induction vl as [|h t]; intros x z el H_A_nontrivial H_Ax H_nAz H_path.
	{ inversion H_path; subst; try solve [contradiction]. }
	case (set_in_dec h A); [intros H_Ah | intros H_nAh].
	- (* h ∈ A -> cross in later part of walk *)
		inversion H_path; subst.
		specialize (IHt h z el0 H_A_nontrivial H_Ah H_nAz H1) as H.
		inversion H as [u [v H_cross [vl1 [el1 [vl2 [el2 vl_prop el_prop]]]]]].
		exists u. exists v.
		+ destruct H_cross. split.
			* assumption.
			* apply in_cons. assumption.
		+	exists (h::vl1). exists ((x ~~ h)::el1).
			exists vl2. exists el2; try solve [simpl; f_equal; assumption].
	- (* h ∉ A -> x -- h is the cross *)
		exists x. exists h.
		+ split.
			* constructor.
				-- inversion H_path. assumption.
				-- split; assumption.
			* inversion H_path. left. reflexivity.
		+ exists nil. exists nil. exists t. exists el.
			* constructor.
			* inversion H_path. simpl. reflexivity.
Qed.

Lemma find_crossing_edge_on_path' :
	forall {V E} (G: Graph V E) A x z vl el,
	nontrivial_cut G A -> x ∈ A -> z ∉ A -> Path V E x z vl el ->
	{u & {v & (edge_crossing_cut G A u v /\ In (u~~v) el) &
	{vl1 & {el1 & {vl2 & {el2 &
	{p1 : Path V E x u vl1 el1 & {p2 : Path V E v z vl2 el2 & vl = vl1 ++ v :: vl2 & el = el1 ++ (u~~v)::el2
	}}}}}}}}.
Proof.
	intros V E G A x z vl. generalize dependent z. generalize dependent x.
	induction vl as [|h t]; intros x z el H_A_nontrivial H_Ax H_nAz H_path.
	{ inversion H_path; subst; try solve [contradiction]. }
	case (set_in_dec h A); [intros H_Ah | intros H_nAh].
	- (* h ∈ A -> cross in later part of walk *)
		inversion H_path; subst.
		specialize (IHt h z el0 H_A_nontrivial H_Ah H_nAz H1) as H.
		inversion H as [u [v H_cross [vl1 [el1 [vl2 [el2 [p1 [p2 vl_prop el_prop]]]]]]]].
		exists u. exists v.
		+ destruct H_cross. split.
			* assumption.
			* apply in_cons. assumption.
		+	exists (h::vl1). exists ((x ~~ h)::el1).
			exists vl2. exists el2; try solve [simpl; f_equal; assumption].
			assert (H_h_notin_vl1 : ~ In h vl1). {
				intros H_h_vl1.
				assert (H_h_in_t : In h t) by (subst; apply in_or_app; left; assumption).
				contradiction.
			}
			assert (H_x_vl1_bad : In x vl1 -> x = u). {
				intros H_x_vl1.
				assert (H_x_in_t : In x t) by (subst; apply in_or_app; left; assumption).
				apply H8 in H_x_in_t. subst.
				contradiction.
			}
			assert (H_edges_bad : forall u, In u el1 -> ~ E_eq u (x~~h)). {
				intros k Hk.
				assert (H_k_in_el0 : In k el0) by (subst; apply in_or_app; left; assumption).
				apply H10. assumption.
			}
			specialize (P_step V E x h u vl1 el1 p1 H2 H3 H4 H_h_notin_vl1 H_x_vl1_bad H_edges_bad) as P1.
			exists P1. exists p2. simpl. f_equal. assumption. simpl. f_equal. assumption.
	- (* h ∉ A -> x -- h is the cross *)
		exists x. exists h.
		+ split.
			* constructor.
				-- inversion H_path. assumption.
				-- split; assumption.
			* inversion H_path. left. reflexivity.

		+ exists nil. exists nil.
			inversion H_path; subst. exists t. exists el0. constructor.
			* constructor. destruct H_A_nontrivial. apply H. assumption.
			* exists H1. simpl. reflexivity. simpl. reflexivity.
Qed.



Lemma find_first_crossing_edge_on_path :
	forall {V E} (G: Graph V E) A x z vl el,
	nontrivial_cut G A -> x ∈ A -> z ∉ A -> Path V E x z vl el ->
	{u & {v & (edge_crossing_cut G A u v /\ In (u~~v) el) &
	{vl1 & {el1 & {vl2 & {el2 &
	{p1 : Path A E x u vl1 el1 & {p2 : Path V E v z vl2 el2 & vl = vl1 ++ v :: vl2 & el = el1 ++ (u~~v)::el2
	}}}}}}}}.
Proof.
	intros V E G A x z vl. generalize dependent z. generalize dependent x.
	induction vl as [|h t]; intros x z el H_A_nontrivial H_Ax H_nAz H_path.
	{ inversion H_path; subst; try solve [contradiction]. }
	case (set_in_dec h A); [intros H_Ah | intros H_nAh].
	- (* h ∈ A -> cross in later part of walk *)
		inversion H_path; subst.
		specialize (IHt h z el0 H_A_nontrivial H_Ah H_nAz H1) as H.
		inversion H as [u [v H_cross [vl1 [el1 [vl2 [el2 [p1 [p2 vl_prop el_prop]]]]]]]].
		exists u. exists v.
		+ destruct H_cross. split.
			* assumption.
			* apply in_cons. assumption.
		+	exists (h::vl1). exists ((x ~~ h)::el1).
			exists vl2. exists el2; try solve [simpl; f_equal; assumption].
			assert (H_h_notin_vl1 : ~ In h vl1). {
				intros H_h_vl1.
				assert (H_h_in_t : In h t) by (subst; apply in_or_app; left; assumption).
				contradiction.
			}
			assert (H_x_vl1_bad : In x vl1 -> x = u). {
				intros H_x_vl1.
				assert (H_x_in_t : In x t) by (subst; apply in_or_app; left; assumption).
				apply H8 in H_x_in_t. subst.
				contradiction.
			}
			assert (H_edges_bad : forall u, In u el1 -> ~ E_eq u (x~~h)). {
				intros k Hk.
				assert (H_k_in_el0 : In k el0) by (subst; apply in_or_app; left; assumption).
				apply H10. assumption.
			}
			specialize (P_step A E x h u vl1 el1 p1 H_Ax H3 H4 H_h_notin_vl1 H_x_vl1_bad H_edges_bad) as P1.
			exists P1. exists p2. simpl. f_equal. assumption. simpl. f_equal. assumption.
	- (* h ∉ A -> x -- h is the cross *)
		exists x. exists h.
		+ split.
			* constructor.
				-- inversion H_path. assumption.
				-- split; assumption.
			* inversion H_path. left. reflexivity.

		+ exists nil. exists nil.
			inversion H_path; subst. exists t. exists el0. constructor.
			* constructor. destruct H_A_nontrivial. apply H_Ax.
			* exists H1. simpl. reflexivity. simpl. reflexivity.
Qed.



(* 
Lemma Path_append :
 forall V E (x y z : Vertex) (vl vl' : V_list) (el el' : E_list),
 Path V E x y vl el -> Path V E y z vl' el' ->
 (x = y -> vl = nil) -> (y = z -> vl' = nil) ->
 (forall v, In v vl -> In v vl' -> False) ->
 Path V E x z (vl ++ vl') (el ++ el').
Proof.
	intros V E x y z vl vl' el el' Hp; induction Hp eqn:P; simpl; intros; try solve [assumption].
	apply P_step; try solve [assumption].
	- apply (IHp p eq_refl).
		+ assumption.
		+ intros H_yz0. subst.
			inversion p; subst; try solve [reflexivity].
			exfalso.
			assert (H_obv : (y::vl0) <> V_nil) by discriminate.
			specialize (P_iny_vl _ _ _ _ _ _ p H_obv) as H'.
			contradiction.
		+ intros H_z0z. subst.
			apply H1. reflexivity.
		+ intros m Hm1 Hm2.
			apply (H2 m).
			* right. assumption.
			* assumption.
	- intros H'. apply in_app_or in H'. destruct H'.
		+ contradiction.
		+ apply (H2 y).
			* left. reflexivity.
			* assumption.
	- intros H'. apply in_app_or in H'. destruct H'.
		+ assert (Hx : In x vl) by assumption.
			apply e in H3. subst.
			assert (Hz0 : y = z0 \/ In z0 vl) by (right; assumption).
			specialize (H2 z0). apply H2 in Hz0.
			* destruct Hz0.
			* assert (Hz0' : z0 = z0) by reflexivity.
				apply H0 in Hz0'. discriminate.
		+ case (V_in_dec x vl); intros H_xvl;
				try solve [exfalso; apply (H2 x); [right; assumption | assumption]].
			case (V_eq_dec x z0); intros H_xz0;
				try solve [apply H0 in H_xz0; discriminate].
			assert (H_obv : (y::vl) <> V_nil) by discriminate.
			specialize (P_iny_vl _ _ _ _ _ _ Hp H_obv) as H'.
			destruct H'.
			* subst z0.
				inversion p.
				-- subst.
Admitted.
 *)

(* 
Lemma Path_reverse :
 forall V E (x y : Vertex) (vl : V_list) (el : E_list),
 Path V E x y vl el -> Path V E y x (cdr (rev (x :: vl))) (E_reverse el).
Proof. Admitted.
 *)

Lemma diff_diff_incl :
	forall T (A B : U_set T),
	(A \ (A \ B)) ⊆ A.
Proof.
	intros. intros x Hx.
	inversion Hx; subst. assumption.
Qed.







Lemma find_last_crossing_edge_on_path :
	forall {V E} (G: Graph V E) A x z vl el,
	nontrivial_cut G A -> x ∈ A -> z ∉ A -> Path V E x z vl el ->
	{u & {v & (edge_crossing_cut G A u v /\ In (u~~v) el) &
	{vl1 & {el1 & {vl2 & {el2 &
	{p1 : Path V E x u vl1 el1 & {p2 : Path (V\A) E v z vl2 el2 & vl = vl1 ++ v :: vl2 & el = el1 ++ (u~~v)::el2
	}}}}}}}}.
Proof.
	intros V E G A x z vl. generalize dependent z. generalize dependent x.
	induction vl as [|h t]; intros x z el H_A_nontrivial H_Ax H_nAz H_path.
	{ inversion H_path; subst; try solve [contradiction]. }
	case (set_in_dec h A); [intros H_Ah | intros H_nAh].
	- (* h ∈ A -> cross in later part of walk *)
		inversion H_path; subst.
		specialize (IHt h z el0 H_A_nontrivial H_Ah H_nAz H1) as H.
		inversion H as [u [v H_cross [vl1 [el1 [vl2 [el2 [p1 [p2 vl_prop el_prop]]]]]]]].
		exists u. exists v.
		+ destruct H_cross. split.
			* assumption.
			* apply in_cons. assumption.
		+	exists (h::vl1). exists ((x ~~ h)::el1).
			exists vl2. exists el2; try solve [simpl; f_equal; assumption].
			assert (H_h_notin_vl1 : ~ In h vl1). {
				intros H_h_vl1.
				assert (H_h_in_t : In h t) by (subst; apply in_or_app; left; assumption).
				contradiction.
			}
			assert (H_x_vl1_bad : In x vl1 -> x = u). {
				intros H_x_vl1.
				assert (H_x_in_t : In x t) by (subst; apply in_or_app; left; assumption).
				apply H8 in H_x_in_t. subst.
				contradiction.
			}
			assert (H_edges_bad : forall u, In u el1 -> ~ E_eq u (x~~h)). {
				intros k Hk.
				assert (H_k_in_el0 : In k el0) by (subst; apply in_or_app; left; assumption).
				apply H10. assumption.
			}
			specialize (P_step V E x h u vl1 el1 p1 H2 H3 H4 H_h_notin_vl1 H_x_vl1_bad H_edges_bad) as P1.
			exists P1. exists p2. simpl. f_equal. assumption. simpl. f_equal. assumption.
	- (* h ∉ A -> x -- h is the cross *)
		exists x. exists h.
		+ split.
			* constructor.
				-- inversion H_path. assumption.
				-- split; assumption.
			* inversion H_path. left. reflexivity.

		+ exists nil. exists nil.
			inversion H_path; subst. exists t. exists el0. constructor.
			* constructor. destruct H_A_nontrivial. apply H. assumption.
			* admit.
			(* * exists H1. simpl. reflexivity. simpl. reflexivity. *)
Admitted.









(* Edges crossing cut with a tree *)

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


Lemma nontrivial_cut_transfer :
	forall {V E E'} (G : Graph V E) (G' : Graph V E') A,
	nontrivial_cut G A -> nontrivial_cut G' A.
Proof.
	intros V E E' G G' A H_A_nontriv.
	unfold nontrivial_cut in *.
	destruct H_A_nontriv as [H_AV H_A_nontriv].
	split; solve [assumption].
Qed.


Theorem tree_has_edge_crossing_cut :
	forall {V GE E} (G : Graph V GE) (T: Tree V E) A, E ⊆ GE -> nontrivial_cut G A ->
	{x: Vertex & {y: Vertex & (x -- y) ∈ E /\ edge_crossing_cut G A x y}}.
Proof.
	intros V GE E G T A H_E_GE H_A_nontriv.
	specialize (Tree_isa_connected _ _ T) as Tcon.
	specialize (Tree_isa_graph _ _ T) as GT.
	specialize (nontrivial_cut_transfer G GT A H_A_nontriv) as H_A_nontriv'.
	(* nontrivial cut => get points inside and outside *)
	specialize (nontrivial_cut_point_inside _ _ GT A H_A_nontriv) as [x H_Ax].
	specialize (nontrivial_cut_point_outside _ _ GT A H_A_nontriv) as [y H_Vy H_not_Ay].
	(* connected => walk between points => crossing edge *)
	assert (H_A_nontriv'' : nontrivial_cut GT A) by assumption.
	destruct H_A_nontriv' as [H_AV H_A_nontriv'].
	assert (H_Vx : x ∈ V) by (apply H_AV; assumption).
	specialize (Connected_walk _ _ Tcon x y H_Vx H_Vy) as [vl [el H_walk]].
	assert (H_V_subset_V : V ⊆ V) by (apply self_inclusion).
	specialize (find_crossing_edge_on_walk GT A x y vl el H_A_nontriv'' H_Ax H_not_Ay H_walk) as H.
	destruct (find_crossing_edge_on_walk GT A x y vl el H_A_nontriv'' H_Ax H_not_Ay H_walk) as
		[u [v edge_crossing_uv _]].
	exists u. exists v. split.
	- unfold edge_crossing_cut in edge_crossing_uv. apply edge_crossing_uv in H_A_nontriv''.
		destruct H_A_nontriv''. assumption.
	- unfold edge_crossing_cut. intros H_A_nontriv_repeat.
		split; unfold edge_crossing_cut in edge_crossing_uv;
				apply edge_crossing_uv in H_A_nontriv''; destruct H_A_nontriv''.
		+ apply H_E_GE. assumption.
		+ assumption.
Qed.




Theorem tree_edge_crossing_cut_unique :
	forall {V GE E} (G : Graph V GE) (T: Tree V E) A, nontrivial_cut G A ->
	forall x y u v, edge_crossing_cut G A x y -> edge_crossing_cut G A u v ->
	x = u /\ y = v.
Proof. Admitted.



Theorem tree_edge_crossing_cut_unique' :
	forall {V GE E} (G : Graph V GE) (T: Tree V E) A, nontrivial_cut G A ->
	forall x y u v vl el, Walk V E x y vl el -> In (u~~v) el -> 
	edge_crossing_cut G A x y -> edge_crossing_cut G A u v ->
	(x--y) ∈ E ->	x = u /\ y = v.
Proof. Admitted.


