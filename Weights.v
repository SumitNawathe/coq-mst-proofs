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

Lemma E_eq_trans :
	forall {a b c}, E_eq a b -> E_eq b c -> E_eq a c.
Proof.
	intros a b c H1 H2. destruct a, b, c.
	inversion H1; inversion H2; subst; constructor.
Qed.

Lemma E_eq_sym :
	forall a b, E_eq a b -> E_eq b a.
Proof.
	intros a b H. destruct a, b. inversion H; subst; constructor.
Qed.

Lemma subset_after_removing_except_removed :
	forall e r l,
	E_in e l -> ~ E_eq e r -> E_in e (remove_edge r l).
Proof.
	intros e r l. generalize dependent r. induction l as [|h t]; intros r He Her.
	- inversion He.
	- generalize dependent He.
		unfold E_in. case (E_eq_dec e h); fold E_in; intros H_eh He.
		+ unfold remove_edge. case (E_eq_dec r h); intros H_rh; fold remove_edge.
			* apply E_eq_sym in H_eh.
				specialize (E_eq_trans H_rh H_eh) as Hre'.
				apply E_eq_sym in Hre'. contradiction.
			* unfold E_in. generalize dependent H_eh.
				case (E_eq_dec e h); intros Edec H_eh'; fold E_in; try solve [contradiction]. constructor.
		+ unfold remove_edge.
			case (E_eq_dec r h); intros H_rh; fold remove_edge; try solve [contradiction].
			* apply IHt; assumption.
			* unfold E_in. case (E_eq_dec e h); intros Edec; fold E_in; try solve [contradiction].
				apply IHt; assumption.
Qed.

Lemma in_after_removal :
	forall {e r l}, E_in e (remove_edge r l) -> E_in e l.
Proof.
	intros e r l. generalize dependent e. induction l as [|h t]; intros e H_in_rem.
	- inversion H_in_rem.
	- generalize dependent H_in_rem.
		unfold remove_edge. case (E_eq_dec r h); intros H_rh; fold remove_edge; intros H_x.
		+ unfold E_in; case (E_eq_dec e h); intros H_eh; fold E_in; try solve [constructor].
			apply IHt; assumption.
		+ generalize dependent H_x. unfold E_in.
			case (E_eq_dec e h); intros H_eh; fold E_in; try solve [constructor].
			apply IHt; assumption.
Qed.

Lemma remove_preserves_nodup :
	forall r l, ENoDup l -> ENoDup (remove_edge r l).
Proof.
	intros r l. induction l as [|h t]; intros H_nodup_l.
	- simpl. constructor.
	- unfold remove_edge. case (E_eq_dec r h); intros H_rh; fold remove_edge.
		+ inversion H_nodup_l. apply IHt; assumption.
		+ constructor.
			* inversion H_nodup_l; subst.
				intros H_h_rem.
				apply (in_after_removal) in H_h_rem. contradiction.
			* apply IHt. inversion H_nodup_l; assumption.
Qed.

Lemma eq_in_equiv :
	forall {x y l}, E_eq x y -> E_in x l -> E_in y l.
Proof.
	intros x y l. induction l as [|h t]; intros H_eq H_in.
	- inversion H_in.
	- generalize dependent H_in.
		unfold E_in. case (E_eq_dec x h); intros H_xh; fold E_in; intros H_in;
		case (E_eq_dec y h); intros H_yh; fold E_in; try solve [constructor].
		+ apply E_eq_sym in H_eq.
			specialize (E_eq_trans H_eq H_xh) as H_yh'.
			contradiction.
		+ apply IHt; assumption.
Qed.


Lemma extract_from_enodup_list : 
	forall (e : Edge) (l : list Edge), 
	ENoDup l -> E_in e l -> exists (l' : list Edge), 
	(forall (y : Edge), E_in y l <-> (E_eq y e \/ E_in y l')) /\ ENoDup l' /\ ~ E_in e l'. 
Proof.
	intros e l. generalize dependent e.
	induction l as [|h t]; intros e H_nodup_l H_e_in_l.
	- exists nil. split.
		+ intros y. split.
			* intros Hy. inversion Hy.
			* inversion H_e_in_l.
		+ split; inversion H_e_in_l.
	- simpl in H_e_in_l. generalize dependent H_e_in_l.
		case (E_eq_dec e h); intros H_eh H_e_in_l.
		+ exists (remove_edge e t). split.
			* intros y. split.
				-- 	intros Hy. simpl in Hy.
						generalize dependent Hy.
						case (E_eq_dec y h); intros H_yh Hyt.
					++ 	apply E_eq_sym in H_yh.
							left. apply E_eq_sym. apply (E_eq_trans H_eh H_yh).
					++ 	right.
							assert (H_ye : ~ E_eq y e). {
								intros H_ye.
								specialize (E_eq_trans H_ye H_eh) as H_yh'.
								contradiction.
							}
							apply (subset_after_removing_except_removed _ _ _ Hyt H_ye).
				-- 	intros Hy. destruct Hy as [Hy | Hy].
					++	specialize (E_eq_trans Hy H_eh) as H_yh.
							unfold E_in.
							case (E_eq_dec y h); intros H_yh'; fold E_in; try solve [contradiction].
							constructor.
					++ 	unfold E_in. case (E_eq_dec y h); intros H_yh; fold E_in; try solve [constructor].
							apply (in_after_removal Hy).
			* inversion H_nodup_l; subst. split.
				--  apply remove_preserves_nodup; assumption.
				--  apply removed_edge_not_in_list.
		+ exists (h::(remove_edge e t)). split.
			* intros y. split.
				-- 	intros Hy. simpl in Hy.
						generalize dependent Hy. simpl.
						case (E_eq_dec y h); intros H_yh Hyt.
						++ 	right. assumption.
						++ 	case (E_eq_dec y e); intros H_ye.
							** 	left. assumption.
							** 	right. apply (subset_after_removing_except_removed _ _ _ Hyt H_ye).
				--  intros Hy. destruct Hy.
					++ 	simpl. case (E_eq_dec y h); intros H_yh; fold E_in; try solve [constructor].
							apply E_eq_sym in H. apply (eq_in_equiv H H_e_in_l).
					++  generalize dependent H.
							unfold E_in. case (E_eq_dec y h); fold E_in; intros H_yh H; try solve [constructor].
							apply (in_after_removal H).
			* split.
				-- 	constructor.
					++ 	intros H_bad. apply (in_after_removal) in H_bad.
							inversion H_nodup_l. contradiction.
					++ 	inversion H_nodup_l. apply remove_preserves_nodup; assumption.
				-- 	intros H. generalize dependent H.
						unfold E_in. case (E_eq_dec e h); intros H_eh'; fold E_in; intros H; try solve [contradiction].
						assert (H_contra : ~ E_in e (remove_edge e t)) by apply removed_edge_not_in_list.
						contradiction.
Qed.

Lemma E_eq_flip :
	forall x y u v, E_eq (x~~y) (u~~v) -> E_eq (y~~x) (u~~v).
Proof.
	intros x y u v H. inversion H; subst; constructor.
Qed.

Lemma Ein_sym :
	forall x y l, E_in (x~~y) l -> E_in (y~~x) l.
Proof.
	intros x y. induction l as [|h t]; intros H.
	- inversion H.
	- destruct h as [u v].
		generalize dependent H. unfold E_in.
		case (E_eq_dec (x~~y) (u~~v)); fold E_in; intros Hdec H.
		+ case (E_eq_dec (y~~x) (u~~v)); intros Hdec'.
			* constructor.
			* apply E_eq_flip in Hdec. contradiction.
		+ case (E_eq_dec (y~~x) (u~~v)); intros Hdec'.
			* constructor.
			* apply IHt. assumption.
Qed.


Lemma edge_list_lemma : 
	forall (l1 l2 : E_list) (w: (A_set -> nat)), 
	ENoDup l1 -> ENoDup l2 -> 
	(forall x, E_in x l1 -> E_in x l2) -> 
	elist_weight l1 w <= elist_weight l2 w.
Proof.
	intros l1. induction l1 as [|h t]; intros l2 w H_nodup_1 H_nodup_2 H_incl; try solve [simpl; lia].
	assert (H_h_in_l2: E_in h l2). {
		apply H_incl. simpl. case (E_eq_dec h h); intros H.
		- constructor.
		- exfalso. apply H.  constructor.
	}
	destruct (extract_from_enodup_list h l2 H_nodup_2 H_h_in_l2) as [l2' [l2'_prop l2'_nodup]].
	destruct h as [x y]; subst.
	assert (H' : w (E_set x y) + elist_weight l2' w = elist_weight l2 w) by admit.
	simpl. rewrite <- H'. 
	assert (Hq : forall x, E_in x t -> E_in x l2'). {
		intros q Hq.
		assert (H_q_in_l2 : E_in q (l2)). {
			apply H_incl. unfold E_in. case (E_eq_dec q (x~~y)).
		- intros. apply I. 
		- intros. fold E_in. apply Hq.  
		}
		apply (l2'_prop q) in H_q_in_l2. destruct H_q_in_l2. 
		- exfalso. inversion H; subst.
			+ inversion H_nodup_1. contradiction.
			+ inversion H_nodup_1. subst.
				apply Ein_sym in Hq. contradiction.
		- assumption.
	}
	inversion H_nodup_1; subst.
	destruct l2'_nodup.
	specialize (IHt l2' w H2 H Hq) as H_special.
	lia.
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
