Require Export MST.Trees.
Require Export MST.Connected.
Require Export MST.Sets.
Require Export MST.CustomNotations.
Require Export MST.Logic.
Require Export MST.SetLogic.

Open Scope uset_scope.


(* Graph vertex list *)

Lemma V_in_graph_list :
	forall {V E} x (G: Graph V E), x ∈ V -> In x (GV_list V E G).
Proof.
	intros V E x G. generalize dependent x. induction G; intros u Hu.
	- inversion Hu.
	- simpl. inversion Hu.
		+ left. subst. inversion H. reflexivity.
		+ right. apply IHG. assumption.
	- simpl. apply IHG. assumption.
	- apply IHG. subst. assumption.
Qed.

Lemma V_in_list_graph :
	forall {V E} x (G: Graph V E), In x (GV_list V E G) -> x ∈ V.
Proof.
	intros V E x G. generalize dependent x. induction G; intros u Hu.
	- inversion Hu.
	- inversion Hu.
		+ subst. repeat constructor.
		+ right. apply IHG. assumption.
	- simpl in Hu. apply IHG. assumption.
	- simpl in Hu. subst. apply IHG. assumption.
Qed.

Theorem V_in_graph_iff_list :
	forall {V E} x (G: Graph V E), x ∈ V <-> In x (GV_list V E G).
Proof. intros. split; [apply V_in_graph_list | apply V_in_list_graph]. Qed.



(* Tree vertex list *)

Fixpoint TV_list {V : V_set} {E : A_set} (T : Tree V E) {struct T} : V_list :=
  match T with
	| T_root r => r :: V_nil
	| T_leaf v e t f n _ _ => f :: TV_list t
	| T_eq v v' a a' _ _ t => TV_list t
  end.

Lemma V_in_tree_list :
	forall {V E} x (T: Tree V E), x ∈ V -> In x (TV_list T).
Proof.
	intros V E x T. generalize dependent x. induction T; intros x Hx.
	- inversion Hx. subst. repeat constructor.
	- inversion Hx.
		+ inversion H. subst. constructor. reflexivity.
		+ subst. constructor 2. apply IHT. assumption.
	- apply IHT. subst. assumption.
Qed.

Lemma V_in_list_tree :
	forall {V E} x (T: Tree V E), In x (TV_list T) -> x ∈ V.
Proof.
	intros V E x T. generalize dependent x. induction T; intros x Hx.
	- inversion Hx.
		+ subst. constructor.
		+ inversion H.
	- inversion Hx.
		+ subst. constructor. constructor.
		+ constructor 2. apply IHT. assumption.
	- simpl TV_list in Hx. subst. apply IHT. assumption.
Qed.

Theorem V_in_tree_iff_list :
	forall {V E} x (T: Tree V E), x ∈ V <-> In x (TV_list T).
Proof. intros. split; [apply V_in_tree_list | apply V_in_list_tree]. Qed.



(* Graph vlist <-> Tree vlist *)

Theorem GV_list_TV_list :
	forall {V E} (G: Graph V E) (T: Tree V E) x, In x (GV_list V E G) <-> In x (TV_list T).
Proof.
	intros. split; intros H.
	- apply V_in_list_graph in H. apply V_in_tree_iff_list. assumption.
	- apply V_in_list_tree in H. apply V_in_graph_iff_list. assumption.
Qed.









(* Graph arc/edge list *)

(* Lemma A_in_graph_list :
	forall {V A} a (G: Graph V A), a ∈ A -> In a (GA_list V A G).
Proof.
	intros V A a G. generalize dependent a. induction G.
	- intros a Ha. inversion Ha.
	- intros arc Harc. simpl. apply IHG. assumption.
	- intros arc Harc. simpl. inversion Harc.
		+ subst. inversion H.
			* left. reflexivity.
			* right. left. reflexivity.
		+ right. right. apply IHG. assumption.
	- intros arc Harc. simpl. apply IHG. subst. assumption.
Qed. *)

Lemma E_in_graph_list :
	forall {V E} x y (G: Graph V E), (x -- y) ∈ E -> E_in (x ~~ y) (GE_list V E G).
Proof.
	intros V E x y G. generalize dependent y. generalize dependent x.
	induction G; intros p q H_pq; simpl in H_pq.
	- inversion H_pq.
	- apply IHG. assumption.
	- simpl. case (E_eq_dec (p ~~ q) (x ~~ y)); intros H.
		+ constructor.
		+ apply IHG. inversion H_pq; subst.
			* inversion H0; subst; exfalso; apply H; constructor.
			* assumption.
	- simpl. apply IHG. subst. assumption.
Qed.

(* Lemma A_in_list_graph :
	forall {V A} a (G: Graph V A), In a (GA_list V A G) -> a ∈ A.
Proof.
	intros V A a G. generalize dependent a.
	induction G; intros arc Harc; simpl in Harc.
	- inversion Harc.
	- apply IHG. assumption.
	- destruct Harc as [Harc | Harc].
		+ constructor. inversion Harc. subst. constructor.
		+ destruct Harc as [Harc | Harc].
			* inversion Harc; subst. constructor. constructor 2.
			* constructor 2. apply IHG. assumption.
	- subst. apply IHG. assumption.
Qed. *)

Lemma E_in_list_graph :
	forall {V E} x y (G: Graph V E), E_in (x ~~ y) (GE_list V E G) -> (x -- y) ∈ E \/ (y -- x) ∈ E.
Proof.
	intros V E x y G. generalize dependent y. generalize dependent x.
	induction G; intros p q H_pq; simpl in H_pq.
	- inversion H_pq.
	- apply IHG. assumption.
	- generalize dependent H_pq. case (E_eq_dec (p ~~ q) (x ~~ y)); intros H_pq H.
		+ inversion H_pq; subst; [left | right]; repeat constructor.
		+ apply IHG in H. inversion H; [left | right]; constructor 2; assumption.
	- subst. apply IHG. assumption.
Qed.

Lemma E_in_symmetry :
	forall x y E_lst, E_in (x ~~ y) E_lst -> E_in (y ~~ x) E_lst.
Proof.
	intros x y E_lst. generalize dependent y. generalize dependent x.
	induction E_lst; intros.
	- contradiction.
	- simpl in H. generalize dependent H. case (E_eq_dec (x ~~ y) a); intros Hxy H.
		+ inversion Hxy; subst; simpl.
			* case (E_eq_dec (y ~~ x) (x ~~ y)); intros Hyx.
				-- constructor.
				-- exfalso. apply Hyx. apply E_rev.
			* case (E_eq_dec (y ~~ x) (y ~~ x)); intros Hyx.
				-- constructor.
				-- exfalso. apply Hyx. constructor.
		+ simpl. case (E_eq_dec (y ~~ x) a); intros Hyx.
			* inversion Hyx; subst; constructor.
			* apply IHE_lst. assumption.
Qed.

(* Lemma A_in_graph_iff_list :
	forall {V A} x y (G: Graph V A), (x -- y) ∈ A <-> In (x -- y) (GA_list V A G).
Proof. intros. split; [apply A_in_graph_list | apply A_in_list_graph]. Qed. *)

Theorem E_in_graph_iff_list :
	forall {V E} x y (G: Graph V E), E_in (x ~~ y) (GE_list V E G) <-> (x -- y) ∈ E \/ (y -- x) ∈ E.
Proof.
	intros. split; intros H.
	- apply E_in_list_graph in H. assumption.
	- destruct H.
		+ apply E_in_graph_list. assumption.
		+ apply E_in_symmetry. apply E_in_graph_list. assumption.
Qed.



(* Tree arc/edge list *)

(* Fixpoint TA_list {V : V_set} {A : A_set} (T : Tree V A) {struct T} : A_list :=
	match T with
		| T_root r => A_nil
		| T_leaf v e t f n _ _ => (n -- f) :: TA_list t
		| T_eq v v' a a' _ _ t => TA_list t
	end. *)

Fixpoint TE_list {V : V_set} {E : A_set} (T : Tree V E) {struct T} : E_list :=
	match T with
		| T_root r => E_nil
		| T_leaf v e t f n _ _ => (n ~~ f) :: TE_list t
		| T_eq v v' a a' _ _ t => TE_list t
	end.

Lemma E_in_tree_list :
	forall {V A} x y (T: Tree V A), (x -- y) ∈ A -> E_in (x ~~ y) (TE_list T).
Proof.
	intros V A x y T. generalize dependent y. generalize dependent x.
	induction T; intros p q H_pq; simpl in H_pq.
	- inversion H_pq.
	- simpl. inversion H_pq; subst.
		+ inversion H; subst.
			* case (E_eq_dec (p ~~ q) (p ~~ q)); intros Hpq.
				-- constructor.
				-- exfalso. apply Hpq. constructor.
			* case (E_eq_dec (p ~~ q) (q ~~ p)); intros Hqp.
				-- constructor.
				-- exfalso. apply Hqp. constructor.
		+ simpl. case (E_eq_dec (p ~~ q) (n ~~ f)); intros H'.
			* constructor.
			* apply IHT. assumption.
	- simpl. subst. apply IHT. assumption.
Qed.

Lemma E_in_list_tree :
	forall {V E} x y (T: Tree V E), E_in (x ~~ y) (TE_list T) -> (x -- y) ∈ E \/ (y -- x) ∈ E.
Proof.
	intros V E x y T. generalize dependent y. generalize dependent x.
	induction T; intros x y Hxy; simpl in Hxy.
	- inversion Hxy.
	- generalize dependent Hxy. case (E_eq_dec (x ~~ y) (n ~~ f)); intros Hxy Hpq.
		+ inversion Hxy; subst; [left | right]; repeat constructor.
		+ apply IHT in Hpq. destruct Hpq as [Hpq | Hpq]; [left | right]; constructor 2; assumption.
	- subst. apply IHT in Hxy. assumption.
Qed.

Theorem E_in_tree_iff_list :
	forall {V E} x y (T: Tree V E), E_in (x ~~ y) (TE_list T) <-> (x -- y) ∈ E \/ (y -- x) ∈ E.
Proof.
	intros. split; intros H.
	- apply E_in_list_tree in H. assumption.
	- destruct H.
		+ apply E_in_tree_list. assumption.
		+ apply E_in_symmetry. apply E_in_tree_list. assumption.
Qed.



(* Graph elist <-> Tree elist *)

Theorem GE_list_TE_list :
	forall {V E} (G: Graph V E) (T: Tree V E) e, E_in e (GE_list V E G) <-> E_in e (TE_list T).
Proof.
	intros. split; intros H.
	- destruct e. apply E_in_graph_iff_list in H. apply E_in_tree_iff_list. assumption.
	- destruct e. apply E_in_tree_iff_list in H. apply E_in_graph_iff_list. assumption.
Qed.









(* Graph order facts *)

Remark order_empty_graph :
	forall (G : Graph V_empty A_empty), G_order V_empty A_empty G = 0.
Proof.
	intros.
	remember V_empty as V. remember A_empty as A. induction G; subst.
	- unfold G_order. unfold GV_list; fold GV_list. reflexivity.
	- exfalso. inversion HeqV.
		assert (nHeqv : ⟨x⟩ ∪ v <> ∅). {
			apply U_set_diff. exists x. split.
			- repeat constructor.
			- intros H. inversion H.
		}
		contradiction.
	- exfalso. inversion HeqA.
		assert (nHeqa : (E_set x y) ∪ a <> ∅). {
			apply U_set_diff. exists (x -- y). split.
			- repeat constructor.
			- intros H. inversion H.
		}
		contradiction.
	- unfold G_order. unfold GV_list; fold GV_list.
		apply IHG; reflexivity.
Qed.

Remark order_singleton_graph :
	forall r A (G : Graph ⟨r⟩ A), G_order ⟨r⟩ A G = 1.
Proof.
	intros. remember ⟨r⟩ as V. generalize dependent r. induction G; intros.
	- exfalso.
		assert (nHeqV : V_empty <> ⟨r⟩). {
			apply U_set_diff_commut. apply U_set_diff. exists r.
			split. - constructor. - intros H. inversion H.
		}
		contradiction.
	- assert (H_rx : r = x). {
			assert (H_x : x ∈ (⟨x⟩ ∪ v)) by repeat constructor.
			unfold V_union in HeqV. unfold V_single in HeqV.
			rewrite HeqV in H_x. inversion H_x. reflexivity.
		}
		subst. unfold G_order. unfold GV_list; fold GV_list. simpl. apply f_equal.
		unfold V_union in *. unfold V_single in *.
		assert (H_v : v = ∅) by (apply (union_single_without_means_empty _ v x); assumption). subst.
		assert (H_a : a = ∅). {
			eapply G_empty_empty.
			- apply G.
			- reflexivity.
		}
		subst. apply order_empty_graph.
	- subst. unfold G_order. unfold GV_list; fold GV_list. simpl. apply (IHG r). reflexivity.
	- subst. unfold G_order. unfold GV_list; fold GV_list. simpl. apply (IHG r). reflexivity.
Qed.

Lemma graph_order_add_vert :
	forall V E (G : Graph V E) x (H_nVx : x ∉ V),
	1 + (G_order _ _ G) = G_order _ E (G_vertex V E G x H_nVx).
Proof.
	intros. unfold G_order. unfold GV_list; fold GV_list. f_equal. reflexivity.
Qed.

Lemma graph_order_add_edge :
	forall V E (G : Graph V E) x y (H_Vx : x ∈ V) (H_Vy : y ∈ V)
	(H_xny : x <> y) (H_Vxy : (x -- y) ∉ E) (H_Eyx : (y -- x) ∉ E),
	G_order _ _ G = G_order _ _ (G_edge V E G x y H_Vx H_Vy H_xny H_Vxy H_Eyx).
Proof.
	intros. unfold G_order. unfold GV_list; fold GV_list. reflexivity.
Qed.



(* Tree order and length *)

Definition T_order {V E} (T : Tree V E) := length (TV_list T).

Remark order_singleton_tree :
	forall r, T_order (T_root r) = 1.
Proof. intros. reflexivity. Qed.

Definition T_size {V E} (T : Tree V E) := length (TE_list T).

Remark size_singleton_tree :
	forall r, T_size (T_root r) = 0.
Proof. intros. reflexivity. Qed.

Theorem tree_order_size_rel :
	forall {V E} (T : Tree V E), T_order T = 1 + T_size T.
Proof.
	intros. induction T.
	- reflexivity.
	- unfold T_order. unfold TV_list; fold (TV_list T). simpl. fold (T_order T).
		unfold T_size. unfold TE_list; fold (TE_list T). simpl. fold (T_size T).
		f_equal. assumption.
	- unfold T_order. unfold TV_list; fold (TV_list T). simpl. fold (T_order T).
		unfold T_size. unfold TE_list; fold (TE_list T). simpl. fold (T_size T).
		f_equal. assumption.
Qed.



(* Theorem tree_paths :
	forall {V: V_set} {E: A_set} (T: Tree V E) x y,
	x ∈ V -> y ∈ V -> exists (vl : V_list) (el : E_list) (p : Path V E x y vl el), True.
Proof.
	Abort. *)



