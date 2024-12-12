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

Lemma V_in_graph_iff_list :
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

Lemma V_in_tree_iff_list :
	forall {V E} x (T: Tree V E), x ∈ V <-> In x (TV_list T).
Proof. intros. split; [apply V_in_tree_list | apply V_in_list_tree]. Qed.



(* Graph vlist = Tree vlist *)

Lemma GV_list_TV_list :
	forall {V E} (G: Graph V E) (T: Tree V E) x, In x (GV_list V E G) <-> In x (TV_list T).
Proof.
	intros. split; intros H.
	- apply V_in_list_graph in H. apply V_in_tree_iff_list. assumption.
	- apply V_in_list_tree in H. apply V_in_graph_iff_list. assumption.
Qed.









(* Graph edge list *)

Lemma E_in_graph_list :
	forall {V E} {x y} (G: Graph V E), (x -- y) ∈ E -> In (x -- y) (GA_list V E G).
Proof.
	intros V E x y G. generalize dependent y. generalize dependent x. induction G.
	- intros x y Hxy. inversion Hxy.
	- 






Theorem tree_paths :
	forall {V: V_set} {E: A_set} (T: Tree V E) x y,
	x ∈ V -> y ∈ V -> exists (vl : V_list) (el : E_list), Path V E x y vl el.



