Require Export Coq.Init.Specif.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Export MST.Graphs.
Require Export MST.Edges.
Require Export MST.Vertices.
Require Export MST.Trees.
Require Export MST.Connected.
Require Export MST.Sets.
Require Export MST.CustomNotations.
Require Export MST.Cuts.

Open Scope uset_scope.


(* Vertex/Edge lists *)

Fixpoint TV_list {V : V_set} {E : A_set} (T : Tree V E) {struct T} : V_list :=
  match T with
	| T_root r => r :: V_nil
	| T_leaf v e t f n _ _ => f :: TV_list t
	| T_eq v v' a a' _ _ t => TV_list t
  end.

Lemma V_in_tree_union_single :
	forall V E x (T: Tree (⟨x⟩ ∪ V) E), In x (TV_list T).
Proof.
	intros. remember (⟨x⟩ ∪ V) as V' eqn:HV'.
	generalize dependent V. generalize dependent x.
	induction T; intros; unfold V_union in *; unfold V_single in *.
	- (* x must be the root *)
		simpl. left.
		case (decideable (r = x)); intros H_r_neq_x; try solve [assumption].
		specialize (V_eq_set (⟨x⟩ ∪ V) (V_single r)) as H2.
		assert (H3 : forall x0, x0 ∈ (⟨x⟩ ∪ V)  -> V_single r x0) by auto.
		assert (Hx: x ∈ (⟨x⟩ ∪ V)) by (repeat constructor).
		apply (H3 x) in Hx. inversion Hx. trivial.
	- (* either x is the new node added or not *)
		case (decideable (x = f)); intros H_xf.
		+ left. auto.
		+ simpl. right.
			assert (H_x_in_v : x ∈ v). {
				apply pbc; intros H_xv. symmetry in HV'.
				specialize (V_eq_set (⟨x⟩ ∪ V) (⟨f⟩ ∪ v)) as H'.
				assert (H'': forall x0, x0 ∈ (⟨x⟩ ∪ V) -> x0 ∈ (⟨f⟩ ∪ v)) by auto.
				assert (Hx : x ∈ (⟨x⟩ ∪ V)) by (repeat constructor).
				apply (H'' x) in Hx. apply V_union_single_dec in Hx.
				- inversion Hx; intuition.
				- assumption.
			}
			apply IHT with (x := x) (V := (v \ ⟨f⟩)). simpl.
			apply V_set_eq. intros y. split; intros Hy.
			* case (decideable (y = x)); intros H_xy; try solve [subst; repeat constructor].
				case (decideable (y = f)); intros H_fy.
				-- subst. contradiction.
				-- constructor 2. constructor.
					++ assumption.
					++ intros H_fy'. inversion H_fy'. intuition.
			* inversion Hy; inversion H; subst; assumption.
	- (* equality case *)
		subst. apply (IHT x V). reflexivity.
Qed.

Lemma tv_gv_list :
	forall {V: V_set }{E: A_set} (G: Graph V E) (T : Tree V E) x,
	In x (GV_list V E G) <-> In x (@TV_list V E T).
Proof.
	intros. split.
	- generalize dependent T. generalize dependent x.
		induction G as [|V' E' G' IHG' x' H_v'x'|V' E' G' IHG' u v Hu Hv Hvu H_E'1 H_E'2
				|V' V'' E' E'' H_Vs H_Es H_G']; intros x T H.
		+ inversion H.
		+ unfold V_union in *; unfold V_single in *.
			apply (pbc (In x (TV_list T))); intros HT.
			case (decideable (x = x')); intros H_xx'.
			* subst. apply HT. apply V_in_tree_union_single.
			* inversion H; try solve [intuition].
				Abort.




Theorem tree_paths :
	forall {V: V_set} {E: A_set} (T: Tree V E) x y,
	x ∈ V -> y ∈ V -> exists (vl : V_list) (el : E_list), Path V E x y vl el.



