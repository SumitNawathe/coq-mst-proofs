Require Export MST.Sets.
Require Export MST.CustomNotations.



(* 
For our proofs, we are assuming that all sets are finite;
that is, there is some finite superset containing all sets we are working with.
We are mainly working with sets of vertices and edges; for both of those, equality is decideable.
Thus, the following relations on finite sets should be decideable
*)

(* This axiom is primarily used exclusively Cuts.v *)
Axiom set_in_dec : forall {T} (x : T) (A : U_set T), {x ∈ A} + {x ∉ A}.
(* The following two are used once, in subset_but_not_equal in this file *)
Axiom set_subset_dec : forall {T} (A B : U_set T), {A ⊆ B} + {A ⊄ B}.
Axiom set_eq_dec : forall {T} (A B : U_set T), {A = B} + {A <> B}.

(* Utlities *)

Lemma not_Single_not_equal :
	forall (T : Set) (x y : T), y ∉ ⟨x⟩ -> x <> y.
Proof.
	intros. unfold not; intros H_xy.
	rewrite H_xy in H. apply H. constructor.
Qed.



(* Lemmas about inclusion *)

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

Lemma subset_of_each_other :
	forall {T} (A B : U_set T), A = B <-> (A ⊆ B /\ B ⊆ A).
Proof.
	intros. split; intros H.
	- split; unfold Included; intros x H';
			[rewrite H in H' | rewrite <- H in H']; assumption.
	- destruct H as [H_AB H_BA]. apply U_set_eq; intros x; split; intros H';
			[apply H_AB | apply H_BA]; assumption.
Qed.

Lemma union_included1 :
	forall {T} {A B C : U_set T}, A ∪ B ⊆ C -> A ⊆ C.
Proof. intros. intros a Ha. apply H. left. assumption. Qed.

Lemma union_included2 :
	forall {T} {A B C : U_set T}, A ∪ B ⊆ C -> B ⊆ C.
Proof. intros. intros a Ha. apply H. right. assumption. Qed.



(* Lemmas about Empty *)

Lemma empty_iff_not_exists :
	forall T (A: U_set T), A = ∅ <-> ~ (exists x : T, A x).
Proof.
	intros. split; intros H.
	- intros [x H_Ax]. rewrite H in H_Ax. inversion H_Ax.
	- apply U_set_eq; intros x; split; intros H'.
		+ exfalso. apply H. exists x. assumption.
		+ inversion H'.
Qed.

Lemma not_empty_iff_exists :
	forall T (A: U_set T), A <> ∅ -> {x : T & A x}.
Proof. Admitted.
(* logically (mathematically) equivalent to the previous lemma,
but not sure it is provable in the current system;
probably needs to be an axiom *)

Lemma single_union_empty :
	forall T (x : T), ⟨x⟩ ∪ ∅ = ⟨x⟩.
Proof.
	intros. apply U_set_eq. intros y. split; intros H.
	- inversion H; [assumption | contradiction].
	- constructor; assumption.
Qed.



(* Finding points in subsets *)

Lemma not_empty_or_included :
	forall {T} (A B : U_set T), B <> ∅ -> B ⊄ A -> {x & x ∈ B & x ∉ A}.
Proof. Admitted.
(* This is also probably an axiom, not sure its provable within the current system,
but it is true for finite sets *)

Lemma subset_but_not_equal :
	forall T (A B : U_set T), A ⊆ B -> A <> B -> {x & x ∈ B & x ∉ A}.
Proof.
	intros T A B H_AB H_A_neq_B.
	case (set_eq_dec B (∅)); intros HB.
	- subst. specialize (subset_empty_is_empty A H_AB) as HA.
		subst. contradiction.
	- case (set_subset_dec B A); intros H_BA.
		+ exfalso. apply H_A_neq_B. apply (subset_of_each_other A B). split; assumption.
		+ apply not_empty_or_included; assumption.
Qed.

