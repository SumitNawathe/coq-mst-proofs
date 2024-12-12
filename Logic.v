Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Decidable.



(* Decideability and proof by contradiction *)
Axiom decideability : forall P, decidable P.

Lemma pbc : forall P, (~P -> False) -> P.
Proof.
	intros. destruct (decideability P); solve [assumption | contradiction].
Qed.



(* Implication logic *)

Lemma iff_PnQ_nPQ :
	forall P Q, (P <-> ~Q) -> (~P <-> Q).
Proof.
	intros. split; intros H'. unfold not in *.
	- case (decideability Q); auto. intros HQ. exfalso. apply H'. apply H. assumption.
	- case (decideability P); auto. intros HP. apply H in HP. contradiction.
Qed.

Lemma negate_implication :
	forall T (P Q: T -> Prop), ~ (forall x, P x -> Q x) <-> (exists x, P x /\ ~ Q x).
Proof.
	intros. split; intros H.
	- apply (pbc (exists x : T, P x /\ ~ Q x)); intros H'.
		apply H; intros x H_Px. specialize H'.
		apply (pbc (Q x)); intros HQ.
		apply H'. exists x. split; assumption.
	- intros H'. destruct H as [x [HP HnQ]].
		apply H' in HP. contradiction.
Qed.



(* Conjunction and disjunction with types *)

Reserved Notation "A /|\ B" (at level 80, right associativity).
Inductive tand (A B : Type): Prop :=
	tconj : A -> B -> A /|\ B
where "A /|\ B" := (tand A B).

Reserved Notation "A \|/ B" (at level 80, right associativity).
Inductive tor (A B : Type): Prop :=
	| tor_introl : A -> A \|/ B
	| tor_intror : B -> A \|/ B
where "A \|/ B" := (tor A B).

Lemma and_tand : forall A B, A /\ B -> A /|\ B.
Proof. intros. destruct H. constructor; assumption. Qed.

Lemma or_tor : forall A B, A \/ B -> A \|/ B.
Proof. intros. destruct H; constructor; assumption. Qed.


