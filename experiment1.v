Require Import List.
Import ListNotations.
Require Import Coq.Logic.FinFun.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Vectors.Fin.
From mathcomp Require Import ssrbool.
From mathcomp Require Import fintype.



Definition rel (V: finType) := V -> V -> option nat.

Definition Symmetric {V: finType} (E: rel V) : Prop :=
	forall x y, E x y = E y x.

Definition Irreflexive {V: finType} (E: rel V) : Prop :=
	forall x, E x x = None. 

Inductive WeightedEdgeRel (V: finType) (E: rel V) :=
	| EdgeRelConstructor :
			Symmetric E ->
			Irreflexive E ->
			WeightedEdgeRel V E
.

Notation "x ~ y ! E" := ((E x y) <> None) (at level 30).

Inductive edge_seq {V: finType} {E: rel V} {G: WeightedEdgeRel V E} : V -> list V -> Prop :=
	| edge_seq_empty : forall x, edge_seq x []
	| edge_seq_nonempty : forall (x h: V) (t: list V), x ~ h ! E -> edge_seq h t -> edge_seq x (h::t)
.

Inductive path {V: finType} {E: rel V} {G: WeightedEdgeRel V E} : V -> V -> list V -> Prop :=
	| path_constructor : forall (x y: V) (p: list V), @edge_seq V E G x p -> last p x = y -> path x y p.

Inductive simple_path {V: finType} {E: rel V} {G: WeightedEdgeRel V E} : V -> V -> list V -> Prop :=
	| simple_path_constructor : forall x y p, @path V E G x y p -> NoDup (x::p) -> simple_path x y p.

Inductive tail_subset {X : Type} : list X -> list X -> Prop :=
	| empty_is_tail_subset: forall l, tail_subset [] l
	| tails_agree: forall l l' t, tail_subset l l' -> tail_subset (l ++ t) (l' ++ t)
.

Lemma in_means_tail_subset {X: Type} : forall (x: X) (l: list X), List.In x l -> exists l', tail_subset (x::l') l.
Proof.
	assert (H_cons_to_app : forall (A: Type) (h: A) (t: list A), h::t = [h] ++ t). {
		intros A h t. simpl. reflexivity.
	}
	intros x l. generalize dependent x.
	induction l as [|h t]; intros x H_x_in_l.
	- inversion H_x_in_l.
	- inversion H_x_in_l as [Hhx | H_x_in_t].
		+ rewrite Hhx. exists t.
			rewrite <- app_nil_l. rewrite <- app_nil_l at 1. constructor. constructor.
		+ apply (IHt x) in H_x_in_t. destruct H_x_in_t as [l' H]. exists l'.
			rewrite <- app_nil_l at 1. rewrite (H_cons_to_app X h t). 

Lemma simple_edge_seq {V: finType} {E: rel V} {G: WeightedEdgeRel V E} :
	forall x p, @edge_seq V E G x p -> exists p', @edge_seq V E G x p' /\ NoDup (x::p') /\ tail_subset p' p.
Proof.
	inversion G as [symE irreflE].
	intros x p. generalize dependent x. induction p as [|h t]; intros x H.
	- exists []. split; repeat (constructor; auto).
	- destruct t as [|x' t'].
		+ exists [h]. split; try solve [assumption].
			inversion H; subst; clear H. constructor.
			* simpl; intros Hhx'; inversion Hhx' as [Hhx|]; try solve [assumption]; clear Hhx'.
				assert (E x h = None). { rewrite Hhx. apply irreflE. }
				rewrite H in H3. solve [contradiction].
			* constructor; auto. constructor.
		+ 

Lemma path_to_simple_path {V: finType} {E: rel V} {G: WeightedEdgeRel V E} :
	forall x y p, @path V E G x y p -> exists p', @simple_path V E G x y p'.
Proof.


	(* WRONG *)
	intros x p. generalize dependent x.
	induction p as [|h t]; intros x H.
	- exists []. constructor. constructor; auto. apply NoDup_nil.
	-  inversion H; subst; clear H.
		apply (IHt h) in H4. inversion H4 as [p']; subst; clear H4.
		exists p'. constructor. apply NoDup_cons.
		+ inversion H; subst; clear H. inversion H0; subst; clear H0.
		+ inversion H. inversion H0. assumption.



Inductive path {V: finType} {E: rel V} {G: WeightedEdgeRel V E}: V -> V -> list V -> Prop :=
	| path_single : forall x: V, path x x [].
	| path_multi : forall (x y: V) (t: list V),
			x -E- y -> 
			


Check [1]. 

