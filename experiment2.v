Require Import List.
Import ListNotations.
Require Import Coq.Logic.FinFun.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Vectors.Fin.

Axioms decideability: forall (P: Prop), P \/ ~ P.

Section OrdinalFiniteType.

Variable n : nat.

Record ordinal := {
	val :> nat;
	_ : val < n;
}.

Lemma ltn_ord (i : ordinal) : i < n.
Proof. destruct i as [vali vali_lt_n]. assumption. Qed.

Definition nat_of_ord (i: ordinal) : nat := i.(val).

Lemma ord_inj : Injective nat_of_ord.
Proof. Admitted.

End OrdinalFiniteType.




Notation "''I_' n" := (ordinal n)
  (at level 8, n at level 2, format "''I_' n").


Hint Resolve ltn_ord : core.


Definition rel {n: nat} := 'I_n -> 'I_n -> option nat.
Definition Symmetric {n: nat} (E: @rel n) : Prop :=
	forall x y, E x y = E y x.
Definition Irreflexive {n: nat} (E: @rel n) : Prop :=
	forall x, E x x = None.

Record Graph := {
	n: nat;
	E : @rel n;
	_ : Symmetric E;
	_ : Irreflexive E;
}.

Notation "x ~ y ! E" := ((E x y) <> None) (at level 30).



Inductive edge_seq {G: Graph} : 'I_G.(n) -> list 'I_G.(n) -> Prop :=
	| edge_seq_nil : forall i, edge_seq i []
	| edge_seq_cons : forall i j t, i ~ j ! G.(E) -> edge_seq j t -> edge_seq i (j::t)
.

Search "uniq".

Definition walk {G: Graph} x y p := @edge_seq G x p /\ last p x = y.
Definition path {G: Graph} x y p := @walk G x y p /\ NoDup (x::p).



Lemma H_cons_to_app : forall (A: Type) (h: A) (t: list A), h::t = [h] ++ t.
Proof. intros A h t. simpl. reflexivity. Qed.

Inductive tail_subset {X : Type} : list X -> list X -> Prop :=
	| tail_subset_constructor : forall l t, tail_subset l (t ++ l)
.

Lemma tail_subset_can_take_beginning :
	forall (X : Type) (l1 l2 t : list X), tail_subset l1 l2 -> tail_subset l1 (t ++ l2).
Proof.
	intros X l1 l2 t. destruct t as [|h t']; intros H.
	- assumption.
	- inversion H; subst. rewrite app_assoc. constructor.
Qed.


Lemma in_means_tail_subset_without {X: Type} :
	forall (x: X) (l: list X), List.In x l -> exists l', tail_subset (x::l') l /\ ~ List.In x l'.
Proof.
	intros x l. generalize dependent x.
	induction l as [|h t]; intros x H_x_in_l.
	- inversion H_x_in_l.
	- inversion H_x_in_l as [Hhx | H_x_in_t]; clear H_x_in_l.
		+ subst. destruct (decideability (List.In x t)).
			* apply (IHt x) in H as [l' [H1 H2]]. exists l'. split.
				-- rewrite (H_cons_to_app X x t). apply tail_subset_can_take_beginning. assumption.
				-- assumption.
			* exists t. split; [rewrite <- app_nil_l; constructor | assumption].
		+ apply (IHt x) in H_x_in_t as [l' [H1 H2]]. exists l'. split.
			* rewrite (H_cons_to_app X h t). apply tail_subset_can_take_beginning. assumption.
			* assumption.
Qed.

Lemma app_equals_nil : forall (X: Type) (l1 l2: list X), l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
Proof.
	intros X l1 l2 H.
	destruct l1 as [|h1 t1]; destruct l2 as [|h2 t2].
	- split; reflexivity.
	- split.
		+ reflexivity.
		+ simpl in H; discriminate.
	- simpl in H; discriminate.
	- simpl in H; discriminate.
Qed.

Lemma no_nonempty_tail_of_empty : forall (X: Type) (h: X) (t: list X), ~ tail_subset (h::t) [].
Proof.
	intros X h t H.
	remember (h::t) as l1. remember [] as l2. induction H.
	rewrite Heql1 in Heql2. apply app_equals_nil in Heql2 as [H1 H2]. discriminate.
Qed.

Lemma extract_inner_seq :
	forall G x l h t, @edge_seq G x (l ++ h::t) -> @edge_seq G h t.
Proof.
	intros G. intros x l. generalize dependent x.
	induction l as [|x' l']; intros x h t H.
	- inversion H. assumption.
	- simpl in H. inversion H.
		apply (IHl' x' h). assumption.
Qed.


Lemma tail_edge_seq_lemma : forall (G: Graph) x p p',
	@edge_seq G x p -> tail_subset (x::p') p -> @edge_seq G x p'.
Proof.
	intros G x p p' Hxp H_ts.
	remember (x::p') as a. remember p as b. induction H_ts. subst.
	generalize dependent x. induction t as [|h t']; intros x Hxp.
	- simpl in Hxp. inversion Hxp; subst. assumption.
	- apply extract_inner_seq with (x := x) (l := h::t'). assumption.
Qed.

Lemma last_app_nonempty_second :
	forall X (d: X) l h t, last (l ++ h::t) d = last (h::t) d.
Proof.
	Admitted.


(* https://stackoverflow.com/questions/45872719/how-to-do-induction-on-the-length-of-a-list-in-coq *)
Require Import Lia.

Section list_length_ind.  
  Variable A : Type.
  Variable P : list A -> Prop.

  Hypothesis H : forall xs, (forall l, length l < length xs -> P l) -> P xs.

  Theorem list_length_ind : forall xs, P xs.
  Proof.
    assert (forall xs l : list A, length l <= length xs -> P l) as H_ind.
    { induction xs; intros l Hlen; apply H; intros l0 H0.
      - inversion Hlen. lia.
      - apply IHxs. simpl in Hlen. lia.
    }
    intros xs.
    apply H_ind with (xs := xs).
    lia.
  Qed.
End list_length_ind.

Lemma tail_preserves_last :
	forall (X : Type) (x y : X) (p p' : list X), last p x = y -> tail_subset (x::p') p -> last p' x = y.
Proof. Admitted.

Lemma strict_tail_subset_smaller :
	forall (X : Type) (h : X) (t l : list X), tail_subset (h::t) l -> length t < length l.
Proof. Admitted.

Lemma path_is_smallest_walk :
	forall (G: Graph) x y p, @path G x y p -> forall p', @walk G x y p' -> length p' <= length p.
Proof. Admitted.


Lemma walk_to_path:
	forall (G: Graph) x y p, @walk G x y p -> exists (p': list 'I_G.(n)), @path G x y p'.
Proof.
	intros G x y p.
	induction p using list_length_ind; intros Hwalk.
	destruct (decideability (NoDup (x::p))).
	- exists p. unfold path. split; assumption.
	- destruct Hwalk as [H_xp H_last].
		Search "NoDup".
	(* Failure *)


	(* One idea to try: follow this proof:
	https://math.stackexchange.com/questions/2182917/i-know-every-path-is-a-walk-but-how-do-i-prove-the-following-question
	to do this, set up some infrastructure to extract a loop from a path
	then use the induction principle above *)



	destruct (decideability (List.In x p)) as [H_x_in_p | H_x_not_in_p].
	- destruct (in_means_tail_subset_without x p H_x_in_p) as [p' [H1 H2]].
		exists p'. unfold path. split.
		+ unfold walk. split.
			* apply (tail_edge_seq_lemma G x p p').
				-- destruct Hwalk as [H' _]. assumption.
				-- assumption.
			* destruct Hwalk as [_ H'].
				apply (tail_preserves_last _ x y p p'); assumption.
		+ assert (H_lens : length p' < length p). {
				apply (strict_tail_subset_smaller _ x p' p). assumption.
			}
			apply H in H_lens.
			* destruct H_lens as [p'' ]



Lemma last_app_nonempty_second :
	forall X (d: X) l h t, last (l ++ h::t) d = last (h::t) d.
Proof.
	Admitted.





Lemma walk_to_path:
	forall (G: Graph) x y p, @walk G x y p -> exists (p': list 'I_G.(n)), @path G x y p'.
Proof.
	intros G x y p Hwalk.
	destruct (decideability (List.In x p)).
	- destruct (in_means_tail_subset_without x p H) as [p' [H1 H2]].
		generalize dependent y. generalize dependent x. induction p' as [|h t]; intros x H H1 H2 y Hwalk.
		+ exists []. unfold path. split.
			* 
		+ exists []. unfold path. split; [assumption | constructor; [inversion H | constructor]].
		+ exists (h::t). unfold path. split.
			* unfold walk. split; unfold walk in Hwalk;
				destruct Hwalk as [H_edge_seq_x_p last_p_x_is_y]; assumption.
			* 
		
		
		destruct (in_means_tail_subset_without x p H) as [p' [H1 H2]].
		exists p'. unfold path. split.
		+ unfold walk. split.
			* unfold walk in Hwalk; destruct Hwalk as [H_edge_seq_x_p last_p_x_is_y].
				apply (tail_edge_seq_lemma G x p p'); assumption.
			* unfold walk in Hwalk; destruct Hwalk as [H_edge_seq_x_p last_p_x_is_y].
				inversion H1; subst.
				rewrite last_app_nonempty_second.
				destruct p' as [|h' t']; reflexivity.
		+ 







	intros G x y p Hwalk.
	destruct (decideability (List.In x p)).
	- destruct (in_means_tail_subset_without x p H) as [p' [H1 H2]].
		exists p'. unfold path. split.
		+ unfold walk. split.
			* unfold walk in Hwalk; destruct Hwalk as [H_edge_seq_x_p last_p_x_is_y].
				apply (tail_edge_seq_lemma G x p p'); assumption.
			* unfold walk in Hwalk; destruct Hwalk as [H_edge_seq_x_p last_p_x_is_y].
				inversion H1; subst.
				rewrite last_app_nonempty_second.
				destruct p' as [|h' t']; reflexivity.
		+ 

					 
					




			* destruct p' as [|h t].
				-- constructor.
				-- inversion H1.






























Inductive tail_subset {X : Type} : list X -> list X -> Prop :=
	| equal_lists : forall l, tail_subset l l
	| append_head: forall l l' t, tail_subset l l' -> tail_subset l (t ++ l')
.

(* Lemma in_means_tail_subset {X: Type} : forall (x: X) (l: list X), List.In x l -> exists l', tail_subset (x::l') l.
Proof.
	assert (H_cons_to_app : forall (A: Type) (h: A) (t: list A), h::t = [h] ++ t). {
		intros A h t. simpl. reflexivity.
	}
	intros x l. generalize dependent x.
	induction l as [|h t]; intros x H_x_in_l.
	- inversion H_x_in_l.
	- inversion H_x_in_l as [Hhx | H_x_in_t].
		+ rewrite Hhx. exists t.
			rewrite <- app_nil_l. rewrite <- app_nil_l at 1. constructor.
		+ apply (IHt x) in H_x_in_t as [l' H]. exists l'.
			rewrite (H_cons_to_app X h t). constructor. assumption.
Qed. *)

Lemma H_cons_to_app : forall (A: Type) (h: A) (t: list A), h::t = [h] ++ t.
Proof. intros A h t. simpl. reflexivity. Qed.

Lemma in_means_tail_subset_without {X: Type} :
	forall (x: X) (l: list X), List.In x l -> exists l', tail_subset (x::l') l /\ ~ List.In x l'.
Proof.
	intros x l. generalize dependent x.
	induction l as [|h t]; intros x H_x_in_l.
	- inversion H_x_in_l.
	- inversion H_x_in_l as [Hhx | H_x_in_t]; clear H_x_in_l.
		+ subst. destruct (decideability (List.In x t)).
			* apply (IHt x) in H as [l' [H1 H2]]. exists l'. split.
				-- rewrite (H_cons_to_app X x t). constructor. assumption.
				-- assumption.
			* exists t. split; [constructor | assumption].
		+ apply (IHt x) in H_x_in_t as [l' [H1 H2]]. exists l'. split.
			* rewrite (H_cons_to_app X h t). constructor. assumption.
			* assumption.
Qed.

Lemma app_equals_nil : forall (X: Type) (l1 l2: list X), l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
Proof.
	intros X l1 l2 H.
	destruct l1 as [|h1 t1]; destruct l2 as [|h2 t2].
	- split; reflexivity.
	- split.
		+ reflexivity.
		+ simpl in H; discriminate.
	- simpl in H; discriminate.
	- simpl in H; discriminate.
Qed.

Lemma no_nonempty_tail_of_empty : forall (X: Type) (h: X) (t: list X), ~ tail_subset (h::t) [].
Proof.
	intros X h t H.
	remember (h::t) as l1.
	remember [] as l2.
	induction H.
	- rewrite Heql2 in Heql1. discriminate.
	- apply IHtail_subset.
		+ assumption.
		+ apply app_equals_nil in Heql2 as [H1' H2']. assumption.
Qed.


Lemma tail_edge_seq_lemma : forall (G: Graph) x p p',
	@edge_seq G x p -> tail_subset (x::p') p -> @edge_seq G x p'.
Proof.
	intros G x p p' Hxp.
	generalize dependent p'.
	induction Hxp; intros p' H_ts.
	- exfalso. apply no_nonempty_tail_of_empty in H_ts. assumption.
	- 
	remember (x::p') as a. remember p as b. induction H_ts; subst.
	- inversion Hxp. assumption.
	- 


	intros G x p p'. generalize dependent p'. generalize dependent x.
	induction p as [|h t]; intros x p' Hxp H_ts.
	- exfalso. apply no_nonempty_tail_of_empty in H_ts. assumption.
	- inversion Hxp; subst; clear Hxp.



	intros G x p p'. generalize dependent p. generalize dependent x.
	induction p' as [|h t]; intros x p Hxp H_ts.
	- constructor.
	- constructor.
		+ inversion H_ts; subst; clear H_ts.
			* inversion Hxp; subst; clear Hxp.
				inversion H3; subst; clear H3.
				assumption.
			* inversion Hxp; subst; clear Hxp.



Lemma walk_to_path:
	forall (G: Graph) x y p, @walk G x y p -> exists (p': list 'I_G.(n)), @path G x y p'.
Proof.
	intros G x y p Hwalk.
	destruct (decideability (List.In x p)).
	- destruct (in_means_tail_subset_without x p H) as [p' [H1 H2]].
		exists p'. unfold path. split.
		+ unfold walk. split.
			* unfold walk in Hwalk; destruct Hwalk as [H_edge_seq_x_p last_p_x_is_y].
				destruct p' as [|h t].
				-- constructor.
				-- inversion H1; subst; clear H1.
					++ rewrite (H_cons_to_app _ x (h::t)) in H_edge_seq_x_p.
						 inversion H_edge_seq_x_p; subst; clear H_edge_seq_x_p. assumption.
					++ 




			* destruct p' as [|h t].
				-- constructor.
				-- inversion H1.

Lemma simple_edge_seq {V: finType} {E: rel V} {G: WeightedEdgeRel V E} :
	forall x p, @edge_seq V E G x p -> exists p', @edge_seq V E G x p' /\ NoDup (x::p') /\ tail_subset p' p.
Proof.
	inversion G as [symE irreflE].
	intros x p. generalize dependent x. induction p as [|h t]; intros x H.
	- exists []. split; repeat (constructor; auto).
	- destruct t as [|x' t'].
		+ exists [h]. split; try solve [assumption].
			inversion H; subst; clear H. constructor.
			* simpl. intros Hhx'; inversion Hhx' as [Hhx|]; try solve [assumption]; clear Hhx'.
				assert (E x h = None). { rewrite Hhx. apply irreflE. }
				rewrite H in H3. solve [contradiction].
			* constructor; auto. constructor.
		+ 





Lemma walk_to_path:
	forall (G: Graph) x y p, @walk G x y p -> exists (p': list 'I_G.(n)), @path G x y p.
Proof.


