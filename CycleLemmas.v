Require Export MST.Trees.
Require Export MST.Connected.
Require Export MST.Sets.
Require Export MST.CustomNotations.
Require Export MST.SetLogic.

Open Scope uset_scope.


Lemma path_uniq_in_acyclic :
	forall V E (G : Acyclic V E) p q vl1 el1 vl2 el2,
	Path V E p q vl1 el1 ->
	Path V E p q vl2 el2 ->
	vl1 = vl2 /\ el1 = el2.
Proof.
	intros V E G p q vl1 el1 vl2 el2 p1 p2.
	(* case (V_eq_dec p q); intros Hpq.
	{
		(* trivial case: p = q => cycles => contradictoin *)
		subst.
		assert (C1 : Cycle _ _ _ _ _ _ p1) by constructor.
		assert (C2 : Cycle _ _ _ _ _ _ p2) by constructor.
		specialize (Acyclic_no_cycle _ _ G _ _ _ _ p1 C1) as Hvl1.
		specialize (Acyclic_no_cycle _ _ G _ _ _ _ p2 C2) as Hvl2.
		subst. inversion p1. inversion p2.
		subst; split; reflexivity.
	} *)
	generalize dependent p2. generalize dependent el2. generalize dependent vl2.
	induction p1 as [q|p y1 q vl1' el1' p1' IHp1 H_Vp H_Epy1 H_pny1
			H_ny2vl1 H_pq1 H_el1] eqn:P1_eq;intros vl2 el2 p2.
	{
		(* p1 degenerate => p2 cycle => contradiction *)
		assert (C: Cycle _ _ _ _ _ _ p2) by constructor.
		specialize (Acyclic_no_cycle _ _ G _ _ _ _ p2 C); intros Hvl2.
		subst. inversion p2; subst; split; reflexivity.
	}
	induction p2 as [q|p y2 q vl2' el2' p2' IHp2 H_Vp' H_Epy2 H_pny2
			H_ny2vl2 H_pq2 H_el2] eqn:P2_eq.
	{
		(* p2 degenerate -> p1 cycle -> contradiction *)
		assert (C: Cycle _ _ _ _ _ _ p1) by constructor.
		specialize (Acyclic_no_cycle _ _ G _ _ _ _ p1 C); intros Hl.
		discriminate.
	}
	case (V_eq_dec p q); intros Hpq.
	{
		(* trivial case: p = q => cycles => contradictoin *)
		subst p.
		assert (C1 : Cycle _ _ _ _ _ _ p1) by constructor.
		assert (C2 : Cycle _ _ _ _ _ _ p2) by constructor.
		specialize (Acyclic_no_cycle _ _ G _ _ _ _ p1 C1) as Hvl1.
		specialize (Acyclic_no_cycle _ _ G _ _ _ _ p2 C2) as Hvl2.
		split; try solve [rewrite Hvl1; rewrite Hvl2; reflexivity].
		clear P2_eq. clear C2. rewrite Hvl2 in p2. inversion p2.
	}
	(* nontrivial case: p <> q *)
	(* p1 : p -> y1 --p1'--> q *)
	(* p2 : p -> y2 --p2'--> q *)
	(* IH: any path from y1 --> q must equal vl1' *)
	specialize (IHp1 p1' eq_refl).
	case (V_eq_dec y1 y2); intros Hy1y2.
			* (* y1 = y2 -> use induction hypothesis *)
				subst. split; f_equal; apply (IHp1 vl2' el2'); assumption.


			* (* y1 <> y2; consider whether y1 in vl2' or not *)
				case (V_in_dec y1 vl2'); intros H_y1_vl2'.
				--	(* y1 in vl2' *)
						admit.
				--	(* y1 not in vl2' => construct y1 -> p -> y2 --> q *)
						admit.
Admitted.
(* To construct the cycle, you need to reverse at least one of the paths *)
(* This will require an enormous amount of infrastructure *)
(* The library has a lemma for reversing walks, nothing on reversing trails or paths *)
