Require Export MST.Trees.
Require Export MST.Connected.
Require Export MST.Sets.
Require Export MST.CustomNotations.
Require Export MST.Logic.
Require Export MST.SetLogic.

Open Scope uset_scope.

Lemma V_extract_not_in :
	forall x vl, ~ In x (V_extract x vl).
Proof.
	intros x vl. generalize dependent x. induction vl as [|h t]; intros x H.
	- inversion H.
	- simpl in H.
		case (V_in_dec x t) as [H_xt | H_xt]; specialize (IHt x); contradiction.
Qed.




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
















(* 

Lemma path_uniq_in_acyclic :
	forall V E (G : Acyclic V E) p q vl1 el1 vl2 el2,
	Path V E p q vl1 el1 ->
	Path V E p q vl2 el2 ->
	vl1 = vl2 /\ el1 = el2.
Proof.
	intros V E G p q vl1 el1 vl2 el2 p1.
	generalize dependent el2. generalize dependent vl2.
	induction p1 as [q|p y1 q vl1' el1' p1' IHp1 H_Vp H_Epy1 H_pny1
			H_ny2vl1 H_pq1 H_el1] eqn:P1_eq;intros vl2 el2 p2.
	- (* p1 degenerate => p2 cycle => contradiction *)
		assert (C: Cycle _ _ _ _ _ _ p2) by constructor.
		specialize (Acyclic_no_cycle _ _ G _ _ _ _ p2 C); intros Hvl2.
		subst. inversion p2; subst; split; reflexivity.
	- induction p2 as [q|p y2 q vl2' el2' p2' IHp2 H_Vp' H_Epy2 H_pny2
				H_ny2vl2 H_pq2 H_el2] eqn:P2_eq.
		+ (* p2 degenerate -> p1 cycle -> contradiction *)
			assert (C: Cycle _ _ _ _ _ _ p1) by constructor.
			specialize (Acyclic_no_cycle _ _ G _ _ _ _ p1 C); intros Hl.
			discriminate.
		+ (* p1 : p -> y1 --p1'--> q *)
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
			* (* y1 <> y2; consider whether y2 in vl1' or not *)
				case (V_in_dec y2 vl1'); intros H_y2_vl1'.
				--	(* y2 in vl1' -> extract path p3: p -> y1 --> y2 *)
						assert (H_y2_in_vl1 : In y2 (p :: y1 :: vl1')) by (right; right; assumption).
						destruct (P_extract _ _ _ _ _ _ _ p1 H_y2_in_vl1) as [el3 p3].
						(* TODO *)
						(* this doesnt work, currently makes path from p2 --> q *)
						(* we need a mechanism to reverse paths *)
						remember (V_extract y2 (p :: y1 :: vl1')) as vl3.
						specialize (V_extract_not_in y2 (p::y1::vl1')) as H_y2_notin_vl3.
						rewrite <- Heqvl3 in H_y2_notin_vl3.
						(* specialize (P_step V E p y2 p (y2::vl3) ((p~~y2)::el3) p3) as p_p_p. *)
						(* p -> y1 --> y2 --> p is a cycle *)
Abort.
 *)



	(* intros V E G p q vl1 el1 vl2 el2 p1.
	generalize dependent el2. generalize dependent vl2.
	induction p1 eqn:P'; intros vl2 el2 p2.
	- (* p1 degenerate -> p2 cycle -> contradiction *)
		assert (C: Cycle _ _ _ _ _ _ p2) by constructor.
		specialize (Acyclic_no_cycle _ _ G _ _ _ _ p2 C); intros Hvl2.
		subst. inversion p2; subst; split; reflexivity.
	- inversion p2.
		+ (* p2 degenerate -> p1 cycle -> contradiction *)
			subst z.
			assert (C: Cycle _ _ _ _ _ _ p1) by constructor.
			specialize (Acyclic_no_cycle _ _ G _ _ _ _ p1 C); intros Hl.
			discriminate.
		+ (* p1 : x -> y --vl--> z *)
			(* p2 : x -> y0 --vl0--> z *)
			(* IH: any path from y --> z must equal vl *)
			specialize (IHp0 p0 eq_refl). subst.
			case (V_eq_dec y y0); intros Hyy0.
			* (* y = y0 -> use induction hypothesis *)
				subst. split; f_equal; apply (IHp0 vl0 el0); assumption.
			* (* y <> y0; consider whether y in vl or not *)
				case (V_in_dec y0 vl); intros H_y0_vl.
				--	(* y0 in vl -> extract path y --> y0, extent y0 -- x -> cycle *)
						admit.
				--	(* y0 not in vl -> make path y -> x -> y0 --> z *)
						(* by IH, must be equal to vl -> x in vl -> contradiction *)
						admit.
Admitted. *)
			
