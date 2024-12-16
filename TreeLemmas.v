Require Export MST.Trees.
Require Export MST.Connected.
Require Export MST.Sets.
Require Export MST.CustomNotations.
Require Export MST.SetLogic.
Require Export MST.Cuts.

Open Scope uset_scope.




(* Connected property *)
Theorem connected_prop :
	forall {V E} (G: Graph V E), V <> ∅ ->
	(forall x y, x ∈ V -> y ∈ V -> {vl : V_list &  {el : E_list &  Walk V E x y vl el}}) ->
	Connected V E.
Proof.
	intros V E G. induction G as [| V E G IHG x H_nVx | | ]; intros HV H; subst.
	- unfold V_empty in HV. contradiction.
	- (* case: adding a vertex to a graph *)
		unfold V_union in *; unfold V_single in *.
		destruct (decideable (V = ∅)) as [HV' | HV'].
		+ (* V empty -> graph is singlecon -> singleton connected. *)
			specialize (G_empty_empty V E G HV') as HE.
			subst. unfold A_empty.
			rewrite single_union_empty. constructor.
		+ (* V nonempty -> get new point y <> x *)
			assert (HV'' : V <> ∅) by assumption.
			apply not_empty_iff_exists in HV'. destruct HV' as [y H_Vy].
			assert (H_xy : x <> y) by (intros H_xy; subst; contradiction).
			(* use walk to get an edge from old graph to new vertex *)
			assert (Hx' : x ∈ (⟨x⟩ ∪ V)) by (repeat constructor).
			assert (Hy' : y ∈ (⟨x⟩ ∪ V)) by (constructor 2; assumption).
			(* walk can technically have loop edges -> bad for us *)
			(* convert to path, get next vertex *)
			destruct (H x y Hx' Hy') as [vlw [elw w]].
			specialize (Walk_to_path _ _ _ _ _ _ w) as [vlp [elp p]].
			inversion p; subst; try solve [contradiction].
			(* setup to apply C_leaf *)
			assert (HE' : E = (E_set y0 x) ∪ E). {
				apply U_set_eq; intros e; split; intros H_e.
				- constructor 2; assumption.
				- inversion H_e; subst; try solve [assumption].
					inversion H7; subst.
					+ apply (G_non_directed _ _ G). assumption.
					+ assumption.
			}
			rewrite HE'.
			assert (H_x_y0 : x <> y0). {
				intros H_x_y0. subst y0.
				inversion p; subst. contradiction.
			}
			assert (H_Vy0 : y0 ∈ (⟨x⟩ ∪ V)) by (apply (P_endx_inv _ _ _ _ _ _ H0)).
			assert (H_Vy0' : y0 ∈ V). {
				inversion H_Vy0; subst.
				- inversion H7. contradiction.
				- assumption.
			}

			(* last thing: show Connected V E by IH *)
			assert (C : Connected V E). {
				apply (IHG HV''). intros u v Hu Hv.
				(* for arbitrary u v, must show that we can get a walk *)
			}
			fold V_union. fold A_union. fold V_single.
			apply (C_leaf V E C y0 x H_Vy0' H_nVx).





	- unfold A_union in *.
		+ apply IHG.
			* assumption.
			* 



(* Join connected *)
Lemma join_connected :
	forall {V1 E1} (G2: Connected V1 E1) {V2 E2} (G2 : Connected V2 E2) x y,
	x ∈ V1 -> y ∈ V2 -> Connected (V1 ∪ V2) ((E_set x y) ∪ (E1 ∪ E2)).
Proof.



(* Join cycle free *)



(* Join trees *)



