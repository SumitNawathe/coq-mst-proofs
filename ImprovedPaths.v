Require Export MST.CustomNotations.
Require Export MST.Paths.



Lemma lift_walk :
	forall {V E x y vl el V' E'}, V ⊆ V' -> E ⊆ E' -> Walk V E x y vl el -> Walk V' E' x y vl el.
Proof.
	intros. induction H1.
	- constructor. apply H. assumption.
	- constructor.
		+ assumption.
		+ apply H. assumption.
		+ apply H0. assumption.
Qed.





Lemma P_inel_inv1 :
	forall V E (x y : Vertex) (vl : V_list) (el : E_list),
	Path V E x y vl el ->
	forall x' y' : Vertex, In (E_ends x' y') el -> V x'.
Proof.
	intros V E x y vl el p; elim p; intros.
	inversion H.

	inversion H0.
	inversion H1.
	subst.
	assumption.
	apply (H _ y'). assumption.
Qed.


Lemma P_inel_inv2 :
	forall V E (x y : Vertex) (vl : V_list) (el : E_list),
	Path V E x y vl el ->
	forall x' y' : Vertex, In (E_ends x' y') el -> V y'.
Proof.
	intros V E x y vl el p; elim p; intros.
	inversion H.

	inversion H0.
	inversion H1.
	subst.
	clear H1. clear H0.
	inversion p0; subst; try solve [assumption].
	apply (H x' _). assumption.
Qed.










Lemma P_eq_edges_eq :
	forall {V E x y z vl el1 el2},
	Path V E x y vl el1 -> Path V E x z vl el2 -> el1 = el2.
Proof.
	intros V E x y z vl. generalize dependent y. generalize dependent x.
	induction vl as [|h t]; intros x y el1 el2 p1 p2.
	- inversion p1. inversion p2. subst. reflexivity.
	- destruct el1 as [|el1h el1t]; inversion p1; subst.
		destruct el2 as [|el2h el2t]; inversion p2; subst.
		f_equal.
		apply (IHt _ _ _ _ H3 H6).
Qed.


Lemma P_extract' :
 forall V E(x y z : Vertex) (vl : V_list) (el : E_list),
 Path V E y z vl el ->
 In x (y :: vl) ->
 {el' : E_list & Path V E x z (V_extract x (y :: vl)) el' & (forall e, In e el' -> In e el)}.
Proof.
	intros V E x y z vl. generalize dependent y.
	induction vl as [|h t]; intros y el p Hx.
	- exists nil.
		+ assert (Hxy : x = y). {
				inversion Hx; auto. inversion H.
			}
			subst. unfold V_extract.
			case (V_in_dec y nil); intros H_y; try solve [inversion H_y].
			inversion p; subst. constructor. assumption.
		+ intros e He. inversion He.
	- specialize (IHt) as H'.
		elim (P_backstep _ _ _ _ _ _ _ p); intros.
		unfold V_extract.
		case (V_in_dec x (h :: t)); fold V_extract; intros.
		+ assert (H_h_ht : In h (h::t)) by (left; reflexivity).
			destruct (H' h x0 p0 i) as [el' P' H_el'].
			exists el'.
			* unfold V_extract in P'; fold V_extract in P'. assumption.
			* intros e He_el'.
				destruct el as [|elh elt]; inversion p; subst.
				specialize (P_eq_edges_eq p0 H3) as H_eq.
				subst. right. apply H_el'. assumption.
		+ exists el.
			* assert (H_xy : x = y) by (inversion Hx; auto; contradiction).
				subst. assumption.
			* intros e He. assumption.
Qed.


Lemma V_extract_sublist :
	forall u x vl, In u (V_extract x vl) -> In u vl.
Proof.
	intros u x vl. generalize dependent x. generalize dependent u.
	induction vl as [|h t]; intros.
	- inversion H.
	- unfold V_extract in H.
		case (V_in_dec x t) as [H_xt | H_nxt].
		+ fold V_extract in H. right. apply (IHt u x). assumption.
		+ right. assumption.
Qed.

Lemma Walk_to_path' :
 forall v a (x y : Vertex) (vl : V_list) (el : E_list),
 Walk v a x y vl el ->
 {vl0 : V_list & {el0 : E_list & Path v a x y vl0 el0} & forall u, In u vl0 -> In u vl}.
Proof.
        intros V E x y vl el w; elim w; intros.
        exists V_nil.
        split with E_nil; apply P_null; trivial.
        intros u Hu. assumption.

        elim H; clear H; intros vl' H H_lst.
        elim H; clear H; intros el' H.
        case (V_in_dec x0 (y0 :: vl')) as [i|n].
        elim (P_extract _ _ _ _ _ _ _ H i); intros.
        exists (V_extract x0 (y0 :: vl')).
        split with x1; auto.
        intros u Hu.
				apply (V_extract_sublist u x0 (y0 :: vl')) in Hu.
				inversion Hu.
				subst. left. reflexivity.
				right. apply H_lst. assumption.

        case (V_in_dec y0 vl') as [e|n0].
				exists (y0 :: V_nil).
        split with (E_ends x0 y0 :: E_nil). apply P_step.
        replace z with y0.
        apply P_null; apply (P_endx_inv _ _ _ _ _ _ H).

        apply (P_when_cycle _ _ _ _ _ _ H); auto.

        trivial.

        trivial.

        red; intros; elim n; rewrite H0; simpl; auto.

        tauto.

	simpl. tauto.

        tauto.

				intros u Hu.
				inversion Hu. subst. left. reflexivity.
				inversion H0.

        exists (y0 :: vl'). split with (E_ends x0 y0 :: el').
        apply P_step.
        trivial.

        trivial.

        trivial.

        red; intros; elim n; rewrite H0; simpl; auto.

        trivial.

        intros; absurd (In x0 vl').
        red; intros; elim n; simpl; auto.

        trivial.

        red; intros.
        elim n; inversion H1.
        apply (P_inxyel_inxvl _ _ _ _ _ _ H x0 y0).
        rewrite <- H3; auto.

        apply (P_inxyel_inyvl _ _ _ _ _ _ H y0 x0).
        rewrite <- H4; rewrite <- H5; rewrite H2; trivial.

				intros u Hu. inversion Hu.
				subst. left. reflexivity.
				right. apply H_lst. assumption.
Qed.





Lemma same_path_same_edges :
	forall V E x y vl el1 el2, Path V E x y vl el1 -> Path V E x y vl el2 -> el1 = el2.
Proof.
	intros V E x y vl. generalize dependent y. generalize dependent x.
	induction vl as [|h t]; intros x y el1 el2 p1 p2.
	- inversion p1. inversion p2. reflexivity.
	- inversion p1. inversion p2. subst. f_equal.
		apply (IHt _ _ _ _ H1 H13).
Qed.

Lemma V_extract_edges :
	forall {V E x y z vl_yz el_yz vl_xz e},
	Path V E y z vl_yz el_yz ->
	Path V E x z (V_extract x (y :: vl_yz)) vl_xz ->
	In e vl_xz -> (exists q, In q vl_yz /\ e = (E_ends x q)) \/ In e el_yz.
Proof.
	intros V E x y z vl_yz el_yz vl_xz. generalize dependent el_yz. generalize dependent vl_yz.
	generalize dependent z. generalize dependent y. generalize dependent x.
	induction vl_xz as [|h t]; intros x y z vl_yz el_yz e path_yz path_xz He.
	- inversion He.
	- destruct He as [H_eh | H_et].
		+ (* case: e = h (the first edge in list) => will be x--q for some q *)
			subst e.
			(* to get the x: induction on vl_yz *)
			generalize dependent path_xz. generalize dependent path_yz.
			generalize dependent el_yz. generalize dependent z. generalize dependent y. generalize dependent x.
			induction vl_yz as [|hx tx]; intros.
			* simpl in path_xz. generalize dependent path_xz.
				case (V_in_dec x nil); intros H_x path_xz; try solve [inversion H_x].
				inversion path_xz.
			* unfold V_extract in path_xz. generalize dependent path_xz.
				case (V_in_dec x (hx::tx)); fold V_extract; intros H_x_vl_yz path_xz.
				-- 	inversion path_yz; subst.
						assert (path_xz' : Path V E x z (V_extract x (hx::tx)) (h::t)) by (unfold V_extract; fold V_extract; assumption).
						destruct (IHtx _ _ _ _ H1 path_xz') as [Hq | H''].
					++ 	destruct Hq as [q [Hq1 Hq2]]. left. exists q. split.
						** 	right. assumption.
						** 	assumption.
					++ 	right. right. assumption.
				-- 	inversion path_xz; subst.
						left. exists hx. split.
					++ 	left. reflexivity.
					++ 	reflexivity.
		+ (* case: e in t (later in the list) *)
			(* need to remove h => induction on vl_yz again *)
			generalize dependent path_xz. generalize dependent path_yz.
			generalize dependent el_yz. generalize dependent z. generalize dependent y. generalize dependent x.
			induction vl_yz as [|hx tx]; intros.
			* simpl in path_xz. generalize dependent path_xz.
				case (V_in_dec x nil); intros H_x path_xz; try solve [inversion H_x].
				inversion path_xz.
			* unfold V_extract in path_xz. generalize dependent path_xz.
				case (V_in_dec x (hx::tx)); fold V_extract; intros H_x_vl_yz path_xz.
				-- 	inversion path_yz; subst.
						assert (path_xz' : Path V E x z (V_extract x (hx::tx)) (h::t)) by (unfold V_extract; fold V_extract; assumption).
						destruct (IHtx _ _ _ _ H1 path_xz') as [Hq | H''].
					++ 	destruct Hq as [q [Hq1 Hq2]]. left. exists q. split.
						** 	right. assumption.
						** 	assumption.
					++ 	right. right. assumption.
				-- 	destruct el_yz as [|elh elt] eqn:E_el; try solve [inversion path_yz].
						inversion path_yz. inversion path_xz. subst.
						right. right.
						(* the have the same endpoints and vertex list -> have the same edge list*)
						assert (H_t_elt : t = elt) by (apply (same_path_same_edges _ _ _ _ _ _ _ H16 H3)).
						subst. assumption.
Qed.


Lemma V_extract_first :
	forall {V E x z hv tv he te},
	Path V E x z (V_extract x (hv::tv)) (he::te) ->
	exists y, In y tv /\ he = E_ends x y.
Proof.
	intros V E x z hv tv. generalize dependent hv. generalize dependent z. generalize dependent x.
	induction tv as [|h t]; intros.
	- inversion H; subst.
		generalize dependent H0.
		case (V_in_dec x nil); intros H_xnil H0; solve [contradiction | discriminate].
	- generalize dependent H. unfold V_extract.
		case (V_in_dec x (h::t)); intros H_x_ht H_path. fold V_extract in H_path.
		+ assert (H_path' : Path V E x z (V_extract x (hv::t)) (he::te)). {
				unfold V_extract; fold V_extract. assumption.
			}
			destruct (IHt _ _ _ _ _ H_path') as [y [Hy1 Hy2]].
			exists y. split.
			* right. assumption.
			* assumption.
		+ inversion H_path; subst.
			exists h. split.
			* left. reflexivity.
			* reflexivity.
Qed.


Lemma V_extract_edges_split :
	forall {V E x y z vl el},
	Path V E x z (V_extract x (y :: vl)) el ->
	~ In x vl \/ exists f_lst t_lst, vl = f_lst ++ x :: t_lst.
Proof.
	intros V E x y z vl. generalize dependent z. generalize dependent y. generalize dependent x.
	induction vl as [|h t]; intros.
	- inversion H; subst; left; intros H'; inversion H'.
	- generalize dependent H. unfold V_extract.
		case (V_in_dec x (h::t)); intros Hx; fold V_extract; intros P.
		+ right.
			assert (P' : Path V E x z (V_extract x (y::t)) el). {
				unfold V_extract; fold V_extract; assumption.
			}
			specialize (IHt _ _ _ _ P') as H'.
			destruct H' as [H_nxt | [f_lst [t_lst H_comb]]].
			* assert (H_xh : x = h). {
				destruct Hx; solve [intuition].
			}
			exists nil. exists t. subst. reflexivity.
			* exists (h::f_lst). exists t_lst. simpl. rewrite H_comb. reflexivity.
		+ left. assumption.
Qed.



Lemma Walk_to_path'' :
	forall v a (x y : Vertex) (vl : V_list) (el : E_list),
	Walk v a x y vl el ->
	{vl0 : V_list & {el0 : E_list & Path v a x y vl0 el0
		& forall e, In e el0 -> In e el} & forall u, In u vl0 -> In u vl}.
Proof.
	intros v a x y vl el w. induction w; intros.
	exists V_nil.
	exists E_nil. apply P_null; trivial.
	intros e Hu. assumption.
	intros u Hu. assumption.

	destruct IHw as [vl' [el' H H_elst] H_vlst].
	case (V_in_dec x (y :: vl')) as [i|n].
	induction (P_extract' _ _ _ _ _ _ _ H i); intros.
	exists (V_extract x (y :: vl')).
	exists x0. auto.
	intros e He.
	specialize (V_extract_edges H p He) as [He' | He'].

	destruct He' as [k [Hk1 Hk2]].
	subst e.
	right. apply H_elst. apply q. assumption.
	right. apply H_elst. assumption.
	intros u Hu.
	apply (V_extract_sublist u x (y :: vl')) in Hu.
	inversion Hu.
	subst. left. reflexivity.
	right. apply H_vlst. assumption.

	case (V_in_dec y vl') as [e|n0].
	exists (y :: V_nil).
	exists (E_ends x y :: E_nil). apply P_step.
	replace z with y.
	apply P_null; apply (P_endx_inv _ _ _ _ _ _ H).

	apply (P_when_cycle _ _ _ _ _ _ H); auto.

	trivial.

	trivial.

	red; intros; elim n; rewrite H0; simpl; auto.

	tauto.

simpl. tauto.

	tauto.

	intros m Hm. inversion Hm. subst m. left. reflexivity.
	inversion H0.

	intros u Hu.
	inversion Hu. subst. left. reflexivity.
	inversion H0.

	exists (y :: vl'). exists (E_ends x y :: el').
	apply P_step.
	trivial.

	trivial.

	trivial.

	red; intros; elim n; rewrite H0; simpl; auto.

	trivial.

	intros; absurd (In x vl').
	red; intros; elim n; simpl; auto.

	trivial.

	red; intros.
	elim n; inversion H1.
	apply (P_inxyel_inxvl _ _ _ _ _ _ H x y).
	rewrite <- H3; auto.

	apply (P_inxyel_inyvl _ _ _ _ _ _ H y x).
	rewrite <- H4; rewrite <- H5; rewrite H2; trivial.

	intros e He. inversion He.
	subst e. left. reflexivity.
	right. apply H_elst. assumption.

	intros u Hu. inversion Hu.
	subst. left. reflexivity.
	right. apply H_vlst. assumption.
Qed.


