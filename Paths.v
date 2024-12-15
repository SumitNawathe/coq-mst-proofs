(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)



(* Different definitions of pathes in a graph, directed or not.         *)

(* The following notions are defined :                                  *)
(*      - Walk : defined by 2 ends,                                     *)
(*                      a list of vertices and a list of edges          *)
(*              constructors : W_null, W_step;                          *)
(*      - Trail : walk without repetition of edge,                      *)
(*              constructors : T_null, T_step;                          *)
(*      - Path : trail without repetition of inner vertex,              *)
(*              constructors : P_null, P_step;                          *)
(*      - Closed_walk, Closed_trail, Cycle.                             *)

Require Export MST.Graphs.
Require Export MST.Degrees.

Section PATH.

Variable v : V_set.
Variable a : A_set.

Inductive Walk : Vertex -> Vertex -> V_list -> E_list -> Type :=
  | W_null : forall x : Vertex, v x -> Walk x x V_nil E_nil
  | W_step :
      forall (x y z : Vertex) (vl : V_list) (el : E_list),
      Walk y z vl el ->
      v x -> a (A_ends x y) -> Walk x z (y :: vl) (E_ends x y :: el).

Definition Closed_walk (x y : Vertex) (vl : V_list) 
  (el : E_list) (w : Walk x y vl el) := x = y.

Inductive Trail : Vertex -> Vertex -> V_list -> E_list -> Type :=
  | T_null : forall x : Vertex, v x -> Trail x x V_nil E_nil
  | T_step :
      forall (x y z : Vertex) (vl : V_list) (el : E_list),
      Trail y z vl el ->
      v x ->
      a (A_ends x y) ->
      (forall u : Edge, In u el -> ~ E_eq u (E_ends x y)) ->
      Trail x z (y :: vl) (E_ends x y :: el).

Definition Closed_trail (x y : Vertex) (vl : V_list) 
  (el : E_list) (t : Trail x y vl el) := x = y.

Inductive Path : Vertex -> Vertex -> V_list -> E_list -> Type :=
  | P_null : forall x : Vertex, v x -> Path x x V_nil E_nil
  | P_step :
      forall (x y z : Vertex) (vl : V_list) (el : E_list),
      Path y z vl el ->
      v x ->
      a (A_ends x y) ->
      x <> y ->
      ~ In y vl ->
      (In x vl -> x = z) ->
      (forall u : Edge, In u el -> ~ E_eq u (E_ends x y)) ->
      Path x z (y :: vl) (E_ends x y :: el).

Definition Cycle (x y : Vertex) (vl : V_list) (el : E_list)
  (p : Path x y vl el) := x = y.

Lemma P_iny_vl :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path x y vl el -> vl <> V_nil -> In y vl.
Proof.
        intros x y vl el p; elim p; intros.
        absurd (V_nil = V_nil); auto.

        inversion p0.
        simpl; auto.

        rewrite H10; simpl; right.
        apply H; rewrite <- H10; discriminate.
Qed.

Lemma P_endx_inv :
 forall (x y : Vertex) (vl : V_list) (el : E_list), Path x y vl el -> v x.
Proof.
        intros x y vl el p; elim p; auto.
Qed.

Lemma P_endy_inv :
 forall (x y : Vertex) (vl : V_list) (el : E_list), Path x y vl el -> v y.
Proof.
        intros x y vl el p; elim p; auto.
Qed.

Lemma P_invl_inv :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path x y vl el -> forall z : Vertex, In z vl -> v z.
Proof.
        intros x y vl el p; elim p; intros.
        inversion H.

        inversion H0.
        rewrite <- H1; apply (P_endx_inv _ _ _ _ p0).

        auto.
Qed.

Lemma P_inel_ina :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path x y vl el ->
 forall x' y' : Vertex, In (E_ends x' y') el -> a (A_ends x' y').
Proof.
        intros x y vl el p; elim p; intros.
        inversion H.

        inversion H0.
        inversion H1.
        rewrite <- H3; rewrite <- H4; trivial.

        auto.
Qed.

Lemma P_inxyel_inxvl :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path x y vl el ->
 forall x' y' : Vertex, In (E_ends x' y') el -> In x' (x :: vl).
Proof.
        intros x y vl el p; elim p; intros.
        inversion H.

        inversion H0.
        inversion H1.
        simpl; auto.

        simpl; right.
        apply (H x' y'); auto.
Qed.

Lemma P_inxyel_inyvl :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path x y vl el ->
 forall x' y' : Vertex, In (E_ends x' y') el -> In y' (x :: vl).
Proof.
        intros x y vl el p; elim p; intros.
        inversion H.

        inversion H0.
        inversion H1.
        simpl; auto.

        simpl; right.
        apply (H x' y'); auto.
Qed.

Lemma P_backstep :
 forall (x y z : Vertex) (vl : V_list) (el : E_list),
 Path x z (y :: vl) el -> {el' : E_list &  Path y z vl el'}.
Proof.
        intros; inversion H.
        split with el0; trivial.
Qed.

Lemma Trail_isa_walk :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Trail x y vl el -> Walk x y vl el.
Proof.
        intros x y vl el t; elim t; intros.
        apply W_null; trivial.

        apply W_step; trivial.
Qed.

Lemma Path_isa_trail :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path x y vl el -> Trail x y vl el.
Proof.
        intros x y vl el t; elim t; intros.
        apply T_null; trivial.

        apply T_step; trivial.
Qed.

End PATH.

Section EXTRACTED.

Variable v : V_set.
Variable a : A_set.

Fixpoint V_extract (x : Vertex) (vl : V_list) {struct vl} : V_list :=
  match vl with
  | nil => V_nil
  | y :: vl' =>
      if V_in_dec x vl' then V_extract x vl' else vl'
  end.

Lemma P_extract :
 forall (x y z : Vertex) (vl : V_list) (el : E_list),
 Path v a y z vl el ->
 In x (y :: vl) -> {el' : E_list &  Path v a x z (V_extract x (y :: vl)) el'}.
Proof.
        intros x y z vl; generalize y; elim vl; simpl; intros.
        split with el.
        replace x with y0; auto.
        case (V_in_dec y0 nil); auto.

        tauto.

        elim (P_backstep _ _ _ _ _ _ _ H0); intros.
        case (V_in_dec x (a0 :: l)). intros.
        apply (H a0 x0); auto.

        simpl. intros. split with el. replace x with y0.
        trivial.
	
        tauto.
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
 forall (x y z : Vertex) (vl : V_list) (el : E_list),
 Path v a y z vl el ->
 In x (y :: vl) ->
 {el' : E_list & Path v a x z (V_extract x (y :: vl)) el' & (forall e, In e el' -> In e el)}.
Proof.
	intros x y z vl. generalize dependent y.
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



Remark P_when_cycle :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path v a x y vl el -> In x vl -> x = y.
Proof.
        intros x y vl el H; inversion H; intros.
        trivial.


        inversion H11.
        absurd (x = y0); auto.

        auto.
Qed.

Lemma Walk_to_path :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Walk v a x y vl el ->
 {vl0 : V_list &  {el0 : E_list &  Path v a x y vl0 el0}}.
Proof.
        intros x y vl el w; elim w; intros.
        split with V_nil; split with E_nil; apply P_null; trivial.

        elim H; clear H; intros vl' H.
        elim H; clear H; intros el' H.
        case (V_in_dec x0 (y0 :: vl')) as [i|n].
        elim (P_extract _ _ _ _ _ H i); intros.
        split with (V_extract x0 (y0 :: vl')); split with x1; auto.

        case (V_in_dec y0 vl') as [e|n0].
        split with (y0 :: V_nil); split with (E_ends x0 y0 :: E_nil). apply P_step.
        replace z with y0.
        apply P_null; apply (P_endx_inv _ _ _ _ _ _ H).

        apply (P_when_cycle _ _ _ _ H); auto.

        trivial.

        trivial.

        red; intros; elim n; rewrite H0; simpl; auto.

        tauto.

	simpl. tauto.

        tauto.

        split with (y0 :: vl'); split with (E_ends x0 y0 :: el').
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
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Walk v a x y vl el ->
 {vl0 : V_list & {el0 : E_list & Path v a x y vl0 el0} & forall u, In u vl0 -> In u vl}.
Proof.
        intros x y vl el w; elim w; intros.
        exists V_nil.
        split with E_nil; apply P_null; trivial.
        intros u Hu. assumption.

        elim H; clear H; intros vl' H H_lst.
        elim H; clear H; intros el' H.
        case (V_in_dec x0 (y0 :: vl')) as [i|n].
        elim (P_extract _ _ _ _ _ H i); intros.
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

        apply (P_when_cycle _ _ _ _ H); auto.

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
	forall (x y : Vertex) (vl : V_list) (el : E_list),
	Walk v a x y vl el ->
	{vl0 : V_list & {el0 : E_list & Path v a x y vl0 el0
		& forall e, In e el0 -> In e el} & forall u, In u vl0 -> In u vl}.
Proof.
	intros x y vl el w. induction w; intros.
	exists V_nil.
	exists E_nil. apply P_null; trivial.
	intros e Hu. assumption.
	intros u Hu. assumption.

	destruct IHw as [vl' [el' H H_elst] H_vlst].
	case (V_in_dec x (y :: vl')) as [i|n].
	induction (P_extract' _ _ _ _ _ H i); intros.
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

	apply (P_when_cycle _ _ _ _ H); auto.

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




End EXTRACTED.

Section PATH_AND_DEGREE.

Variable v : V_set.
Variable a : A_set.
Variable g : Graph v a.

Lemma Path_degree_one :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path v a x y vl el -> forall z : Vertex, In z vl -> degree z v a g > 0.
Proof.
        intros x y vl el p; elim p; intros.
        inversion H.

        inversion H0.
        rewrite <- H1; apply Degree_not_isolated.
        split with x0; apply (G_non_directed v a g); trivial.

        apply H; auto.
Qed.

Lemma Path_consx_degree_one :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path v a x y vl el ->
 vl <> V_nil -> forall z : Vertex, In z (x :: vl) -> degree z v a g > 0.
Proof.
        simple destruct vl; intros.
        absurd (nil = V_nil); auto.

        inversion H1.
        rewrite <- H2; apply Degree_not_isolated.
        inversion H; split with v0; trivial.

        apply (Path_degree_one x y (v0 :: l) el H); auto.
Qed.

Lemma Path_degree_two :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path v a x y vl el ->
 forall z : Vertex, In z vl -> z <> y -> degree z v a g > 1.
Proof.
        intros x y vl el p; elim p; intros.
        inversion H.

        inversion H0.
        inversion p0.
        absurd (z0 = z).
        trivial.

        rewrite <- H2; auto.

        rewrite <- H2; apply Degree_not_pendant.
        split with x0.
        apply (G_non_directed v a g); trivial.

        split with y1.
        trivial.

        red; intros.
        elim (n1 (E_ends y0 y1)).
        rewrite <- H13; simpl; auto.

        rewrite H14; apply E_rev.

        apply H; trivial.
Qed.

Lemma Path_last_step :
 forall (x y : Vertex) (vl : V_list) (el : E_list) (p : Path v a x y vl el),
 el <> E_nil -> exists z : Vertex, In (E_ends z y) el.
Proof.
        intros x y vl el p; elim p.
        intros; elim H; trivial.

        simple destruct el0; intros.
        split with x0.
        inversion p0.
        simpl; left; trivial.

        elim H; intros.
        split with x1.
        simpl; auto.

        discriminate.
Qed.

Lemma Cycle_degree_two :
 forall (x y : Vertex) (vl : V_list) (el : E_list) (p : Path v a x y vl el),
 Cycle v a x y vl el p -> forall z : Vertex, In z vl -> degree z v a g > 1.
Proof.
        intros; case (V_eq_dec z y) as [e|n].
        rewrite e; apply Degree_not_pendant.
        inversion p.
        rewrite <- H4 in H0; inversion H0.

        inversion H.
        split with y0.
        rewrite <- H12; trivial.

        elim (Path_last_step y0 y vl0 el0 H1); intros.
        split with x1.
        apply (G_non_directed v a g); apply (P_inel_ina v a y0 y vl0 el0 H1);
         trivial.

        red; intros; elim (H7 (E_ends x1 y)).
        trivial.

        rewrite H12; rewrite H14; apply E_rev.

        inversion H1.
        absurd (x = y0).
        trivial.

        rewrite H15; trivial.

        discriminate.

        apply (Path_degree_two x y vl el p); trivial.
Qed.

Lemma Cycle_consx_degree_two :
 forall (x y : Vertex) (vl : V_list) (el : E_list) (p : Path v a x y vl el),
 vl <> V_nil ->
 Cycle v a x y vl el p ->
 forall z : Vertex, In z (x :: vl) -> degree z v a g > 1.
Proof.
        intros; inversion H1.
        rewrite <- H2; inversion H0.
        apply (Cycle_degree_two x y vl el p H0 y).
        apply (P_iny_vl v a x y vl el p); trivial.

        apply (Cycle_degree_two x y vl el p H0); trivial.
Qed.

Lemma Path_degree_zero_nil :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Path v a x y vl el ->
 (exists2 z : Vertex, In z (x :: vl) & degree z v a g = 0) -> vl = V_nil.
Proof.
        simple destruct vl; intros.
        trivial.

        elim H0; intros.
        absurd (degree x0 v a g > 0).
        lia.

        apply (Path_consx_degree_one _ _ _ _ H).
        discriminate.

        trivial.
Qed.

Lemma Cycle_degree_one_nil :
 forall (x y : Vertex) (vl : V_list) (el : E_list) (p : Path v a x y vl el),
 Cycle v a x y vl el p ->
 (exists2 z : Vertex, In z (x :: vl) & degree z v a g <= 1) -> vl = V_nil.
Proof.
        simple destruct vl; intros.
        trivial.

        elim H0; intros.
        absurd (degree x0 v a g > 1).
        lia.

        apply (Cycle_consx_degree_two _ _ _ _ p).
        discriminate.

        trivial.

        trivial.
Qed.

End PATH_AND_DEGREE.

Section PATH_EQ.

Lemma Walk_eq :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (el : E_list),
 Walk v a x y vl el -> v = v' -> a = a' -> Walk v' a' x y vl el.
Proof.
        intros; elim H; intros.
        apply W_null.
        rewrite <- H0; trivial.

        apply W_step.
        trivial.

        rewrite <- H0; trivial.

        rewrite <- H1; trivial.
Qed.

Lemma Trail_eq :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (el : E_list),
 Trail v a x y vl el -> v = v' -> a = a' -> Trail v' a' x y vl el.
Proof.
        intros; elim H; intros.
        apply T_null.
        rewrite <- H0; trivial.

        intros; apply T_step.
        trivial.

        rewrite <- H0; trivial.

        rewrite <- H1; trivial.

        trivial.
Qed.

Lemma Path_eq :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (el : E_list),
 Path v a x y vl el -> v = v' -> a = a' -> Path v' a' x y vl el.
Proof.
        intros; elim H; intros.
        apply P_null.
        rewrite <- H0; trivial.

        intros; apply P_step.
        trivial.

        rewrite <- H0; trivial.

        rewrite <- H1; trivial.

        trivial.

        trivial.

        trivial.

        trivial.
Qed.

End PATH_EQ.

Section PATH_IN_A_SUBGRAPH.

Lemma Walk_subgraph :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (el : E_list),
 Walk v a x y vl el ->
 V_included v v' -> A_included a a' -> Walk v' a' x y vl el.
Proof.
        intros; elim H; intros.
        apply W_null; apply (H0 x0); trivial.

        apply W_step.
        trivial.

        apply (H0 x0); trivial.

        apply (H1 (A_ends x0 y0)); trivial.
Qed.

Lemma Trail_subgraph :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (el : E_list),
 Trail v a x y vl el ->
 V_included v v' -> A_included a a' -> Trail v' a' x y vl el.
Proof.
        intros; elim H; intros.
        apply T_null; apply (H0 x0); trivial.

        apply T_step.
        trivial.

        apply (H0 x0); trivial.

        apply (H1 (A_ends x0 y0)); trivial.

        trivial.
Qed.

Lemma Path_subgraph :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (el : E_list),
 Path v a x y vl el ->
 V_included v v' -> A_included a a' -> Path v' a' x y vl el.
Proof.
        intros; elim H; intros.
        apply P_null; apply (H0 x0); trivial.

        apply P_step.
        trivial.

        apply (H0 x0); trivial.

        apply (H1 (A_ends x0 y0)); trivial.

        trivial.

        trivial.

        trivial.

        trivial.
Qed.

Lemma Path_supergraph_vertex :
 forall (v v' : V_set) (a : A_set) (x y : Vertex) (vl : V_list) (el : E_list),
 Path v a x y vl el ->
 v' x -> (forall z : Vertex, In z vl -> v' z) -> Path v' a x y vl el.
Proof.
        intros v v' a x y vl el p; elim p; intros.
        apply P_null; trivial.

        apply P_step.
        apply H.
        apply H1; simpl; auto.

        intros; apply H1; simpl; auto.

        trivial.

        trivial.

        trivial.

        trivial.

        trivial.

        trivial.
Qed.

Lemma Path_supergraph_cons_vertex :
 forall (v : V_set) (a : A_set) (x y z : Vertex) (vl : V_list) (el : E_list),
 Path (V_union (V_single z) v) a x y vl el ->
 z <> x -> ~ In z vl -> Path v a x y vl el.
Proof.
        intros v a x y z vl el p; elim p; intros.
        apply P_null.
        inversion v0.
        inversion H1; absurd (z = x0); auto.

        trivial.

        apply P_step.
        apply H.
        red; intros; elim H1.
        rewrite H2; simpl; auto.

        red; intros; elim H1; simpl; auto.

        inversion v0.
        inversion H2; absurd (z = x0); auto.

        trivial.

        trivial.

        trivial.

        trivial.

        trivial.

        trivial.
Qed.

Lemma Path_supergraph_arc :
 forall (v v' : V_set) (a a' : A_set) (x y : Vertex) 
   (vl : V_list) (el : E_list),
 Path v a x y vl el ->
 Graph v' a' ->
 v' x ->
 (forall x' y' : Vertex, In (E_ends x' y') el -> a' (A_ends x' y')) ->
 Path v' a' x y vl el.
Proof.
        intros v v' a a' x y vl el p; elim p.
        intros x0 v0 X H H0.
        apply P_null; trivial.

        intros x0 y0 z vl0 el0 p0 H v0 a0 n n0 e n1 X H0 H1.
        apply P_step.
        apply H.
        trivial.

        apply (G_ina_inv2 v' a' X x0 y0).
        apply H1; simpl; auto.

        intros; apply H1; simpl; auto.

        trivial.

        apply H1; simpl; auto.

        trivial.

        trivial.

        trivial.

        trivial.
Qed.

Lemma Path_supergraph_cons_arc :
 forall (v : V_set) (a : A_set) (x y x' y' : Vertex) 
   (vl : V_list) (el : E_list),
 Path v (A_union (E_set x' y') a) x y vl el ->
 ~ In (E_ends x' y') el -> ~ In (E_ends y' x') el -> Path v a x y vl el.
Proof.
        intros v a x y x' y' vl el p; elim p; intros.
        apply P_null; trivial.

        apply P_step.
        apply H.
        red; intros; elim H0.
        simpl; auto.

        red; intros; elim H1; simpl; auto.

        trivial.

        inversion a0.
        inversion H2.
        absurd (In (E_ends x' y') (E_ends x0 y0 :: el0)).
        trivial.

        rewrite H5; rewrite H6; simpl; auto.

        absurd (In (E_ends y' x') (E_ends x0 y0 :: el0)).
        trivial.

        rewrite H5; rewrite H6; simpl; auto.

        trivial.

        trivial.

        trivial.

        trivial.

        trivial.
Qed.

End PATH_IN_A_SUBGRAPH.

Section APPEND_WALKS.

Variable v : V_set.
Variable a : A_set.

Lemma Walk_append :
 forall (x y z : Vertex) (vl vl' : V_list) (el el' : E_list),
 Walk v a x y vl el ->
 Walk v a y z vl' el' -> Walk v a x z (vl ++ vl') (el ++ el').
Proof.
        intros x y z vl vl' el el' Hw; elim Hw; simpl; intros.
        trivial.

        apply W_step; auto.
Qed.

End APPEND_WALKS.

Section REVERSE_WALK.

Variable v : V_set.
Variable a : A_set.
Variable g : Graph v a.

Definition cdr (vl : V_list) : V_list :=
  match vl with
  | nil => V_nil
  | x :: vl' => vl'
  end.

Lemma cdr_app :
 forall vl vl' : V_list, vl <> V_nil -> cdr (vl ++ vl') = cdr vl ++ vl'.
Proof.
        simple induction vl; simpl; intros.
        absurd (V_nil = V_nil); auto.

        trivial.
Qed.

Fixpoint E_reverse (el : E_list) : E_list :=
  match el with
  | nil => E_nil
  | E_ends x y :: el' => E_reverse el' ++ E_ends y x :: E_nil
  end.

Lemma G_ends_in : forall x y : Vertex, a (A_ends x y) -> v x.
Proof.
        elim g; intros.
        inversion H.

        case (V_eq_dec x x0) as [e|n0].
        rewrite e; apply V_in_left; apply V_in_single.

        apply V_in_right; apply (H x0 y); trivial.

        inversion H0.
        inversion H1; rewrite <- H4; trivial.

        apply (H x0 y0); trivial.

        rewrite <- e; apply (H x y); rewrite e0; trivial.
Qed.

Lemma Walk_reverse :
 forall (x y : Vertex) (vl : V_list) (el : E_list),
 Walk v a x y vl el -> Walk v a y x (cdr (rev (x :: vl))) (E_reverse el).
Proof.
        intros; elim H; simpl; intros.
        apply W_null; trivial.

        rewrite cdr_app.
        apply (Walk_append v a z y0 x0).
        trivial.

        apply W_step.
        apply W_null; trivial.

        apply (G_ina_inv2 v a g x0 y0); trivial.

        apply (G_non_directed v a g); trivial.

        case (rev vl0); intros; simpl; discriminate.
Qed.

End REVERSE_WALK.

