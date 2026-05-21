/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.RNS.cornrealCReals

-- (* Copyright © 1998-2006
--  * Henk Barendregt
--  * Luís Cruz-Filipe
--  * Herman Geuvers
--  * Mariusz Giero
--  * Rik van Ginneken
--  * Dimitri Hendriks
--  * Sébastien Hinderer
--  * Bart Kirkels
--  * Pierre Letouzey
--  * Iris Loeb
--  * Lionel Mamane
--  * Milad Niqui
--  * Russell O’Connor
--  * Randy Pollack
--  * Nickolay V. Shmyrev
--  * Bas Spitters
--  * Dan Synek
--  * Freek Wiedijk
--  * Jan Zwanenburg
--  *
--  * This work is free software; you can redistribute it and/or modify
--  * it under the terms of the GNU General Public License as published by
--  * the Free Software Foundation; either version 2 of the License, or
--  * (at your option) any later version.
--  *
--  * This work is distributed in the hope that it will be useful,
--  * but WITHOUT ANY WARRANTY; without even the implied warranty of
--  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--  * GNU General Public License for more details.
--  *
--  * You should have received a copy of the GNU General Public License along
--  * with this work; if not, write to the Free Software Foundation, Inc.,
--  * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
--  *)
-- (* begin hide *)
-- (* In this file a notion of morphism between two arbitrary real number
--    structures, is introduced together with te proofs that this notion of
--    morphism preserves the basic algebraic structure. *)

-- Require Import CoRN.reals.CReals.

-- (* This comes from CReals1.v *)
-- Definition Cauchy_Lim_prop2 (IR : CReals) (seq : nat -> IR)
--   (y : IR) :=
--   forall eps : IR,
--   [0][<]eps ->
--   {N : nat | forall m : nat, N <= m -> AbsSmall eps (seq m[-]y)}.


-- Section morphism.
-- Variables R1 R2 : CReals.

-- Section morphism_details.
-- Variable phi : R1 -> R2.


-- Variable p1 : R1 -> R1 -> CProp.
-- Variable p2 : R2 -> R2 -> CProp.
-- Variable f1 : R1 -> R1.
-- Variable f2 : R2 -> R2.
-- Variable g1 : R1 -> R1 -> R1.
-- Variable g2 : R2 -> R2 -> R2.

-- Definition fun_pres_relation := forall x y : R1, p1 x y -> p2 (phi x) (phi y).

-- Definition fun_pres_un_fun := forall x : R1, phi (f1 x)[=]f2 (phi x).

-- Definition fun_pres_bin_fun :=
--   forall x y : R1, phi (g1 x y)[=]g2 (phi x) (phi y).

-- (*
-- Definition fun_pres_partial_fun:=(x:R1;H1:x[#][0];H2:(phi x)[#][0])
-- (phi (nzinj R1 (i1 (nzpro R1 x H1))))[=](nzinj R2 (i2 (nzpro R2 (phi x) H2))).
-- *)

-- Definition fun_pres_Lim :=
--   forall (a : nat -> R1) (l_a : R1),
--   Cauchy_Lim_prop2 R1 a l_a ->
--   Cauchy_Lim_prop2 R2 (fun n : nat => phi (a n)) (phi l_a).


-- End morphism_details.


-- Record Homomorphism : Type :=
--   {map :> R1 -> R2;
--    map_strext : fun_strext map;
--    map_pres_less :
--     fun_pres_relation map (cof_less (c:=R1)) (cof_less (c:=R2));
--    map_pres_plus : fun_pres_bin_fun map (csg_op (c:=R1)) (csg_op (c:=R2));
--    map_pres_mult : fun_pres_bin_fun map (cr_mult (c:=R1)) (cr_mult (c:=R2));
--    map_pres_Lim : fun_pres_Lim map}.




-- (* This might be useful later...
-- Definition Homo_as_CSetoid_fun:=
--     [f:Homomorphism]
--          (Build_CSetoid_fun R1 R2 f
--            (fun_strext_imp_wd R1 R2 f (!map_strext f))
--            (!map_strext f)
--           ).
-- *****************)


-- Lemma map_strext_unfolded :
--  forall (f : Homomorphism) (x y : R1), f x[#]f y -> x[#]y.
-- Proof.
--  intro f.
--  case f.
--  intros. rename X into H.
--  apply map_strext0.
--  exact H.
-- Qed.

-- Lemma map_wd_unfolded :
--  forall (f : Homomorphism) (x y : R1), x[=]y -> f x[=]f y.
-- Proof.
--  intros.
--  apply not_ap_imp_eq.
--  intro H0.
--  cut (Not (x[#]y)).
--   intro H1.
--   apply H1.
--   apply map_strext_unfolded with (f := f).
--   exact H0.
--  apply eq_imp_not_ap.
--  exact H.
-- Qed.

-- Lemma map_pres_less_unfolded :
--  forall (f : Homomorphism) (x y : R1), x[<]y -> f x[<]f y.
-- Proof.
--  intro f.
--  case f.
--  intros. rename X into H.
--  apply map_pres_less.
--  exact H.
-- Qed.

-- Lemma map_pres_plus_unfolded :
--  forall (f : Homomorphism) (x y : R1), f (x[+]y)[=]f x[+]f y.
-- Proof.
--  intros.
--  case f.
--  intros.
--  apply map_pres_plus.
-- Qed.

-- Lemma map_pres_mult_unfolded :
--  forall (f : Homomorphism) (x y : R1), f (x[*]y)[=]f x[*]f y.
-- Proof.
--  intros.
--  case f.
--  intros.
--  apply map_pres_mult.
-- Qed.

-- (* Now we start to derive some useful properties of a Homomorphism *)

-- Lemma map_pres_zero : forall f : Homomorphism, f (cm_unit R1)[=]cm_unit R2.
-- Proof.
--  intros.
--  apply cg_cancel_lft with (x := f [0]).
--  apply eq_transitive_unfolded with (f [0]).
--   apply eq_transitive_unfolded with (f ([0][+][0])).
--    apply eq_symmetric_unfolded.
--    apply map_pres_plus_unfolded.
--   apply map_wd_unfolded with (f := f).
--   algebra.
--  algebra.
-- Qed.

-- Lemma map_pres_zero_unfolded : forall f : Homomorphism, f [0][=][0].
-- Proof.
--  intro.
--  apply map_pres_zero.
-- Qed.


-- Lemma map_pres_minus :
--  forall f : Homomorphism, fun_pres_un_fun f (cg_inv (c:=R1)) (cg_inv (c:=R2)).
-- Proof.
--  intro f.
--  red in |- *.
--  intro.
--  apply cg_cancel_lft with (x := f x).
--  astepr ([0]:R2).
--  apply eq_transitive_unfolded with (f (x[+][--]x)).
--   apply eq_symmetric_unfolded.
--   apply map_pres_plus_unfolded.
--  astepl (f [0]).
--   apply map_pres_zero_unfolded.
--  apply map_wd_unfolded.
--  algebra.
-- Qed.

-- Lemma map_pres_minus_unfolded :
--  forall (f : Homomorphism) (x : R1), f [--]x[=][--](f x).
-- Proof.
--  exact map_pres_minus.
-- Qed.

-- Lemma map_pres_apartness :
--  forall (f : Homomorphism) (x y : R1), x[#]y -> f x[#]f y.
-- Proof.
--  intros f x y H.
--  cut (x[<]y or y[<]x).
--   intro H0.
--   case H0.
--    intro.
--    apply less_imp_ap.
--    apply map_pres_less_unfolded.
--    assumption.
--   intro H1.
--   apply Greater_imp_ap.
--   apply map_pres_less_unfolded.
--   exact H1.
--  apply ap_imp_less.
--  exact H.
-- Qed.

--      (* Merely a useful special case *)
-- Lemma map_pres_ap_zero :
--  forall (f : Homomorphism) (x : R1), x[#][0] -> f x[#][0].
-- Proof.
--  intros. rename X into H.
--  apply ap_wdr_unfolded with (y := f [0]).
--   apply map_pres_apartness with (y := [0]:R1).
--   exact H.
--  apply map_pres_zero_unfolded.
-- Qed.

-- Lemma map_pres_one : forall f : Homomorphism, f (cr_one R1)[=]cr_one R2.
-- Proof.
--  intros.
--  apply eq_symmetric_unfolded.
--  apply mult_cancel_lft with (z := f [1]).
--   apply map_pres_ap_zero.
--   apply ring_non_triv.
--  astepl (f [1]).
--  astepl (f ([1][*][1])).
--   apply map_pres_mult_unfolded.
--  apply map_wd_unfolded with (f := f).
--  algebra.
-- Qed.

-- Lemma map_pres_one_unfolded : forall f : Homomorphism, f [1][=][1].
-- Proof.
--  intro.
--  apply map_pres_one.
-- Qed.

-- (* I will not use the following lemma *)

-- Lemma map_pres_inv_unfolded :
--  forall (f : Homomorphism) (x : R1) (H : x[#][0]),
--  f ([1][/] x[//]H)[=]([1][/] f x[//]map_pres_ap_zero f x H).
-- Proof.
--  intros.
--  apply mult_cancel_lft with (z := f x).
--   apply map_pres_ap_zero.
--   assumption.
--  rstepr ([1]:R2).
--  astepl (f [1]).
--   apply map_pres_one_unfolded.
--  astepl (f (x[*]([1][/] x[//]H))).
--   apply map_pres_mult_unfolded.
--  apply map_wd_unfolded.
--  rational.
-- Qed.

-- End morphism.

-- Section composition.
-- Variables R1 R2 R3 : CReals.
-- Variable f : Homomorphism R1 R2.
-- Variable g : Homomorphism R2 R3.


-- Definition compose (x : R1) := g (f x).

-- Lemma compose_strext : fun_strext compose.
-- Proof.
--  red in |- *.
--  unfold compose in |- *.
--  case f.
--  intro f_.
--  intros f_1 f_2 f_3 f_4.
--  case g.
--  intro g_.
--  intros g_1 g_2 g_3 g_4.
--  intros. rename X into H.
--  simpl in H.
--  apply f_1.
--  apply g_1.
--  assumption.
-- Qed.


-- Lemma compose_pres_less :
--  fun_pres_relation R1 R3 compose (cof_less (c:=R1)) (cof_less (c:=R3)).
-- Proof.
--  red in |- *.
--  unfold compose in |- *.
--  case f.
--  intro f_.
--  intros f_1 f_2 f_3 f_4.
--  case g.
--  intro g_.
--  intros g_1 g_2 g_3 g_4.
--  intros.
--  simpl in |- *.
--  apply g_2.
--  apply f_2.
--  assumption.
-- Qed.

-- Lemma compose_pres_plus :
--  fun_pres_bin_fun R1 R3 compose (csg_op (c:=R1)) (csg_op (c:=R3)).
-- Proof.
--  red in |- *.
--  unfold compose in |- *.
--  case f.
--  intro f_.
--  intros f_1 f_2 f_3 f_4.
--  cut (fun_wd g).
--   case g.
--   intro g_.
--   intros g_1 g_2 g_3 g_4.
--   intros.
--   simpl in H.
--   simpl in |- *.
--   astepl (g_ (f_ x[+]f_ y)).
--   apply g_3.
--  red in |- *.
--  intros.
--  apply map_wd_unfolded.
--  assumption.
-- Qed.

-- Lemma compose_pres_mult :
--  fun_pres_bin_fun R1 R3 compose (cr_mult (c:=R1)) (cr_mult (c:=R3)).
-- Proof.
--  red in |- *.
--  unfold compose in |- *.
--  case f.
--  intro f_.
--  intros f_1 f_2 f_3 f_4.
--  cut (fun_wd g).
--   case g.
--   intro g_.
--   intros g_1 g_2 g_3 g_4.
--   intros.
--   simpl in H.
--   simpl in |- *.
--   astepl (g_ (f_ x[*]f_ y)).
--   apply g_4.
--  red in |- *.
--  intros.
--  apply map_wd_unfolded.
--  assumption.
-- Qed.

-- Lemma compose_pres_Lim : fun_pres_Lim R1 R3 compose.
-- Proof.
--  red in |- *.
--  unfold compose in |- *.
--  case f.
--  intro f_.
--  intros f_1 f_2 f_3 f_4 f_5.
--  case g.
--  intro g_.
--  intros g_1 g_2 g_3 g_4 g_5.
--  intros.
--  simpl in |- *.
--  apply g_5 with (a := fun n : nat => f_ (a n)).
--  apply f_5.
--  assumption.
-- Qed.


-- Definition Compose :=
--   Build_Homomorphism R1 R3 compose compose_strext compose_pres_less
--     compose_pres_plus compose_pres_mult compose_pres_Lim.



-- End composition.

-- Section isomorphism.

-- Variables R1 R2 : CReals.


-- Section identity_map.
-- Variable R3 : CReals.
-- Variable f : R3 -> R3.

-- Definition map_is_id := forall x : R3, f x[=]x.

-- End identity_map.


-- Record Isomorphism : Type :=
--   {iso_map_lft : Homomorphism R1 R2;
--    iso_map_rht : Homomorphism R2 R1;
--    inversity_lft : map_is_id R2 (Compose R2 R1 R2 iso_map_rht iso_map_lft);
--    inversity_rht : map_is_id R1 (Compose R1 R2 R1 iso_map_lft iso_map_rht)}.

-- End isomorphism.


-- Section surjective_map.
-- Variables R1 R2 : CReals.
-- Variable f : R1 -> R2.

-- Definition map_is_surjective := forall y : R2, {x : R1 | y[=]f x}.

-- End surjective_map.


-- Section simplification.
-- Variables R1 R2 : CReals.
-- Variable f : R1 -> R2.

-- Hypothesis H1 : fun_strext f.


-- Lemma f_well_def : forall x y : R1, x[=]y -> f x[=]f y.
-- Proof.
--  intros.
--  apply not_ap_imp_eq.
--  intro.
--  cut (Not (x[#]y)).
--   intro H2.
--   apply H2.
--   red in H1.
--   apply H1.
--   assumption.
--  apply eq_imp_not_ap.
--  assumption.
-- Qed.

-- Section with_less.

-- Hypothesis
--   H2 : fun_pres_relation R1 R2 f (cof_less (c:=R1)) (cof_less (c:=R2)).

-- Lemma less_pres_f : forall x y : R1, f x[<]f y -> x[<]y.
-- Proof.
--  intros.
--  case (ap_imp_less R1 x y).
--    red in H1.
--    apply H1.
--    apply less_imp_ap.
--    assumption.
--   intro.
--   assumption.
--  intro.
--  exfalso.
--  cut (f y[<]f x).
--   change (Not (f y[<]f x)) in |- *.
--   apply less_antisymmetric_unfolded.
--   assumption.
--  red in H2.
--  apply H2.
--  assumption.
-- Qed.

-- Lemma leEq_pres_f : forall x y : R1, f x[<=]f y -> x[<=]y.
-- Proof.
--  intros; rewrite -> leEq_def; intro.
--  apply less_irreflexive_unfolded with (x := f x).
--  apply leEq_less_trans with (f y); auto.
-- Qed.

-- Lemma f_pres_leEq : forall x y : R1, x[<=]y -> f x[<=]f y.
-- Proof.
--  intros; rewrite -> leEq_def; intro.
--  apply less_irreflexive_unfolded with (x := x).
--  apply leEq_less_trans with y; auto.
--  apply less_pres_f; auto.
-- Qed.

-- Lemma f_pres_apartness : forall x y : R1, x[#]y -> f x[#]f y.
-- Proof.
--  intros.
--  cut (x[<]y or y[<]x).
--   intro H0.
--   case H0.
--    intro.
--    apply less_imp_ap.
--    red in H2.
--    apply H2.
--    assumption.
--   intro.
--   apply Greater_imp_ap.
--   red in H2.
--   apply H2.
--   assumption.
--  apply ap_imp_less.
--  assumption.
-- Qed.

-- End with_less.

-- Section with_plus.

-- Hypothesis H3 : fun_pres_bin_fun R1 R2 f (csg_op (c:=R1)) (csg_op (c:=R2)).

-- Lemma f_pres_One : f [0][=][0].
-- Proof.
--  intros.
--  apply cg_cancel_lft with (x := f [0]).
--  astepr (f [0]).
--  astepl (f ([0][+][0])).
--  apply eq_symmetric_unfolded.
--  red in H3.
--  apply f_well_def.
--  algebra.
-- Qed.

-- Lemma f_pres_minus : forall x : R1, f [--]x[=][--](f x).
-- Proof.
--  intro.
--  apply cg_cancel_lft with (x := f x).
--  astepr ([0]:R2).
--  astepl (f (x[+][--]x)).
--  astepr (f [0]).
--   apply f_well_def.
--   algebra.
--  apply f_pres_One.
-- Qed.


-- Lemma f_pres_min : forall x y : R1, f (x[-]y)[=]f x[-]f y.
-- Proof.
--  intros.
--  astepr (f (x[+][--]y)).
--   apply f_well_def.
--   algebra.
--  astepr (f x[+][--](f y)).
--  red in H3.
--  astepr (f x[+]f [--]y).
--   apply H3.
--  apply bin_op_wd_unfolded.
--   apply eq_reflexive_unfolded.
--  apply f_pres_minus.
-- Qed.

-- End with_plus.

-- Section with_plus_less.

-- Hypothesis
--   H2 : fun_pres_relation R1 R2 f (cof_less (c:=R1)) (cof_less (c:=R2)).

-- Hypothesis H3 : fun_pres_bin_fun R1 R2 f (csg_op (c:=R1)) (csg_op (c:=R2)).

-- Lemma f_pres_ap_zero : forall x : R1, x[#][0] -> f x[#][0].
-- Proof.
--  intros.
--  apply ap_wdr_unfolded with (y := f [0]).
--   apply f_pres_apartness with (y := [0]:R1).
--    assumption.
--   assumption.
--  apply f_pres_One.
--  assumption.
-- Qed.

-- Section surjectivity_helps.
-- Hypothesis f_surj : map_is_surjective R1 R2 f.

-- Lemma f_pres_Lim : fun_pres_Lim R1 R2 f.
-- Proof.
--  red in |- *.
--  intros. rename X into H.
--  unfold Cauchy_Lim_prop2 in |- *.
--  intros e2 H0.
--  red in f_surj.
--  unfold Cauchy_Lim_prop2 in H.
--  cut {x : R1 | e2[=]f x}.
--   intro H4.
--   case H4.
--   intros e1 H5.
--   cut {N : nat | forall m : nat, N <= m -> AbsSmall e1 (a m[-]l_a)}.
--    intro H6.
--    case H6.
--    intro N.
--    intros.
--    exists N.
--    intros.
--    cut (AbsSmall e1 (a m[-]l_a)).
--     intro.
--     elim H8.
--     intros.
--     astepl (f e1).
--     astepr (f (a m[-]l_a)).
--      split.
--       astepl (f [--]e1).
--        apply f_pres_leEq.
--         assumption.
--        assumption.
--       apply f_pres_minus.
--       assumption.
--      apply f_pres_leEq.
--       assumption.
--      assumption.
--     apply f_pres_min.
--     assumption.
--    apply a0.
--    assumption.
--   apply H.
--   apply less_pres_f.
--    assumption.
--   astepl ([0]:R2).
--    astepr e2.
--    assumption.
--   apply eq_symmetric_unfolded.
--   apply f_pres_One.
--   assumption.
--  apply f_surj.
-- Qed.

-- End surjectivity_helps.

-- Section with_mult_plus_less.

-- Hypothesis H4 : fun_pres_bin_fun R1 R2 f (cr_mult (c:=R1)) (cr_mult (c:=R2)).

-- Lemma f_pres_one : f [1][=][1].
-- Proof.
--  intros.
--  apply eq_symmetric_unfolded.
--  apply mult_cancel_lft with (z := f [1]).
--   apply f_pres_ap_zero.
--   apply ring_non_triv.
--  astepl (f [1]).
--  astepr (f ([1][*][1])).
--  apply f_well_def.
--  algebra.
-- Qed.

-- Lemma f_pres_inv :
--  forall (x : R1) (H : x[#][0]),
--  f ([1][/] x[//]H)[=]([1][/] f x[//]f_pres_ap_zero x H).
-- Proof.
--  intros.
--  apply mult_cancel_lft with (z := f x).
--   apply f_pres_ap_zero.
--   assumption.
--  rstepr ([1]:R2).
--  astepr (f [1]).
--   astepl (f (x[*]([1][/] x[//]H))).
--   apply eq_symmetric_unfolded.
--   apply f_well_def.
--   rational.
--  apply f_pres_one.
-- Qed.

-- Definition simplified_Homomorphism (f_surj : map_is_surjective R1 R2 f) :=
--   Build_Homomorphism R1 R2 f H1 H2 H3 H4 (f_pres_Lim f_surj).

-- End with_mult_plus_less.

-- End with_plus_less.

-- End simplification.

-- (* end hide *)
