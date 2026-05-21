/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import  LeanPool.HopfieldNet.CReals.Core.CoRNmetric2Metric
import  LeanPool.HopfieldNet.CReals.Core.metric2UniformContinuity
import  LeanPool.HopfieldNet.CReals.Core.CoRNmodeltotalorderQMinMax
import  LeanPool.HopfieldNet.CReals.Core.CornQposMinMax
import  LeanPool.HopfieldNet.CReals.Core.CoRNmodelmetric2Qmetric
import LeanPool.HopfieldNet.CReals.Core.Cornmodelmetric2CRmetric
import LeanPool.HopfieldNet.CReals.Cauchy_IR
-- (*
-- Copyright © 2006-2008 Russell O’Connor

-- Permission is hereby granted, free of charge, to any person obtaining a copy of
-- this proof and associated documentation files (the "Proof"), to deal in
-- the Proof without restriction, including without limitation the rights to
-- use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
-- the Proof, and to permit persons to whom the Proof is furnished to do so,
-- subject to the following conditions:

-- The above copyright notice and this permission notice shall be included in all
-- copies or substantial portions of the Proof.

-- THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
-- IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
-- FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
-- COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
-- IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
-- CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
-- *)

-- Require Import CoRN.algebra.RSetoid.
-- Require Import CoRN.metric2.Metric.
-- Require Import CoRN.metric2.UniformContinuity.
-- Require Import CoRN.model.totalorder.QposMinMax.
-- Require Import CoRN.model.reals.Cauchy_IR.
-- Require Import CoRN.model.metric2.Qmetric.
-- Require Import CoRN.model.totalorder.QMinMax.

-- Require Import CoRN.tactics.CornTac.

-- From Coq Require Import Lia.

-- From Coq Require Import Qabs.

open RegularFunction QposInf

-- Require Export CoRN.reals.fast.CRFieldOps.

-- (* Backwards compatibility for Hint Rewrite locality attributes *)
-- Set Warnings "-unsupported-attributes".

-- Local Open Scope nat_scope.

-- Opaque Qmin Qmax.

-- (**
-- ** Isomorphism between CR and Cauchy_IR
-- In prove that CR is a real number structure, we must climb the algebraic
-- heirarchy.  The easiest way of doing this is to construct an isomorphism
-- between Cauchy_IR and CR because they are similar strucutres.
-- Then we can leverage the proofs that Cauchy_IR is a real number structure.

-- *** CR to Cauchy_IR
-- *)

#check Cauchy_IR
#check CR

-- Definition CRasCauchy_IR_raw (x:CR) (n:nat)
--   := approximate x (Qpos2QposInf (1 # P_of_succ_nat n)).

--do this for 0 = n maybe too.
def CRasCauchy_IR_raw (x : CR_carrier) (n : Nat) :=
  approximate x (Qpos2QposInf (⟨1/n+1, by {
    refine Right.add_pos_of_pos_of_nonneg ?_ rfl
    simp only [one_div, inv_pos, Nat.cast_pos]
    sorry
  }⟩))

#check Cauchy_prop

-- Show that CRasCauchy_IR_raw is a Cauchy sequence
theorem CRasCauchy_IR_raw_is_Cauchy (x : CR_carrier) :
  Cauchy_prop (K := ℚ) (CRasCauchy_IR_raw x) := sorry

-- Lemma CRasCauchy_IR_raw_is_Cauchy : forall (x:CR),
-- Cauchy_prop (R:=Q_as_COrdField) (CRasCauchy_IR_raw x).
-- Proof.
--  intros x e He.
--  destruct e as [en ed].
--  destruct en as [|en|en]. inversion He. 2: inversion He.
--  unfold CRasCauchy_IR_raw.
--  exists (pred (nat_of_P (2*ed))).
--  rewrite <- anti_convert_pred_convert.
--  intros m Hm.
--  change (ball (en#ed) (approximate x (Qpos2QposInf (1 # P_of_succ_nat m)))
--               (approximate x (Qpos2QposInf (1#(2*ed))))).
--  eapply ball_weak_le ;[|apply regFun_prf].
--  simpl.
--  apply Qle_trans with (((1 # P_of_succ_nat (pred (nat_of_P (2*ed)))) + (1 # 2 * ed)))%Q.
--   eapply plus_resp_leEq.
--   change (P_of_succ_nat (pred (nat_of_P (2*ed))) <= P_of_succ_nat m)%Z.
--   rewrite <-!POS_anti_convert. apply inj_le. lia.
--  rewrite <- anti_convert_pred_convert.
--  stepl ((2#1)*(1#(2*ed)))%Q; [|simpl; ring].
--  change ((2#1)*((1/2)*(1/ed)) <= en#ed)%Q.
--  ring_simplify.
--  change ((2#2)*(1/ed)<=en#ed)%Q.
--  setoid_replace (2#2)%Q  with 1%Q by constructor.
--  ring_simplify.
--  auto with *.
-- Qed.


-- Definition CRasCauchy_IR (x:CR) : Cauchy_IR :=
-- Build_CauchySeq _ _ (CRasCauchy_IR_raw_is_Cauchy x).

#check Cauchy_IR
def CRasCauchy_IR (x : CR_carrier) : CauchySeq' ℚ := by {
   constructor
   · apply CRasCauchy_IR_raw_is_Cauchy x
}

-- Show that CRasCauchy_IR respects equality
theorem CRasCauchy_IR_wd (x y : CR_carrier) (h : x = y) :
  CRasCauchy_IR x = CRasCauchy_IR y := sorry

-- Lemma CRasCauchy_IR_wd : forall (x y:CR), (x==y)%CR -> CRasCauchy_IR x[=]CRasCauchy_IR y.
-- Proof.
--  intros x y Hxy.
--  eapply Eq_alt_2_2.
--  intros e He.
--  destruct e as [en ed].
--  destruct en as [|en|en]. inversion He. 2: inversion He.
--  exists (pred(nat_of_P (2*ed))).
--  intros m Hm.
--  simpl.
--  unfold CRasCauchy_IR_raw.
--  set (d:=(1 # P_of_succ_nat m)%Qpos).
--  change (ball (en#ed) (approximate x (Qpos2QposInf d)) (approximate y (Qpos2QposInf d))).
--  eapply ball_weak_le;[|apply Hxy].
--  unfold d. simpl.
--  ring_simplify.
--  apply Qle_trans with ((2#1)*(1#(2 * ed)))%Q.
--   eapply mult_resp_leEq_lft;try discriminate.
--   change ((2*ed)<=P_of_succ_nat m)%Z.
--   rewrite <- Zpos_mult_morphism.
--   rewrite (anti_convert_pred_convert (2*ed)).
--   do 2 rewrite <- POS_anti_convert.
--   apply inj_le.
--   auto with *.
--  change (1#2*ed)%Q with ((1#2)*(1#ed))%Q.
--  ring_simplify.
--  auto with *.
-- Qed.

-- (**
-- *** Cauchy_IR to CR
-- *)

-- Definition Cauchy_IRasCR_raw (x:Cauchy_IR) (e:QposInf) : Q.
-- Proof.
--  revert e.
--  intros [e|];[|exact 0%Q].
--  destruct x as [f Hf].
--  unfold Cauchy_prop in Hf.
--  destruct (Hf (proj1_sig e) (Qpos_ispos e)) as [n Hn].
--  exact (f n).
-- Defined.

def Cauchy_IRasCR_raw (x : CauchySeq' ℚ) (e : QposInf) : ℚ := sorry

#check is_RegularFunction
-- Show that Cauchy_IRasCR_raw is a regular function

theorem Cauchy_IRasCR_is_Regular (x : CauchySeq' ℚ) :
  is_RegularFunction Qball (Cauchy_IRasCR_raw x) := sorry

-- Lemma Cauchy_IRasCR_is_Regular : forall (x:Cauchy_IR),
--     is_RegularFunction Qball (Cauchy_IRasCR_raw x).
-- Proof.
--  intros [f Hf] e1 e2.
--  simpl.
--  destruct (Hf (proj1_sig e1) (Qpos_ispos e1)) as [n1 Hn1].
--  destruct (Hf (proj1_sig e2) (Qpos_ispos e2)) as [n2 Hn2].
--  cut (forall (e1 e2:Qpos) n1 n2, n2 <= n1 ->
--    (forall m : nat, n1 <= m -> AbsSmall (R:=Q_as_COrdField) (proj1_sig e1) (f m[-]f n1)) ->
--      (forall m : nat, n2 <= m -> AbsSmall (R:=Q_as_COrdField) (proj1_sig e2) (f m[-]f n2)) ->
--        Qball (proj1_sig e1 + proj1_sig e2) (f n1) (f n2)).
--   intros H.
--   destruct (le_ge_dec n1 n2).
--    eapply ball_sym;simpl.
--    assert (QposEq (e1+e2) (e2+e1)) by (unfold QposEq; simpl; ring).
--    apply (ball_wd _ H0 _ _ (reflexivity _) _ _ (reflexivity _)). clear H0.
--    apply H; assumption.
--   auto.
--  clear - Hf.
--  intros e1 e2 n1 n2 H Hn1 Hn2.
--  assert (QposEq (e1+e2) (e2+e1)) by (unfold QposEq; simpl; ring).
--  apply (ball_wd _ H0 _ _ (reflexivity _) _ _ (reflexivity _)). clear H0.
--  eapply ball_weak. apply Qpos_nonneg.
--  eapply Hn2.
--  assumption.
-- Qed.

-- Definition Cauchy_IRasCR (x:Cauchy_IR) : CR :=
-- Build_RegularFunction (Cauchy_IRasCR_is_Regular x).

def Cauchy_IRasCR (x : CauchySeq' ℚ) : CR_carrier := by {
  apply RegularFunction.mk
  exact (Cauchy_IRasCR_is_Regular x)
}

-- Lemma Cauchy_IRasCR_wd
--   : forall (x y:Cauchy_IR), x[=]y -> (Cauchy_IRasCR x==Cauchy_IRasCR y)%CR.
-- Proof.
--  intros [x Hx] [y Hy] Hxy.
--  apply regFunEq_equiv, regFunEq_e.
--  intros e.
--  apply ball_closed.
--  intros d dpos.
--  simpl.
--  destruct (Hx (proj1_sig e) (Qpos_ispos e)) as [a Ha].
--  destruct (Hy (proj1_sig e) (Qpos_ispos e)) as [b Hb].
--  destruct (Eq_alt_2_1 _ _ _ Hxy _ dpos) as [c Hc].
--  simpl in Hc.
--  unfold Qball.
--  set (n:= Nat.max (Nat.max a b) c).
--  unfold QAbsSmall.
--  setoid_replace (x a - y b)%Q
--    with ((x a - x n) + (y n - y b) + (x n - y n))%Q.
--  2: ring.
--  autorewrite with QposElim.
--  repeat (eapply AbsSmall_plus).
--    apply AbsSmall_minus.
--    apply Ha;unfold n;apply Nat.le_trans with (Nat.max a b); auto with *.
--   apply Hb; unfold n;apply Nat.le_trans with (Nat.max a b); auto with *.
--  apply Hc; unfold n;auto with *.
-- Qed.

-- (** Composition is the identity *)
-- Lemma CRasCR : forall x:CR, (Cauchy_IRasCR (CRasCauchy_IR x)==x)%CR.
-- Proof.
--  intros x.
--  apply regFunEq_equiv, regFunEq_e.
--  intros e.
--  simpl.
--  destruct (CRasCauchy_IR_raw_is_Cauchy x (proj1_sig e) (Qpos_ispos e)) as [n Hn].
--  unfold CRasCauchy_IR_raw in *.
--  apply ball_closed.
--  intros d dpos.
--  setoid_replace (proj1_sig e+proj1_sig e+d)%Q
--    with (proj1_sig (e+(exist _ _ dpos+e))%Qpos)
--    by (simpl; ring).
--  destruct d as [dn dd].
--  destruct dn as [|dn|dn]. inversion dpos. 2: inversion dpos.
--  apply ball_triangle with (approximate x (Qpos2QposInf (1#P_of_succ_nat (n+(nat_of_P dd)))))%Qpos.
--  - apply ball_sym.
--   eapply Hn;auto with *.
--  - eapply ball_weak_le;[|apply regFun_prf].
--  simpl.
--  eapply plus_resp_leEq;simpl.
--  apply Qle_trans with (1#dd)%Q.
--   change (dd <= P_of_succ_nat (n + nat_of_P dd))%Z.
--   destruct n.
--    simpl.
--    rewrite P_of_succ_nat_o_nat_of_P_eq_succ.
--    rewrite Pplus_one_succ_r.
--    rewrite Zpos_plus_distr.
--    auto with *.
--   rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ.
--   rewrite <- nat_of_P_plus_morphism.
--   rewrite P_of_succ_nat_o_nat_of_P_eq_succ.
--   rewrite Pplus_one_succ_r.
--   repeat rewrite Zpos_plus_distr.
--   rewrite <- Zplus_assoc.
--   rewrite Zplus_comm.
--   rewrite <- Zplus_assoc.
--   rewrite <- Zpos_plus_distr.
--   rewrite <- Pplus_one_succ_l.
--   change (dd+0 <=  dd + Pos.succ (P_of_succ_nat n))%Z.
--   auto with *.
--  change (dd <= dn*dd)%Z.
--  auto with *.
-- Qed.

-- Lemma Cauchy_IRasCauchy_IR : forall x:Cauchy_IR, CRasCauchy_IR (Cauchy_IRasCR x)[=]x.
-- Proof.
--  intros [x Hx].
--  eapply Eq_alt_2_2.
--  intros e He.
--  assert (Z:(0<(1#2)*e)%Q).
--   rewrite <- (Qmult_0_r (1#2)).
--   eapply mult_resp_less_lft.
--    exact He.
--   constructor.
--  destruct (Hx _ Z) as [n Hn].
--  destruct e as [en ed].
--  destruct en as [|en|en]. inversion He. 2: inversion He.
--  exists (Nat.max n (nat_of_P ed)).
--  intros m Hm.
--  simpl.
--  destruct Hx as [n' Hn'].
--  apply AbsSmall_minus.
--  destruct (le_lt_dec n' m) as [H|H].
--   eapply AbsSmall_trans;[|apply Hn';assumption].
--   change (ed < en*(P_of_succ_nat m))%Z.
--   apply Z.lt_le_trans with (P_of_succ_nat m).
--    rewrite <- POS_anti_convert.
--    rewrite Zpos_eq_Z_of_nat_o_nat_of_P.
--    apply inj_lt.
--    apply Nat.lt_succ_r.
--    apply Nat.le_trans with (Nat.max n (nat_of_P ed));auto with *.
--   change (1*P_of_succ_nat m <= en * P_of_succ_nat m)%Z.
--   apply Zmult_lt_0_le_compat_r;auto with *.
--  stepl ((1#2)*(Z.pos en#ed)+(1#2)*(Z.pos en#ed))%Q; [| simpl; ring].
--  rstepr ((x m[-]x n)[+](x n[-]x n')).
--  assert (Y:n <= m).
--   apply Nat.le_trans with (Nat.max n (nat_of_P ed));auto with *.
--  apply AbsSmall_plus.
--   apply Hn.
--   assumption.
--  apply AbsSmall_minus; auto with *.
-- Qed.

-- (** Equalities are well defined. *)
-- Lemma Cauchy_IR_eq_as_CR_eq : forall (x y:Cauchy_IR),
-- ((Cauchy_IRasCR x) == (Cauchy_IRasCR y))%CR <-> x[=]y.
-- Proof.
--  intros x y.
--  split;[|apply Cauchy_IRasCR_wd].
--  intros H.
--  stepl (CRasCauchy_IR (Cauchy_IRasCR x)); [| apply Cauchy_IRasCauchy_IR].
--  stepr (CRasCauchy_IR (Cauchy_IRasCR y)); [| apply Cauchy_IRasCauchy_IR].
--  apply CRasCauchy_IR_wd.
--  assumption.
-- Qed.

-- Lemma CR_eq_as_Cauchy_IR_eq : forall (x y:CR),
-- (CRasCauchy_IR x [=] CRasCauchy_IR y) <-> (x==y)%CR.
-- Proof.
--  intros x y.
--  set (x':=CRasCauchy_IR x).
--  set (y':=CRasCauchy_IR y).
--  rewrite <- (CRasCR x).
--  rewrite <- (CRasCR y).
--  symmetry.
--  apply Cauchy_IR_eq_as_CR_eq.
-- Qed.

-- Local Open Scope uc_scope.
-- (**
-- *** Functions preserved by isomorphism.
-- *)
-- Lemma reverse_iso_wd_fun : forall
-- (f:Cauchy_IR -> Cauchy_IR)
-- (g:CR -> CR),
-- (forall x y, (x==y -> g x == g y)%CR) ->
-- (forall (x:Cauchy_IR),
-- (g (Cauchy_IRasCR x) == Cauchy_IRasCR (f x))%CR) ->
-- forall (x:CR),
-- (f (CRasCauchy_IR x) [=] CRasCauchy_IR (g x)).
-- Proof.
--  intros f g g_wd H x.
--  stepl (CRasCauchy_IR (Cauchy_IRasCR (f (CRasCauchy_IR x)))); [| apply Cauchy_IRasCauchy_IR].
--  apply CRasCauchy_IR_wd.
--  symmetry.
--  transitivity (g (Cauchy_IRasCR (CRasCauchy_IR x))).
--   apply g_wd.
--   symmetry.
--   apply CRasCR.
--  apply H.
-- Qed.

-- Lemma reverse_iso_uc_fun : forall
-- (f:Cauchy_IR -> Cauchy_IR)
-- (g:CR --> CR),
-- (forall (x:Cauchy_IR),
-- (g (Cauchy_IRasCR x) == Cauchy_IRasCR (f x))%CR) ->
-- forall (x:CR),
-- (f (CRasCauchy_IR x) [=] CRasCauchy_IR (g x)).
-- Proof.
--  intros f g H x.
--  apply reverse_iso_wd_fun.
--   apply uc_wd.
--  assumption.
-- Qed.

-- Lemma reverse_iso_bin_wd_fun : forall
-- (f:Cauchy_IR -> Cauchy_IR -> Cauchy_IR)
-- (g:CR -> CR -> CR),
-- (forall w x, (w == x)%CR -> forall y z, (y == z -> g w y == g x z)%CR) ->
-- (forall (x y:Cauchy_IR),
-- (g (Cauchy_IRasCR x) (Cauchy_IRasCR y) == Cauchy_IRasCR (f x y))%CR) ->
-- forall (x y:CR),
-- (f (CRasCauchy_IR x) (CRasCauchy_IR y) [=] CRasCauchy_IR (g x y)).
-- Proof.
--  intros f g g_wd H x y.
--  stepl (CRasCauchy_IR (Cauchy_IRasCR (f (CRasCauchy_IR x) (CRasCauchy_IR y))));
--    [| apply Cauchy_IRasCauchy_IR].
--  apply CRasCauchy_IR_wd.
--  symmetry.
--  transitivity (g (Cauchy_IRasCR (CRasCauchy_IR x)) (Cauchy_IRasCR (CRasCauchy_IR y))); [|apply H].
--  apply g_wd; symmetry; apply CRasCR.
-- Qed.

-- Lemma reverse_iso_bin_uc_fun : forall
-- (f:Cauchy_IR -> Cauchy_IR -> Cauchy_IR)
-- (g:CR --> CR --> CR),
-- (forall (x y:Cauchy_IR),
-- (g (Cauchy_IRasCR x) (Cauchy_IRasCR y) == Cauchy_IRasCR (f x y))%CR) ->
-- forall (x y:CR),
-- (f (CRasCauchy_IR x) (CRasCauchy_IR y) [=] CRasCauchy_IR (g x y)).
-- Proof.
--  intros f g H x y.
--  apply (reverse_iso_bin_wd_fun f (ucFun2 g)).
--   apply ucFun2_wd.
--  assumption.
-- Qed.

-- (** injection of rationals is preserved. *)
-- Lemma Cauchy_IR_inject_Q_as_CR_inject_Q : forall x:Q,
-- (' x == Cauchy_IRasCR (Cauchy_CReals.inject_Q _ x))%CR.
-- Proof.
--  intros x.
--  apply regFunEq_equiv, regFunEq_e.
--  intros e.
--  simpl.
--  destruct (CS_seq_const Q_as_COrdField x (proj1_sig e) (Qpos_ispos e)).
--  eapply ball_refl.
--  apply (Qpos_nonneg (e + e)).
-- Qed.

-- #[global]
-- Hint Rewrite Cauchy_IR_inject_Q_as_CR_inject_Q : CRtoCauchy_IR.

-- Lemma CR_inject_Q_as_Cauchy_IR_inject_Q : forall x:Q,
-- Cauchy_CReals.inject_Q _ x [=] CRasCauchy_IR (' x)%CR.
-- Proof.
--  intros x.
--  eapply Eq_alt_2_2.
--  simpl.
--  intros e He.
--  exists 0.
--  intros m Hm.
--  unfold cg_minus.
--  rstepr ([0]:Q).
--  apply zero_AbsSmall.
--  apply Qlt_le_weak.
--  assumption.
-- Qed.

-- (** plus is preserved. *)
-- Lemma Cauchy_IR_plus_as_CR_plus : forall x y:Cauchy_IR,
-- (Cauchy_IRasCR x + Cauchy_IRasCR y == Cauchy_IRasCR (x[+]y))%CR.
-- Proof.
--  intros [x Hx] [y Hy].
--  apply regFunEq_equiv, regFunEq_e.
--  intros e.
--  simpl.
--  unfold Cap_raw.
--  simpl.
--  destruct (Hx (proj1_sig ((1 # 2) * e)%Qpos)) as [n1 Hn1].
--  destruct (Hy (proj1_sig ((1 # 2) * e)%Qpos)) as [n2 Hn2].
--  destruct (CS_seq_plus) as [n3 Hn3].
--  set (n:= Nat.max n3 (Nat.max n1 n2)).
--  change (@ball Q_as_MetricSpace (proj1_sig e+proj1_sig e) (x n1 + y n2) (x n3 + y n3))%Q.
--  apply ball_triangle with (x n + y n)%Q.
--   assert (QposEq e (((1 # 2) * e +(1 # 2) * e))) by (unfold QposEq; simpl; ring).
--   apply (ball_wd _ H _ _ (reflexivity _) _ _ (reflexivity _)). clear H.
--   apply ball_triangle with (x n1 + y n)%Q; simpl; unfold Qball.
--   unfold QAbsSmall.
--   setoid_replace (x n1 + y n2 - (x n1 + y n))%Q with (y n2 - y n)%Q.
--   2: ring.
--    apply AbsSmall_minus.
--    apply Hn2.
--    unfold n.
--    rewrite Nat.max_assoc.
--    auto with *.
--    unfold QAbsSmall.
--    setoid_replace (x n1 + y n - (x n + y n))%Q with (x n1 - x n)%Q.
--    2: ring.
--   apply AbsSmall_minus.
--   apply Hn1.
--   unfold n.
--   rewrite (Nat.max_comm n1).
--   rewrite Nat.max_assoc.
--   auto with *.
--  eapply Hn3; unfold n; auto with *.
-- Qed.

-- #[global]
-- Hint Rewrite Cauchy_IR_plus_as_CR_plus : CRtoCauchy_IR.

-- Lemma CR_plus_as_Cauchy_IR_plus : forall x y:CR,
-- CRasCauchy_IR x [+] CRasCauchy_IR y [=] CRasCauchy_IR (x+y)%CR.
-- Proof.
--  apply reverse_iso_bin_uc_fun.
--  apply Cauchy_IR_plus_as_CR_plus.
-- Qed.

-- (** opp is preserved. *)
-- Lemma Cauchy_IR_opp_as_CR_opp : forall x:Cauchy_IR,
-- (-Cauchy_IRasCR x == Cauchy_IRasCR ([--]x))%CR.
-- Proof.
--  intros [x Hx].
--  apply regFunEq_equiv, regFunEq_e.
--  intros e.
--  simpl.
--  destruct (Hx (proj1_sig e) (Qpos_ispos e)) as [n1 Hn1].
--  destruct (CS_seq_inv Q_as_COrdField x Hx (proj1_sig e) (Qpos_ispos e)) as [n2 Hn2].
--  set (n:=(Nat.max n1 n2)).
--  change (@ball Q_as_MetricSpace (proj1_sig e+proj1_sig e) (- x n1) (- x n2))%Q.
--  apply (@ball_triangle Q_as_MetricSpace _ _ _ (- x n)%Q). simpl; unfold Qball.
--  unfold QAbsSmall.
--  setoid_replace (- x n1 - - x n)%Q with (x n - x n1)%Q.
--  2: ring. apply (Hn1 n). apply Nat.le_max_l.
--  apply Hn2. apply Nat.le_max_r.
-- Qed.

-- #[global]
-- Hint Rewrite Cauchy_IR_opp_as_CR_opp : CRtoCauchy_IR.

-- Lemma CR_opp_as_Cauchy_IR_opp : forall x:CR,
-- [--](CRasCauchy_IR x) [=] CRasCauchy_IR (- x)%CR.
-- Proof.
--  apply reverse_iso_uc_fun.
--  apply Cauchy_IR_opp_as_CR_opp.
-- Qed.

-- (** le is preserved. *)
-- Lemma Cauchy_IR_le_as_CR_le : forall (x y:Cauchy_IR),
-- (Cauchy_IRasCR x <= Cauchy_IRasCR y)%CR <-> x[<=]y.
-- Proof.
--  intros [x Hx] [y Hy].
--  split.
--   intros H1 [n [e He H2]].
--   assert (H1':=H1 ((1#3)*(exist _ _ He))%Qpos).
--   clear H1.
--   simpl in H1'.
--   unfold Cap_raw in H1'; simpl in H1'.
--   destruct (Hy (proj1_sig ((1 # 2) * ((1#3)* exist _ _ He))%Qpos)) as [n1 Hn1] in H1'.
--   destruct (Hx (proj1_sig ((1 # 2) * ((1#3)* exist _ _ He))%Qpos)) as [n2 Hn2] in H1'.
--   simpl in H2.
--   set (m:=Nat.max n (Nat.max n1 n2)).
--   assert (m1:n<=m);[unfold m; auto with *|].
--   assert (m2:n1<=m);[unfold m; apply Nat.le_trans with (Nat.max n1 n2); auto with *|].
--   assert (m3:n2<=m);[unfold m; apply Nat.le_trans with (Nat.max n1 n2); auto with *|].
--   apply (Qle_not_lt _ _ H1').
--   eapply inv_cancel_less;simpl.
--   clear H1'.
--   autorewrite with QposElim in *.
--   apply Qlt_le_trans with ((2#3)*e)%Q.
--    ring_simplify.
--    eapply mult_resp_less.
--     constructor.
--    assumption.
--   stepl (e + - ((1#2)*((1#3)*e)) + - ((1#2)*((1#3)*e)))%Q; [| simpl; ring].
--   stepr ((x m - y m) + (y m - y n1) + -(x m - x n2))%Q; [| simpl; ring].
--   eapply plus_resp_leEq_both.
--    apply plus_resp_leEq_both.
--     apply H2; assumption.
--    refine (proj1 (Hn1 m _));assumption.
--   apply inv_resp_leEq.
--   refine (proj2 (Hn2 m _));assumption.
--  (*Other Direction*)
--  intros H e.
--  simpl.
--  unfold Cap_raw; simpl.
--  destruct (Hy (proj1_sig ((1 # 2) * e)%Qpos)) as [n1 Hn1].
--  destruct (Hx (proj1_sig ((1 # 2) * e)%Qpos)) as [n2 Hn2].
--  apply Qnot_lt_le.
--  intros A.
--  apply H; clear H.
--  exists (Nat.max n1 n2).
--  simpl.
--  set (n:=Nat.max n1 n2).
--  exists (- proj1_sig e + - (y n1 + - x n2))%Q.
--   rewrite <- Qlt_minus_iff.
--   assumption.
--  intros m Hm.
--  unfold cg_minus.
--  simpl.
--  stepr ((x m - x n2) + -(y m - y n1) + -(y n1 + - x n2))%Q; [| simpl; ring].
--  eapply plus_resp_leEq.
--  stepl (-((1 # 2) * proj1_sig e) + - ((1 # 2) * proj1_sig e))%Q; [| simpl; ring].
--  apply plus_resp_leEq_both.
--   refine (proj1 (Hn2 _ _)).
--   apply Nat.le_trans with n; [unfold n;auto with *|assumption].
--  apply inv_resp_leEq.
--  refine (proj2 (Hn1 _ _)).
--  apply Nat.le_trans with n; [unfold n;auto with *|assumption].
-- Qed.


-- #[global]
-- Hint Rewrite Cauchy_IR_le_as_CR_le : CRtoCauchy_IR.

-- Lemma CR_le_as_Cauchy_IR_le : forall (x y:CR),
-- CRasCauchy_IR x[<=]CRasCauchy_IR y <-> (x<=y)%CR.
-- Proof.
--  intros x y.
--  rewrite <- Cauchy_IR_le_as_CR_le.
--  do 2 rewrite -> CRasCR.
--  reflexivity.
-- Qed.

-- (** mult is preserved. *)
-- Lemma Cauchy_IR_mult_as_CRmult_bounded : forall x y:Cauchy_IR,
-- forall (z:Qpos) (N:nat), (forall i:nat, (N<=i) -> AbsSmall (proj1_sig z) (CS_seq _ y i)) ->
-- (ucFun2 (CRmult_bounded z) (Cauchy_IRasCR x) (Cauchy_IRasCR y) == Cauchy_IRasCR (x[*]y))%CR.
-- Proof.
--  intros [x Hx] y z N Hz.
--  destruct y as [y Hy].
--  apply regFunEq_equiv, regFunEq_e.
--  intros e.
--  simpl.
--  destruct CS_seq_mult as [n3 Hn3].
--  unfold Cap_raw.
--  simpl in *.
--  destruct Hx as [n1 Hn1].
--  apply Qscale_modulus_elim.
--   intros Hxn1.
--   pose (n:=(Nat.max n3 (Nat.max n1 N))).
--   rewrite -> Hxn1.
--   assert (Qeq (0 * Qmax (- proj1_sig z) (Qmin (proj1_sig z)
--     (Cauchy_IRasCR_raw (Build_CauchySeq Q_as_COrdField y Hy)(QposInf_bind (fun e0 : Qpos => e0) QposInfinity))))%Q (0 * y n)%Q).
--    ring.
--   rewrite -> H. clear H.
--   change (@ball Q_as_MetricSpace (proj1_sig e+proj1_sig e) (0 * y n) (x n3 * y n3))%Q.
--   apply ball_triangle with (x n*y n)%Q;[|eapply Hn3; unfold n; auto with *].
--   apply ball_sym.
--   simpl.
--   setoid_replace (0 * y n)%Q with (x n1 * y n)%Q.
--   2: rewrite Hxn1; reflexivity.
--   unfold Qball.
--   unfold QAbsSmall.
--   setoid_replace (x n * y n - x n1 * y n)%Q with ((x n - x n1)*y n)%Q.
--   2: ring.
--   apply AbsSmall_trans with ((1#2)*proj1_sig e)%Q.
--    apply half_3.
--    apply Qpos_ispos.
--    stepl (((1#2)*proj1_sig e/ proj1_sig z)* proj1_sig z)%Q;
--      [| simpl;field;apply Qpos_nonzero].
--   apply mult_AbsSmall;[apply Hn1|apply Hz]; unfold n; apply Nat.le_trans with (Nat.max n1 N); auto with *.
--  intros w Hw.
--  simpl.
--  destruct (Hy (proj1_sig w) (Qpos_ispos w)) as [n2 Hn2].
--  pose (n:=(Nat.max (Nat.max n1 n2) (Nat.max n3 N))).
--  assert (n1 <= n);[unfold n; apply Nat.le_trans with (Nat.max n1 n2); auto with *|].
--  assert (n2 <= n);[unfold n; apply Nat.le_trans with (Nat.max n1 n2); auto with *|].
--  assert (n3 <= n);[unfold n; apply Nat.le_trans with (Nat.max n3 N); auto with *|].
--  assert (N <= n);[unfold n; apply Nat.le_trans with (Nat.max n3 N); auto with *|].
--  change (Qball (proj1_sig e+proj1_sig e))
--    with (@ball Q_as_MetricSpace (proj1_sig e + proj1_sig e)).
--  apply ball_triangle with (x n * y n)%Q;[|eapply Hn3; assumption].
--  clear Hn3.
--  assert (QposEq e ((1#2)*e + (1#2)*e)) by (unfold QposEq; simpl; ring).
--  apply (ball_wd _ H3 _ _ (reflexivity _) _ _ (reflexivity _)). clear H3.
--  apply ball_triangle with (x n1 * y n)%Q; apply ball_sym; simpl; unfold Qball.
--  unfold QAbsSmall.
--  setoid_replace (x n1 * y n - x n1 * Qmax (- proj1_sig z) (Qmin (proj1_sig z) (y n2)))%Q
--    with (x n1*(y n - Qmax (- proj1_sig z) (Qmin (proj1_sig z) (y n2))))%Q. 2: ring.
--  simpl.
--   stepl (((1#2)*proj1_sig e/proj1_sig w)*proj1_sig w)%Q; [| simpl;field;apply Qpos_nonzero].
--   apply mult_AbsSmall;[apply Hw|].
--   destruct (Hz n H2) as [X0 X1].
--   destruct (Hn2 _ H0) as [X2 X3].
--   unfold cg_minus in *.
--   simpl in *.
--   change (Qmax (- proj1_sig z) (Qmin (proj1_sig z) (y n2)))%Q
--     with (QboundAbs z (y n2))%Q.
--   assert (A0:(- proj1_sig w<=0)%Q).
--    rewrite -> Qle_minus_iff.
--    ring_simplify.
--    apply Qpos_nonneg.
--   rewrite -> Qle_minus_iff in *.
--   clear - A0 X0 X1 X2 X3 Hn2 H0.
--   ring_simplify in A0.
--   ring_simplify in X0.
--   ring_simplify in X1.
--   ring_simplify in X2.
--   ring_simplify in X3.
--   apply QboundAbs_elim; intros I; try solve [apply Hn2;assumption]; rewrite -> Qle_minus_iff in I.
--    apply AbsSmall_minus.
--    unfold cg_minus;simpl.
--    apply leEq_imp_AbsSmall.
--     apply X1.
--    rewrite -> Qle_minus_iff.
--    stepr ((y n + (-1 # 1) * y n2 + proj1_sig w)+(y n2 + - proj1_sig z))%Q; [| simpl; ring].
--    eapply plus_resp_nonneg; assumption.
--   eapply leEq_imp_AbsSmall; simpl; ring_simplify.
--    apply X0.
--   rewrite -> Qle_minus_iff.
--   stepr ((proj1_sig w + (-1 # 1) * y n + y n2)+(- proj1_sig z + - y n2))%Q; [| simpl; ring].
--   eapply plus_resp_nonneg; assumption.
--   unfold QAbsSmall.
--   setoid_replace (x n * y n - x n1 * y n)%Q with ((x n - x n1)*y n)%Q. 2: ring.
--  autorewrite with QposElim.
--  stepl (((1#2)*proj1_sig e/proj1_sig z)*proj1_sig z)%Q; [| simpl; field; apply Qpos_nonzero].
--  apply mult_AbsSmall;[apply Hn1;assumption|apply Hz;assumption].
-- Qed.

-- Lemma AbsSmall_Qabs : forall x y, (Qabs y <= x)%Q <-> AbsSmall x y.
-- Proof.
--  cut (forall x y, (0 <= y)%Q -> ((Qabs y <= x)%Q <-> AbsSmall (R:=Q_as_COrdField) x y)).
--   intros H x y.
--   generalize (H x y) (H x (-y)%Q).
--   clear H.
--   rewrite -> Qabs_opp.
--   apply Qabs_case; intros H H1 H2.
--    auto.
--   assert (X:AbsSmall (R:=Q_as_COrdField) x y <-> AbsSmall (R:=Q_as_COrdField) x (- y)%Q).
--    split.
--     apply inv_resp_AbsSmall.
--    intros X.
--    stepr (- - y)%Q; [| simpl; ring].
--    apply inv_resp_AbsSmall.
--    assumption.
--   rewrite -> X.
--   eapply H2.
--   rewrite -> Qle_minus_iff in H.
--   ring_simplify in H.
--   ring_simplify.
--   apply H.
--  intros x y H.
--  rewrite -> Qabs_pos;[|assumption].
--  split.
--   intros H0.
--   apply leEq_imp_AbsSmall; assumption.
--  intros [_ H0].
--  assumption.
-- Qed.

-- Lemma Cauchy_IR_mult_as_CR_mult : forall x y:Cauchy_IR,
-- ((Cauchy_IRasCR x)*(Cauchy_IRasCR y) == Cauchy_IRasCR (x[*]y))%CR.
-- Proof.
--  intros x [y Hy].
--  destruct (CS_seq_bounded _ y Hy) as [k Hk [n Hn]].
--  set (y':=Build_CauchySeq Q_as_COrdField y Hy).
--  set (k':=(exist _ _ Hk)).
--  transitivity ((ucFun2 (CRmult_bounded (CR_b (1 # 1) (Cauchy_IRasCR y')+k')%Qpos) (Cauchy_IRasCR x)
--    (Cauchy_IRasCR y'))).
--   apply CRmult_bounded_weaken.
--     apply CR_b_lowerBound.
--    apply CR_b_upperBound.
--    simpl.
--   rewrite -> Qle_minus_iff.
--   ring_simplify.
--   auto with *.
--  apply Cauchy_IR_mult_as_CRmult_bounded with n.
--  intros i Hi.
--  eapply AbsSmall_trans;[|apply Hn;assumption].
--  simpl.
--  rewrite -> Qlt_minus_iff.
--  unfold k'.
--  autorewrite with QposElim.
--  ring_simplify.
--  clear.
--  destruct Hy.
--  rewrite Qplus_comm.
--  apply Q.Qplus_lt_le_0_compat.
--  reflexivity. apply Qabs_nonneg.
-- Qed.

-- #[global]
-- Hint Rewrite Cauchy_IR_mult_as_CR_mult : CRtoCauchy_IR.

-- Lemma CR_mult_as_Cauchy_IR_mult : forall x y:CR,
-- (CRasCauchy_IR x)[*](CRasCauchy_IR y) [=] CRasCauchy_IR (x*y)%CR.
-- Proof.
--  apply reverse_iso_bin_wd_fun.
--   apply CRmult_wd.
--  apply Cauchy_IR_mult_as_CR_mult.
-- Qed.

-- (** lt is preserved. *)
-- Lemma Cauchy_IR_lt_as_CR_lt_1 : forall (x y:Cauchy_IR),
-- x[<]y -> (Cauchy_IRasCR x < Cauchy_IRasCR y)%CR.
-- Proof.
--  intros x y [n [e He Hn]].
--  exists (exist _ _ He).
--  abstract ( autorewrite with CRtoCauchy_IR; intros [m [d Hd Hm]];
--    refine (Qle_not_lt _ _ (Hn (Nat.max n m) _) _);[auto with *|]; rewrite -> Qlt_minus_iff;
--      apply Qlt_le_trans with d;[assumption|]; autorewrite with QposElim in Hm; eapply Hm; auto with *
--        ).
-- Defined.

-- Lemma CR_lt_as_Cauchy_IR_lt_1 : forall (x y:CR),
-- (x < y)%CR -> (CRasCauchy_IR x)[<](CRasCauchy_IR y).
-- Proof.
--  intros x y [e He].
--  apply shift_zero_less_minus'.
--  apply (less_leEq_trans _ [0] (Cauchy_CReals.inject_Q _ (proj1_sig e))).
--   eapply ing_lt.
--   apply Qpos_ispos.
--  unfold cg_minus.
--  stepr (CRasCauchy_IR (y-x))%CR.
--   stepl (CRasCauchy_IR (' proj1_sig e)%CR).
--    rewrite <- Cauchy_IR_le_as_CR_le.
--    do 2 rewrite -> CRasCR.
--    assumption.
--   eapply CR_inject_Q_as_Cauchy_IR_inject_Q.
--  stepl (CRasCauchy_IR y[+]CRasCauchy_IR(- x)%CR).
--   apply plus_resp_eq.
--   eapply CR_opp_as_Cauchy_IR_opp.
--  eapply CR_plus_as_Cauchy_IR_plus.
-- Qed.

-- Lemma Cauchy_IR_lt_as_CR_lt_2 : forall (x y:Cauchy_IR),
-- ((Cauchy_IRasCR x) < (Cauchy_IRasCR y))%CR -> x[<]y.
-- Proof.
--  intros x y H.
--  stepl (CRasCauchy_IR (Cauchy_IRasCR (x))); [| apply Cauchy_IRasCauchy_IR].
--  stepr (CRasCauchy_IR (Cauchy_IRasCR (y))); [| apply Cauchy_IRasCauchy_IR].
--  apply CR_lt_as_Cauchy_IR_lt_1.
--  assumption.
-- Qed.

-- Lemma CR_lt_as_Cauchy_IR_lt_2 : forall (x y:CR),
-- (CRasCauchy_IR x)[<](CRasCauchy_IR y) -> (x < y)%CR.
-- Proof.
--  intros x y H.
--  eapply CRltT_wd;try apply CRasCR.
--  apply Cauchy_IR_lt_as_CR_lt_1.
--  assumption.
-- Qed.

-- (** appartness is preserved. *)
-- Lemma Cauchy_IR_ap_as_CR_ap_1 : forall (x y:Cauchy_IR),
-- x[#]y -> (CRapartT (Cauchy_IRasCR x) (Cauchy_IRasCR y))%CR.
-- Proof.
--  intros x y [H|H];[left|right];apply Cauchy_IR_lt_as_CR_lt_1; apply H.
-- Defined.

-- Lemma CR_ap_as_Cauchy_IR_ap_1 : forall (x y:CR),
-- CRapartT x y -> (CRasCauchy_IR x) [#] (CRasCauchy_IR y).
-- Proof.
--  intros x y [H|H];[left|right];apply CR_lt_as_Cauchy_IR_lt_1; apply H.
-- Defined.

-- Lemma Cauchy_IR_ap_as_CR_ap_2 : forall (x y:Cauchy_IR),
-- (CRapartT (Cauchy_IRasCR x) (Cauchy_IRasCR y))%CR -> x[#]y.
-- Proof.
--  intros x y [H|H];[left|right];apply Cauchy_IR_lt_as_CR_lt_2; apply H.
-- Qed.

-- Lemma CR_ap_as_Cauchy_IR_ap_2 : forall (x y:CR),
-- (CRasCauchy_IR x) [#] (CRasCauchy_IR y) -> CRapartT x y.
-- Proof.
--  intros x y [H|H];[left|right];apply CR_lt_as_Cauchy_IR_lt_2; apply H.
-- Defined.

-- (** inv is preserved. *)
-- Lemma Cauchy_IR_inv_as_CRinv_pos : forall (x:Cauchy_IR) x_,
-- forall (z:Qpos) (N:nat), (forall i:nat, (N<=i) -> (proj1_sig z <= (CS_seq _ x i))%Q) ->
-- (CRinv_pos z (Cauchy_IRasCR x) == Cauchy_IRasCR (f_rcpcl x (@inr _ _ x_)))%CR.
-- Proof.
--  intros [x Hx] [a [d d_ x_]] z n Hn.
--  apply regFunEq_equiv, regFunEq_e.
--  intros e.
--  simpl.
--  unfold Qinv_modulus.
--  destruct (Hx (proj1_sig z * proj1_sig z * proj1_sig e)%Q) as [b Hb].
--  destruct (CS_seq_recip) as [c Hc].
--  set (y := (CS_seq_recip_seq Q_as_COrdField x d d_ a
--              (fun (n : nat) (H : le a n) =>
--               leEq_wdr Q_as_COrdField d
--                 (@cg_minus Q_as_CGroup (x n) (Qmake Z0 xH)) (x n) (x_ n H)
--                 (cg_inv_zero Q_as_CGroup (x n))))) in *.
--  unfold CS_seq_recip_seq in y.
--  simpl in y.
--  set (m:=Nat.max (Nat.max a n) (Nat.max b c)).
--  assert (Hm1: c<=m).
--   unfold m; apply Nat.le_trans with (Nat.max b c); auto with *.
--  change (@ball Q_as_MetricSpace (proj1_sig e+proj1_sig e) (/ Qmax (proj1_sig z) (x b))%Q (y c)).
--  apply ball_triangle with (y m);[|eapply Hc;assumption].
--  clear Hc.
--  unfold y.
--  destruct (lt_le_dec m a) as [Z|Z].
--   elim (proj1 (Nat.le_ngt _ _) Z).
--   unfold m.
--   apply Nat.lt_le_trans with (S (Nat.max a n)); auto with *.
--  change (AbsSmall (proj1_sig e) (/ Qmax (proj1_sig z) (x b)-1 * / x m))%Q.
--  clear y.
--  assert (T:(~ (x m == 0)%Q /\ ~ (Qmax (proj1_sig z) (x b) == 0)%Q)).
--   split; apply (ap_symmetric_unfolded Q_as_CSetoid); eapply Qlt_not_eq.
--    apply Qlt_le_trans with (proj1_sig z).
--     apply Qpos_ispos.
--    apply Hn.
--    apply Nat.le_trans with (Nat.max a n).
--     auto with *.
--    unfold m; auto with *.
--   apply Qlt_le_trans with (proj1_sig z); auto with *.
--   stepr ((/(Qmax (proj1_sig z) (x b))*/(x m))*(x m - (Qmax (proj1_sig z) (x b))))%Q;
--     [| simpl; field; assumption].
--   stepl ((/ Qmax (proj1_sig z) (x b) * / x m)*((Qmax (proj1_sig z) (x b))*(x m)* proj1_sig e))%Q;
--     [| simpl;field; assumption].
--  apply mult_resp_AbsSmall.
--   assert (foo:forall q:Q, (0<=q -> 0<=/q)%Q).
--    intros [[|p|p] q] qH; apply qH.
--   apply mult_resp_nonneg.
--    apply foo.
--    apply Qle_trans with (proj1_sig z).
--     apply Qpos_nonneg.
--    apply Qmax_ub_l.
--   apply foo.
--   apply Qle_trans with (proj1_sig z).
--    apply Qpos_nonneg.
--   apply Hn.
--   apply Nat.le_trans with (Nat.max a n); unfold m; auto with *.
--  simpl in x_.
--  apply (AbsSmall_leEq_trans _ (proj1_sig z*proj1_sig z*proj1_sig e)%Q).
--   apply mult_resp_leEq_rht;[apply mult_resp_leEq_both|]; try apply Qpos_nonneg.
--    apply Qmax_ub_l.
--   apply Hn.
--   apply Nat.le_trans with (Nat.max a n); unfold m; auto with *.
--  assert (W:AbsSmall (R:=Q_as_COrdField) (proj1_sig z * proj1_sig z * proj1_sig e)%Q (x m - x b)%Q).
--   apply Hb.
--   apply Nat.le_trans with (Nat.max b c); unfold m; auto with *.
--  apply Qmax_case;intros C;[|assumption].
--  apply leEq_imp_AbsSmall.
--   unfold Qminus.
--   rewrite <- Qle_minus_iff.
--   apply Hn.
--   apply Nat.le_trans with (Nat.max a n); unfold m; auto with *.
--  apply Qle_trans with (x m - x b)%Q.
--   rewrite -> Qle_minus_iff.
--   stepr (proj1_sig z + - x b)%Q; [| simpl; ring].
--   rewrite <- Qle_minus_iff.
--   assumption.
--  destruct W; assumption.
-- Qed.

-- Lemma Cauchy_IR_nonZero_as_CR_nonZero_1 : forall (x:Cauchy_IR),
-- Dom (f_rcpcl' _) x -> (CRapartT (Cauchy_IRasCR x) 0)%CR.
-- Proof.
--  intros x x_.
--  eapply CRapartT_wd.
--    reflexivity.
--   symmetry.
--   apply Cauchy_IR_inject_Q_as_CR_inject_Q.
--  apply Cauchy_IR_ap_as_CR_ap_1.
--  assumption.
-- Defined.

-- Lemma CR_nonZero_as_Cauchy_IR_nonZero_1 : forall (x:CR),
-- (CRapartT x 0)%CR -> Dom (f_rcpcl' _) (CRasCauchy_IR x).
-- Proof.
--  intros x x_.
--  change ((CRasCauchy_IR x)[#][0]).
--  stepr (CRasCauchy_IR 0%CR).
--   apply CR_ap_as_Cauchy_IR_ap_1.
--   assumption.
--  eapply CR_inject_Q_as_Cauchy_IR_inject_Q.
-- Defined.

-- Lemma Cauchy_IR_inv_as_CR_inv_short : forall (x:Cauchy_IR) x_,
-- (@CRinvT (Cauchy_IRasCR x) (Cauchy_IR_nonZero_as_CR_nonZero_1 _ x_) == Cauchy_IRasCR (f_rcpcl x x_))%CR.
-- Proof.
--  intros [x Hx] [H|H].
--   set (x':=(Build_CauchySeq Q_as_COrdField x Hx)) in *.
--   assert (H':(cm_unit Cauchy_IR)[<][--](x':Cauchy_IR)).
--    apply inv_cancel_less.
--    rstepl x'.
--    assumption.
--   set (y:= (Cauchy_IRasCR [--](f_rcpcl (F:=Cauchy_IR) ([--](x':Cauchy_IR)) (@inr _ _ H')))%CR).
--   transitivity y.
--    destruct H as [n [e He H]].
--    change (-(CRinv_pos (exist _ _ He) (- Cauchy_IRasCR (Build_CauchySeq Q_as_COrdField x Hx)))==y)%CR.
--    unfold y.
--    rewrite <- Cauchy_IR_opp_as_CR_opp.
--    apply CRopp_wd.
--    set (X := (Cauchy_IRasCR (f_rcpcl (F:=Cauchy_IR) [--](x':Cauchy_IR)
--      (@inr (R_lt Q_as_COrdField [--](x':Cauchy_IR) ([0]:Cauchy_IR)) ([0][<][--](x':Cauchy_IR)) H')))%CR).
--    rewrite -> Cauchy_IR_opp_as_CR_opp.
--    eapply Cauchy_IR_inv_as_CRinv_pos.
--    intros i Hi.
--    autorewrite with QposElim.
--    simpl.
--    stepr (0 - x i)%Q; [| simpl; ring].
--    eapply H.
--    apply Hi.
--   unfold y.
--   apply Cauchy_IRasCR_wd.
--   eapply mult_cancel_lft.
--    left.
--    apply H.
--   stepr ([1]:Cauchy_IR).
--    eapply eq_transitive.
--     apply cring_inv_mult_lft.
--    apply eq_symmetric.
--    eapply eq_transitive;[|apply cring_inv_mult_rht].
--    apply eq_symmetric.
--    apply x_div_x.
--   apply eq_symmetric.
--   apply x_div_x.
--  destruct H as [n [e He H]].
--   eapply Cauchy_IR_inv_as_CRinv_pos.
--  intros i Hi.
--  autorewrite with QposElim.
--  simpl in *.
--  stepr (x i- 0)%Q; [| simpl; ring].
--  apply H.
--  apply Hi.
-- Qed.

-- #[global]
-- Hint Rewrite Cauchy_IR_inv_as_CR_inv_short : CRtoCauchy_IR.

-- Lemma Cauchy_IR_inv_as_CR_inv : forall (x:Cauchy_IR) x_ H,
-- (@CRinvT (Cauchy_IRasCR x) H == Cauchy_IRasCR (f_rcpcl x x_))%CR.
-- Proof.
--  intros x x_ H.
--  rewrite <- Cauchy_IR_inv_as_CR_inv_short.
--  apply CRinvT_irrelevant.
-- Qed.

-- Lemma CR_inv_as_Cauchy_IR_inv : forall (x:CR) x_ H,
-- f_rcpcl (CRasCauchy_IR x) H [=] CRasCauchy_IR (@CRinvT x x_).
-- Proof.
--  intros x x_ H.
--  stepl (CRasCauchy_IR (Cauchy_IRasCR (f_rcpcl (CRasCauchy_IR x) H))); [| apply Cauchy_IRasCauchy_IR].
--  apply CRasCauchy_IR_wd.
--  rewrite <- Cauchy_IR_inv_as_CR_inv_short.
--  apply CRinvT_wd.
--  apply CRasCR.
-- Qed.

-- Lemma CR_inv_as_Cauchy_IR_inv_short : forall (x:CR) x_,
-- f_rcpcl (CRasCauchy_IR x) (CR_nonZero_as_Cauchy_IR_nonZero_1 _ x_) [=] CRasCauchy_IR (@CRinvT x x_).
-- Proof.
--  intros.
--  apply CR_inv_as_Cauchy_IR_inv.
-- Qed.
