/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

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
-- Require Export CoRN.reals.CauchySeq.
-- Require Import CoRN.reals.iso_CReals.
-- Require Import CoRN.reals.R_morphism.
-- Require Import CoRN.reals.fast.CRArith.
-- Require Export CoRN.model.reals.CRreal.
-- Require Import CoRN.tactics.CornTac.

-- (* Backwards compatibility for Hint Rewrite locality attributes *)
-- Set Warnings "-unsupported-attributes".

-- Opaque CR inject_Q.
-- (**
-- ** Isomorphism between CR and IR
-- Because CR and IR are both real number structures, they are isomorphic.
-- This module develops lemmas for translating between expressions over CR
-- and IR.  A rewrite database [IRtoCR] contains rewrite lemmas for
-- converting expressions over IR to expressions over CR.
-- *)
-- Lemma CRIR_iso : Isomorphism CRasCReals IR.
-- Proof.
--  apply Canonic_Isomorphism_between_CReals.
-- Qed.

-- Definition CRasIR : CR -> IR := iso_map_lft _ _ CRIR_iso.
-- Definition IRasCR : IR -> CR := iso_map_rht _ _ CRIR_iso.

-- Lemma CRasIRasCR_id : forall (x:CR), (IRasCR (CRasIR x)==x)%CR.
-- Proof.
--  apply (inversity_rht _ _ CRIR_iso).
-- Qed.

-- Lemma IRasCRasIR_id : forall (x:IR), (CRasIR (IRasCR x)[=]x).
-- Proof.
--  apply (inversity_lft _ _ CRIR_iso).
-- Qed.

-- Lemma IRasCR_wd : forall x y, x[=]y -> (IRasCR x == IRasCR y)%CR.
-- Proof.
--  apply (map_wd_unfolded _ _ (iso_map_rht _ _ CRIR_iso)).
-- Qed.

-- Lemma IR_eq_as_CR : forall x y, x[=]y <-> (IRasCR x == IRasCR y)%CR.
-- Proof.
--  split.
--   apply (map_wd_unfolded _ _ (iso_map_rht _ _ CRIR_iso)).
--  intros H.
--  stepl (CRasIR (IRasCR x)); [| now apply IRasCRasIR_id].
--  stepr (CRasIR (IRasCR y)); [| now apply IRasCRasIR_id].
--  apply map_wd_unfolded.
--  assumption.
-- Qed.

-- Lemma CRasIR_wd : forall x y, (x==y)%CR -> CRasIR x [=] CRasIR y.
-- Proof.
--  apply (map_wd_unfolded _ _ (iso_map_lft _ _ CRIR_iso)).
-- Qed.

-- Lemma CR_less_as_IR : forall x y, (IRasCR x < IRasCR y -> x[<]y)%CR.
-- Proof.
--  intros x y H.
--  stepl (CRasIR (IRasCR x)); [| now apply IRasCRasIR_id].
--  stepr (CRasIR (IRasCR y)); [| now apply IRasCRasIR_id].
--  apply map_pres_less.
--  assumption.
-- Qed.

-- Lemma CR_ap_as_IR : forall x y, (IRasCR x >< IRasCR y -> x[#]y)%CR.
-- Proof.
--  intros.
--  stepl (CRasIR (IRasCR x)); [| now apply IRasCRasIR_id].
--  stepr (CRasIR (IRasCR y)); [| now apply IRasCRasIR_id].
--  apply map_pres_apartness.
--  assumption.
-- Qed.

-- Lemma IR_leEq_as_CR : forall x y, x[<=]y <-> (IRasCR x <= IRasCR y)%CR.
-- Proof.
--  intros x y.
--  split;[apply: f_pres_leEq|apply: leEq_pres_f]; solve [ apply map_strext |apply map_pres_less].
-- Qed.

-- Lemma IR_Zero_as_CR : (IRasCR [0]==0)%CR.
-- Proof.
--  apply (map_pres_zero_unfolded _ _ (iso_map_rht _ _ CRIR_iso)).
-- Qed.

-- #[global]
-- Hint Rewrite IR_Zero_as_CR : IRtoCR.

-- Lemma CR_ap_zero_as_IR : forall x, (IRasCR x >< 0 -> x[#][0])%CR.
-- Proof.
--  intros x H.
--  apply CR_ap_as_IR.
--  generalize H.
--  apply CRapartT_wd.
--   reflexivity.
--  symmetry.
--  apply IR_Zero_as_CR.
-- Qed.

-- Lemma IR_plus_as_CR : forall x y,
--  (IRasCR (x[+]y)== IRasCR x + IRasCR y)%CR.
-- Proof.
--  apply (map_pres_plus _ _ (iso_map_rht _ _ CRIR_iso)).
-- Qed.

-- #[global]
-- Hint Rewrite IR_plus_as_CR : IRtoCR.

-- Lemma IR_Sum0_as_CR : forall m x,
--  (IRasCR (Sum0 m x)==@Sum0 CRasCAbGroup m (fun n => IRasCR (x n)))%CR.
-- Proof.
--  intros m x.
--  induction m.
--   apply IR_Zero_as_CR.
--  simpl in *.
--  set (a:=Sum0 (G:=CRasCAbGroup) m (fun n : nat => IRasCR (x n))) in *.
--  clearbody a.
--  rewrite <- IHm.
--  apply IR_plus_as_CR.
-- Qed.

-- Lemma IR_opp_as_CR : forall x,
--  (IRasCR ([--]x)== - IRasCR x)%CR.
-- Proof.
--  apply (map_pres_minus _ _ (iso_map_rht _ _ CRIR_iso)).
-- Qed.

-- #[global]
-- Hint Rewrite IR_opp_as_CR : IRtoCR.

-- Lemma IR_minus_as_CR : forall x y,
--  (IRasCR (x[-]y)== IRasCR x - IRasCR y)%CR.
-- Proof.
--  unfold cg_minus.
--  intros x y.
--  rewrite -> IR_plus_as_CR.
--  rewrite -> IR_opp_as_CR.
--  reflexivity.
-- Qed.

-- #[global]
-- Hint Rewrite IR_minus_as_CR : IRtoCR.

-- Lemma IR_One_as_CR : (IRasCR [1]==1)%CR.
-- Proof.
--  apply (map_pres_one_unfolded _ _ (iso_map_rht _ _ CRIR_iso)).
-- Qed.

-- #[global]
-- Hint Rewrite IR_One_as_CR : IRtoCR.

-- Lemma IR_mult_as_CR : forall x y,
--  (IRasCR (x[*]y)==(IRasCR x * IRasCR y))%CR.
-- Proof.
--  apply (map_pres_mult _ _ (iso_map_rht _ _ CRIR_iso)).
-- Qed.

-- #[global]
-- Hint Rewrite IR_mult_as_CR : IRtoCR.

-- Lemma IR_div_as_CR : forall x y y_ y__,
--  (IRasCR (x[/]y[//]y_) == IRasCR x * CRinvT (IRasCR y) y__)%CR.
-- Proof.
--  intros x y y_ y__.
--  apply (@mult_cancel_lft CRasCField _ _ (IRasCR y)).
--   apply (map_pres_ap_zero _ _ (iso_map_rht _ _ CRIR_iso) y y_).
--  rewrite <- IR_mult_as_CR.
--  transitivity (IRasCR x).
--  apply IRasCR_wd; rational.
--  simpl.
--  rewrite (CRmult_comm (IRasCR x)), <- CRmult_assoc, CRmult_inv_r.
--  rewrite CRmult_1_l. reflexivity.
-- Qed.

-- Lemma IR_div_as_CR_1 :forall x y y_,
--  (IRasCR (x[/]y[//]y_)== IRasCR x * CRinvT (IRasCR y) (map_pres_ap_zero _ _ (iso_map_rht _ _ CRIR_iso) y y_))%CR.
-- Proof.
--  intros; apply IR_div_as_CR.
-- Qed.

-- Lemma IR_div_as_CR_2 :forall x y y_,
--  (IRasCR (x[/]y[//](CR_ap_zero_as_IR _ y_))== IRasCR x * CRinvT (IRasCR y) y_)%CR.
-- Proof.
--  intros; apply IR_div_as_CR.
-- Qed.

-- Lemma IR_recip_as_CR :forall y y_ y__,
--  (IRasCR ([1][/]y[//]y_)==(CRinvT (IRasCR y) y__))%CR.
-- Proof.
--  intros y y_ y__.
--  assert (X:=(IR_div_as_CR [1] y y_ y__)).
--  rewrite -> X.
--  change ((IRasCR [1] * CRinvT (IRasCR y) y__) == (CRinvT (IRasCR y) y__))%CR.
--  rewrite -> IR_One_as_CR.
--  change ((1 * CRinvT (IRasCR y) y__ == CRinvT (IRasCR y) y__)%CR).
--  ring.
-- Qed.

-- Lemma IR_recip_as_CR_1 :forall y y_,
--  (IRasCR ([1][/]y[//]y_)==(CRinvT (IRasCR y) (map_pres_ap_zero _ _ (iso_map_rht _ _ CRIR_iso) y y_)))%CR.
-- Proof.
--  intros; apply IR_recip_as_CR.
-- Qed.

-- Lemma IR_recip_as_CR_2 :forall y y_,
--  (IRasCR ([1][/]y[//](CR_ap_zero_as_IR _ y_))==(CRinvT (IRasCR y) y_))%CR.
-- Proof.
--  intros; apply IR_recip_as_CR.
-- Qed.

-- Lemma IR_nring_as_CR : forall (n:nat),
--  (IRasCR (nring n) == @nring CRasCRing n)%CR.
-- Proof.
--  induction n.
--   apply IR_Zero_as_CR.
--  simpl in *.
--  set (a:= (nring (R:=CRasCRing) n)) in *.
--  clearbody a.
--  rewrite -> IR_plus_as_CR.
--  rewrite -> IHn.
--  rewrite -> IR_One_as_CR.
--  reflexivity.
-- Qed.

-- #[global]
-- Hint Rewrite IR_nring_as_CR : IRtoCR.

-- Lemma IR_pring_as_CR : forall p,
--  (IRasCR (pring _ p) == @pring CRasCRing p)%CR.
-- Proof.
--  unfold pring.
--  intro p. simpl.
--  cut (IRasCR [1] == 1)%CR;[|apply IR_One_as_CR].
--  generalize ([1]:IR).
--  generalize (1%CR).
--  induction p;intros a b Hab.
--  - simpl.
--    assert (IRasCR (([0][+][1][+][1])[*]b) == (0+1+1)*a)%CR as H.
--    { simpl.
--     rewrite -> IR_mult_as_CR.
--     repeat rewrite -> IR_plus_as_CR.
--     repeat rewrite -> IR_One_as_CR.
--     rewrite -> IR_Zero_as_CR.
--     rewrite -> Hab.
--     reflexivity. }
--    pose proof (IHp _ _ H) as X.
--    simpl in X.
--    set (c:=pring_aux CRasCRing p ((0 + 1 + 1) * a)%CR) in *.
--    clearbody c.
--    rewrite <- X.
--    rewrite -> IR_plus_as_CR.
--    rewrite -> Hab.
--    reflexivity.
--  - simpl.
--   assert (IRasCR (([0][+][1][+][1])[*]b)== (0+1+1)*a)%CR.
--    simpl.
--    rewrite -> IR_mult_as_CR.
--    repeat rewrite -> IR_plus_as_CR.
--    repeat rewrite -> IR_One_as_CR.
--    simpl.
--    rewrite -> IR_Zero_as_CR.
--    simpl.
--    rewrite -> Hab.
--    reflexivity.
--   apply (IHp _ _ H).
--  - simpl.
--  assumption.
-- Qed.

-- Lemma IR_zring_as_CR : forall z,
--  (IRasCR (zring z) == @zring CRasCRing z)%CR.
-- Proof.
--  intros [|p|p].
--    apply IR_Zero_as_CR.
--   apply IR_pring_as_CR.
--  change ((IRasCR [--](pring IR p) == - ((pring CRasCRing p):CR))%CR).
--  rewrite -> IR_opp_as_CR.
--  apply CRopp_wd.
--  apply IR_pring_as_CR.
-- Qed.

-- #[global]
-- Hint Rewrite IR_zring_as_CR : IRtoCR.

-- Lemma IR_inj_Q_as_CR : forall (a:Q), (IRasCR (inj_Q IR a)==('a))%CR.
-- Proof.
--  intros [n d].
--  unfold inj_Q.
--  rewrite -> IR_div_as_CR_1.
--  generalize (map_pres_ap_zero IR CRasCReals (iso_map_rht CRasCReals IR CRIR_iso) (nring (R:=IR) (nat_of_P d))
--    (den_is_nonzero IR (n # d)%Q)).
--  intros d_.
--  setoid_replace (n#d)%Q with ((n # 1) * / (d # 1))%Q
--    by (unfold Qeq; simpl; rewrite Z.mul_1_r; reflexivity).
--  rewrite <- CRmult_Qmult.
--  assert (d__:('d >< 0)%CR).
--  { apply Qap_CRap. discriminate. }
--  rewrite <- (CRinv_Qinv d d__).
--  unfold cf_div.
--  assert (X:(forall (n:positive), IRasCR (nring (R:=IR) (nat_of_P n)) == ' Zpos n)%CR).
--  { intros x.
--   clear -x.
--   rewrite <- convert_is_POS.
--   induction (nat_of_P x); clear x.
--    apply IR_Zero_as_CR.
--   simpl.
--   rewrite -> IR_plus_as_CR.
--   rewrite -> IHn.
--   rewrite -> IR_One_as_CR.
--   simpl.
--   rewrite -> CRplus_Qplus.
--   rewrite -> CReq_Qeq.
--   unfold Qeq.
--   simpl.
--   rewrite Pmult_1_r.
--   rewrite <- POS_anti_convert.
--   ring_simplify.
--   symmetry.
--   rewrite Zplus_comm.
--   apply (inj_plus 1 n). }
--  apply (mult_wd CRasCRing);[|apply: f_rcpcl_wd;apply (X d)].
--  destruct n as [|p|p];[apply IR_Zero_as_CR| |];simpl.
--   transitivity (IRasCR (nring (nat_of_P p))).
--    apply IRasCR_wd.
--    apply pring_convert.
--   apply (X p).
--  transitivity (IRasCR [--](nring (nat_of_P p))).
--   apply IRasCR_wd.
--   apply csf_wd_unfolded.
--   apply pring_convert.
--  rewrite -> IR_opp_as_CR.
--  rewrite -> X.
--  rewrite -> CRopp_Qopp.
--  reflexivity.
-- Qed.

-- #[global]
-- Hint Rewrite IR_inj_Q_as_CR : IRtoCR.

-- Lemma IR_Cauchy_prop_as_CR : forall (x:CauchySeq IR),
--     (@Cauchy_prop CRasCOrdField (fun n => (IRasCR (x n)))).
-- Proof.
--  intros x.
--  assert (X:=map_pres_Lim _ _ (iso_map_rht CRasCReals IR CRIR_iso) _ _ (Cauchy_complete x)).
--  intros e He.
--  destruct (X _ (pos_div_two _ _ He)) as [n Hn].
--  exists n.
--  intros m Hm.
--  assert (A:=Hn m Hm).
--  assert (B:=Hn n (le_n n)).
--  set (a:=(IRasCR (x m))) in  *.
--  set (b:=IRasCR (Lim (IR:=IR) x)) in *.
--  set (c:=IRasCR (x n)) in *.
--  setoid_replace (@cg_minus CRasCGroup a c) with (a-b+(b-c))%CR
--    by (unfold cg_minus; simpl; ring).
--  apply (AbsSmall_eps_div_two CRasCOrdField e (a-b)%CR (b-c)%CR).
--   assumption.
--  apply (AbsSmall_minus CRasCOrdField (e [/]TwoNZ) c b).
--  assumption.
-- Qed.

-- Lemma IR_Lim_as_CR : forall (x:CauchySeq IR),
-- (IRasCR (Lim x)==Lim (Build_CauchySeq _ _ (IR_Cauchy_prop_as_CR x)))%CR.
-- Proof.
--  intros x.
--  apply (SeqLimit_unique CRasCReals).
--  apply (map_pres_Lim _ _ (iso_map_rht CRasCReals IR CRIR_iso) _ _ (Cauchy_complete x)).
-- Qed.

-- Lemma IR_AbsSmall_as_CR : forall (x y:IR),
-- AbsSmall x y <-> AbsSmall (R:=CRasCOrdField) (IRasCR x) (IRasCR y).
-- Proof.
--  unfold AbsSmall.
--  intros x y.
--  simpl.
--  do 2 rewrite -> IR_leEq_as_CR.
--  rewrite -> IR_opp_as_CR.
--  reflexivity.
-- Qed.
