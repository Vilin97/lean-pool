/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.Core.CoRNmetric2Metric
-- import HopfieldNet.CReals.modelstructuresPosinf


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

-- Require Import CoRN.model.totalorder.QposMinMax.
-- Require Export CoRN.metric2.Metric.
-- Require Export CoRN.model.structures.QposInf.
-- Require Import CoRN.stdlib_omissions.List.

-- Set Implicit Arguments.

-- (** This extended notition of ball operates over QposInf, allowing
-- one to say, ball Infinity a b, holds for all a and b.
-- *)

-- Definition ball_ex (X: MetricSpace) (e: QposInf): X -> X -> Prop :=
--  match e with
--   | Qpos2QposInf e' => ball (proj1_sig e')
--   | QposInfinity => fun a b => True
--  end.
-- (* begin hide *)
-- Arguments ball_ex [X].
-- (* end hide *)
-- Lemma ball_ex_weak_le : forall (X:MetricSpace)
   --(e d:QposInf) (a b:X), QposInf_le e d ->  ball_ex e a b -> ball_ex d a b.
-- Proof.
--  intros X e d a b Hed Hab.
--  destruct d as [d|]; destruct e as [e|].
--     eapply (ball_weak_le X).
--      apply Hed.
--     assumption.
--    elim Hed.
--   constructor.
--  assumption.
-- Qed.

-- Lemma ball_ex_dec : forall (X:MetricSpace), (forall e (a b:X), {ball e a b}+{~ball e a b}) -> forall e (a b:X), {ball_ex e a b}+{~ball_ex e a b}.
-- Proof.
--  intros X ball_dec e a b.
--  destruct e as [e|].
--   apply (ball_dec (proj1_sig e) a b).
--  simpl.
--  auto.
-- Defined.

-- Section UniformlyContinuousFunction.

-- (**
-- ** Uniform Continuity
-- *)

-- Variable X Y : MetricSpace.

-- (** This is the traditional definitition of uniform continuity with
-- an explicitly given modulus of continuity
-- *)
-- Definition is_UniformlyContinuousFunction
--  (f: X -> Y) (mu: Qpos -> QposInf) :=
--  forall e a b, ball_ex (mu e) a b -> ball (proj1_sig e) (f a) (f b).

-- (** Every uniformly continuous function is automatically well defined *)
-- Lemma is_UniformlyContinuousFunction_wd : forall (f1 f2:X -> Y) (mu1 mu2: Qpos -> QposInf),
--  (forall x, msp_eq (f1 x) (f2 x)) ->
--  (forall x, QposInf_le (mu2 x) (mu1 x)) ->
--  (is_UniformlyContinuousFunction f1 mu1) ->
--  (is_UniformlyContinuousFunction f2 mu2).
-- Proof.
--  intros f1 f2 mu1 mu2 Hf Hmu H e a b Hab.
--  assert (QposEq e e) by reflexivity.
--  apply (ball_wd Y H0 _ _ (Hf a) _ _ (Hf b)).
--  apply H.
--  eapply ball_ex_weak_le.
--   apply Hmu.
--  assumption.
-- Qed.

-- (** A uniformly continuous function consists of a function, a modulus
-- of continuity, and a proof that the function is uniformly continuous
-- with that modulus *)
-- Record UniformlyContinuousFunction : Type :=
-- {ucFun :> X -> Y
-- ;mu : Qpos -> QposInf
-- ;uc_prf : is_UniformlyContinuousFunction ucFun mu
-- }.

-- (** Given a uniformly continuous function with a modulus mu, it is
-- also uniformly continuous with any smaller modulus *)
-- Lemma uc_prf_smaller : forall (f:UniformlyContinuousFunction) (mu2 : Qpos -> QposInf),
--  (forall e, QposInf_le (mu2 e) (mu f e)) ->
--  is_UniformlyContinuousFunction (ucFun f) mu2.
-- Proof.
--  intros f my2 H.
--  eapply is_UniformlyContinuousFunction_wd.
--    intros; reflexivity.
--   apply H.
--  apply uc_prf.
-- Qed.

-- (** *** The metric space of uniformly continuous functions
-- The space of uniformly continuous functions from a metric space *)
-- Definition ucEq (f g : UniformlyContinuousFunction) :=
--   forall x:X, msp_eq (f x) (g x).

-- Definition ucBall e (f g : UniformlyContinuousFunction)
--   := 0 <= e /\ forall a:X, ball e (f a) (g a).

-- Lemma uc_is_MetricSpace : is_MetricSpace ucBall.
-- Proof.
--  constructor.
--  - firstorder using ball_refl.
--  - firstorder using ball_sym.
--  - intros e1 e2 f g h H1 H2.
--    destruct H1, H2. split. apply (Qle_trans _ (e1+0)).
--    rewrite Qplus_0_r. exact H.
--    apply Qplus_le_r, H1. intro a.
--    apply ball_triangle with (g a); auto.
--  - intros e f g H. split.
--    + apply Qnot_lt_le. intro abs.
--      specialize (H (-e *(1#2))). destruct H.
--      rewrite <- (Qmult_0_l (1#2)). apply Qmult_lt_r.
--      reflexivity. apply (Qplus_lt_r _ _ e).
--      ring_simplify. exact abs.
--      ring_simplify in H. apply (Qlt_not_le _ _ abs).
--      rewrite <- (Qmult_le_l _ _ (1#2)).
--      rewrite Qmult_0_r. exact H. reflexivity.
--    + intro a. apply ball_closed. firstorder.
--  - intros e a b H. apply H.
--  - intros. split.
--    apply Qnot_lt_le.
--    intro abs.
--    contradict H; intro H.
--    destruct H.
--    apply (Qle_not_lt _ _ H abs).
--    intros. apply (msp_stable (msp Y)).
--    intro abs.
--    contradict H; intro H.
--    apply abs, H.
-- Qed.

-- Lemma ucBall_e_wd : forall (e1 e2:Q) x y,
--     e1 == e2 -> (ucBall e1 x y <-> ucBall e2 x y).
-- Proof.
--  intros.
--  unfold ucBall in *.
--  split.
--  - intros H0. destruct H0. split. rewrite <- H. exact H0.
--    intro a. apply (ball_e_wd _ _ _ H), H1.
--  - intros. destruct H0. split.
--    rewrite H. exact H0. intro a.
--    apply (ball_e_wd _ _ _ H), H1.
-- Qed.

-- (** mu_ex generalizes mu analogous to how ball_ex generalizes ball: *)

-- Definition mu_ex (f: UniformlyContinuousFunction) (e: QposInf): QposInf :=
--   match e with
--   | Qpos2QposInf e' => mu f e'
--   | QposInfinity => QposInfinity
--   end.

-- Lemma uc_ex_prf (u: UniformlyContinuousFunction) (e: QposInf) (a b: X):
--   ball_ex (mu_ex u e) a b -> ball_ex e (ucFun u a) (ucFun u b).
-- Proof with auto.
--  intros.
--  destruct e...
--  simpl in *.
--  apply uc_prf.
--  assumption.
-- Qed.

-- End UniformlyContinuousFunction.

-- (* begin hide *)
-- Arguments is_UniformlyContinuousFunction [X Y].

-- (*
-- Add Setoid UniformlyContinuousFunction ucEq uc_setoid as uc_Setoid.
-- *)
-- (* end hide *)

-- Definition UniformlyContinuousSpace (X Y:MetricSpace) : MetricSpace :=
--   Build_MetricSpace (@ucBall_e_wd X Y) (@uc_is_MetricSpace X Y).

-- Lemma ucEq_equiv : forall X Y (x y : UniformlyContinuousSpace X Y),
--     ucEq x y <-> msp_eq x y.
-- Proof.
--   unfold msp_eq, ucEq. split.
--   - intros. split. apply Qle_refl.
--     intros. apply H.
--   - intros. destruct H.
--     apply H0.
-- Qed.

-- Notation "x --> y" := (UniformlyContinuousSpace x y) (at level 55, right associativity) : uc_scope.

-- Local Open Scope uc_scope.
-- (* begin hide *)
-- Add Parametric Morphism (X Y:MetricSpace) (f : X --> Y) : (ucFun f)
--     with signature (@msp_eq X) ==> (@msp_eq Y) as uc_wd.
-- Proof.
--  intros x0 x1 Hx.
--  apply ball_eq.
--  intros e epos.
--  apply (uc_prf f (exist _ _ epos)).
--  destruct (mu f (exist _ _ epos));[|constructor].
--  simpl.
--  assert (QposEq q q) by reflexivity.
--  apply (ball_wd X H _ _ Hx x1 x1 (reflexivity _)).
--  apply ball_refl. apply Qpos_nonneg.
-- Qed.

-- #[global]
-- Instance uc_wd_more_Proper (X Y : MetricSpace):
--   Proper (@ucEq _ _ ==> @msp_eq X ==> @msp_eq Y) (@ucFun X Y).
-- Proof. intros ?? E ?? F. now rewrite F. Qed.

-- Definition ucFun2 (X Y Z:MetricSpace) (f: X --> Y --> Z) (x:X) (y:Y) := f x y.

-- Add Parametric Morphism (X Y Z:MetricSpace) f : (@ucFun2 X Y Z f)
--     with signature (@msp_eq X) ==> (@msp_eq Y) ==> (@msp_eq Z) as ucFun2_wd.
-- Proof.
--  intros x y Hxy x0 y0 Hxy0.
--  unfold ucFun2.
--  rewrite -> Hxy0.
--  generalize y0.
--  apply ucEq_equiv.
--  rewrite -> Hxy.
--  reflexivity.
-- Qed.
-- (* end hide *)
-- (**
-- *** The category of metric spaces.
-- Metric spaces with uniformly continuous functions form a category.

-- The identity function is uniformly continuous.
-- *)
-- Lemma uc_id_prf (X:MetricSpace) : is_UniformlyContinuousFunction  (fun (x:X) => x) Qpos2QposInf.
-- Proof.
--  intros e a b Hab.
--  assumption.
-- Qed.

-- Definition uc_id (X:MetricSpace) : UniformlyContinuousFunction X X :=
-- Build_UniformlyContinuousFunction (uc_id_prf X).

-- (** The composition of two uniformly continuous functions is uniformly
-- continuous *)
-- Lemma uc_compose_prf (X Y Z:MetricSpace) (g: Y --> Z) (f:X --> Y) :
-- is_UniformlyContinuousFunction (fun x => g (f x)) (fun e => QposInf_bind (mu f) (mu g e)).
-- Proof.
--  revert g f.
--  intros [g mu_g Hg] [f mu_f Hf] e a b Hab.
--  unfold is_UniformlyContinuousFunction in *.
--  simpl in *.
--  apply Hg.
--  clear Hg.
--  destruct (mu_g e) as [mge|]; firstorder.
-- Qed.

-- Definition uc_compose (X Y Z:MetricSpace) (g: Y --> Z) (f:X --> Y) : X --> Z :=
-- Build_UniformlyContinuousFunction (uc_compose_prf g f).

-- (* begin hide *)
-- Add Parametric Morphism X Y Z : (@uc_compose X Y Z)
--     with signature (@msp_eq _) ==> (@msp_eq _) ==> (@msp_eq _) as uc_compose_wd.
-- Proof.
--  intros x1 x2 Hx y1 y2 Hy.
--  apply ucEq_equiv. intros x.
--  simpl.
--  apply ucEq_equiv in Hx.
--  rewrite -> (Hx (y1 x)).
--  apply uc_wd.
--  apply ucEq_equiv in Hy.
--  rewrite -> (Hy x).
--  reflexivity.
-- Qed.
-- (* end hide *)

-- Notation "f ∘ g" := (uc_compose f g) (at level 40, left associativity) : uc_scope.

-- Lemma is_uc_uc_compose0 : forall X Y Z (f:Y-->Z),
--  is_UniformlyContinuousFunction (@uc_compose X Y Z f) (mu f).
-- Proof.
--   intros X Y Z f e x y Hxy. split.
--   apply Qpos_nonneg. intro z.
--  simpl.
--  simpl in Hxy.
--  apply uc_prf.
--  destruct (mu f e); auto.
--  apply Hxy.
-- Qed.

-- Definition uc_compose_uc0 X Y Z (f:Y-->Z) : (X-->Y) --> X --> Z :=
--  Build_UniformlyContinuousFunction (is_uc_uc_compose0 f).

-- Lemma is_uc_uc_compose : forall X Y Z,
--  is_UniformlyContinuousFunction (@uc_compose_uc0 X Y Z) Qpos2QposInf.
-- Proof.
--   intros X Y Z e x y Hxy. split.
--   apply Qpos_nonneg.
--   intro z. split. apply Qpos_nonneg.
--   intro z0.
--   simpl.
--   apply Hxy.
-- Qed.

-- Definition uc_compose_uc X Y Z : (Y-->Z)-->(X-->Y)-->X-->Z :=
--  Build_UniformlyContinuousFunction (@is_uc_uc_compose X Y Z).
