/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.Core.metric2UniformContinuity
import LeanPool.HopfieldNet.CReals.Core.CoRNmetric2Metric
import LeanPool.HopfieldNet.CReals.Core.CoRNmodelmetric2Qmetric
import LeanPool.HopfieldNet.CReals.modelstructuresPosinf
--import HopfieldNet.CReals.cornmetric2Complete
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

-- Require Import CoRN.metric2.Metric.
-- Require Import CoRN.metric2.UniformContinuity.
-- Require Import CoRN.model.metric2.Qmetric.
-- Require Import MathClasses.interfaces.canonical_names.

-- Require Export CoRN.metric2.Complete.
-- Require Export CoRN.metric2.Prelength.


-- Set Implicit Arguments.

-- Local Open Scope uc_scope.

-- (**
-- * Complete Metric Space: Computable Reals (CR)
-- *)

-- Require Export CoRN.metric2.UniformContinuity.
-- Require Export CoRN.model.structures.QposInf.
-- Require Export CoRN.metric2.Classification.
-- Require Import CoRN.model.totalorder.QposMinMax.
-- Require Import CoRN.model.totalorder.QMinMax.


-- Set Implicit Arguments.

-- Local Open Scope Q_scope.
-- Local Open Scope uc_scope.
-- (**
-- ** Complete metric space
-- *)
-- (**
-- *** Regular functions
-- A regular function is one way of representing elements in a complete
-- metric space.  A regular function that take a given error e, and returns
-- an approximation within e of the value it is representing.  These
-- approximations must be coherent and the definition belows state this
-- property.
-- *)

-- Definition is_RegularFunction {X:Type} (ball : Q->X->X->Prop) (x:QposInf -> X) : Prop :=
--  forall (e1 e2:Qpos), ball (proj1_sig e1 + proj1_sig e2) (x e1) (x e2).

def is_RegularFunction {X : Type} (ball : ℚ → X → X → Prop)
  (x : QposInf → X) : Prop :=
  ∀ (e1 e2 : Qpos), ball (e1.val + e2.val)
    (x (QposInf.Qpos2QposInf e1)) (x (QposInf.Qpos2QposInf e2))

-- (** A regular function consists of an approximation function, and
-- a proof that the approximations are coherent. *)
-- Record RegularFunction {X:Type} (ball : Q->X->X->Prop) : Type :=
-- {approximate : QposInf -> X
-- ;regFun_prf : is_RegularFunction ball approximate
-- }.

structure RegularFunction {X : Type} (ball : ℚ → X → X → Prop) where
  approximate : QposInf → X
  regFun_prf : is_RegularFunction ball approximate

-- Lemma is_RegularFunction_wd
--   : forall (X : MetricSpace) (x y:QposInf -> X),
--     (forall q : Qpos, msp_eq (x q) (y q))
--     -> is_RegularFunction (@ball X) x
--     -> is_RegularFunction (@ball X) y.
-- Proof.
--   intros. intros e1 e2.
--   rewrite <- H, <- H.
--   apply H0.
-- Qed.

-- Definition regFunEq {X:Type} (ball : Q->X->X->Prop)
--            (f g : RegularFunction ball) : Prop
--   := forall (e1 e2 : Qpos),
--     ball (proj1_sig e1 + proj1_sig e2) (approximate f e1) (approximate g e2).

def regFunBall {X : Type} (ball : ℚ → X → X → Prop)
  (e : ℚ) (f g : RegularFunction ball) : Prop :=
  ∀ (d1 d2 : Qpos), ball (d1.val + e + d2.val)
  (f.approximate (QposInf.Qpos2QposInf d1)) (g.approximate (QposInf.Qpos2QposInf d2))


-- Definition regFunBall {X:Type} (ball : Q->X->X->Prop)
--            (e:Q) (f g : RegularFunction ball) : Prop :=
--   forall (d1 d2:Qpos), ball (proj1_sig d1 + e + proj1_sig d2)
--                        (approximate f d1) (approximate g d2).

-- Section RegularFunction.

-- Variable X:MetricSpace.


-- (** The value of the approximation function at infinity is irrelevant,
--  so we make a smart constructor that just takes a Qpos->X. *)

-- Definition is_RegularFunction_noInf (x: Qpos -> X): Prop :=
--   forall e1 e2 : Qpos, ball (proj1_sig e1 + proj1_sig e2) (x e1) (x e2).

-- Section mkRegularFunction.

--   Variables (dummy: X).

--   Let lift (f: Qpos -> X) (e: QposInf): X :=
--     match e with
--     | QposInfinity => dummy (* if the recipient doesn't care, fine with me! *)
--     | Qpos2QposInf e' => f e'
--     end.

--   Let transport (f: Qpos -> X): is_RegularFunction_noInf f
--                                -> is_RegularFunction (@ball X) (lift f).
--   Proof. firstorder. Qed.

--   Definition mkRegularFunction (f: Qpos -> X) (H: is_RegularFunction_noInf f)
--     : RegularFunction (@ball X)
--     := Build_RegularFunction (transport H).

-- End mkRegularFunction.

-- (** Regular functions form a metric space *)
-- Lemma regFunEq_e : forall (f g : RegularFunction (@ball X)),
--     (forall e : Qpos, ball (m:=X) (proj1_sig e + proj1_sig e) (approximate f e) (approximate g e)) -> (regFunEq f g).
-- Proof.
--  unfold regFunEq.
--  intros f g H e1 e2.
--  apply ball_closed.
--  intros d dpos.
--  setoid_replace (proj1_sig e1 + proj1_sig e2 + d)
--    with ((proj1_sig e1 + ((1#4) *d)
--           + (((1#4)*d) + ((1#4)*d))
--           +(((1#4)*d)+proj1_sig e2)))
--    by (simpl; ring).
--   eapply ball_triangle.
--    eapply ball_triangle.
--     apply (regFun_prf _ e1 ((1#4)*exist _ _ dpos)%Qpos).
--    apply (H ((1 # 4) * exist (Qlt 0) d dpos)%Qpos).
--   apply (regFun_prf _ ((1 # 4) * exist (Qlt 0) d dpos)%Qpos e2).
-- Qed.

-- Lemma regFunEq_e_small : forall (f g : RegularFunction (@ball X)) (E:Qpos),
--     (forall (e:Qpos), proj1_sig e <= proj1_sig E -> ball (m:=X) (proj1_sig e+ proj1_sig e) (approximate f e) (approximate g e)) -> (regFunEq f g).
-- Proof.
--  intros f g E H.
--  apply regFunEq_e.
--  intros e.
--  apply ball_closed.
--  intros d dpos.
--  assert (0 < (1#4)) as quarterPos. reflexivity.
--  set (e':=Qpos_min (exist _ _ quarterPos*exist _ _ dpos) E).
--  apply ball_weak_le with (proj1_sig ((e+e')+(e'+e')+(e'+e))%Qpos).
--  apply (Qle_trans _
--                   (proj1_sig ((e+exist _ _ quarterPos*exist _ _ dpos)
--                    +(exist _ _ quarterPos*exist _ _ dpos+exist _ _ quarterPos*exist _ _ dpos)
--                    +(exist _ _ quarterPos*exist _ _ dpos+e))%Qpos)).
--  - simpl. ring_simplify. apply Qplus_le_r.
--    apply (Qle_trans _ ((4#1) * ((1 # 4) * d))).
--    2: simpl; ring_simplify; apply Qle_refl.
--    apply Qmult_le_l. reflexivity. apply Qpos_min_lb_l.
--  - simpl. ring_simplify. apply Qle_refl.
--  - apply ball_triangle with (approximate g e').
--   apply ball_triangle with (approximate f e').
--    apply regFun_prf.
--   apply H.
--   apply Qpos_min_lb_r.
--  apply regFun_prf.
-- Qed.

-- Lemma regFunBall_wd : forall (e1 e2:Q) (x y : RegularFunction (@ball X)),
--     (e1 == e2) -> (regFunBall e1 x y <-> regFunBall e2 x y).
-- Proof.
--   unfold regFunBall. split.
--   - intros. rewrite <- H. apply H0.
--   - intros. rewrite H. apply H0.
-- Qed.

-- If e1 = e2, then regFunBall e1 x y ↔ regFunBall e2 x y.
theorem regFunBall_wd {X : Type} {ball : ℚ → X → X → Prop}
  {e1 e2 : ℚ} {x y : RegularFunction ball} (h : e1 = e2) :
  (regFunBall ball e1 x y ↔ regFunBall ball e2 x y) :=
by
  unfold regFunBall
  constructor
  · intro H d1 d2
    rw [←h]
    exact H d1 d2
  · intro H d1 d2
    rw [h]
    exact H d1 d2

-- The metric space structure for regular functions.
def regFun_is_MetricSpace {X : MetricSpace'} :
  IsMetricSpace (regFunBall X.ball) := sorry

def Complete (X : MetricSpace') : MetricSpace' :=
  { carrier := RegularFunction X.ball
    ball := regFunBall X.ball
    ball_e_wd := fun e d x y h => @regFunBall_wd X.carrier X.ball e d x y h
    is_metric := regFun_is_MetricSpace
  }

def CR : MetricSpace' := Complete Q_as_MetricSpace

def CR_carrier : Type := (Complete Q_as_MetricSpace).carrier

-- Delimit Scope CR_scope with CR.
-- Bind Scope CR_scope with CR.

-- Delimit Scope CR_scope with CR.
-- Bind Scope CR_scope with CR.
-- #[global]

def Cunit (q : ℚ) : CR_carrier :=
  {
    approximate := fun _ => q,
    regFun_prf := fun _ _ => by {
      simp only
      refine ball_weak Q_as_MetricSpace ?_ ?_
      · (expose_names; exact Qpos_nonneg x_1)
      · refine ball_refl Q_as_MetricSpace ?_
        (expose_names; exact Qpos_nonneg x)
    }
  }

instance inject_Q_CR : Coe ℚ CR_carrier := ⟨Cunit⟩

-- Instance inject_Q_CR: Cast Q (msp_car CR)
--   := ucFun (@Cunit Q_as_MetricSpace).

-- (*
-- Since (@Cunit Q_as_MetricSpace) is a bundled function with a modulus
-- and uses a bundled representation of a metricspace as its domain, we
-- can't define:
--   Coercion inject_Q: Q_as_MetricSpace --> CR := (@Cunit Q_as_MetricSpace).
-- However, is is possible to define:
--   Coercion inject_Q' (x : Q) : CR := (@Cunit Q_as_MetricSpace x).
-- We omit this for backward, and forward, compatibity
-- (we can't define it for Q → AR either).
-- *)

-- (* begin hide *)
-- #[global]
-- Instance inject_Q_CR_wd: Proper (Qeq ==> (=)) inject_Q_CR.
-- Proof.
--   intros x y xyeq. apply (uc_wd (@Cunit Q_as_MetricSpace)).
--   unfold msp_eq. simpl.
--   rewrite xyeq. apply Qball_Reflexive.
--   discriminate.
-- Qed.
-- (* end hide *)

-- Prove that the coercion from ℚ to CR_carrier
-- is proper with respect to equality.
theorem inject_Q_CR_wd {x y : ℚ} (h : x = y) :
   (x : CR_carrier) = (y : CR_carrier) := by rw [h]

-- Local Open Scope uc_scope.

-- (**
-- * Complete Metric Space: Computable Reals (CR)
-- *)

-- Definition CR : MetricSpace
--   := Complete Q_as_MetricSpace.

-- Delimit Scope CR_scope with CR.
-- Bind Scope CR_scope with CR.

-- #[global]
-- Instance inject_Q_CR: Cast Q (msp_car CR)
--   := ucFun (@Cunit Q_as_MetricSpace).

-- (*
-- Since (@Cunit Q_as_MetricSpace) is a bundled function with a modulus
-- and uses a bundled representation of a metricspace as its domain, we
-- can't define:
--   Coercion inject_Q: Q_as_MetricSpace --> CR := (@Cunit Q_as_MetricSpace).
-- However, is is possible to define:
--   Coercion inject_Q' (x : Q) : CR := (@Cunit Q_as_MetricSpace x).
-- We omit this for backward, and forward, compatibity
-- (we can't define it for Q → AR either).
-- *)

-- (* begin hide *)
-- #[global]
-- Instance inject_Q_CR_wd: Proper (Qeq ==> (=)) inject_Q_CR.
-- Proof.
--   intros x y xyeq. apply (uc_wd (@Cunit Q_as_MetricSpace)).
--   unfold msp_eq. simpl.
--   rewrite xyeq. apply Qball_Reflexive.
--   discriminate.
-- Qed.
-- (* end hide *)

-- Notation "' x" := (inject_Q_CR x) : CR_scope.

-- Notation "x == y" := (@msp_eq CR x y) (at level 70, no associativity) : CR_scope.
