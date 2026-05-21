/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import  LeanPool.HopfieldNet.CReals.Core.CoRNmodeltotalorderQMinMax
import LeanPool.HopfieldNet.CReals.Core.CornQposMinMax
import LeanPool.HopfieldNet.CReals.modelstructuresPosinf
import LeanPool.HopfieldNet.CReals.Core.metric2UniformContinuity
-- (*
-- Copyright © 2006-2008 Russell O’Connor
-- Copyright © 2020 Vincent Semeria

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


def isRegularFunction {X : Type} (ball : ℚ → X → X → Prop)
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
  regFun_prf : isRegularFunction ball approximate

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

-- Lemma regFun_is_MetricSpace : is_MetricSpace (@regFunBall _ (@ball X)).
-- Proof.
--  unfold regFunBall.
--  split.
--  - intros e epos f d1 d2.
--    rewrite <- Qplus_assoc, (Qplus_comm e), Qplus_assoc.
--    apply ball_weak. exact epos.
--    apply regFun_prf.
--  - intros e f g H d1 d2.
--     apply ball_sym.
--     rewrite Qplus_comm, <- (Qplus_comm e), Qplus_assoc.
--     apply H.
--  - intros e1 e2 a b c Hab Hbc d1 d2.
--    apply ball_closed.
--    intros d3 dpos.
--    setoid_replace (proj1_sig d1+(e1+e2)+proj1_sig d2+d3)
--      with ((proj1_sig d1 + e1 + (1#2)*d3)+((1#2)*d3 + e2 + proj1_sig d2))
--      by (simpl; ring).
--    eapply ball_triangle.
--     apply (Hab d1 ((1#2)*exist _ _ dpos)%Qpos).
--    apply (Hbc ((1#2)*exist _ _ dpos)%Qpos).
--  - intros e a b H d1 d2.
--    apply ball_closed.
--    intros d dpos.
--    setoid_replace (proj1_sig d1+e+ proj1_sig d2+d)
--      with (proj1_sig d1 + (e+d) + proj1_sig d2)
--      by (simpl; ring).
--    apply H, dpos.
--  - intros. apply Qnot_lt_le. intro abs.
--    assert (0 < -e * (1#3)).
--    { apply (Qmult_lt_l _ _ (3#1)). reflexivity.
--      apply (Qplus_lt_l _ _ e).
--      ring_simplify. apply (Qlt_le_trans _ _ _ abs).
--      discriminate. }
--    specialize (H (exist _ _ H0) (exist _ _ H0)). simpl in H.
--    apply msp_nonneg in H. 2: apply X.
--    ring_simplify in H. apply (Qlt_not_le _ _ abs).
--    apply (Qmult_le_l _ _ (3#9)). reflexivity.
--    rewrite Qmult_0_r. exact H.
--  - intros. apply (msp_stable (msp X)).
--    intro abs.
--    contradict H; intro H.
--    apply abs.
--    apply H.
-- Qed.

-- (** We define the completion of a metric space to be the space of
-- regular functions *)
-- Definition Complete : MetricSpace :=
-- Build_MetricSpace regFunBall_wd regFun_is_MetricSpace.

def Complete (X : MetricSpace') : MetricSpace' :=
  {
    carrier := RegularFunction X.ball
    ball := regFunBall X.ball
    ball_e_wd := fun e d x y h => @regFunBall_wd X.carrier X.ball e d x y h
    is_metric := regFun_is_MetricSpace
  }


-- Lemma regFunEq_equiv : forall (x y : Complete),
--     regFunEq x y <-> msp_eq x y.
-- Proof.
--   (* Remove the middle 0. *)
--   unfold regFunEq, msp_eq. split.
--   - intros H e1 e2. rewrite Qplus_0_r. apply H.
--   - intros H e1 e2.
--     specialize (H e1 e2).
--     rewrite Qplus_0_r in H. apply H.
-- Qed.


-- (** The ball of regular functions is related to the underlying ball
-- in ways that you would expect. *)
-- Lemma regFunBall_ball : forall (x y:Complete) (e0 : Q) (e1 e2:Qpos),
--     ball e0 (approximate x e1) (approximate y e2)
--     -> ball (proj1_sig e1 + e0 + proj1_sig e2) x y.
-- Proof.
--  intros x y e0 e1 e2 H d1 d2.
--  setoid_replace (proj1_sig d1+(proj1_sig e1+e0+proj1_sig e2)+proj1_sig d2)%Q
--    with ((proj1_sig d1+proj1_sig e1)+e0+(proj1_sig e2+proj1_sig d2))
--    by (simpl; ring).
--   eapply ball_triangle.
--    eapply ball_triangle.
--     apply regFun_prf.
--    apply H.
--   apply regFun_prf.
-- Qed.

-- Lemma regFunBall_e : forall (x y:Complete) (e:Q),
--     (forall d:Qpos, ball (proj1_sig d + e + proj1_sig d)
--                     (approximate x d) (approximate y d))
--     -> ball e x y.
-- Proof.
--  intros x y e H.
--  apply ball_closed.
--  intros d dpos.
--  setoid_replace (e + d)
--    with ((1#4)*d + ((1#4)*d+ e+(1#4)*d) + (1#4)*d)
--    by (simpl; ring).
--  apply (regFunBall_ball
--           x y
--           ((1 # 4) * d + e + (1 # 4) * d)%Q
--           ((1#4)*exist _ _ dpos)%Qpos
--           ((1#4)*exist _ _ dpos)%Qpos ).
--  apply (H ((1#4)*(exist _ _ dpos))%Qpos).
-- Qed.

-- (**
-- *** Cunit
-- There is an injection from the original space to the complete space
-- given by the constant regular function. *)
-- Lemma Cunit_fun_prf (x:X) : is_RegularFunction (@ball X) (fun _ => x).
-- Proof.
--  intros d1 d2.
--  apply ball_refl.
--  apply (Qpos_nonneg (d1+d2)).
-- Qed.

-- Definition Cunit_fun (x:X) : Complete :=
-- Build_RegularFunction (Cunit_fun_prf x).

-- Lemma Cunit_prf : is_UniformlyContinuousFunction Cunit_fun Qpos2QposInf.
-- Proof.
--  intros e a b Hab d1 d2.
--  simpl in *.
--  assert (QposEq (d1+e+d2) (e+(d1+d2))).
--  { unfold QposEq; simpl; ring. }
--  unfold QposEq in H. rewrite H. clear H.
--  apply ball_weak. apply Qpos_nonneg.
--  assumption.
-- Qed.

-- Definition Cunit : X --> Complete :=
-- Build_UniformlyContinuousFunction Cunit_prf.

-- (** This injection preserves the metric *)
-- Lemma ball_Cunit : forall (e:Q) a b,
--     ball e (Cunit a) (Cunit b) <-> ball e a b.
-- Proof.
--   intros e a b. split.
--   - intros. simpl in H.
--     do 2 (apply ball_closed; intros).
--     rewrite <- (Qplus_comm d).
--     apply (H (exist _ _ H0) (exist _ _ H1)).
--   - intros H d1 d2.
--     pose proof (msp_nonneg (msp X) _ _ _ H).
--     apply Qle_lteq in H0. destruct H0.
--     apply (Cunit_prf (exist _ _ H0)). exact H.
--     rewrite <- H0, Qplus_0_r.
--     rewrite <- H0 in H.
--     simpl. rewrite H. apply ball_refl.
--     apply (Qpos_nonneg (d1+d2)).
-- Qed.

-- Lemma Cunit_eq : forall a b, msp_eq (Cunit a) (Cunit b) <-> msp_eq a b.
-- Proof.
--  intros a b.
--  do 2 rewrite <- ball_eq_iff.
--  split; intros H e epos; [rewrite <- (ball_Cunit e) | rewrite -> (ball_Cunit e)];
--  apply H; assumption.
-- Qed.

-- Lemma ball_approx_r : forall (x:Complete) (e:Qpos),
--     ball (proj1_sig e) x (Cunit (approximate x e)).
-- Proof.
--  intros x e d1 d2.
--  simpl.
--  apply ball_weak. apply Qpos_nonneg.
--  apply regFun_prf.
-- Qed.

-- Lemma ball_approx_l : forall (x:Complete) (e:Qpos),
--     ball (proj1_sig e) (Cunit (approximate x e)) x.
-- Proof.
--  (* Set Firstorder Depth 6.
--  firstorder fail with ball_sym ball_approx_r.
--  *)
--  pose ball_approx_r.
--  pose ball_sym.
--  auto.
-- Qed.

-- Lemma ball_ex_approx_r : forall (x:Complete) e, ball_ex e x (Cunit (approximate x e)).
-- Proof.
--  intros x [e|]; simpl.
--   apply ball_approx_r.
--  constructor.
-- Qed.

-- Lemma ball_ex_approx_l : forall (x:Complete) e, ball_ex e (Cunit (approximate x e)) x.
-- Proof.
--  intros x [e|]; simpl.
--   apply ball_approx_l.
--  constructor.
-- Qed.

-- Lemma regFunBall_Cunit (e: Qpos) (x: Complete) (y: X):
--   regFunBall (proj1_sig e) x (Cunit y)
--   <-> (forall d: Qpos, ball (proj1_sig d + proj1_sig e) (approximate x d) y).
-- Proof with auto.
--  unfold regFunBall.
--   split; intros.
--   apply ball_closed.
--   simpl in *...
--   intros. apply (H d (exist _ _ H0)).
--   apply ball_weak... apply Qpos_nonneg.
-- Qed.

-- Lemma regFun_prf_ex :
--  forall (r : Complete) (e1 e2 : QposInf),
--   ball_ex  (e1 + e2) (approximate r e1) (approximate r e2).
-- Proof.
--  intros r [e1|] [e2|]; try constructor.
--  apply (@regFun_prf X (@ball X)).
-- Qed.

-- End RegularFunction.

-- (* begin hide *)
-- Arguments regFunEq_e_small [X].
-- Arguments is_RegularFunction [X].

-- Arguments Cunit {X}.

-- Add Parametric Morphism X : (@Cunit_fun X)
--     with signature (@msp_eq _) ==> (@msp_eq _) as Cunit_wd.
-- Proof.
--  exact (@uc_wd _ _ Cunit).
-- Qed.
-- (* end hide *)

-- (** If two functions between complete metric spaces are equal on the images
-- of [Cunit], then they are equal everywhere *)

-- Lemma lift_eq_complete {X Y : MetricSpace} (f g : Complete X --> Y) :
--   (forall x : X, msp_eq (f (Cunit x)) (g (Cunit x)))
--   -> (forall x : Complete X, msp_eq (f x) (g x)).
-- Proof.
-- intros A x. apply ball_eq; intros e epos.
-- pose (exist (Qlt 0) (1#2) eq_refl) as half.
-- set (e2 := (half * exist _ _ epos)%Qpos).
-- set (d := QposInf_min (mu f e2) (mu g e2)).
-- setoid_replace e with (proj1_sig (e2+e2)%Qpos) by (simpl; ring).
-- apply ball_triangle with (b := f (Cunit (approximate x d))).
-- + apply (UniformContinuity.uc_prf f).
--   apply (ball_ex_weak_le _ d); [apply QposInf_min_lb_l | apply ball_ex_approx_r].
-- + apply (ball_wd _ eq_refl _ _ (A (approximate x d)) _ _ (reflexivity _)).
--   apply (UniformContinuity.uc_prf g).
--   apply (ball_ex_weak_le _ d); [apply QposInf_min_lb_r | apply ball_ex_approx_l].
-- Qed.

-- Lemma lift_eq_complete_2
--   : forall (A B C: MetricSpace)
--       (f g : Complete A --> Complete B --> C),
--     (forall a b, msp_eq (f (Cunit a) (Cunit b)) (g (Cunit a) (Cunit b)))
--     -> (forall a b, msp_eq (f a b) (g a b)).
-- Proof.
--   intros A B C f g H a.
--   apply lift_eq_complete.
--   intro b.
--   revert a.
--   assert (@is_UniformlyContinuousFunction
--             (Complete A) C
--             (fun a => f a (Cunit b)) (mu f)).
--   { intros e x y H0.
--     apply (uc_prf f e x y H0). }
--   assert (@is_UniformlyContinuousFunction
--             (Complete A) C
--             (fun a => g a (Cunit b)) (mu g)).
--   { intros e x y H1.
--     apply (uc_prf g e x y H1). }
--   apply (@lift_eq_complete
--            A C (Build_UniformlyContinuousFunction H0)
--            (Build_UniformlyContinuousFunction H1)).
--   simpl. intro a. apply H.
-- Qed.


-- Section Faster.

-- Variable X : MetricSpace.
-- Variable x : Complete X.

-- (** A regular function is equivalent to the same function that returns
-- a better approximation with a given error.  One would not generally want
-- to do this when doing computation; however it is quite a useful
-- substitution to be able to make during reasoning. *)

-- Section FasterInGeneral.

-- Variable f : Qpos -> Qpos.
-- Hypothesis Hf : forall x, proj1_sig (f x) <= proj1_sig x.


variable (f : Qpos → Qpos)
variable (Hf : ∀ x, (f x).val ≤ x.val)

-- Lemma fasterIsRegular : is_RegularFunction (@ball X) (fun e => (approximate x (QposInf_bind f e))).
-- Proof.
--  intros e1 e2.
--  simpl.
--  apply ball_weak_le with (proj1_sig (f e1 + f e2)%Qpos).
--  simpl. apply Qplus_le_compat. apply Hf. apply Hf.
--  apply regFun_prf.
-- Qed.

-- Definition faster : Complete X := Build_RegularFunction fasterIsRegular.

-- Lemma fasterIsEq : msp_eq faster x.
-- Proof.
--   apply regFunEq_equiv.
--  apply regFunEq_e.
--  intros e.
--  simpl.
--  apply ball_weak_le with (proj1_sig (f e + e)%Qpos).
--  simpl. apply Qplus_le_l. apply Hf.
--  apply regFun_prf.
-- Qed.

-- End FasterInGeneral.

-- Lemma QreduceApprox_prf : forall (e:Qpos), proj1_sig (Qpos_red e) <= proj1_sig e.
-- Proof.
--  intros e.
--  destruct e. simpl.
--  rewrite -> Qred_correct.
--  apply Qle_refl.
-- Qed.

-- Definition QreduceApprox := faster Qpos_red QreduceApprox_prf.

-- Lemma QreduceApprox_Eq : msp_eq QreduceApprox x.
-- Proof.
--   apply (fasterIsEq _ _).
-- Qed.
-- (** In particular, halving the error of the approximation is a common
-- case. *)
-- Lemma doubleSpeed_prf : forall (e:Qpos),
--     proj1_sig ((1#2) * e)%Qpos <= proj1_sig e.
-- Proof.
--  intros e.
--  autorewrite with QposElim.
--  rewrite -> Qle_minus_iff. simpl.
--  ring_simplify. apply (Qle_trans _ ((1#2) * 0)).
--  rewrite Qmult_0_r. apply Qle_refl.
--  apply Qmult_le_l. reflexivity.
--  destruct e. apply Qlt_le_weak, q.
-- Qed.

-- Definition doubleSpeed
--   := faster (Qpos_mult (exist (Qlt 0) (1#2) eq_refl)) doubleSpeed_prf.

-- Lemma doubleSpeed_Eq : msp_eq doubleSpeed x.
-- Proof.
--   apply (fasterIsEq _ _).
-- Qed.

-- End Faster.

-- Section Cjoin.

-- Variable X : MetricSpace.

-- (**
-- *** Cjoin
-- There is an injection from a twice completed space into a once completed
-- space.  This injection along with [Cunit] forms an isomorphism between
-- a twice completed space and a once completed space.  This proves that
-- a complete metric space is complete. *)
-- Definition Cjoin_raw (x:Complete (Complete X)) (e:QposInf) :=
--   (approximate (approximate x (QposInf_mult (Qpos2QposInf (1#2)) e))
--                (QposInf_mult (Qpos2QposInf (1#2)) e))%Qpos.

-- Lemma Cjoin_fun_prf (x:Complete (Complete X))
--   : is_RegularFunction (@ball X) (Cjoin_raw x).
-- Proof.
--  intros d1 d2.
--  rewrite <- ball_Cunit.
--  setoid_replace (proj1_sig d1 + proj1_sig d2)
--    with (proj1_sig ((1#2)*d1 + ((1#2)*d1+(1#2)*d2) + (1#2)*d2)%Qpos)
--    by (simpl; ring).
--  apply ball_triangle with (approximate x (Qpos_mult (exist (Qlt 0) (1#2) eq_refl) d2)).
--   apply ball_triangle with (approximate x (Qpos_mult (exist (Qlt 0) (1#2) eq_refl) d1)).
--    apply ball_approx_l.
--   apply regFun_prf.
--  apply ball_approx_r.
-- Qed.

-- Definition Cjoin_fun (x:Complete (Complete X)) : Complete X :=
-- Build_RegularFunction (Cjoin_fun_prf x).

-- Lemma Cjoin_prf : is_UniformlyContinuousFunction Cjoin_fun Qpos2QposInf.
-- Proof.
--  intros e x y Hab d1 d2.
--  do 2 rewrite <- ball_Cunit.
--  setoid_replace (proj1_sig d1 + proj1_sig e + proj1_sig d2)
--    with (proj1_sig (((1#2)*d1 + (1#2)*d1)
--                     + e + (((1#2)*d2) + (1#2)*d2)))%Qpos
--    by (simpl; ring).
--  apply ball_triangle with y.
--   apply ball_triangle with x.
--    apply ball_triangle with (Cunit (approximate x ((1#2) * d1)%Qpos)).
--     rewrite -> ball_Cunit.
--     refine (ball_approx_l _ _).
--    apply ball_approx_l.
--   assumption.
--  eapply ball_triangle.
--   apply ball_approx_r.
--  rewrite -> ball_Cunit.
--  refine (ball_approx_r _ _).
-- Qed.

-- Definition Cjoin : (Complete (Complete X)) --> (Complete X) :=
-- Build_UniformlyContinuousFunction Cjoin_prf.

-- End Cjoin.

-- Arguments Cjoin {X}.

-- Lemma Cjoin_ball : forall (X : MetricSpace) (x : Complete (Complete X)) (e : Qpos),
--     ball (proj1_sig e) (Cjoin_fun x) (approximate x e).
-- Proof.
--   intros X x e d1 d2. simpl.
--   unfold Cjoin_raw. simpl.
--   destruct x as [x xreg]; simpl.
--   specialize (xreg ((1#2)*d1)%Qpos e ((1#2)*d1)%Qpos d2).
--   simpl in xreg.
--   setoid_replace (proj1_sig d1 + proj1_sig e + proj1_sig d2)
--     with ((1 # 2) * proj1_sig d1 + ((1 # 2) * proj1_sig d1 + proj1_sig e) +
--             proj1_sig d2)
--     by ring.
--   exact xreg.
-- Qed.


-- Section Cmap.

-- Variable X Y : MetricSpace.
-- Variable f : X --> Y.



-- (**
-- *** Cmap (slow)
-- Uniformly continuous functions can be lifted to the completion of metric
-- spaces.  A faster version that works under some mild assumptions will be
-- given later.  But first the most generic version that we call
-- [Cmap_slow]. *)

-- Definition Cmap_slow_raw (x:Complete X) (e:QposInf) :=
--   f (approximate x (QposInf_mult (Qpos2QposInf (1#2)%Qpos)
--                                  (QposInf_bind (mu f) e))).

-- Lemma Cmap_slow_raw_strongInf
--   : forall (x:Complete X) (d:QposInf) (e:QposInf),
--     QposInf_le d (QposInf_mult (Qpos2QposInf (exist (Qlt 0) (1#2) eq_refl)) (QposInf_bind (mu f) e)) ->
-- ball_ex e (f (approximate x d)) (Cmap_slow_raw x e).
-- Proof.
--  intros x [d|] [e|] Hd; try constructor.
--  - apply uc_prf.
--   simpl.
--   case_eq (mu f e); simpl; trivial.
--   intros q Hq.
--   simpl in Hd.
--   rewrite Hq in Hd.
--   eapply ball_weak_le;[|apply regFun_prf].
--   simpl. simpl in Hd.
--   apply (Qplus_le_l _ _ (-(1#2)*proj1_sig q)).
--   ring_simplify. exact Hd.
--  - unfold Cmap_slow_raw.
--  simpl in *.
--  apply uc_prf.
--  destruct (mu f e) as [q|].
--   contradiction.
--  constructor.
-- Qed.

-- Lemma Cmap_slow_raw_strong : forall (x:Complete X) (d:QposInf) (e:Qpos),
--     QposInf_le d (QposInf_mult (Qpos2QposInf (exist (Qlt 0) (1#2) eq_refl)) (mu f e)) ->
-- ball (proj1_sig e) (f (approximate x d)) (Cmap_slow_raw x e).
-- Proof.
--  intros.
--  apply (Cmap_slow_raw_strongInf x d e).
--  assumption.
-- Qed.

-- Lemma Cmap_slow_fun_prf (x:Complete X)
--   : is_RegularFunction (@ball Y) (Cmap_slow_raw x).
-- Proof.
--  intros e1 e2.
--  unfold Cmap_slow_raw.
--  cut (forall (e1 e2:Qpos), (QposInf_le (mu f e2) (mu f e1)) -> ball (m:=Y) (proj1_sig e1 + proj1_sig e2)
--    (f (approximate x (QposInf_mult (Qpos2QposInf (1#2)) (QposInf_bind (mu f) e1))))
--      (f (approximate x (QposInf_mult (Qpos2QposInf (1#2)) (QposInf_bind (mu f) e2))))).
--   intros H.
--   (* move this out *)
--   assert (forall a b, {QposInf_le a b}+{QposInf_le b a}).
--    intros [a|] [b|]; simpl; try tauto.
--    apply Qle_total.
--   destruct (H0 (mu f e2) (mu f e1)).
--    auto.
--   apply ball_sym.
--   rewrite Qplus_comm.
--    auto.
--  clear e1 e2.
--  intros e1 e2 H.
--  apply ball_weak. apply Qpos_nonneg.
--  apply ball_sym.
--  simpl.
--  apply Cmap_slow_raw_strong.
--  simpl.
--  destruct (mu f e1).
--   simpl.
--   destruct (mu f e2).
--    simpl.
--    apply Qmult_le_l. reflexivity. exact H.
--   elim H.
--  constructor.
-- Qed.

-- Definition Cmap_slow_fun (x:Complete X) : Complete Y :=
-- Build_RegularFunction (Cmap_slow_fun_prf x).

-- Definition Cmap_slow_prf
--   : is_UniformlyContinuousFunction
--       Cmap_slow_fun (fun e => (QposInf_mult (Qpos2QposInf (1#2)) (mu f e))%Qpos).
-- Proof.
--  intros e0 x y Hxy.
--  intros e1 e2.
--  simpl.
--  unfold Cmap_slow_raw.
--  set (d1:=(QposInf_bind (fun y' : Qpos => ((1#2) * y')%Qpos) (mu f e1))).
--  set (d2:=(QposInf_bind (fun y' : Qpos => ((1#2) * y')%Qpos) (mu f e2))).
--  set (d0:=(QposInf_bind (fun y' : Qpos => ((1#4) * y')%Qpos) (mu f e0))).
--  apply ball_triangle with (f (approximate y (QposInf_min d0 d2 ))).
--   apply ball_triangle with (f (approximate x (QposInf_min d0 d1))).
--  - apply uc_prf.
--    eapply ball_ex_weak_le;[|apply regFun_prf_ex].
--    unfold d1.
--    simpl.
--    destruct (mu f e1); try constructor.
--    destruct d0. simpl. rewrite Q_Qpos_min. simpl.
--    apply (Qplus_le_l _ _ (-(1#2)*proj1_sig q)).
--    ring_simplify. apply Qmin_lb_r.
--    simpl. ring_simplify. apply Qle_refl.
-- - apply uc_prf.
--   destruct (mu f e0); try constructor.
--   cut (forall z0 z1:Qpos, (proj1_sig z0 <= proj1_sig ((1#4)*q)%Qpos)
--                      -> (proj1_sig z1 <= proj1_sig ((1#4)*q)%Qpos)
--                      -> ball (proj1_sig q) (approximate x z0) (approximate y z1)).
--    intros H.
--    destruct d1; destruct d2; simpl; apply H; autorewrite with  QposElim; auto with *.
--   intros z0 z1 Hz0 Hz1.
--   eapply ball_weak_le.
--    2:apply Hxy.
--   rewrite -> Qle_minus_iff in *.
--   simpl. simpl in Hz0, Hz1.
--   apply (Qplus_le_compat _ _ _ _ Hz0) in Hz1.
--   ring_simplify in Hz1. setoid_replace (8 # 16) with (1#2) in Hz1.
--   ring_simplify. exact Hz1. reflexivity.
--  - apply uc_prf.
--  eapply ball_ex_weak_le;[|apply regFun_prf_ex].
--  unfold d2.
--  simpl.
--  destruct (mu f e2); try constructor.
--  destruct d0; simpl. rewrite Q_Qpos_min. simpl.
--  apply (Qplus_le_l _ _ (-(1#2)*proj1_sig q)).
--  ring_simplify. apply Qmin_lb_r.
--  ring_simplify. apply Qle_refl.
-- Qed.

-- Definition Cmap_slow : (Complete X) --> (Complete Y) :=
-- Build_UniformlyContinuousFunction Cmap_slow_prf.

-- End Cmap.

-- (** Cbind can be defined in terms of map and join *)
-- Definition Cbind_slow (X Y:MetricSpace) (f:X-->Complete Y) := uc_compose Cjoin (Cmap_slow f).

-- (** The completion operation, along with the map functor from a monad
-- in the catagory of metric spaces. *)
-- Section Monad_Laws.

-- Variable X Y Z : MetricSpace.

-- Notation "a =m b" := (msp_eq a b)  (at level 70, no associativity).

-- Lemma MonadLaw1 : forall a, Cmap_slow_fun (uc_id X) a =m a.
-- Proof.
--  intros x e1 e2.
--  rewrite Qplus_0_r.
--  simpl.
--  eapply ball_weak_le; [|apply regFun_prf].
--  simpl. apply Qplus_le_l.
--  rewrite <- (Qmult_1_l (proj1_sig e1)), Qmult_assoc.
--  apply Qmult_le_r. apply Qpos_ispos. discriminate.
-- Qed.

-- Lemma MonadLaw2 : forall (f:Y --> Z) (g:X --> Y) a, Cmap_slow_fun (uc_compose f g) a =m (Cmap_slow_fun f (Cmap_slow_fun g a)).
-- Proof.
--  simpl.
--  intros f g x e1 e2.
--  rewrite Qplus_0_r.
--  set (a := approximate (Cmap_slow_fun (uc_compose f g) x) e1).
--  set (b:=(approximate (Cmap_slow_fun f (Cmap_slow_fun g x)) e2)).
--  set (d0 := (QposInf_min (QposInf_mult (Qpos2QposInf (exist (Qlt 0) (1#2) eq_refl)) (mu (uc_compose f g) e1))
--                          ((Qpos2QposInf (exist (Qlt 0) (1#2) eq_refl)) * QposInf_bind (mu g) (QposInf_mult (Qpos2QposInf (exist (Qlt 0) (1#2) eq_refl)) (mu f e2))))).
--  apply ball_triangle with ((uc_compose f g) (approximate x d0)).
--   apply ball_sym.
--   apply Cmap_slow_raw_strong.
--   unfold d0.
--   apply QposInf_min_lb_l.
--  unfold b; simpl.
--  unfold Cmap_slow_raw.
--  apply uc_prf.
--  simpl.
--  destruct (mu f e2) as [q|]; try constructor.
--  simpl.
--  apply ball_weak_le with (proj1_sig ((1#2)*q)%Qpos).
--  simpl.
--  rewrite <- (Qmult_1_l (proj1_sig q)) at 2.
--  apply Qmult_le_r. apply Qpos_ispos. discriminate.
--  apply (Cmap_slow_raw_strong g x d0).
--  apply QposInf_min_lb_r.
-- Qed.

-- Lemma MonadLaw3 : forall (f:X --> Y) a, (Cmap_slow_fun f (Cunit_fun _ a)) =m (Cunit_fun _ (f a)).
-- Proof.
--  intros f x e1 e2.
--  rewrite Qplus_0_r.
--  refine (regFun_prf _ _ _).
-- Qed.

-- Lemma MonadLaw4 : forall (f:X --> Y) a, (Cmap_slow_fun f (Cjoin_fun a)) =m (Cjoin_fun ((Cmap_slow_fun (Cmap_slow f)) a)).
-- Proof.
--  intros f x e1 e2.
--  pose (exist (Qlt 0) (1#2) eq_refl) as half.
--  pose (exist (Qlt 0) (1#4) eq_refl) as quarter.
--  pose (exist (Qlt 0) (1#8) eq_refl) as eightth.
--  set (e2' := (half*e2)%Qpos).
--  set (d0 := (QposInf_min (Qpos2QposInf quarter*(mu f e1))
--                          (Qpos2QposInf (exist (Qlt 0) (1#8) eq_refl)
--                           *(mu f (half*e2))))%QposInf).
--  simpl.
--  unfold Cmap_slow_raw; simpl.
--  unfold Cjoin_raw; simpl.
--  unfold Cmap_slow_raw; simpl.
--  assert (halfhalf: forall q, QposEq (quarter * q) (half * (half * q))%Qpos).
--  { unfold QposEq. intro. simpl. ring. }
--  apply ball_triangle with (f (approximate (approximate x d0) d0)).
--  rewrite Qplus_0_r.
--   apply uc_prf.
--   destruct (mu f e1) as [q|]; try constructor.
--   simpl.
--   do 2 rewrite <- ball_Cunit. unfold d0.
--   assert (QposEq q ((quarter*q + quarter*q) + (quarter*q+ quarter*q))%Qpos) as qeq.
--   { unfold QposEq. simpl. ring. }
--   pose proof (ball_wd (Complete (Complete X)) qeq) as bwd.
--   apply (bwd _ _ (reflexivity _) _ _ (reflexivity _)).
--   apply ball_triangle with x.
--    apply ball_triangle with (Cunit (approximate x (half * (half * q))%Qpos)).
--     rewrite -> ball_Cunit.
--     unfold QposEq in halfhalf. rewrite halfhalf.
--     apply ball_approx_l.
--    unfold QposEq in halfhalf. rewrite halfhalf.
--    apply ball_approx_l.
--   apply ball_triangle with (Cunit (approximate x d0)).
--    change (ball_ex (quarter * q)%Qpos x (Cunit (approximate x d0))).
--    apply ball_ex_weak_le with (d0)%QposInf.
--     apply QposInf_min_lb_l.
--    destruct d0 as [d0|]; try constructor.
--    apply ball_approx_r.
--   rewrite -> ball_Cunit.
--   change (ball_ex (quarter * q)%Qpos (approximate x d0) (Cunit (approximate (approximate x d0) d0))).
--   apply ball_ex_weak_le with (d0)%QposInf.
--    apply QposInf_min_lb_l.
--   destruct d0 as [d0|]; try constructor.
--   apply ball_approx_r.
--  apply ball_sym.
--  apply ball_weak_le with (proj1_sig (half*e2)%Qpos).
--  simpl.
--  rewrite <- (Qmult_1_l (proj1_sig e2)), Qmult_assoc.
--  apply Qmult_le_r. apply Qpos_ispos. discriminate.
--  apply uc_prf.
--  unfold half. simpl. unfold half in d0. simpl in d0.
--  destruct (@mu X Y f (exist (Qlt 0) (1 # 2) (@eq_refl comparison Lt) * e2));
--    try constructor.
--  simpl.
--  do 2 rewrite <- ball_Cunit.
--  assert (QposEq q ((half*q + quarter*q)+ (eightth*q+ eightth*q))%Qpos) as qeq.
--  { unfold QposEq. simpl. ring. }
--  pose proof (ball_wd (Complete (Complete X)) qeq) as bwd.
--  apply (bwd _ _ (reflexivity _) _ _ (reflexivity _)).
--  apply ball_triangle with x.
--  apply ball_triangle with (Cunit (approximate x (half * (half * q))%Qpos)).
--  - rewrite -> ball_Cunit. apply ball_approx_l.
--  - unfold QposEq in halfhalf. rewrite halfhalf. apply ball_approx_l.
--  - apply ball_triangle with (Cunit (approximate x d0)).
--   change (ball_ex (eightth * q)%Qpos x (Cunit (approximate x d0))).
--   apply ball_ex_weak_le with (d0)%QposInf.
--    apply QposInf_min_lb_r.
--   destruct d0 as [d0|]; try constructor.
--   apply ball_approx_r.
--  rewrite -> ball_Cunit.
--  change (ball_ex (eightth * q)%Qpos (approximate x d0) (Cunit (approximate (approximate x d0) d0))).
--  apply ball_ex_weak_le with (d0)%QposInf.
--   apply QposInf_min_lb_r.
--  destruct d0 as [d0|]; try constructor.
--  apply ball_approx_r.
-- Qed.

-- Lemma MonadLaw5 : forall a, (Cjoin_fun (X:=X) (Cunit_fun _ a)) =m a.
-- Proof.
--  intros x e1 e2.
--  simpl.
--  setoid_replace (proj1_sig e1+0+proj1_sig e2)
--    with (proj1_sig ((1#2)*e1 + e2 + (1#2)*e1)%Qpos)
--    by (simpl; ring).
--  apply ball_weak. apply Qpos_nonneg.
--  apply regFun_prf.
-- Qed.

-- Lemma MonadLaw6 : forall a, Cjoin_fun ((Cmap_slow_fun (X:=X) Cunit) a) =m a.
-- Proof.
--  intros a e1 e2.
--  simpl.
--  setoid_replace (proj1_sig e1 + 0 + proj1_sig e2)
--    with (proj1_sig ((1#2)*((1#2)*e1) + e2 + (3#4)*e1)%Qpos)
--    by (simpl; ring).
--  apply ball_weak. apply Qpos_nonneg.
--  apply regFun_prf.
-- Qed.

-- Lemma MonadLaw7 : forall a, Cjoin_fun ((Cmap_slow_fun (X:=Complete (Complete X)) Cjoin) a) =m Cjoin_fun (Cjoin_fun a).
-- Proof.
--  intros x e1 e2.
--  pose (half := fun e:Qpos => ((1#2)*e)%Qpos).
--  apply ball_weak_le with (proj1_sig ((half (half e1)) + ((half (half e1)) + (half (half e1) + (half (half e2))) + (half (half e2))) + (half e2))%Qpos).
--   unfold half.
--   simpl. ring_simplify.
--   apply Qplus_le_l.
--   rewrite <- (Qmult_1_l (proj1_sig e1)) at 2.
--   apply Qmult_le_r. apply Qpos_ispos. discriminate.
--  apply (regFun_prf x).
-- Qed.

-- (** This final law isn't a monad law, rather it completes the isomorphism
-- between a twice completed metric space and a one completed metric space. *)
-- Lemma CunitCjoin : forall a, (Cunit_fun _ (Cjoin_fun (X:=X) a)) =m a.
-- Proof.
--  intros x e1 e2 d1 d2.
--  rewrite Qplus_0_r.
--  change (ball (proj1_sig d1 + (proj1_sig e1 + proj1_sig e2) + proj1_sig d2)
--    (approximate (approximate x ((1#2) * d1)%Qpos) ((1#2) * d1)%Qpos)
--      (approximate (approximate x e2) (Qpos2QposInf d2))).
--  apply ball_weak_le with (proj1_sig (((1#2) * d1 + ((1#2) * d1 + e2) + d2))%Qpos).
--   rewrite -> Qle_minus_iff. simpl.
--   ring_simplify.
--   auto with *.
--  apply (regFun_prf x).
-- Qed.

-- End Monad_Laws.

-- (** The monad laws are sometimes expressed in terms of bind and unit. *)
-- Lemma BindLaw1 : forall X Y (f:X--> Complete Y) a,
--     msp_eq (Cbind_slow f (Cunit_fun _ a)) (f a).
-- Proof.
--  intros X Y f a.
--  change (msp_eq (Cjoin (Cmap_slow_fun f (Cunit_fun X a))) (f a)).
--  rewrite -> (MonadLaw3 f a).
--  apply MonadLaw5.
-- Qed.

-- Lemma BindLaw2 : forall X a, (msp_eq (Cbind_slow (Cunit:X --> Complete X) a) a).
-- Proof.
--  apply MonadLaw6.
-- Qed.

-- Lemma BindLaw3 : forall X Y Z (a:Complete X) (f:X --> Complete Y) (g:Y-->Complete Z),
--     msp_eq (Cbind_slow g (Cbind_slow f a)) (Cbind_slow (uc_compose (Cbind_slow g) f) a).
-- Proof.
--  intros X Y Z a f g.
--  change (msp_eq (Cjoin (Cmap_slow_fun g (Cjoin_fun (Cmap_slow f a))))
--    (Cjoin (Cmap_slow_fun (uc_compose (Cbind_slow g) f) a))).
--  rewrite -> (MonadLaw2 (Cbind_slow g) f).
--  unfold Cbind_slow.
--  rewrite -> (MonadLaw4 g).
--  rewrite -> (MonadLaw2 (Cjoin (X:=Z)) (Cmap_slow g)).
--  symmetry.
--  apply MonadLaw7.
-- Qed.

-- (**
-- *** Strong Monad
-- The monad is a strong monad because the map function itself is
-- a uniformly continuous function. *)
-- Section Strong_Monad.

-- Variable X Y : MetricSpace.
-- Let X_Y := UniformlyContinuousSpace X Y.
-- Let CX_CY := UniformlyContinuousSpace (Complete X) (Complete Y).

-- Lemma Cmap_strong_slow_prf : is_UniformlyContinuousFunction ((Cmap_slow (Y:=Y)):(X_Y -> CX_CY)) Qpos2QposInf.
-- Proof.
--   intros e f g H. split. apply Qpos_nonneg.
--   intro x.
--  apply ball_closed.
--  intros e0 epos.
--  set (he0 := ((1#2)*exist _ _ epos)%Qpos).
--  set (d0 := QposInf_min (Qpos2QposInf (1#2)*(mu f he0)) (Qpos2QposInf (1#2)*(mu g he0))).
--  set (a0 := approximate x d0).
--  setoid_replace (proj1_sig e+e0) with (proj1_sig (he0 + e + he0)%Qpos)
--    by (simpl; ring).
--  apply ball_triangle with (Cunit (g a0)).
--   apply ball_triangle with (Cunit (f a0)).
--   assert (QposEq he0 he0) by reflexivity.
--   pose proof (MonadLaw3 f a0). symmetry in H1.
--   apply (ball_wd _ H0 _ _ (reflexivity _) _ _ H1). clear H1 H0.
--    refine (uc_prf _ _ _ _ _).
--    simpl.
--    destruct (mu f he0) as [d1|];[|constructor].
--    eapply ball_ex_weak_le with d0.
--     apply QposInf_min_lb_l.
--    destruct d0 as [d0|];[|constructor].
--    apply ball_approx_r.
--   rewrite -> ball_Cunit.
--   apply H.
--   assert (QposEq he0 he0) by reflexivity.
--   pose proof (MonadLaw3 g a0). symmetry in H1.
--   apply (ball_wd _ H0 _ _ H1 _ _ (reflexivity _)). clear H1 H0.
--  apply (uc_prf (Cmap_slow g)).
--  simpl.
--  destruct (mu g he0) as [d2|];[|constructor].
--  eapply ball_ex_weak_le with d0.
--   apply QposInf_min_lb_r.
--  destruct d0 as [d0|];[|constructor].
--  apply ball_approx_l.
-- Qed.

-- Definition Cmap_strong_slow : (X --> Y) --> (Complete X --> Complete Y) :=
-- Build_UniformlyContinuousFunction Cmap_strong_slow_prf.

-- (** Using strength we can show that [Complete] forms an applicative
-- functor. The [ap] function is useful for making multiple argument maps.
-- *)
-- Definition Cap_slow_raw (f:Complete (X --> Y)) (x:Complete X) (e:QposInf) :=
--   approximate (Cmap_slow (approximate f ((Qpos2QposInf (exist (Qlt 0) (1#2) eq_refl))*e)%QposInf) x)
--               ((Qpos2QposInf (exist (Qlt 0) (1#2) eq_refl))*e)%QposInf.


-- Lemma Cap_slow_fun_prf (f:Complete (X --> Y)) (x:Complete X)
--   : is_RegularFunction (@ball Y) (Cap_slow_raw f x).
-- Proof.
--  intros e1 e2.
--  unfold Cap_slow_raw.
--  unfold QposInf_mult, QposInf_bind.
--  pose (exist (Qlt 0) (1#2) eq_refl) as half.
--  set (he1 := (half * e1)%Qpos).
--  set (he2 := (half * e2)%Qpos).
--  set (f1 := (approximate f he1)).
--  set (f2 := (approximate f he2)).
--  change (Cmap_slow (Y:=Y) f1) with (Cmap_strong_slow f1).
--  change (Cmap_slow (Y:=Y) f2) with (Cmap_strong_slow f2).
--  set (y1 :=(Cmap_strong_slow f1 x)).
--  set (y2 :=(Cmap_strong_slow f2 x)).
--  setoid_replace (proj1_sig e1 + proj1_sig e2)
--    with (proj1_sig (he1 + (he1 + he2) + he2)%Qpos)
--    by (simpl; ring).
--  rewrite <- ball_Cunit.
--  apply ball_triangle with y2;[|apply ball_approx_r].
--  apply ball_triangle with y1;[apply ball_approx_l|].
--  apply (uc_prf Cmap_strong_slow).
--  apply (@regFun_prf _ (@ball (X-->Y))).
-- Qed.

-- Definition Cap_slow_fun (f:Complete (X --> Y)) (x:Complete X) : Complete Y :=
-- Build_RegularFunction (Cap_slow_fun_prf f x).

-- Lemma Cap_slow_help (f:Complete (X --> Y)) (x:Complete X) (e:Qpos) :
--  ball (proj1_sig e) (Cap_slow_fun f x) (Cmap_slow (approximate f e) x).
-- Proof.
--  intros d1 d2.
--  pose (exist (Qlt 0) (1#2) eq_refl) as half.
--  set (d1' := (half * d1)%Qpos).
--  set (f1 := (approximate f d1')).
--  set (f2 := (approximate f e)).
--  set (y1 := (Cmap_slow f1 x)).
--  set (y2 := (Cmap_slow f2 x)).
--  change (ball (proj1_sig d1 + proj1_sig e + proj1_sig d2) (approximate y1 d1') (approximate y2 (Qpos2QposInf d2))).
--  setoid_replace (proj1_sig d1 + proj1_sig e + proj1_sig d2)
--    with (proj1_sig (d1' + (d1' + e) + d2)%Qpos)
--    by (simpl; ring).
--  rewrite <- ball_Cunit.
--  apply ball_triangle with y2;[|apply ball_approx_r].
--  apply ball_triangle with y1;[apply ball_approx_l|].
--  apply (uc_prf Cmap_strong_slow).
--  apply (@regFun_prf _ (@ball (X-->Y))).
-- Qed.

-- Definition Cap_slow_modulus (f:Complete (X --> Y)) (e:Qpos) : QposInf
--   := ((Qpos2QposInf (1#2))
--       *(mu (approximate f (Qpos2QposInf ((1#3)*e))%Qpos)
--            ((1#3)*e)%Qpos))%QposInf.

-- Lemma Cap_weak_slow_prf (f:Complete (X --> Y)) : is_UniformlyContinuousFunction (Cap_slow_fun f) (Cap_slow_modulus f).
-- Proof.
--  intros e x y H.
--  set (e' := ((1#3)*e)%Qpos).
--  setoid_replace (proj1_sig e) with (proj1_sig (e'+e'+e')%Qpos)
--    by (simpl; ring).
--  apply ball_triangle with (Cmap_slow (approximate f e') y).
--   apply ball_triangle with (Cmap_slow (approximate f e') x).
--    apply Cap_slow_help.
--   apply (uc_prf).
--   apply H.
--  apply ball_sym.
--  apply Cap_slow_help.
-- Qed.

-- Definition Cap_weak_slow (f:Complete (X --> Y)) : Complete X --> Complete Y :=
-- Build_UniformlyContinuousFunction (Cap_weak_slow_prf f).

-- Lemma Cap_slow_prf : is_UniformlyContinuousFunction Cap_weak_slow Qpos2QposInf.
-- Proof.
--   intros e f1 f2 H. split. apply Qpos_nonneg.
--   intro x.
--  apply ball_closed.
--  intros d dpos.
--  setoid_replace (proj1_sig e + d)
--    with (proj1_sig ((1#4)*exist _ _ dpos
--                     + ((1#4)*exist _ _ dpos + e + (1#4)*exist _ _ dpos)
--                     + (1#4)*exist _ _ dpos)%Qpos)
--    by (simpl; ring).
--  apply ball_triangle with (Cmap_strong_slow (approximate f2 ((1#4)*exist _ _ dpos)%Qpos) x).
--   apply ball_triangle with (Cmap_strong_slow (approximate f1 ((1#4)*exist _ _ dpos)%Qpos) x).
--    apply Cap_slow_help.
--   apply (uc_prf Cmap_strong_slow).
--   apply H.
--  apply ball_sym.
--  apply Cap_slow_help.
-- Qed.

-- Definition Cap_slow : Complete (X --> Y) --> Complete X --> Complete Y :=
-- Build_UniformlyContinuousFunction Cap_slow_prf.

-- Lemma StrongMonadLaw1 : forall a b,
--     msp_eq (Cap_slow_fun (Cunit_fun _ a) b) (Cmap_strong_slow a b).
-- Proof.
--  intros f x.
--  apply regFunEq_equiv, regFunEq_e.
--  intros e.
--  apply ball_weak_le with (proj1_sig ((1#2)*e+e)%Qpos).
--  simpl. rewrite -> Qle_minus_iff; ring_simplify.
--  apply Qmult_le_0_compat. discriminate. apply Qpos_nonneg.
--  refine (regFun_prf _ _ _).
-- Qed.

-- End Strong_Monad.

-- Lemma Cmap_slow_wd_loc
--   : forall (X Y : MetricSpace)
--       (f g : X --> Y) (x : Complete X) (e : Qpos),
--     (forall a : X, ball (proj1_sig e) (Cunit a) x -> msp_eq (f a) (g a)) ->
--     @msp_eq _ (Cmap_slow_fun f x) (Cmap_slow_fun g x).
-- Proof.
--   intros. intros e1 e2. simpl.
--   unfold Cmap_slow_raw; simpl.
--   pose (QposInf_min (Qpos2QposInf (1#2)*(mu g e2))
--                     (QposInf_min (Qpos2QposInf (1#2)*(mu f e1)) e)) as d.
--   rewrite Qplus_0_r.
--   apply (ball_triangle _ (proj1_sig e1) (proj1_sig e2) _
--            (f (approximate x d))).
--   - apply (uc_prf f).
--     destruct (mu f e1). 2: reflexivity.
--     simpl.
--     destruct d eqn:des.
--     assert (Qle (proj1_sig q0) ((1 # 2) * proj1_sig q)).
--     { pose proof (QposInf_min_lb_r (Qpos2QposInf (1 # 2) * mu g e2)
--                                    (QposInf_min (Qpos2QposInf (1 # 2) * q) e)).
--       subst d. rewrite des in H0. simpl in H0.
--       apply (Qle_trans _ _ _ H0), Qpos_min_lb_l. }
--     apply (Qplus_le_l _ _ ((1#2)*proj1_sig q)) in H0.
--     ring_simplify in H0. rewrite Qplus_comm in H0.
--     apply (ball_weak_le _ _ _ H0).
--     apply (regFun_prf x ((1#2)*q)%Qpos q0).
--     exfalso. subst d.
--     destruct (mu g e2); discriminate.
--   - rewrite H.
--     + apply (uc_prf g).
--       destruct (mu g e2). 2: reflexivity.
--       simpl. destruct d eqn:des.
--       assert (Qle (proj1_sig q0) ((1 # 2) * proj1_sig q)).
--       { pose proof (QposInf_min_lb_l (Qpos2QposInf (1 # 2) * q)
--                                      (QposInf_min (Qpos2QposInf (1 # 2) * mu f e1) e)).
--         subst d. rewrite des in H0. exact H0. }
--       apply (Qplus_le_l _ _ ((1#2)*proj1_sig q)) in H0.
--       ring_simplify in H0.
--       apply (ball_weak_le _ _ _ H0).
--       apply (regFun_prf x q0 ((1#2)*q)%Qpos).
--       exfalso. subst d.
--       destruct (mu f e1); discriminate.
--     + destruct d eqn:des.
--       assert (proj1_sig q <= proj1_sig e).
--       { destruct (Qpos2QposInf (1 # 2) * mu g e2)%QposInf.
--         destruct (Qpos2QposInf (1 # 2) * mu f e1)%QposInf.
--         simpl in d. subst d. inversion des.
--         apply (Qle_trans _ (proj1_sig (Qpos_min q1 e))).
--         apply Qpos_min_lb_r. apply Qpos_min_lb_r.
--         subst d. simpl in des. inversion des.
--         apply Qpos_min_lb_r.
--         simpl in d. subst d. destruct (mu f e1).
--         simpl in des. inversion des. apply Qpos_min_lb_r.
--         simpl in des. inversion des. apply Qle_refl. }
--       apply (ball_weak_le _ _ _ H0). apply ball_approx_l.
--       exfalso. destruct (mu g e2), (mu f e1); discriminate.
-- Qed.

-- (* begin hide *)
-- Opaque Complete.

-- Add Parametric Morphism X Y : (@Cmap_slow_fun X Y)
--     with signature (@msp_eq (UniformlyContinuousSpace X Y))
--                      ==> (@msp_eq (Complete X)) ==> (@msp_eq (Complete Y))
--       as Cmap_slow_wd.
-- Proof.
--  intros f g Hfg x1 x2 Hy.
--  transitivity (Cmap_slow_fun f x2).
--   apply (@uc_wd _ _ (Cmap_slow f) _ _ Hy).
--  generalize x2.
--  apply (@uc_wd (X --> Y) (Complete X --> Complete Y) (Cmap_strong_slow X Y) _ _ Hfg).
-- Qed.

-- Add Parametric Morphism X Y : (@Cap_weak_slow X Y)
--     with signature (@msp_eq _) ==> (@msp_eq _) as Cap_weak_slow_wd.
-- Proof.
--  intros x1 x2 Hx.
--  apply (@uc_wd _ _ (Cap_slow X Y));assumption.
-- Qed.

-- Add Parametric Morphism X Y : (@Cap_slow_fun X Y)
--     with signature (@msp_eq _) ==> (@msp_eq _) ==> (@msp_eq _) as Cap_slow_wd.
-- Proof.
--  intros x1 x2 Hx y1 y2 Hy.
--  transitivity (Cap_slow_fun x1 y2).
--   apply (@uc_wd _ _ (Cap_weak_slow x1) _ _ Hy).
--  generalize y2.
--  apply (@uc_wd _ _ (Cap_slow X Y));assumption.
-- Qed.
-- Transparent Complete.
-- (* end hide *)

-- (** A binary version of map *)
-- Definition Cmap2_slow (X Y Z:MetricSpace) (f:X --> Y --> Z) := uc_compose (@Cap_slow Y Z) (Cmap_slow f).

-- (**
-- *** Completion and Classification
-- The completion operations preserve locatedness, but not decidability.
-- *)
-- Lemma Complete_located : forall (X : MetricSpace),
--     locatedMetric X -> locatedMetric (Complete X).
-- Proof.
--  intros X Hx e d x y Hed.
--  pose (d - e) as c.
--  assert (0 < c) as Hc.
--  { apply Qlt_minus_iff in Hed. exact Hed. }
--  set (c':=((1#5)*exist _ _ Hc)%Qpos).
--  assert (proj1_sig c'+e+ proj1_sig c' < e+(3#1)*proj1_sig c') as H.
--  { rewrite -> Qlt_minus_iff. simpl. ring_simplify.
--    apply (Qpos_ispos ((25#125)*exist _ _ Hc)). }
--  destruct (Hx _ _ (approximate x c') (approximate y c') H) as [H0 | H0].
--  - left.
--    rewrite <- ball_Cunit in H0.
--   setoid_replace d
--     with (proj1_sig c' + (e + (3#1) * proj1_sig c') + proj1_sig c')%Q
--     by (simpl; unfold c; ring).
--   eapply ball_triangle;[eapply ball_triangle;[|apply H0]|];
--     [apply ball_approx_r|apply ball_approx_l].
--  - right.
--  abstract ( intros H1; apply H0; rewrite <- ball_Cunit;
--    eapply ball_triangle;[eapply ball_triangle;[|apply H1]|];
--      [apply ball_approx_l|apply ball_approx_r]).
-- Defined.
