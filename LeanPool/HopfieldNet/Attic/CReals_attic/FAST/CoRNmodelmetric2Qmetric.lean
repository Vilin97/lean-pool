/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Analysis.Normed.Field.Lemmas
import LeanPool.HopfieldNet.CReals.Core.CoRNmetric2Metric
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
-- Require Export CoRN.metric2.Metric.
-- Require Import CoRN.metric2.Prelength.
-- Require Import CoRN.metric2.Classification.
-- Require Import CoRN.model.totalorder.QMinMax.
-- Require Import CoRN.model.totalorder.QposMinMax.
-- From Coq Require Import Qabs.
-- Require Import CoRN.metric2.UniformContinuity.
-- Require Import MathClasses.implementations.stdlib_rationals.

-- Set Implicit Arguments.

-- Local Open Scope Q_scope.

-- Opaque Qabs.

-- Definition QAbsSmall (e x : Q) : Prop := -e <= x /\ x <= e.

-- Lemma QAbsSmall_opp : forall x y : Q, QAbsSmall x y -> QAbsSmall x (-y).
-- Proof.
--   intros x y H. split.
--   apply Qopp_le_compat. apply H.
--   rewrite <- (Qopp_involutive x).
--   apply Qopp_le_compat. apply H.
-- Qed.

open Rat

/-- `QAbsSmall e x` means `-e ≤ x ≤ e` for rationals. -/
def QAbsSmall (e x : ℚ) : Prop := -e ≤ x ∧ x ≤ e

lemma QAbsSmall_opp (x y : ℚ) (h : QAbsSmall x y) : QAbsSmall x (-y) :=
  ⟨by simpa [neg_le_neg_iff] using h.2,
    (by
     unfold QAbsSmall at *
     obtain ⟨h1,h2⟩:= h
     exact neg_le.mp h1
    )⟩

-- (**
-- ** Example of a Metric: <Q, Qball>
-- *)

-- Definition Qball (e : Q) (a b : Q) := QAbsSmall e (a - b).

/-- `Qball e a b` means `-e ≤ a - b ≤ e` for rationals. -/
def Qball (e a b : ℚ) : Prop := QAbsSmall e (a - b)

-- Lemma AbsSmall_Qabs : forall x y, (Qabs y <= x)%Q <-> QAbsSmall x y.
-- Proof.
--  cut (forall x y, (0 <= y)%Q -> ((Qabs y <= x)%Q <-> QAbsSmall x y)).
--   intros H x y.
--   generalize (H x y) (H x (-y)%Q).
--   clear H.
--   rewrite -> Qabs_opp.
--   apply Qabs_case; intros H H1 H2.
--    auto.
--   assert (X:QAbsSmall x y <-> QAbsSmall x (- y)%Q).
--    split.
--     apply QAbsSmall_opp.
--     intros X. unfold QAbsSmall.
--     rewrite <- (Qopp_involutive y).
--    apply QAbsSmall_opp.
--    assumption.
--   rewrite -> X.
--   apply H2.
--   rewrite -> Qle_minus_iff in H.
--   ring_simplify in H.
--   ring_simplify.
--   apply H.
--  intros x y H.
--  rewrite -> Qabs_pos;[|assumption].
--  split.
--   intros H0.
--   split. 2 : exact H0.
--   refine (Qle_trans _ 0 _ _ H).
--   apply (Qopp_le_compat 0 x).
--   exact (Qle_trans _ _ _ H H0).
--  intros [_ H0].
--  assumption.
-- Qed.

-- Lemma Qball_Qabs : forall e a b, Qball e a b <-> Qabs (a - b) <= e.
-- Proof. split; apply AbsSmall_Qabs. Qed.

-- Lemma Qle_closed : (forall e x, (forall d : Qpos, x <= e+ proj1_sig d) -> x <= e).
-- Proof.
--  intros.
--  apply Qnot_lt_le. intro abs.
--  assert (0 < (x - e) * (1#2)) as H0.
--  { apply (Qle_lt_trans _ (0*(1#2))). discriminate.
--    apply Qmult_lt_r. reflexivity.
--    rewrite <- (Qplus_opp_r e). apply Qplus_lt_l. exact abs. }
--  specialize (H (exist _ _ H0)). simpl in H.
--  apply (Qplus_le_l _ _ (-x*(1#2))) in H.
--  ring_simplify in H. apply Qmult_le_l in H.
--  exact (Qle_not_lt _ _ H abs). reflexivity.
-- Qed.

-- (* Useful to interact with QArith lemmas.
--    ball_wd uses the metric setoid instead. *)
-- Add Parametric Morphism : Qball
--     with signature Qeq ==> Qeq ==> Qeq ==> iff as Qball_wd.
-- Proof.
--   intros.
--   unfold Qball, QAbsSmall.
--   rewrite H, H0, H1. reflexivity.
-- Qed.

-- #[global]
-- Instance Qball_Reflexive e: 0 <= e -> Reflexive (Qball e).
-- Proof.
--  intros epos x.
--  unfold Qball. unfold QAbsSmall, Qminus.
--  rewrite Qplus_opp_r. split.
--  apply (Qopp_le_compat 0). exact epos. exact epos.
-- Qed.

-- #[global]
-- Instance Qball_symmetric e: Symmetric (Qball e).
-- Proof.
--  intros x y.
--  unfold Qball.
--  intros. apply QAbsSmall_opp in H.
--  unfold QAbsSmall. destruct H. split.
--  apply (Qle_trans _ _ _ H). ring_simplify. apply Qle_refl.
--  refine (Qle_trans _ _ _ _ H0). ring_simplify. apply Qle_refl.
-- Qed.

-- Qball is a metric space on ℚ

open Set

instance Qball_refl {e : ℚ} (he : 0 ≤ e) : Reflexive (Qball e) :=
  λ x => by
    simp [Qball, QAbsSmall]
    exact he

instance Qball_symm {e : ℚ} : Symmetric (Qball e) :=
  λ x y h => by
    simp [Qball, QAbsSmall] at *
    have : -(e) ≤ y - x ∧ y - x ≤ e := by
      rw [←neg_sub, ←neg_le_neg_iff, ←neg_le_neg_iff]
      exact ⟨by linarith [h.2], by linarith [h.1]⟩
    simp_all only [neg_le_sub_iff_le_add, tsub_le_iff_right, and_self]

instance Qball_triangle : ∀ {e₁ e₂ : ℚ} {a b c : ℚ},
    Qball e₁ a b → Qball e₂ b c → Qball (e₁ + e₂) a c :=
  λ {e₁ e₂ a b c} h₁ h₂ =>
    by
      simp [Qball, QAbsSmall] at *
      have : a - c = (a - b) + (b - c) := Eq.symm (sub_add_sub_cancel a b c)
      constructor
      · linarith [h₁.1, h₂.1, this]
      · linarith [h₁.2, h₂.2, this]

-- Now we can package this as a metric space structure if desired.
-- For example, as a UniformSpace or PseudoMetricSpace, but here is a minimal structure:

structure QballMetricSpace where
  ball : ℚ → ℚ → ℚ → Prop := Qball
  refl : ∀ {e : ℚ}, 0 ≤ e → Reflexive (Qball e) := Qball_refl
  symm : ∀ {e : ℚ}, Symmetric (Qball e) := by {
   sorry
  }
  triangle : ∀ {e₁ e₂ : ℚ} {a b c : ℚ}, Qball e₁ a b →
    Qball e₂ b c → Qball (e₁ + e₂) a c := Qball_triangle

lemma Q_is_MetricSpace : IsMetricSpace Qball := sorry

-- Lemma Q_is_MetricSpace : is_MetricSpace Qball.
-- Proof.
--  split; auto with typeclass_instances.
--  - (* triangle inequality *)
--    intros e1 e2 a b c H1 H2.
--    unfold Qball. unfold QAbsSmall. simpl.
--    assert (Qeq (a-c) ((a-b)+(b-c))) by ring.
--    rewrite H. clear H.
--    split. apply (Qle_trans _ (-e1 + -e2)).
--    ring_simplify. apply Qle_refl.
--    apply Qplus_le_compat. apply H1. apply H2.
--    apply Qplus_le_compat. apply H1. apply H2.
--  - (* distance closed *)
--    intros e a b H. split.
--    apply Qle_closed. intros [d dpos]. simpl.
--    specialize (H d dpos). destruct H.
--    apply (Qplus_le_l _ _ (-d)). ring_simplify.
--    simpl in H. ring_simplify in H. exact H.
--    apply Qle_closed. intros. apply H.
--    apply Qpos_ispos.
--  - intros. destruct H. apply (Qle_trans _ _ _ H) in H0.
--    apply (Qplus_le_l _ _ e) in H0. ring_simplify in H0.
--    rewrite <- (Qmult_0_r (2#1)) in H0. apply Qmult_le_l in H0.
--    exact H0. reflexivity.
--  - intros. split.
--    + apply Qnot_lt_le. intro abs.
--      contradict H; intros [H _].
--      exact (Qlt_not_le _ _ abs H).
--    + apply Qnot_lt_le. intro abs.
--      contradict H; intros [_ H].
--      exact (Qlt_not_le _ _ abs H).
-- Qed.

-- (* begin hide *)
-- Lemma Qball_e_wd : forall (e1 e2:Q) x y,
--     e1 == e2 -> (Qball e1 x y <-> Qball e2 x y).
-- Proof.
--   intros.
--   unfold Qball, QAbsSmall.
--   rewrite -> H.
--   reflexivity.
-- Qed.

lemma Qball_e_wd (e₁ e₂ x y : ℚ) (h : e₁ = e₂) : Qball e₁ x y ↔ Qball e₂ x y := by
  rw [h]

-- (* end hide *)
-- Definition Q_as_MetricSpace : MetricSpace :=
--   @Build_MetricSpace Q _ Qball_e_wd Q_is_MetricSpace.


/-- The metric space structure on ℚ with Qball as the metric. -/
def Q_as_MetricSpace : MetricSpace' where
  carrier := ℚ
  ball := Qball
  ball_e_wd := Qball_e_wd
  is_metric := Q_is_MetricSpace

-- Canonical Structure Q_as_MetricSpace.

-- Lemma QPrelengthSpace_help
--   : forall (e d1 d2:Qpos), proj1_sig e < proj1_sig d1+ proj1_sig d2 -> forall (a b c:Q),
--       ball (proj1_sig e) a b -> (c == (a*proj1_sig d2 + b*proj1_sig d1)/proj1_sig (d1+d2)%Qpos) -> ball (proj1_sig d1) a c.
-- Proof with auto with *.
--  intros e d1 d2 He a b c Hab Hc.
--  simpl.
--  unfold Qball.
--  unfold QAbsSmall. rewrite Hc. clear Hc c.
--  assert (0 < proj1_sig (d1 + d2)%Qpos).
--  { apply (Qlt_trans _ (proj1_sig e)). destruct e. exact q. exact He. }
--  split.
--  - apply (Qmult_le_r _ _ (proj1_sig (d1+d2)%Qpos)). exact H.
--    simpl. field_simplify.
--    apply (Qle_trans _ (proj1_sig d1 * (-proj1_sig (d1 + d2)%Qpos))).
--    simpl. field_simplify. apply Qle_refl.
--    apply (Qle_trans _ (proj1_sig d1 * (a - b))).
--    apply Qmult_le_l. destruct d1. exact q.
--    destruct Hab. apply (Qle_trans _ (-proj1_sig e)).
--    apply Qopp_le_compat, Qlt_le_weak, He. exact H0.
--    field_simplify. apply Qle_refl.
--    intro abs. destruct d1, d2. simpl in abs.
--    simpl in H. rewrite abs in H. exact (Qlt_irrefl _ H).
--  - apply (Qmult_le_r _ _ (proj1_sig (d1+d2)%Qpos)). exact H.
--    simpl. field_simplify.
--    apply (Qle_trans _ (proj1_sig d1 * (a-b))).
--    field_simplify. apply Qle_refl.
--    apply (Qle_trans _ (proj1_sig (d1 * (d1 + d2))%Qpos)).
--    apply Qmult_le_l. destruct d1. exact q.
--    destruct Hab. apply (Qle_trans _ (proj1_sig e)). exact H1.
--    apply Qlt_le_weak, He.
--    simpl. field_simplify. apply Qle_refl.
--    intro abs. destruct d1,d2. simpl in H, abs.
--    rewrite abs in H. exact (Qlt_irrefl _ H).
-- Qed.

-- (** Q is a prelength space *)
-- Lemma QPrelengthSpace : PrelengthSpace Q_as_MetricSpace.
-- Proof.
--  intros a b e d1 d2 He Hab.
--  pose ((a * proj1_sig d2 + b * proj1_sig d1) / proj1_sig (d1 + d2)%Qpos) as c.
--  exists c.
--   apply (@QPrelengthSpace_help e d1 d2 He a b c); try assumption.
--   reflexivity.
--  apply ball_sym.
--  eapply QPrelengthSpace_help.
--    rewrite -> Qplus_comm.
--    apply He.
--   apply ball_sym.
--   apply Hab.
--  unfold c.
--  unfold Qdiv.
--  apply Qmult_comp.
--   ring.
--  apply Qinv_comp.
--  simpl. ring.
-- Qed.

-- (** Q is a decideable metric, and hence located and stable. *)
-- Lemma Qmetric_dec : decidableMetric Q_as_MetricSpace.
-- Proof.
--  intros e a b.
--  simpl.
--  simpl.
--  unfold Qball, QAbsSmall.
--  set (c:=-e).
--  set (d:=(a-b)).
--  destruct (Qlt_le_dec_fast d c) as [Hdc|Hdc].
--   right.
--   abstract( intros [H1 H2]; apply (Qlt_not_le _ _ Hdc H1) ).
--  destruct (Qlt_le_dec_fast e d) as [Hed|Hed].
--   right.
--   abstract( intros [H1 H2]; apply (Qlt_not_le _ _ Hed H2) ).
--  left.
--  abstract auto.
-- Defined.

-- #[global]
-- Hint Resolve Qmetric_dec : metricQ.

-- Lemma locatedQ : locatedMetric Q_as_MetricSpace.
-- Proof.
--  apply decidable_located.
--  auto with *.
-- Defined.

-- #[global]
-- Hint Resolve locatedQ : metricQ.

-- Lemma in_Qball (r: Q) (x y: Q)
--   : (x - r <= y <= x + r) <-> Qball r x y.
-- Proof.
--  now rewrite Qball_Qabs, Q.Qabs_diff_Qle.
-- Qed.

-- Lemma in_centered_Qball (w: Q) (m x: Q):
--   m <= x <= m + w ->
--   Qball ((1#2) * w) (m + (1#2) * w) x.
-- Proof.
--  intros [??].
--  apply in_Qball.
--  split; simpl; ring_simplify; assumption.
-- Qed.

-- Lemma nonneg_in_Qball_0 (x : Q) (Eq : 0 <= x) (ε : Q) :
--   x <= ε <-> ball ε x 0.
-- Proof.
--   rewrite <-in_Qball. split.
--   - intros ?. split.
--     apply (Q.Qplus_le_r ε). now ring_simplify.
--     apply (Qle_trans _ (x+0)). rewrite Qplus_0_r.
--     exact Eq. apply Qplus_le_r.
--     exact (Qle_trans _ _ _ Eq H).
--   - intros [? ?].
--     apply (Q.Qplus_le_r (- ε)).
--     rewrite Qplus_comm. now ring_simplify.
-- Qed.

-- Section Qball_Qmult.

--   Variables (d : Qpos) (z x y: Q) (B: Qball (proj1_sig d / (Qabs z)) x y).

--   Lemma Qball_Qmult_Q_r : Qball (proj1_sig d) (x * z) (y * z).
--   Proof.
--    destruct (Qeq_dec z 0) as [E|E].
--    rewrite E, Qmult_0_r, Qmult_0_r.
--    apply Qball_Reflexive.
--    apply Qpos_nonneg.
--    apply Qball_Qabs.
--    apply Qball_Qabs in B.
--    assert (Qeq (x * z - y * z) ((x - y) * z)) by (simpl; ring).
--    rewrite H. clear H.
--    rewrite Qabs_Qmult.
--    assert (0 < Qabs z).
--    { apply Qabs_case.
--      intros. apply Qle_lteq in H. destruct H. exact H.
--      contradict E. symmetry. exact H.
--      intros. apply Qle_lteq in H. destruct H.
--      apply (Qplus_lt_l _ _ z). ring_simplify. exact H.
--      contradict E. exact H. }
--    simpl in B. apply (Qmult_le_l _ _ (/(Qabs z))).
--    apply Qinv_lt_0_compat, H.
--    rewrite Qmult_comm, <- Qmult_assoc, Qmult_inv_r, Qmult_1_r.
--    rewrite Qmult_comm.
--    exact B.
--    intro abs. rewrite abs in H. exact (Qlt_irrefl _ H).
--   Qed.

--   Lemma Qball_Qmult_Q_l : Qball (proj1_sig d) (z * x) (z * y).
--   Proof.
--    intros.
--    do 2 rewrite (Qmult_comm z).
--    apply Qball_Qmult_Q_r.
--   Qed.

-- End Qball_Qmult.

-- Section more_Qball_Qmult.

--   Variables (d z : Qpos) (x y: Q) (B: Qball (proj1_sig d / proj1_sig z) x y).

--   Lemma Qball_Qmult_r: Qball (proj1_sig d) (x * proj1_sig z) (y * proj1_sig z).
--   Proof.
--     apply Qball_Qmult_Q_r. destruct z, x0, Qnum; simpl.
--     exfalso. apply (Qlt_not_le _ _ q). simpl. apply (Qle_refl 0).
--     exact B. exfalso. inversion q.
--   Qed.

--   Lemma Qball_Qmult_l: Qball (proj1_sig d) (proj1_sig z * x) (proj1_sig z * y).
--   Proof.
--     apply Qball_Qmult_Q_l. destruct z, x0, Qnum; simpl.
--     exfalso. apply (Qlt_not_le _ _ q). simpl. apply (Qle_refl 0).
--     exact B. exfalso. inversion q.
--   Qed.

-- End more_Qball_Qmult.

-- Lemma Qball_plus (e d: Q) (x x' y y': Q):
--   Qball e x x' -> Qball d y y'
--   -> Qball (e + d) (x + y) (x' + y').
-- Proof with auto.
--  intros.
--  apply ball_triangle with (x' + y); apply Qball_Qabs.
--  assert (Qeq (x + y - (x' + y)) (x - x')) by (simpl; ring).
--  rewrite H1. clear H1. apply Qball_Qabs...
--  assert (Qeq (x' + y - (x' + y')) (y - y')) by (simpl; ring).
--  rewrite H1. apply Qball_Qabs...
-- Qed.

-- Lemma Qmult_AbsSmall : forall x y X Y : Q,
--     QAbsSmall X x -> QAbsSmall Y y -> QAbsSmall (X*Y) (x*y).
-- Proof.
--   intros. apply AbsSmall_Qabs.
--   rewrite Qabs_Qmult.
--   apply (Qle_trans _ (X * Qabs y)).
--   apply Qmult_le_compat_r.
--   apply AbsSmall_Qabs in H. exact H.
--   apply Qabs_nonneg.
--   rewrite Qmult_comm, (Qmult_comm X).
--   apply Qmult_le_compat_r.
--   apply AbsSmall_Qabs in H0. exact H0.
--   destruct H. apply (Qle_trans _ _ _ H) in H1.
--   apply (Qplus_le_l _ _ X) in H1.
--   ring_simplify in H1.
--   apply (Qmult_le_l _ _ (2#1)). reflexivity.
--   rewrite Qmult_0_r. exact H1.
-- Qed.

-- Lemma QAbsSmall_plus : forall e1 e2 x1 x2 : Q,
--  QAbsSmall e1 x1 -> QAbsSmall e2 x2 -> QAbsSmall (e1+e2) (x1+x2).
-- Proof.
--   intros. pose proof (@Qball_plus e1 e2 x1 0 x2 0).
--   unfold Qball, QAbsSmall, Qminus in H1.
--   do 4 rewrite Qplus_0_r in H1.
--   apply H1. exact H. exact H0.
-- Qed.

-- Lemma Qball_plus_r (e: Q) (x y y': Q):
--  Qball e y y' -> Qball e (x + y) (x + y').
-- Proof with auto.
--  intros B.
--  apply Qball_Qabs.
--  apply Qball_Qabs in B.
--  assert (Qeq (x + y - (x + y')) (y - y')) by (simpl; ring).
--  rewrite H. exact B.
-- Qed.

-- Lemma Qball_0_r (e: Qpos) : Qball (proj1_sig e) (proj1_sig e) 0.
-- Proof with auto with qarith.
--  apply Qball_Qabs.
--  unfold Qminus. rewrite Qplus_0_r.
--  rewrite Qabs_pos...
-- Qed.

-- Lemma Qball_0_l (e: Qpos) : Qball (proj1_sig e) 0 (proj1_sig e).
-- Proof with auto with qarith.
--  apply ball_sym. apply Qball_0_r.
-- Qed.

-- Lemma Qball_Qdiv_inv (d z: Qpos) (x y: Q):
--   Qball (proj1_sig d / proj1_sig z) (x / proj1_sig z) (y / proj1_sig z)
--   -> Qball (proj1_sig d) x y.
-- Proof.
--  intros.
--  rewrite
--    <- (Qmult_1_r x), <- (Qmult_1_r y),
--    <- (Qmult_inv_r (proj1_sig z)), (Qmult_comm (proj1_sig z)),
--    Qmult_assoc, Qmult_assoc...
--  apply Qball_Qmult_r... auto.
--  intro abs. destruct z. simpl in abs.
--  clear H. rewrite abs in q. exact (Qlt_irrefl _ q).
-- Qed.

-- Lemma Qball_opp (e : Q) (x x' : Q):
--  Qball e x x' -> Qball e (-x) (-x').
-- Proof with auto.
--  intros.
--  apply Qball_Qabs.
--  unfold Qminus.
--  rewrite Qopp_involutive.
--  rewrite Qplus_comm.
--  apply Qball_Qabs.
--  apply ball_sym...
-- Qed.

-- From Coq Require Import Qround.

-- Lemma Qfloor_ball q:
--   Qball (1#2) ((Qfloor q # 1) + (1#2)) q.
-- Proof with auto with *.
--  intros.
--  apply Qball_Qabs.
--  simpl.
--  apply Qabs_case; intros.
--  apply Q.Qplus_le_l with ((-1#2)%Q + q).
--  ring_simplify. apply Qfloor_le.
--  pose proof (Qlt_floor q).
--  apply (Qplus_le_l _ _ ((1#2) + (Qfloor q # 1))). ring_simplify.
--  apply Qlt_le_weak. rewrite inject_Z_plus in H0. apply H0.
-- Qed.

-- (** A boolean version of Qball. *)
-- Definition Qball_ex_bool (e:QposInf) (a b:Q) : bool :=
--  match ball_ex_dec _ Qmetric_dec e a b with left _ => true | right _ => false end.

-- #[global]
-- Instance: Proper (QposInfEq ==> @msp_eq _ ==> @msp_eq _ ==> eq) Qball_ex_bool.
-- Proof.
--   intros [ε1|] [ε2|] E1 x1 x2 E2 y1 y2 E3; try easy.
--   unfold Qball_ex_bool.
--   case (ball_ex_dec _ Qmetric_dec ε1 x1 y1); case
   --    (ball_ex_dec _ Qmetric_dec ε2 x2 y2); intros E4 E5; try easy.
--    destruct E4. now eapply ball_wd; eauto; symmetry.
--   destruct E5. now eapply ball_wd; eauto; symmetry.
-- Qed.

-- Lemma Qball_ex_bool_correct (ε : Qpos) x y
--   : Is_true (Qball_ex_bool ε x y) <-> Qball (proj1_sig ε) x y.
-- Proof.
--   split; intros E.
--   apply Is_true_eq_true in E.
--   unfold Qball_ex_bool in E.
--   destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec ε x y).
--   apply b. discriminate.
--   apply Is_true_eq_left. unfold Qball_ex_bool.
--   destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec ε x y).
--   reflexivity. contradiction.
-- Qed.

-- Lemma gball_Qabs (e a b : Q) : ball e a b <-> (Qabs (a - b) <= e).
-- Proof.
--   simpl. unfold Qball.
--   rewrite <- AbsSmall_Qabs. reflexivity.
-- Qed.

-- Lemma Qball_0 : forall a b : Q,
--     Qball 0 a b <-> Qeq a b.
-- Proof.
--   intros.
--   split.
--   - intros. apply Qle_antisym.
--     + apply (Qplus_le_l _ _ (-b)).
--       rewrite Qplus_opp_r. apply H.
--     + rewrite Qle_minus_iff. apply H.
--   - intros. rewrite H.
--     apply Qball_Reflexive.
--     discriminate.
-- Qed.
