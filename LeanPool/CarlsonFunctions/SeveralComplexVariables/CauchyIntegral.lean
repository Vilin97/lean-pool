/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Polydisc

/-!
# Cauchy's integral formula on a polydisc

The vector-valued iterated Cauchy formula assumes continuity and coordinatewise analyticity
on the closed polydisc. It does not depend on the several-variable Osgood theorem.
-/

@[expose] public section

open Complex Filter Function MeasureTheory Metric Set
open scoped Classical ENNReal NNReal Real Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-! ### Cauchy's formula on a polydisc -/

omit [CompleteSpace E] in
/-- The vector-valued Cauchy kernel of a continuous function is integrable on a torus whenever
the evaluation point lies in the interior polydisc. -/
lemma torusIntegrable_cauchyKernelWithRadii {n : ℕ} {f : (Fin n → ℂ) → E} {c w : Fin n → ℂ} {R : Fin n → ℝ}
    (hR : ∀ i, 0 < R i) (hw : ∀ i, ‖w i - c i‖ < R i)
    (hfc : ContinuousOn f (closedPolydiscWithRadii c R)) :
    TorusIntegrable (fun z => (∏ i, (z i - w i)⁻¹) • f z) c R := by
  have hmaps : MapsTo (torusMap c R)
      (Icc (0 : Fin n → ℝ) fun _ => 2 * π) (closedPolydiscWithRadii c R) :=
    fun θ _ => torusMap_mem_closedPolydiscWithRadii (fun i => (hR i).le) θ
  have hfθ : ContinuousOn (fun θ => f (torusMap c R θ))
      (Icc (0 : Fin n → ℝ) fun _ => 2 * π) :=
    hfc.comp (continuous_torusMapWithRadii c R).continuousOn hmaps
  have hker : ContinuousOn
      (fun θ : Fin n → ℝ => (∏ i, (torusMap c R θ i - w i)⁻¹))
      (Icc (0 : Fin n → ℝ) fun _ => 2 * π) := by
    refine continuousOn_finsetProd _ fun i _ => ?_
    refine ((((continuous_apply i).comp (continuous_torusMapWithRadii c R)).continuousOn).sub
      continuousOn_const).inv₀ ?_
    intro θ _
    exact sub_ne_zero.2 (cauchyKernel_ne_zero_on_torusWithRadii hR (hw i))
  exact (hker.smul hfθ).integrableOn_compact isCompact_Icc

/-- Splitting off the first coordinate factors the finite-product Cauchy kernel. -/
lemma cauchyKernel_cons {n : ℕ} (x : ℂ) (y : Fin n → ℂ) (w : Fin (n + 1) → ℂ) :
    (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - w i)⁻¹) =
      (x - w 0)⁻¹ * ∏ i, (y i - w i.succ)⁻¹ := by
  simp [Fin.prod_univ_succ, mul_comm]

/-- Iterated Cauchy integral formula on a closed polydisc. -/
theorem polydisc_cauchyWithRadii {n : ℕ} {f : (Fin n → ℂ) → E} {c w : Fin n → ℂ} {R : Fin n → ℝ}
    (hR : ∀ i, 0 < R i) (hw : ∀ i, ‖w i - c i‖ < R i)
    (hfc : ContinuousOn f (closedPolydiscWithRadii c R))
    (hfa : ∀ z ∈ closedPolydiscWithRadii c R, ∀ i,
      AnalyticAt ℂ (fun x => f (update z i x)) (z i)) :
    ((2 * π * I : ℂ) ^ n)⁻¹ •
      torusIntegral (fun z => (∏ i, (z i - w i)⁻¹) • f z) c R = f w := by
  induction n with
  | zero =>
    have : w = c := Subsingleton.elim _ _
    subst this
    simp [torusIntegral_dim0]
  | succ n ih =>
    set F : (Fin (n + 1) → ℂ) → E :=
      fun z => (∏ i, (z i - w i)⁻¹) • f z
    have hFint : TorusIntegrable F c R :=
      torusIntegrable_cauchyKernelWithRadii hR hw hfc
    have hx_sphere : ∀ x, x ∈ sphere (c 0) (R 0) →
        x ∈ closedBall (c 0) (R 0) ∧ x ≠ w 0 ∧ ‖x - c 0‖ = R 0 := by
      intro x hx
      have hxR : ‖x - c 0‖ = R 0 := by
        rw [← dist_eq_norm]
        exact mem_sphere.1 hx
      refine ⟨mem_closedBall.2 (by rw [dist_eq_norm, hxR]), ?_, hxR⟩
      intro h
      rw [h] at hxR
      exact (hw 0).not_ge hxR.ge
    have hinter : ∀ x ∈ sphere (c 0) (R 0),
        torusIntegral (fun y => F (Fin.cons x y)) (c ∘ Fin.succ) (R ∘ Fin.succ) =
          (x - w 0)⁻¹ • ((2 * π * I : ℂ) ^ n •
            f (Fin.cons x (w ∘ Fin.succ))) := by
      intro x hx
      obtain ⟨hxcl, hxw, hxR⟩ := hx_sphere x hx
      have hgcont : ContinuousOn (fun y => f (Fin.cons x y))
          (closedPolydiscWithRadii (c ∘ Fin.succ) (R ∘ Fin.succ)) :=
        hfc.comp (continuousOn_const.finCons continuousOn_id)
          (fun y hy => cons_mem_closedPolydiscWithRadii hxcl hy)
      have hga : ∀ y ∈ closedPolydiscWithRadii (c ∘ Fin.succ) (R ∘ Fin.succ), ∀ j,
          AnalyticAt ℂ (fun t => f (Fin.cons x (update y j t))) (y j) := by
        intro y hy j
        have hz := cons_mem_closedPolydiscWithRadii hxcl hy
        simpa [Fin.cons_update] using hfa (Fin.cons x y) hz j.succ
      have hw' : ∀ i : Fin n, ‖w i.succ - c i.succ‖ < R i.succ := fun i => hw i.succ
      have ih' :=
        ih (f := fun y => f (Fin.cons x y)) (c := c ∘ Fin.succ) (w := w ∘ Fin.succ)
          (fun i => hR i.succ) hw' hgcont hga
      have ih_int :
          torusIntegral (fun y => (∏ i, (y i - w i.succ)⁻¹) • f (Fin.cons x y))
            (c ∘ Fin.succ) (R ∘ Fin.succ) =
            (2 * π * I : ℂ) ^ n • f (Fin.cons x (w ∘ Fin.succ)) :=
        ((eq_inv_smul_iff₀ (two_pi_I_pow_ne_zero n)).mp ih'.symm).symm
      have hsmul := torusIntegral_smul (x - w 0)⁻¹
        (fun y => (∏ i, (y i - w i.succ)⁻¹) • f (Fin.cons x y))
        (c ∘ Fin.succ) (R ∘ Fin.succ)
      calc
        torusIntegral (fun y => F (Fin.cons x y)) (c ∘ Fin.succ) (R ∘ Fin.succ)
            = torusIntegral (fun y => (x - w 0)⁻¹ •
                (∏ i, (y i - w i.succ)⁻¹) • f (Fin.cons x y))
                (c ∘ Fin.succ) (R ∘ Fin.succ) := by
              congr 1
              funext y
              simp only [F]
              rw [cauchyKernel_cons x y w, mul_smul]
        _ = (x - w 0)⁻¹ • torusIntegral
              (fun y => (∏ i, (y i - w i.succ)⁻¹) • f (Fin.cons x y))
              (c ∘ Fin.succ) (R ∘ Fin.succ) := hsmul
        _ = (x - w 0)⁻¹ • ((2 * π * I : ℂ) ^ n •
              f (Fin.cons x (w ∘ Fin.succ))) := by rw [ih_int]
    have hcons : Continuous (fun x : ℂ => (Fin.cons x (w ∘ Fin.succ) : Fin (n + 1) → ℂ)) :=
      Continuous.finCons (A := fun _ : Fin (n + 1) => ℂ) continuous_id continuous_const
    have hψcont : ContinuousOn (fun x => f (Fin.cons x (w ∘ Fin.succ)))
        (closedBall (c 0) (R 0)) :=
      hfc.comp hcons.continuousOn fun x hx =>
        cons_mem_closedPolydiscWithRadii hx (fun i _ =>
          mem_closedBall.2 (le_of_lt (by simpa [dist_eq_norm] using hw i.succ)))
    have hψdiff : ∀ x ∈ ball (c 0) (R 0),
        DifferentiableAt ℂ (fun t => f (Fin.cons t (w ∘ Fin.succ))) x := by
      intro x hx
      have hz : Fin.cons x (w ∘ Fin.succ) ∈ closedPolydiscWithRadii c R :=
        cons_mem_closedPolydiscWithRadii (ball_subset_closedBall hx) fun i _ =>
          mem_closedBall.2 (le_of_lt (by simpa [dist_eq_norm] using hw i.succ))
      simpa [Fin.update_cons_zero] using (hfa _ hz 0).differentiableAt
    have hcircle :
        ((2 * π * I : ℂ)⁻¹ •
          ∮ x in C(c 0, R 0), (x - w 0)⁻¹ • f (Fin.cons x (w ∘ Fin.succ))) =
          f (Fin.cons (w 0) (w ∘ Fin.succ)) := by
      have hw0 : w 0 ∈ ball (c 0) (R 0) := by simpa [dist_eq_norm] using hw 0
      simpa using
        two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
          (s := (∅ : Set ℂ)) countable_empty hw0 hψcont fun x hx => hψdiff x hx.1
    have houter :
        torusIntegral F c R =
          (2 * π * I : ℂ) ^ n •
            ∮ x in C(c 0, R 0), (x - w 0)⁻¹ • f (Fin.cons x (w ∘ Fin.succ)) := by
      rw [torusIntegral_succ hFint]
      refine (circleIntegral.integral_congr (hR 0).le fun x hx => hinter x hx).trans ?_
      rw [show (fun x => (x - w 0)⁻¹ • ((2 * π * I : ℂ) ^ n •
            f (Fin.cons x (w ∘ Fin.succ)))) =
          fun x => ((2 * π * I : ℂ) ^ n) • ((x - w 0)⁻¹ •
            f (Fin.cons x (w ∘ Fin.succ))) by
        funext x; simp [smul_smul, mul_comm]]
      rw [circleIntegral.integral_smul]
    have hw_eq : Fin.cons (w 0) (w ∘ Fin.succ) = w := Fin.cons_self_tail w
    rw [← hw_eq, houter, smul_smul]
    convert hcircle using 2
    simp [pow_succ, two_pi_I_pow_ne_zero n]

omit [CompleteSpace E] in
/-- Equal-radius compatibility form of Cauchy-kernel integrability. -/
lemma torusIntegrable_cauchyKernel {n : ℕ} {f : (Fin n → ℂ) → E}
    {c w : Fin n → ℂ} {R : ℝ} (hR : 0 < R) (hw : ∀ i, ‖w i - c i‖ < R)
    (hfc : ContinuousOn f (closedPolydisc c R)) :
    TorusIntegrable (fun z => (∏ i, (z i - w i)⁻¹) • f z) c (fun _ => R) :=
  torusIntegrable_cauchyKernelWithRadii (fun _ => hR) hw hfc

/-- Equal-radius compatibility form of the polydisc Cauchy formula. -/
theorem polydisc_cauchy {n : ℕ} {f : (Fin n → ℂ) → E} {c w : Fin n → ℂ} {R : ℝ}
    (hR : 0 < R) (hw : ∀ i, ‖w i - c i‖ < R)
    (hfc : ContinuousOn f (closedPolydisc c R))
    (hfa : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun x => f (update z i x)) (z i)) :
    ((2 * π * I : ℂ) ^ n)⁻¹ •
      torusIntegral (fun z => (∏ i, (z i - w i)⁻¹) • f z) c (fun _ => R) = f w :=
  polydisc_cauchyWithRadii (fun _ => hR) hw hfc hfa

end SeveralComplexVariables

end
