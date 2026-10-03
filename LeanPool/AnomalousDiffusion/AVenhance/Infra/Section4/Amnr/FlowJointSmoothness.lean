/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TimeParameterizedCurve

/-! Actual joint smoothness of a flow from its parameterized integral equation. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- The actual target-time and initial-position flow map is smooth locally
on a short interval. A parameter scaling makes its augmented Volterra
operator invertible; no mixed flow derivative is assumed. -/
theorem amnr_flow_contDiffAt_joint_of_short {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {M : ℝ} (hM : 0 ≤ M) (hstate : ∀ t x, ‖jointSpatialFDeriv b t x‖ ≤ M)
    (s t : ℝ) (x : Vec 2) (hshort : |t - s| * M ≤ 1 / 4) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℝ × Vec 2 => X z.1 z.2 s) (t, x) := by
  let d := t - s
  change |d| * M ≤ 1 / 4 at hshort
  obtain ⟨B₀, hB₀, hB₀b⟩ := exists_global_iteratedFDeriv_bound hb 0
  obtain ⟨B₁, hB₁, hB₁b⟩ := exists_global_iteratedFDeriv_bound hb 1
  let L := B₀ + |d| * B₁
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let α := (4 * (L + 1))⁻¹
  have hα : 0 < α := by dsimp [α]; positivity
  have hαL : |α| * L ≤ 1 / 4 := by
    rw [abs_of_pos hα]
    dsimp [α]
    have hd : 0 < 4 * (L + 1) := by positivity
    rw [inv_mul_eq_div, div_le_iff₀ hd]
    linarith
  let Q := amnrTimeParameterizedCurve hX s d α
  let f := amnrTimeParameterizedField b s d α
  have hf := amnrTimeParameterizedField_contDiff hb s d α
  let V : C(Icc (0 : ℝ) 1, ℝ × Vec 2) →L[ℝ] C(Icc (0 : ℝ) 1, ℝ × Vec 2) :=
    amnrCurveIntegral (by norm_num) 0 ⟨le_rfl, by norm_num⟩
  have hcoeff : ‖amnrCurveJacobianCoefficient f hf (amnrTimeCurve 0 1) V (Q (0, x))‖ < 1 := by
    have hh := amnrCurveJacobianCoefficient_norm_le_along hf (amnrTimeCurve 0 1) V (Q (0, x))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (fun τ => by
        dsimp [Q, amnrTimeParameterizedCurve, amnrTimeCurve]
        simp only [mul_zero, add_zero]
        change ‖amnrStateDerivative f ((τ : ℝ), (0, X (s + (τ : ℝ) * d) x s))‖ ≤ 1 / 2
        have hp := amnrTimeParameterizedField_stateDerivative_norm_le hb s d α τ
          (X (s + (τ : ℝ) * d) x s) hB₀ hB₁ hM
          (by simpa only [norm_iteratedFDeriv_zero, Function.uncurry_apply_pair] using hB₀b (s +
              (τ : ℝ) * d, X (s + (τ : ℝ) * d) x s))
          (by simpa only [norm_iteratedFDeriv_one] using hB₁b (s + (τ : ℝ) * d, X (s + (τ : ℝ) *
              d) x s))
          (hstate _ _) (by rw [abs_of_nonneg τ.property.1]; exact τ.property.2)
        exact hp.trans (by change |d| * M + |α| * L ≤ 1 / 2; linarith))
    have hV : ‖V‖ ≤ 1 := by
      simpa only [sub_zero] using amnrCurveIntegral_norm_le (E := ℝ × Vec 2)
        (a := (0 : ℝ)) (b := 1) (by norm_num) 0 ⟨le_rfl, by norm_num⟩
    exact (hh.trans ((mul_le_mul_of_nonneg_right hV (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq
        (one_mul _))).trans_lt (by norm_num)
  have hQ : ContDiffAt ℝ (⊤ : ℕ∞) Q ((0 : ℝ), x) :=
    amnrCurveResidual_solution_contDiffAt_local hf (amnrTimeCurve 0 1) V
      (amnrTimeParameterizedCurve_continuous hb hX s d α).continuousAt
      (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) 1)).contDiff.contDiffAt
      (amnrTimeParameterizedCurve_residual_eq_const hb hX s d α) hcoeff
  let P : C(Icc (0 : ℝ) 1, ℝ × Vec 2) →L[ℝ] Vec 2 :=
    (ContinuousLinearMap.snd ℝ ℝ (Vec 2)).comp
      (ContinuousMap.evalCLM ℝ (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1))
  let R := fun z : ℝ × Vec 2 => (α⁻¹ * (z.1 - t), z.2)
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := by fun_prop
  have hRx : R (t, x) = ((0 : ℝ), x) := by simp [R]
  have hQr : ContDiffAt ℝ (⊤ : ℕ∞) (P ∘ Q) (R (t, x)) := by
    rw [hRx]
    exact P.contDiff.contDiffAt.comp _ hQ
  have hh := hQr.comp (t, x) hR.contDiffAt
  have he : (P ∘ Q) ∘ R = fun z : ℝ × Vec 2 => X z.1 z.2 s := by
    funext z
    change X (s + 1 * (d + α * (α⁻¹ * (z.1 - t)))) z.2 s = X z.1 z.2 s
    congr 1
    dsimp [d]
    rw [one_mul, ← mul_assoc, mul_inv_cancel₀ hα.ne', one_mul]
    ring
  rwa [he] at hh

end AVenhance.Infra.Section4
