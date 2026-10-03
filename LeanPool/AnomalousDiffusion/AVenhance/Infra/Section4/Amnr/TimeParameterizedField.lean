/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CurveLocalImplicit

/-! Encode target-time variation as an actual constant state parameter. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- The actual field for an ODE on a fixed unit time interval. Its first
state coordinate stays constant and determines the actual target time. -/
def amnrTimeParameterizedField (b : ℝ → Vec 2 → Vec 2) (s d α : ℝ)
    (z : ℝ × (ℝ × Vec 2)) : ℝ × Vec 2 :=
  (0, (d + α * z.2.1) • b (s + z.1 * (d + α * z.2.1)) z.2.2)

/-- The augmented primitive field is smooth by ordinary joint composition. -/
theorem amnrTimeParameterizedField_contDiff {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) (s d α : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrTimeParameterizedField b s d α) := by
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (ℝ × Vec 2) => d + α * z.2.1) := by fun_prop
  have hT : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (ℝ × Vec 2) => s + z.1 * (d + α * z.2.1)) := by
      fun_prop
  exact contDiff_const.prodMk (hD.smul (hb.smooth.comp (hT.prodMk (contDiff_snd.snd))))

/-- The actual state derivative at zero parameter is an explicit operator
with the small time-interval Jacobian on its spatial diagonal. -/
theorem amnrTimeParameterizedField_stateDerivative_apply {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) (s d α τ : ℝ) (x : Vec 2) (h : ℝ × Vec 2) :
    amnrStateDerivative (amnrTimeParameterizedField b s d α) (τ, ((0 : ℝ), x)) h =
      (0, (α * h.1) • b (s + τ * d) x +
        d • fderiv ℝ (Function.uncurry b) (s + τ * d, x) (τ * (α * h.1), h.2)) := by
  let D : (ℝ × Vec 2) → ℝ := fun y => d + α * y.1
  let T : (ℝ × Vec 2) → ℝ := fun y => s + τ * (d + α * y.1)
  have hD : HasFDerivAt D (α • ContinuousLinearMap.fst ℝ ℝ (Vec 2)) ((0 : ℝ), x) := by
    exact ((ContinuousLinearMap.fst ℝ ℝ (Vec 2)).hasFDerivAt.const_smul α).const_add d
  have hT : HasFDerivAt T (τ • (α • ContinuousLinearMap.fst ℝ ℝ (Vec 2))) ((0 : ℝ), x) :=
    (hD.const_smul τ).const_add s
  have hb' : HasFDerivAt (Function.uncurry b)
      (fderiv ℝ (Function.uncurry b) (s + τ * d, x))
      (T ((0 : ℝ), x), (ContinuousLinearMap.snd ℝ ℝ (Vec 2)) ((0 : ℝ), x)) := by
    simpa [T, D] using (hb.smooth.differentiable (by simp) (s + τ * d, x)).hasFDerivAt
  have hpair := hT.prodMk (ContinuousLinearMap.snd ℝ ℝ (Vec 2)).hasFDerivAt
  have hc := hb'.comp ((0 : ℝ), x) hpair
  have hzero : HasFDerivAt (fun _ : ℝ × Vec 2 => (0 : ℝ)) 0 ((0 : ℝ), x) :=
    hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) ((0 : ℝ), x)
  have hF := hzero.prodMk (hD.smul hc)
  have he : (fun y : ℝ × Vec 2 => amnrTimeParameterizedField b s d α (τ, y)) =
      fun y => (0, D y • b (T y) y.2) := rfl
  have hs := (amnrTimeParameterizedField_contDiff hb s d α).differentiable (by simp) (τ, ((0 : ℝ),
      x))
  have hrestriction := hs.hasFDerivAt.comp ((0 : ℝ), x) (hasFDerivAt_prodMk_right τ ((0 : ℝ), x))
  change HasFDerivAt (fun y => amnrTimeParameterizedField b s d α (τ, y))
    (amnrStateDerivative (amnrTimeParameterizedField b s d α) (τ, ((0 : ℝ), x))) ((0 : ℝ), x)
        at hrestriction
  rw [he] at hrestriction
  have hd := hrestriction.unique hF
  change amnrStateDerivative (amnrTimeParameterizedField b s d α) (τ, ((0 : ℝ), x)) = _ at hd
  rw [hd]
  simp [D, T, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smulRight_apply,
    add_comm, ContinuousLinearMap.comp_apply]

/-- Actual primitive bounds make the augmented state Jacobian small. The
parameter column can be made small by choosing its scale `α`. -/
theorem amnrTimeParameterizedField_stateDerivative_norm_le {b : ℝ → Vec 2 → Vec 2}
    (hb : SmoothPeriodicField b) (s d α τ : ℝ) (x : Vec 2)
    {B₀ B₁ M : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hM : 0 ≤ M)
    (hvel : ‖b (s + τ * d) x‖ ≤ B₀)
    (hjoint : ‖fderiv ℝ (Function.uncurry b) (s + τ * d, x)‖ ≤ B₁)
    (hstate : ‖jointSpatialFDeriv b (s + τ * d) x‖ ≤ M) (hτ : |τ| ≤ 1) :
    ‖amnrStateDerivative (amnrTimeParameterizedField b s d α) (τ, ((0 : ℝ), x))‖ ≤
      |d| * M + |α| * (B₀ + |d| * B₁) := by
  let J := fderiv ℝ (Function.uncurry b) (s + τ * d, x)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  rw [amnrTimeParameterizedField_stateDerivative_apply hb]
  simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  have hh₁ : |h.1| ≤ ‖h‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le h
  have hh₂ : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
  have htime : ‖J (τ * (α * h.1), 0)‖ ≤ B₁ * (|α| * ‖h‖) := by
    have he : ‖(τ * (α * h.1), (0 : Vec 2))‖ ≤ |α| * ‖h‖ := by
      simp only [Prod.norm_def, norm_zero, Real.norm_eq_abs, abs_mul, max_eq_left (by positivity :
          0 ≤ |τ| * (|α| * |h.1|))]
      exact (mul_le_mul hτ (mul_le_mul_of_nonneg_left hh₁ (abs_nonneg α))
        (by positivity) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
    exact (J.le_opNorm _).trans (mul_le_mul hjoint he (norm_nonneg _) hB₁)
  have hspace : ‖J (0, h.2)‖ ≤ M * ‖h‖ := by
    change ‖jointSpatialFDeriv b (s + τ * d) x h.2‖ ≤ _
    exact ((jointSpatialFDeriv b (s + τ * d) x).le_opNorm _).trans
      (mul_le_mul hstate hh₂ (norm_nonneg _) hM)
  have hsplit : J (τ * (α * h.1), h.2) = J (τ * (α * h.1), 0) + J (0, h.2) := by
    rw [← map_add]
    congr 1
    simp
  have hc : ‖J (τ * (α * h.1), h.2)‖ ≤ B₁ * (|α| * ‖h‖) + M * ‖h‖ := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add htime hspace)
  calc
    _ ≤ ‖(α * h.1) • b (s + τ * d) x‖ + ‖d • J (τ * (α * h.1), h.2)‖ := norm_add_le _ _
    _ ≤ (|α| * ‖h‖) * B₀ + |d| * (B₁ * (|α| * ‖h‖) + M * ‖h‖) := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hh₁ (abs_nonneg α)) hvel
        (norm_nonneg _) (by positivity)) (mul_le_mul_of_nonneg_left hc (abs_nonneg d))
    _ = _ := by
      change |α| * ‖h‖ * B₀ + |d| * (B₁ * (|α| * ‖h‖) + M * ‖h‖) =
        (|d| * M + |α| * (B₀ + |d| * B₁)) * ‖h‖
      ring

end AVenhance.Infra.Section4
