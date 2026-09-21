/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.HilbertWeakLimit
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Function.L2Space

/-! # The weak derivative criterion from bounded actual difference quotients -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology Convolution

namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual directional translation difference quotient as an L² class. -/
def directionalDifferenceQuotient (u : Lp ℝ 2 (volume : Measure E)) (v : E) (h : ℝ) :
    Lp ℝ 2 (volume : Measure E) :=
  h⁻¹ • (Lp.compMeasurePreserving (fun x => x + h • v)
    (measurePreserving_add_right volume (h • v)) u - u)

/-- The L² class has the expected pointwise difference-quotient representative. -/
theorem directionalDifferenceQuotient_ae_eq
    (u : Lp ℝ 2 (volume : Measure E)) (v : E) (h : ℝ) :
    directionalDifferenceQuotient u v h =ᵐ[volume]
      (fun x => h⁻¹ * (u (x + h • v) - u x)) := by
  let T := Lp.compMeasurePreserving (fun x : E => x + h • v)
    (measurePreserving_add_right volume (h • v)) u
  filter_upwards [Lp.coeFn_smul h⁻¹ (T - u), Lp.coeFn_sub T u,
    Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume (h • v))]
    with x hx hs ht
  change (h⁻¹ • (T - u)) x = _
  rw [hx]
  change h⁻¹ * (T - u) x = _
  rw [hs]
  change h⁻¹ * (T x - u x) = _
  rw [ht]
  rfl

/-- Differentiate a translated test pairing without differentiating the L² function. -/
theorem hasDerivAt_translated_test_pairing
    {u : E → ℝ} (hu : LocallyIntegrable u volume) {φ : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (v : E) :
    HasDerivAt (fun h : ℝ => ∫ y, u y * φ (y - h • v))
      (-(∫ y, u y * fderiv ℝ φ y v)) 0 := by
  let ρ : E → ℝ := fun y => φ (-y)
  have hρ : ContDiff ℝ 1 ρ := hφ.comp contDiff_id.neg
  have hcρ : HasCompactSupport ρ := hcφ.comp_homeomorph (Homeomorph.neg E)
  have hdρ (y : E) : fderiv ℝ ρ (-y) v = -(fderiv ℝ φ y v) := by
    have hd := (hφ.differentiable (by simp) (-(-y))).hasFDerivAt
    have hh := hd.comp (-y) (hasFDerivAt_id (-y)).neg
    simpa [ρ, Function.comp_def] using congrArg (fun T : E →L[ℝ] ℝ => T v) hh.fderiv
  have hd := hcρ.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hu hρ 0
  have hs : HasDerivAt (fun h : ℝ => h • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hd' : HasFDerivAt (u ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ)
      ((u ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR E, volume] fderiv ℝ ρ) 0)
      ((0 : ℝ) • v) := by simpa using hd
  have hh := hd'.comp_hasDerivAt 0 hs
  have he : ((u ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR E, volume]
      fderiv ℝ ρ) 0) v = -(∫ y, u y * fderiv ℝ φ y v) := by
    rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hu
      (hcρ.fderiv ℝ) (hρ.continuous_fderiv (by simp))]
    change (∫ y, u y * fderiv ℝ ρ (0 - y) v) = _
    simp_rw [zero_sub, hdρ, mul_neg]
    exact integral_neg _
  rw [he] at hh
  have heq : (fun h : ℝ => ∫ y, u y * φ (y - h • v)) =
      (fun h : ℝ => (u ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) (h • v)) := by
    funext h
    simp [convolution_def, ρ, neg_sub]
  rw [heq]
  exact hh

/-- Pairing the actual L² difference quotient with a test is the scalar
difference quotient of the translated test pairing. -/
theorem inner_directionalDifferenceQuotient
    (u : Lp ℝ 2 (volume : Measure E)) (v : E) (h : ℝ)
    {φ : E → ℝ} (hφ : MemLp φ 2 (volume : Measure E)) :
    inner ℝ (directionalDifferenceQuotient u v h) (hφ.toLp φ) =
      h⁻¹ * ((∫ y, u y * φ (y - h • v)) - ∫ y, u y * φ y) := by
  let T := Lp.compMeasurePreserving (fun x : E => x + h • v)
    (measurePreserving_add_right volume (h • v)) u
  have hpair (f : Lp ℝ 2 (volume : Measure E)) :
      inner ℝ f (hφ.toLp φ) = ∫ y, f y * φ y := by
    simp only [L2.inner_def, RCLike.inner_apply, conj_trivial]
    apply integral_congr_ae
    filter_upwards [hφ.coeFn_toLp] with y hy
    simp [hy, mul_comm]
  change inner ℝ (h⁻¹ • (T - u)) (hφ.toLp φ) = _
  rw [real_inner_smul_left, inner_sub_left, hpair, hpair]
  congr 2
  calc
    (∫ y, T y * φ y) = ∫ y, u (y + h • v) * φ y := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_compMeasurePreserving u
        (measurePreserving_add_right volume (h • v))] with y hy
      rw [hy]
      rfl
    _ = ∫ y, u y * φ (y - h • v) := by
      simpa using integral_add_right_eq_self (fun y => u y * φ (y - h • v)) (h • v)

/-- The test pairings of actual difference quotients converge to the negative
distributional derivative pairing. -/
theorem tendsto_inner_directionalDifferenceQuotient
    (u : Lp ℝ 2 (volume : Measure E)) (v : E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    Tendsto (fun h => inner ℝ (directionalDifferenceQuotient u v h)
      ((hφ.continuous.memLp_of_hasCompactSupport hcφ : MemLp φ 2 volume).toLp φ))
      (𝓝[≠] 0) (𝓝 (-(∫ y, u y * fderiv ℝ φ y v))) := by
  have hd := hasDerivAt_translated_test_pairing
    (Lp.memLp u |>.locallyIntegrable (by norm_num)) hφ hcφ v
  simpa only [inner_directionalDifferenceQuotient, zero_add, zero_smul, sub_zero,
    smul_eq_mul] using hd.tendsto_slope_zero

/-- A uniform bound on the actual directional difference quotients yields a
genuine L² weak derivative with the same norm bound. Tests may be compactly
supported C¹ functions. -/
theorem exists_weakDerivative_of_bounded_differenceQuotient
    (u : Lp ℝ 2 (volume : Measure E)) (v : E) (C : ℝ)
    (hbound : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖directionalDifferenceQuotient u v h‖ ≤ C) :
    ∃ g : Lp ℝ 2 (volume : Measure E), ‖g‖ ≤ C ∧
      ∀ (φ : E → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
        (∫ y, u y * fderiv ℝ φ y v) = -(∫ y, g y * φ y) := by
  obtain ⟨g, hg, hlim⟩ := exists_hilbert_pairing_limit (𝓝[≠] (0 : ℝ))
    (directionalDifferenceQuotient u v) C hbound
  refine ⟨g, hg, ?_⟩
  intro φ hφ hcφ
  have hφLp : MemLp φ 2 (volume : Measure E) :=
    hφ.continuous.memLp_of_hasCompactSupport hcφ
  have hh := hlim (hφLp.toLp φ) _ (tendsto_inner_directionalDifferenceQuotient u v hφ hcφ)
  have hp : inner ℝ g (hφLp.toLp φ) = ∫ y, g y * φ y := by
    simp only [L2.inner_def, RCLike.inner_apply, conj_trivial]
    apply integral_congr_ae
    filter_upwards [hφLp.coeFn_toLp] with y hy
    simp [hy, mul_comm]
  rw [hp] at hh
  linarith

/-- A small-radius version of the criterion, convenient for difference-quotient
estimates obtained after applying a compactly supported cutoff. -/
theorem exists_weakDerivative_of_differenceQuotient_bound_on_ball
    (u : Lp ℝ 2 (volume : Measure E)) (v : E) (C δ : ℝ) (hδ : 0 < δ)
    (hbound : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      ‖directionalDifferenceQuotient u v h‖ ≤ C) :
    ∃ g : Lp ℝ 2 (volume : Measure E), ‖g‖ ≤ C ∧
      ∀ (φ : E → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
        (∫ y, u y * fderiv ℝ φ y v) = -(∫ y, g y * φ y) := by
  apply exists_weakDerivative_of_bounded_differenceQuotient u v C
  have hn : ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact hh
  have hr : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < δ := by
    have hh : Metric.ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hδ
    filter_upwards [nhdsWithin_le_nhds hh] with h hh
    simpa [Metric.mem_ball, Real.dist_eq] using hh
  filter_upwards [hn, hr] with h hn hr
  exact hbound h hn hr

end AlmostSchur
