/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Local mollification of a function with zero weak derivatives

Source APIs: Mathlib `Analysis/Calculus/ContDiff/Convolution.lean`
(`HasCompactSupport.hasFDerivAt_convolution_right`) and
`Analysis/Convolution.lean` (`convolution_precompR_apply`).
Only the mollification is differentiated classically; no regularity of `u` is assumed.
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric
open scoped ContDiff Convolution

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Interior localization of the support of a translated reflected kernel. -/
theorem translated_kernel_tsupport_subset {ρ : E → ℝ} {a x : E} {R r ε : ℝ}
    (hρ : tsupport ρ ⊆ closedBall 0 ε) (hx : x ∈ ball a r) (hε : ε < R - r) :
    tsupport (fun y => ρ (x - y)) ⊆ closedBall a R := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  have hy' := hρ (subset_tsupport ρ hy)
  have hd : dist y x ≤ ε := by
    simpa only [mem_closedBall, dist_zero_right, dist_eq_norm_sub, norm_sub_rev, sub_zero] using hy'
  have hx' : dist x a < r := hx
  exact (dist_triangle y x a).trans (by linarith)

/-- Weakly vanishing directional derivatives force every directional evaluation of the
derivative of an interior mollification to vanish. The weak hypothesis uses actual Fréchet
derivatives of smooth tests, evaluated in arbitrary directions. -/
theorem fderiv_indicator_convolution_eq_zero
    {U : Set E} {u ρ : E → ℝ} {a : E} {R r ε : ℝ}
    (hu : LocallyIntegrableOn u U volume)
    (hweak : ∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∀ v : E, ∫ y, u y * fderiv ℝ φ y v = 0)
    (hball : closedBall a R ⊆ U)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hsρ : tsupport ρ ⊆ closedBall 0 ε) (hε : ε < R - r)
    {x : E} (hx : x ∈ ball a r) :
    fderiv ℝ ((closedBall a R).indicator u ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) x = 0 := by
  let f := (closedBall a R).indicator u
  have hf : LocallyIntegrable f volume :=
    ((integrable_indicator_iff isClosed_closedBall.measurableSet).2
      (hu.integrableOn_compact_subset hball (isCompact_closedBall a R))).locallyIntegrable
  let φ : E → ℝ := fun y => ρ (x - y)
  have hφ : ContDiff ℝ ∞ φ := hρ.comp (contDiff_const.sub contDiff_id : ContDiff ℝ ∞ (fun y : E => x - y))
  have hcφ : HasCompactSupport φ := hcρ.comp_homeomorph (Homeomorph.subLeft x)
  have hsφ : tsupport φ ⊆ closedBall a R := translated_kernel_tsupport_subset hsρ hx hε
  have hdφ (y v : E) : fderiv ℝ φ y v = -(fderiv ℝ ρ (x - y) v) := by
    have hd := (hρ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    simpa [φ, Function.comp_def, Pi.sub_def] using congrArg (fun T : E →L[ℝ] ℝ => T v) hd.fderiv
  rw [(hcρ.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hf (hρ.of_le (by simp)) x).fderiv]
  ext v
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf (hcρ.fderiv ℝ)
    ((hρ.of_le (by simp) : ContDiff ℝ 1 ρ).continuous_fderiv (by simp))]
  change (∫ y, f y * fderiv ℝ ρ (x - y) v) = 0
  have heq : (∫ y, f y * fderiv ℝ ρ (x - y) v) =
      -(∫ y, u y * fderiv ℝ φ y v) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ closedBall a R
    · simp [f, hy, hdφ]
    · have hz : fderiv ℝ φ y = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hy (hsφ (tsupport_fderiv_subset ℝ h)))
      have hz' : fderiv ℝ ρ (x - y) v = 0 := by
        have := hdφ y v
        simp [hz] at this
        exact this
      simp [f, hy, hz, hz']
  rw [heq, hweak φ hφ hcφ (hsφ.trans hball) v, neg_zero]

end AlmostSchur
