/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFourierSetup
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactSchwartz
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Weak uniqueness for the weighted Fourier representation

Compact smooth functions are Schwartz functions, so a locally integrable
function annihilating every Schwartz test vanishes almost everywhere. Applied
to the weighted conjugate of an `L²` function, this removes the Fourier
Laplacian multiplier away from its single zero at the origin.
-/

@[expose] public section



noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace NavierStokesR3.WeakFourierUniqueness

open ProblemStatement

/-- The real-test fundamental lemma, with multiplication written in `ℂ`. -/
theorem ae_eq_zero_of_integral_real_test_mul_eq_zero
    (h : Space → ℂ) (hh : LocallyIntegrable h (volume : Measure Space))
    (hzero : ∀ g : Space → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      (∫ x : Space, (g x : ℂ) * h x) = 0) :
    h =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hh
  intro g hg hs
  have hsmul : (fun x : Space => g x • h x) =
      (fun x : Space => (g x : ℂ) * h x) := by
    funext x
    apply Complex.ext <;> simp
  rw [hsmul]
  exact hzero g hg hs

/-- A locally integrable function is determined by its Schwartz pairings. -/
theorem ae_eq_zero_of_integral_schwartz_test_mul_eq_zero
    (h : Space → ℂ) (hh : LocallyIntegrable h (volume : Measure Space))
    (hzero : ∀ ψ : Comparison.ComplexTest, (∫ x : Space, h x * ψ x) = 0) :
    h =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_real_test_mul_eq_zero h hh
  intro g hg hs
  have hgC : ContDiff ℝ ∞ (fun x : Space => (g x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hg
  have hsC : HasCompactSupport (fun x : Space => (g x : ℂ)) :=
    hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have htest :=
    hzero (CompactSchwartz.ofCompactSupport (fun x : Space => (g x : ℂ)) hgC hsC)
  change (∫ x : Space, h x * (g x : ℂ)) = 0 at htest
  simpa only [mul_comm] using htest

/-- Polynomial weights preserve the local integrability of an `L²` function. -/
theorem locallyIntegrable_weighted_star (q : Lp ℂ 2 (volume : Measure Space)) :
    LocallyIntegrable (fun ξ : Space =>
      star (q ξ) * (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ))
      (volume : Measure Space) := by
  have hqstar : LocallyIntegrable (fun ξ : Space => star (q ξ))
      (volume : Measure Space) :=
    (Complex.conjCLE.toContinuousLinearMap.comp_memLp q).locallyIntegrable (by norm_num)
  have hw : Continuous (fun ξ : Space => (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.continuous.comp
      ((continuous_const.add (continuous_norm.pow 2)).pow 2)
  have hn : Continuous (fun ξ : Space => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.continuous.comp (continuous_norm.pow 2)
  exact locallyIntegrableOn_univ.mp
    (((hqstar.locallyIntegrableOn univ).mul_continuousOn hw.continuousOn
      isClosed_univ.isLocallyClosed).mul_continuousOn hn.continuousOn
      isClosed_univ.isLocallyClosed)

/-- If the weighted Fourier Laplacian pairings of an `L²` function vanish,
the function is zero in `L²`. No regularity beyond membership in `L²` is used. -/
theorem eq_zero_of_integral_weight_normSq_test_eq_zero
    (q : Lp ℂ 2 (volume : Measure Space))
    (hq : ∀ ψ : Comparison.ComplexTest,
      (∫ ξ : Space, star (q ξ) * (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) *
        ((‖ξ‖ ^ 2 : ℝ) : ℂ) * ψ ξ) = 0) :
    q = 0 := by
  have hz : (fun ξ : Space =>
      star (q ξ) * (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) * ((‖ξ‖ ^ 2 : ℝ) : ℂ))
      =ᵐ[volume] 0 :=
    ae_eq_zero_of_integral_schwartz_test_mul_eq_zero _
      (locallyIntegrable_weighted_star q) hq
  have hne : ∀ᵐ ξ : Space ∂volume, ξ ≠ 0 := by
    simp [ae_iff]
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hz, hne] with ξ hξ hξne
  have hwR : (1 + ‖ξ‖ ^ 2) ^ 2 ≠ (0 : ℝ) :=
    pow_ne_zero 2 (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)))
  have hw : (((1 + ‖ξ‖ ^ 2) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simpa only [ne_eq, Complex.ofReal_eq_zero] using hwR
  have hnR : ‖ξ‖ ^ 2 ≠ (0 : ℝ) :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hξne)
  have hn : ((‖ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simpa only [ne_eq, Complex.ofReal_eq_zero] using hnR
  have hs : star (q ξ) = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hξ).resolve_right hn)).resolve_right hw
  simpa only [star_star, star_zero, Pi.zero_apply] using congrArg star hs

end NavierStokesR3.WeakFourierUniqueness
