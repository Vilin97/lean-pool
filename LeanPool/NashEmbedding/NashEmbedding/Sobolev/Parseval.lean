/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Periodization

/-!
# Parseval's identity for continuous periodic functions

For `f : ℝⁿ → ℂ` continuous and `2πℤⁿ`-periodic,
    ∑_{m ∈ ℤⁿ} |ĉ_m|² = (2π)⁻ⁿ ∫_{[0,2π]ⁿ} |f|²,
where `ĉ_m = stdFourierCoeff n f m = (2π)⁻ⁿ ∫_{[0,2π]ⁿ} f e^{-i m·θ}`.

Route: `toUnitTorusCM n f` is a continuous function on Mathlib's `UnitAddTorus (Fin n)`;
its Mathlib Fourier coefficients are `stdFourierCoeff n f` (`mFourierCoeff_toUnitTorusCM`);
Mathlib's `hasSum_sq_mFourierCoeff` on `L²` (via `mFourierCoeff_toLp`) gives the identity
with the torus integral of `|f|²`, which `integral_periodCube_eq_torus` converts to the
cube integral.
-/

open scoped BigOperators
open Real MeasureTheory

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

-- Mathlib's Fourier theory on `UnitAddTorus` normalises `ℝ/ℤ` to have total volume `1`;
-- we bring that measure-space structure (and its basic properties) into scope here.
attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The volume measure on the unit torus is the product of the Haar measures on `ℝ/ℤ`. -/
lemma volume_unitAddTorus :
    (volume : Measure (UnitAddTorus (Fin n)))
      = Measure.pi fun _ : Fin n => AddCircle.haarAddCircle := rfl

/-- The squared norm of the descent of `f` is the descent of the squared norm of `f`. -/
lemma toUnitTorusFun_normSq (f : (Fin n → ℝ) → ℂ) (z : UnitAddTorus (Fin n)) :
    toUnitTorusFun n (fun θ => ((‖f θ‖ ^ 2 : ℝ) : ℂ)) z
      = ((‖toUnitTorusFun n f z‖ ^ 2 : ℝ) : ℂ) := rfl

/-- The `L²` norm of the descent of `f` to the unit torus, in terms of the cube integral. -/
lemma integral_normSq_toUnitTorusCM {f : (Fin n → ℝ) → ℂ} (hf : Continuous f)
    (hper : IsPeriodic2Pi f) :
    ∫ z, ‖toUnitTorusFun n f z‖ ^ 2 ∂(Measure.pi fun _ : Fin n => AddCircle.haarAddCircle)
      = ((2 * π) ^ n)⁻¹
          * ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)), ‖f θ‖ ^ 2 := by
  have hgc : Continuous fun θ : Fin n → ℝ => ((‖f θ‖ ^ 2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hf.norm.pow 2)
  have hgper : IsPeriodic2Pi fun θ : Fin n → ℝ => ((‖f θ‖ ^ 2 : ℝ) : ℂ) := by
    intro x k
    simp only [hper x k]
  have hkey := integral_periodCube_eq_torus hgc hgper
  simp_rw [toUnitTorusFun_normSq] at hkey
  rw [integral_complex_ofReal, integral_complex_ofReal, Complex.real_smul] at hkey
  have hpow : ((0 : ℝ) < (2 * π) ^ n) := by positivity
  have hreal :
      (∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)), ‖f θ‖ ^ 2)
        = (2 * π) ^ n
            * ∫ z, ‖toUnitTorusFun n f z‖ ^ 2
                ∂(Measure.pi fun _ : Fin n => AddCircle.haarAddCircle) := by
    exact_mod_cast hkey
  rw [hreal, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpow), one_mul]

/-- **Parseval.** For continuous `2πℤⁿ`-periodic `f`,
  `∑ m, ‖stdFourierCoeff n f m‖² = (2π)⁻ⁿ ∫_{[0,2π]ⁿ} ‖f θ‖²` (as a `HasSum`). -/
theorem parseval_stdFourierCoeff {f : (Fin n → ℝ) → ℂ} (hf : Continuous f)
    (hper : IsPeriodic2Pi f) :
    HasSum (fun m : Fin n → ℤ => ‖stdFourierCoeff n f m‖ ^ 2)
      (((2 * π) ^ n)⁻¹ * ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)), ‖f θ‖ ^ 2) := by
  have hs := UnitAddTorus.hasSum_sq_mFourierCoeff
    ((toUnitTorusCM n f hf hper).toLp 2 volume ℂ)
  simp only [UnitAddTorus.mFourierCoeff_toLp, mFourierCoeff_toUnitTorusCM hf hper] at hs
  have hint : ∫ t, ‖((toUnitTorusCM n f hf hper).toLp 2 volume ℂ :
        UnitAddTorus (Fin n) → ℂ) t‖ ^ 2
      = ∫ t, ‖toUnitTorusFun n f t‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [(toUnitTorusCM n f hf hper).coeFn_toLp (p := 2)
      (μ := (volume : Measure (UnitAddTorus (Fin n)))) (𝕜 := ℂ)] with t ht
    rw [ht]
    rfl
  rw [hint, volume_unitAddTorus, integral_normSq_toUnitTorusCM hf hper] at hs
  exact hs

/-- Parseval in one variable: `∑ m, ‖ĉ_m‖² = (2π)⁻¹ ∫_{[0,2π]} ‖f‖²`. -/
theorem parseval_stdFourierCoeff_one {f : (Fin 1 → ℝ) → ℂ} (hf : Continuous f)
    (hper : IsPeriodic2Pi f) :
    HasSum (fun m : Fin 1 → ℤ => ‖stdFourierCoeff 1 f m‖ ^ 2)
      ((2 * π)⁻¹ * ∫ θ in Set.Icc (0 : Fin 1 → ℝ) (2 * π • (1 : Fin 1 → ℝ)), ‖f θ‖ ^ 2) := by
  simpa using parseval_stdFourierCoeff hf hper

end NashEmbedding.Sobolev

end
