/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! # A weighted Fourier regularity criterion

This is a global Fourier-side intermediate result, not a local weak-jet
embedding. The missing step is to establish its weighted hypotheses for the
Fourier transform of a localized weak jet and identify the inverse transform
almost everywhere. The inverse-weight calculation follows the proof of
`TemperedDistribution.MemSobolev.fourier_memL1` in pinned Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem memLp_inverse_polynomial_weight {s : ℝ}
    (hs : (Module.finrank ℝ E : ℝ) < 2 * s) :
    MemLp (fun x : E => (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 := by
  rw [MemLp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  · suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
      norm_cast
      simp_rw [ofReal_norm] at h
      simp_rw [← enorm_pow]
      convert h
      rw [← Real.rpow_mul_natCast (by positivity)]
      simp
    apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
    congr
    ring
  · have h : (fun x : E => (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
      fun_prop
    exact h.1.continuous.aestronglyMeasurable

/-- Weighted L² control yields genuine L¹ control above half the dimension. -/
theorem integrable_of_polynomial_weight_memLp {s : ℝ}
    (hs : (Module.finrank ℝ E : ℝ) < 2 * s) {f : E → ℝ}
    (hf : MemLp (fun x => f x * (1 + ‖x‖ ^ 2) ^ (s / 2)) 2) :
    Integrable f := by
  have hp : MemLp (fun x => (f x * (1 + ‖x‖ ^ 2) ^ (s / 2)) *
      (1 + ‖x‖ ^ 2) ^ (-s / 2)) 1 :=
    hf.fun_mul (memLp_inverse_polynomial_weight hs)
  have he : (fun x => (f x * (1 + ‖x‖ ^ 2) ^ (s / 2)) *
      (1 + ‖x‖ ^ 2) ^ (-s / 2)) = f := by
    funext x
    rw [mul_assoc, ← Real.rpow_add (by positivity)]
    ring_nf
    simp
  rw [he] at hp
  exact memLp_one_iff_integrable.mp hp

/-- Quantitative weighted Cauchy--Schwarz estimate; both factors on the right
are finite under the stated hypotheses. -/
theorem eLpNorm_one_le_polynomial_weight {s : ℝ}
    (hs : (Module.finrank ℝ E : ℝ) < 2 * s) {f : E → ℝ}
    (hf : MemLp (fun x => f x * (1 + ‖x‖ ^ 2) ^ (s / 2)) 2) :
    eLpNorm f 1 volume ≤
      eLpNorm (fun x => f x * (1 + ‖x‖ ^ 2) ^ (s / 2)) 2 volume *
      eLpNorm (fun x : E => (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 volume := by
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
    hf.aestronglyMeasurable (memLp_inverse_polynomial_weight hs).aestronglyMeasurable
  have he : (fun x => f x * (1 + ‖x‖ ^ 2) ^ (s / 2)) •
      (fun x : E => (1 + ‖x‖ ^ 2) ^ (-s / 2)) = f := by
    funext x
    change (f x * _) * _ = f x
    rw [mul_assoc, ← Real.rpow_add (by positivity)]
    ring_nf
    simp
  rwa [he] at h

/-- Every weighted Fourier moment through order `k` in L² produces a Cᵏ
inverse Fourier integral. No weak-jet or representative claim is implicit. -/
theorem contDiff_inverseFourier_of_weighted_moments {s : ℝ} {k : ℕ}
    (hs : (Module.finrank ℝ E : ℝ) < 2 * s) (f : E → ℂ)
    (hf : ∀ j : ℕ, j ≤ k → MemLp
      (fun x => (‖x‖ ^ j * ‖f x‖) * (1 + ‖x‖ ^ 2) ^ (s / 2)) 2) :
    ContDiff ℝ k (𝓕⁻ f) := by
  have h : ContDiff ℝ k (𝓕 f) := Real.contDiff_fourier (fun j hj =>
    integrable_of_polynomial_weight_memLp hs (hf j (by exact_mod_cast hj)))
  have he : 𝓕⁻ f = (𝓕 f) ∘ (fun x => -x) := by
    funext x
    exact Real.fourierInv_eq_fourier_neg f x
  rw [he]
  exact h.comp contDiff_neg

end AlmostSchur
