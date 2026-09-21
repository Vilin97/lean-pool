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

public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Quantitative weighted Fourier embedding endpoint

The weight is `(1 + ‖ξ‖)^s`. The dimension threshold is the strict inequality
`finrank ℝ E < 2 * (s - k)`. Weighted L² control implies integrable Fourier
moments, with an explicit Cauchy--Schwarz bound, and hence a classical C^k
inverse Fourier transform. These are analytic frequency-space hypotheses,
not a regularity premise. A local weak jet still needs a proved localization
and weak-derivative/Fourier identification before this endpoint applies.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff FourierTransform
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The reciprocal Fourier weight is L² precisely in the range needed here. -/
theorem memLp_reciprocal_fourier_weight {t : ℝ}
    (ht : (Module.finrank ℝ E : ℝ) < 2 * t) :
    MemLp (fun x : E => (1 + ‖x‖) ^ (-t)) 2 volume := by
  have hc : Continuous (fun x : E => (1 + ‖x‖) ^ (-t)) :=
    (show Continuous (fun x : E => 1 + ‖x‖) by fun_prop).rpow_const
      (fun x => Or.inl (ne_of_gt (by positivity)))
  apply (memLp_two_iff_integrable_sq (μ := (volume : Measure E))
    hc.aestronglyMeasurable).mpr
  have hi : Integrable (fun x : E => (1 + ‖x‖) ^ (-(2 * t))) (volume : Measure E) :=
    integrable_one_add_norm ht
  apply hi.congr
  filter_upwards [] with x
  rw [← Real.rpow_mul_natCast (by positivity)]
  congr 1
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise factorization used in the Fourier Cauchy--Schwarz estimate. -/
theorem fourier_moment_le_weight_product (s : ℝ) (j : ℕ) (F : E → ℂ) (x : E) :
    ‖x‖ ^ j * ‖F x‖ ≤ (1 + ‖x‖) ^ (-(s - j)) *
      ((1 + ‖x‖) ^ s * ‖F x‖) := by
  rw [← mul_assoc, ← Real.rpow_add (by positivity)]
  have he : -(s - (j : ℝ)) + s = j := by ring
  rw [he, Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (by linarith : ‖x‖ ≤ 1 + ‖x‖) j) (norm_nonneg _)

/-- Weighted L² Fourier control gives genuine integrability of the j-th moment. -/
theorem integrable_fourier_moment_of_weightedL2
    {F : E → ℂ} (hF : AEStronglyMeasurable F volume) {s : ℝ} (j : ℕ)
    (hs : (Module.finrank ℝ E : ℝ) < 2 * (s - j))
    (hw : MemLp (fun x => (1 + ‖x‖) ^ s * ‖F x‖) 2 volume) :
    Integrable (fun x => ‖x‖ ^ j * ‖F x‖) volume := by
  apply ((memLp_reciprocal_fourier_weight hs).integrable_mul hw).mono'
    ((by fun_prop : AEStronglyMeasurable (fun x : E => ‖x‖ ^ j) volume).mul hF.norm)
  filter_upwards [] with x
  simpa only [Pi.mul_apply, norm_mul, norm_pow, norm_norm] using
    fourier_moment_le_weight_product s j F x

/-- Explicit finite Cauchy--Schwarz bound for every Fourier moment.
The first factor depends only on dimension, measure normalization and s-j. -/
theorem integral_fourier_moment_le_weightedL2
    {F : E → ℂ} (hF : AEStronglyMeasurable F volume) {s : ℝ} (j : ℕ)
    (hs : (Module.finrank ℝ E : ℝ) < 2 * (s - j))
    (hw : MemLp (fun x => (1 + ‖x‖) ^ s * ‖F x‖) 2 volume) :
    (∫ x, ‖x‖ ^ j * ‖F x‖) ≤
      (∫ x : E, ((1 + ‖x‖) ^ (-(s - j))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
      (∫ x, ((1 + ‖x‖) ^ s * ‖F x‖) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hd := memLp_reciprocal_fourier_weight hs
  apply (integral_mono (integrable_fourier_moment_of_weightedL2 hF j hs hw)
    (hd.integrable_mul hw) (fourier_moment_le_weight_product s j F)).trans
  apply integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun x => by positivity))
    (Filter.Eventually.of_forall (fun x => by positivity))
  · simpa using hd
  · simpa using hw

/-- The strict dimension/order threshold yields a C^k inverse Fourier
integral. This theorem constructs classical regularity from weighted L²
frequency data, without assuming continuity of the inverse integral. -/
theorem contDiff_fourierInv_of_weightedL2
    {F : E → ℂ} (hF : AEStronglyMeasurable F volume) {s : ℝ} (k : ℕ)
    (hs : (Module.finrank ℝ E : ℝ) < 2 * (s - k))
    (hw : MemLp (fun x => (1 + ‖x‖) ^ s * ‖F x‖) 2 volume) :
    ContDiff ℝ k (𝓕⁻ F) := by
  have hc : ContDiff ℝ k (𝓕 F) := by
    apply Real.contDiff_fourier
    intro j hj
    have hjk : j ≤ k := by exact_mod_cast hj
    apply integrable_fourier_moment_of_weightedL2 hF j _ hw
    have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
    linarith
  have he : 𝓕⁻ F = fun x => 𝓕 F (-x) := by
    funext x
    exact Real.fourierInv_eq_fourier_neg F x
  rw [he]
  exact hc.comp contDiff_id.neg

/-- Uniform quantitative bound on the inverse Fourier integral. Both right
side factors are finite real integrals under the stated weighted L² hypothesis. -/
theorem norm_fourierInv_le_weightedL2
    {F : E → ℂ} (hF : AEStronglyMeasurable F volume) {s : ℝ}
    (hs : (Module.finrank ℝ E : ℝ) < 2 * s)
    (hw : MemLp (fun x => (1 + ‖x‖) ^ s * ‖F x‖) 2 volume) (x : E) :
    ‖𝓕⁻ F x‖ ≤
      (∫ y : E, ((1 + ‖y‖) ^ (-s)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
      (∫ y, ((1 + ‖y‖) ^ s * ‖F y‖) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hb : ‖𝓕⁻ F x‖ ≤ ∫ y, ‖F y‖ := by
    rw [Real.fourierInv_eq]
    apply (norm_integral_le_integral_norm _).trans
    simp only [Circle.norm_smul]
    exact le_rfl
  apply hb.trans
  simpa using integral_fourier_moment_le_weightedL2 hF 0 (by simpa using hs) hw

end AlmostSchur
