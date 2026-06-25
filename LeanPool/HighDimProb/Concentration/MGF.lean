/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Concentration.MomentImplications
import Mathlib.Probability.Moments.SubGaussian

/-!
# MGF-to-tail concentration bridges

This file starts the MGF branch of the scalar subGaussian implication graph.
The existing `CenteredSubGaussianMGF` predicate wraps Mathlib's real-valued
`HasSubgaussianMGF`; the auxiliary lintegral predicate below is a
proof-friendly ENNReal form for HighDimProb tail probabilities.

Verified Wikipedia references:
* Moment generating function: https://en.wikipedia.org/wiki/Moment-generating_function
* Chernoff bound: https://en.wikipedia.org/wiki/Chernoff_bound
-/

namespace HighDimProb

open MeasureTheory

open scoped ENNReal

noncomputable section

/--
Proof-friendly centered MGF formulation using `lintegral`.

Formula reference: the moment-generating function has the form
`M_X(lambda) = E[exp(lambda * X)]`; see
https://en.wikipedia.org/wiki/Moment-generating_function

The bound is intentionally stated with `exp (K^2 * lambda^2)`, matching the
book-style convention used by the Chernoff wrapper below.  Mathlib's
`HasSubgaussianMGF` convention is slightly stronger for the same `K`, with a
`1/2` in the exponent.
-/
def CenteredSubGaussianMGFLIntegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  IsRealRandomVariable P X ∧
    0 < K ∧
      ∀ lambda : ℝ,
        (∫⁻ ω, ENNReal.ofReal (Real.exp (lambda * X ω)) ∂P) ≤
          ENNReal.ofReal (Real.exp (K ^ 2 * lambda ^ 2))

/--
The existing Mathlib-backed MGF predicate implies the lintegral MGF predicate
when measurability of `X` is supplied in the HighDimProb form.
-/
theorem centeredSubGaussianMGFLIntegral_of_centeredSubGaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X)
    (hMGF : CenteredSubGaussianMGF P X K) :
    CenteredSubGaussianMGFLIntegral P X K := by
  refine ⟨hX, hMGF.1, ?_⟩
  intro lambda
  have h_nonneg : 0 ≤ᵐ[P] fun ω => Real.exp (lambda * X ω) :=
    ae_of_all P fun _ => (Real.exp_pos _).le
  have h_lintegral :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (lambda * X ω)) ∂P) =
        ENNReal.ofReal (ProbabilityTheory.mgf X P lambda) := by
    rw [ProbabilityTheory.mgf]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hMGF.2.integrable_exp_mul lambda) h_nonneg).symm
  have h_mgf :
      ProbabilityTheory.mgf X P lambda ≤
        Real.exp (K ^ 2 * lambda ^ 2) := by
    have h_half :
        (K ^ 2 : ℝ) * lambda ^ 2 / 2 ≤ K ^ 2 * lambda ^ 2 := by
      nlinarith [sq_nonneg K, sq_nonneg lambda]
    exact (hMGF.2.mgf_le lambda).trans (Real.exp_le_exp.mpr h_half)
  rw [h_lintegral]
  exact ENNReal.ofReal_le_ofReal h_mgf

private lemma ofReal_exp_div_exp_eq_ofReal_exp_sub (a b : ℝ) :
    ENNReal.ofReal (Real.exp a) / ENNReal.ofReal (Real.exp b) =
      ENNReal.ofReal (Real.exp (a - b)) := by
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos b)]
  apply congrArg ENNReal.ofReal
  rw [Real.exp_sub]

/--
One-sided upper-tail Chernoff bound from the lintegral centered MGF predicate.

Formula reference: Chernoff applies Markov to `exp(lambda * X)` and optimizes
`M_X(lambda) * exp(-lambda * t)`; see
https://en.wikipedia.org/wiki/Chernoff_bound

The denominator `4 * K^2` matches the looser book-style convention
`E exp(lambda X) <= exp(K^2 lambda^2)`.
-/
theorem upperTailProb_le_exp_neg_sq_of_centeredSubGaussianMGFLIntegral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {K t : ℝ}
    (hMGF : CenteredSubGaussianMGFLIntegral P X K) (ht : 0 ≤ t) :
    upperTailProb P X t ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * K ^ 2)))) := by
  rcases hMGF with ⟨hX, hK, hbound⟩
  let lambda : ℝ := t / (2 * K ^ 2)
  have hKsq_pos : 0 < K ^ 2 := sq_pos_of_pos hK
  have hden_pos : 0 < 2 * K ^ 2 := mul_pos (by norm_num) hKsq_pos
  have hlambda_nonneg : 0 ≤ lambda := by
    exact div_nonneg ht hden_pos.le
  let f : Ω → ENNReal := fun ω => ENNReal.ofReal (Real.exp (lambda * X ω))
  have h_meas : AEMeasurable f P := by
    have h_real : Measurable fun ω => Real.exp (lambda * X ω) :=
      (hX.const_mul lambda).exp
    exact h_real.aemeasurable.ennreal_ofReal
  have h_threshold_ne_zero :
      ENNReal.ofReal (Real.exp (lambda * t)) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h_markov :
      P {ω | ENNReal.ofReal (Real.exp (lambda * t)) ≤ f ω} ≤
        (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp (lambda * t)) :=
    MeasureTheory.meas_ge_le_lintegral_div h_meas h_threshold_ne_zero ENNReal.ofReal_ne_top
  have h_event :
      upperTailEvent X t ⊆
        {ω | ENNReal.ofReal (Real.exp (lambda * t)) ≤ f ω} := by
    intro ω hω
    have hmul : lambda * t ≤ lambda * X ω :=
      mul_le_mul_of_nonneg_left hω hlambda_nonneg
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hmul)
  calc
    upperTailProb P X t
        ≤ P {ω | ENNReal.ofReal (Real.exp (lambda * t)) ≤ f ω} :=
            measure_mono h_event
    _ ≤ (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp (lambda * t)) := h_markov
    _ ≤ ENNReal.ofReal (Real.exp (K ^ 2 * lambda ^ 2)) /
          ENNReal.ofReal (Real.exp (lambda * t)) := by
            gcongr
            exact hbound lambda
    _ = ENNReal.ofReal (Real.exp (K ^ 2 * lambda ^ 2 - lambda * t)) :=
            ofReal_exp_div_exp_eq_ofReal_exp_sub (K ^ 2 * lambda ^ 2) (lambda * t)
    _ = ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * K ^ 2)))) := by
            apply congrArg ENNReal.ofReal
            apply congrArg Real.exp
            simp only [lambda]
            field_simp [hK.ne']
            ring

/--
One-sided lower-tail Chernoff bound from the lintegral centered MGF predicate.

Formula reference: this is the left-tail version of the same exponential
moment/Chernoff argument; see
https://en.wikipedia.org/wiki/Chernoff_bound
-/
theorem lowerTailProb_le_exp_neg_sq_of_centeredSubGaussianMGFLIntegral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {K t : ℝ}
    (hMGF : CenteredSubGaussianMGFLIntegral P X K) (ht : 0 ≤ t) :
    lowerTailProb P X (-t) ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * K ^ 2)))) := by
  rcases hMGF with ⟨hX, hK, hbound⟩
  let lambda : ℝ := -t / (2 * K ^ 2)
  have hKsq_pos : 0 < K ^ 2 := sq_pos_of_pos hK
  have hden_pos : 0 < 2 * K ^ 2 := mul_pos (by norm_num) hKsq_pos
  have hlambda_nonpos : lambda ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hden_pos.le
  let f : Ω → ENNReal := fun ω => ENNReal.ofReal (Real.exp (lambda * X ω))
  have h_meas : AEMeasurable f P := by
    have h_real : Measurable fun ω => Real.exp (lambda * X ω) :=
      (hX.const_mul lambda).exp
    exact h_real.aemeasurable.ennreal_ofReal
  have h_threshold_ne_zero :
      ENNReal.ofReal (Real.exp (lambda * (-t))) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h_markov :
      P {ω | ENNReal.ofReal (Real.exp (lambda * (-t))) ≤ f ω} ≤
        (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp (lambda * (-t))) :=
    MeasureTheory.meas_ge_le_lintegral_div h_meas h_threshold_ne_zero ENNReal.ofReal_ne_top
  have h_event :
      lowerTailEvent X (-t) ⊆
        {ω | ENNReal.ofReal (Real.exp (lambda * (-t))) ≤ f ω} := by
    intro ω hω
    have hmul : lambda * (-t) ≤ lambda * X ω :=
      mul_le_mul_of_nonpos_left hω hlambda_nonpos
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hmul)
  calc
    lowerTailProb P X (-t)
        ≤ P {ω | ENNReal.ofReal (Real.exp (lambda * (-t))) ≤ f ω} :=
            measure_mono h_event
    _ ≤ (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp (lambda * (-t))) := h_markov
    _ ≤ ENNReal.ofReal (Real.exp (K ^ 2 * lambda ^ 2)) /
          ENNReal.ofReal (Real.exp (lambda * (-t))) := by
            gcongr
            exact hbound lambda
    _ = ENNReal.ofReal (Real.exp (K ^ 2 * lambda ^ 2 - lambda * (-t))) :=
            ofReal_exp_div_exp_eq_ofReal_exp_sub (K ^ 2 * lambda ^ 2) (lambda * (-t))
    _ = ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * K ^ 2)))) := by
            apply congrArg ENNReal.ofReal
            apply congrArg Real.exp
            simp only [lambda]
            field_simp [hK.ne']
            ring

/-- One-sided upper-tail Chernoff bound from the Mathlib-backed MGF predicate. -/
theorem upperTailProb_le_exp_neg_sq_of_centeredSubGaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {K t : ℝ}
    (hX : IsRealRandomVariable P X)
    (hMGF : CenteredSubGaussianMGF P X K) (ht : 0 ≤ t) :
    upperTailProb P X t ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * K ^ 2)))) :=
  upperTailProb_le_exp_neg_sq_of_centeredSubGaussianMGFLIntegral
    (centeredSubGaussianMGFLIntegral_of_centeredSubGaussianMGF hX hMGF) ht

/-- One-sided lower-tail Chernoff bound from the Mathlib-backed MGF predicate. -/
theorem lowerTailProb_le_exp_neg_sq_of_centeredSubGaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {K t : ℝ}
    (hX : IsRealRandomVariable P X)
    (hMGF : CenteredSubGaussianMGF P X K) (ht : 0 ≤ t) :
    lowerTailProb P X (-t) ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * K ^ 2)))) :=
  lowerTailProb_le_exp_neg_sq_of_centeredSubGaussianMGFLIntegral
    (centeredSubGaussianMGFLIntegral_of_centeredSubGaussianMGF hX hMGF) ht

/-- Absolute-tail event is contained in the union of upper and lower tails. -/
theorem absTailEvent_subset_upperTailEvent_union_lowerTailEvent_neg
    {Ω : Type*} [MeasurableSpace Ω] (X : RealRandomVariable Ω) (t : ℝ) :
    absTailEvent X t ⊆ upperTailEvent X t ∪ lowerTailEvent X (-t) := by
  intro ω hω
  simp only [mem_absTailEvent] at hω
  simp only [Set.mem_union, mem_upperTailEvent, mem_lowerTailEvent]
  rw [le_abs] at hω
  rcases hω with hupper | hlower
  · exact Or.inl hupper
  · exact Or.inr (by linarith)

private lemma add_two_ofReal_exp (a : ℝ) :
    ENNReal.ofReal (Real.exp a) + ENNReal.ofReal (Real.exp a) =
      ENNReal.ofReal (2 * Real.exp a) := by
  rw [← ENNReal.ofReal_add (Real.exp_pos a).le (Real.exp_pos a).le]
  congr 1
  ring

/--
Two-sided subGaussian tail bound from the lintegral centered MGF predicate.

Formula reference: combines the upper and lower Chernoff tail bounds into
`P(|X| >= t) <= 2 * exp(-t^2 / (2*K)^2)`; see
https://en.wikipedia.org/wiki/Chernoff_bound

The resulting `SubGaussianTail` scale is `2 * K`.
-/
theorem subGaussianTail_of_centeredSubGaussianMGFLIntegral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {K : ℝ}
    (hMGF : CenteredSubGaussianMGFLIntegral P X K) :
    SubGaussianTail P X (2 * K) := by
  refine ⟨mul_pos two_pos hMGF.2.1, ?_⟩
  intro t ht
  have hupper :=
    upperTailProb_le_exp_neg_sq_of_centeredSubGaussianMGFLIntegral
      (P := P) (X := X) (K := K) (t := t) hMGF ht
  have hlower :=
    lowerTailProb_le_exp_neg_sq_of_centeredSubGaussianMGFLIntegral
      (P := P) (X := X) (K := K) (t := t) hMGF ht
  let a : ℝ := -(t ^ 2 / (4 * K ^ 2))
  calc
    absTailProb P X t
        ≤ P (upperTailEvent X t ∪ lowerTailEvent X (-t)) :=
            measure_mono (absTailEvent_subset_upperTailEvent_union_lowerTailEvent_neg X t)
    _ ≤ P (upperTailEvent X t) + P (lowerTailEvent X (-t)) :=
            measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp a) + ENNReal.ofReal (Real.exp a) := by
            simpa [a] using add_le_add hupper hlower
    _ = ENNReal.ofReal (2 * Real.exp a) :=
            add_two_ofReal_exp a
    _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (2 * K) ^ 2))) := by
            apply congrArg ENNReal.ofReal
            apply congrArg (fun z : ℝ => 2 * Real.exp z)
            simp only [a]
            have hscale : (2 * K) ^ 2 = 4 * K ^ 2 := by ring
            rw [hscale]

/--
Two-sided subGaussian tail bound from the Mathlib-backed MGF predicate.
-/
theorem subGaussianTail_of_centeredSubGaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X)
    (hMGF : CenteredSubGaussianMGF P X K) :
    SubGaussianTail P X (2 * K) :=
  subGaussianTail_of_centeredSubGaussianMGFLIntegral
    (centeredSubGaussianMGFLIntegral_of_centeredSubGaussianMGF hX hMGF)

/--
Centered MGF control implies the `ψ₂` Orlicz bound through the existing
tail-to-Orlicz bridge.
-/
theorem psi2Bound_of_centeredSubGaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X)
    (hMGF : CenteredSubGaussianMGF P X K) :
    Psi2Bound P X (4 * K) := by
  have hTail :
      SubGaussianTail P X (2 * K) :=
    subGaussianTail_of_centeredSubGaussianMGF
      (P := P) (X := X) (K := K) hX hMGF
  have hψ :=
    psi2Bound_of_subGaussianTail
      (P := P) (X := X) (K := 2 * K) hX hTail
  have hscale : 2 * (2 * K) = 4 * K := by ring
  simpa [hscale] using hψ

/--
Centered MGF control implies sharp natural-exponent moment growth by
composition through the two-sided tail theorem.
-/
theorem subGaussianMomentNatSqrt_of_centeredSubGaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X)
    (hMGF : CenteredSubGaussianMGF P X K) :
    SubGaussianMomentNatSqrt P X (16 * K) := by
  have hTail :
      SubGaussianTail P X (2 * K) :=
    subGaussianTail_of_centeredSubGaussianMGF
      (P := P) (X := X) (K := K) hX hMGF
  have hMoment :=
    subGaussianMomentNatSqrt_of_subGaussianTail
      (P := P) (X := X) (K := 2 * K) hX hTail
  have hscale : 8 * (2 * K) = 16 * K := by ring
  simpa [hscale] using hMoment

end

end HighDimProb
