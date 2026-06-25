/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Concentration.Markov
import LeanPool.HighDimProb.SubGaussian
import LeanPool.HighDimProb.SubExponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Orlicz-to-tail concentration bridges

This file contains the first implication proofs from the Orlicz layer to the
tail layer. The proofs use Mathlib's `lintegral` Markov inequality directly:
the Orlicz predicates are already stated as nonnegative `lintegral` bounds.

Verified Wikipedia references:
* Orlicz space: https://en.wikipedia.org/wiki/Orlicz_space
* Markov's inequality: https://en.wikipedia.org/wiki/Markov%27s_inequality
-/

namespace HighDimProb

open MeasureTheory

open scoped ENNReal

noncomputable section

-- Formula reference: Orlicz `psi_2` tails use the nonnegative integrand
-- `exp ((|x| / K)^2) - 1`; see https://en.wikipedia.org/wiki/Orlicz_space
private lemma exp_sq_div_sub_one_nonneg {K x : ℝ} :
    0 ≤ Real.exp ((|x| / K) ^ 2) - 1 := by
  have hsq : 0 ≤ (|x| / K) ^ 2 := sq_nonneg _
  have hexp : (1 : ℝ) ≤ Real.exp ((|x| / K) ^ 2) := Real.one_le_exp hsq
  linarith

-- Formula reference: Orlicz `psi_1` tails use the nonnegative integrand
-- `exp (|x| / K) - 1`; see https://en.wikipedia.org/wiki/Orlicz_space
private lemma exp_abs_div_sub_one_nonneg {K x : ℝ} (hK : 0 < K) :
    0 ≤ Real.exp (|x| / K) - 1 := by
  have hdiv : 0 ≤ |x| / K := div_nonneg (abs_nonneg _) hK.le
  have hexp : (1 : ℝ) ≤ Real.exp (|x| / K) := Real.one_le_exp hdiv
  linarith

-- Formula reference: this rewrites `exp ((|x| / K)^2)` as
-- `(exp ((|x| / K)^2) - 1) + 1`, the Orlicz integrand plus mass term;
-- see https://en.wikipedia.org/wiki/Orlicz_space
private lemma ofReal_exp_sq_div_eq_add {K x : ℝ} :
    ENNReal.ofReal (Real.exp ((|x| / K) ^ 2)) =
      ENNReal.ofReal (Real.exp ((|x| / K) ^ 2) - 1) + 1 := by
  have h_nonneg : 0 ≤ Real.exp ((|x| / K) ^ 2) - 1 :=
    exp_sq_div_sub_one_nonneg (K := K) (x := x)
  calc
    ENNReal.ofReal (Real.exp ((|x| / K) ^ 2))
        = ENNReal.ofReal ((Real.exp ((|x| / K) ^ 2) - 1) + 1) := by ring_nf
    _ = ENNReal.ofReal (Real.exp ((|x| / K) ^ 2) - 1) + ENNReal.ofReal (1 : ℝ) :=
        ENNReal.ofReal_add h_nonneg zero_le_one
    _ = ENNReal.ofReal (Real.exp ((|x| / K) ^ 2) - 1) + 1 := by simp

-- Formula reference: this rewrites `exp (|x| / K)` as
-- `(exp (|x| / K) - 1) + 1`, the `psi_1` Orlicz integrand plus mass term;
-- see https://en.wikipedia.org/wiki/Orlicz_space
private lemma ofReal_exp_abs_div_eq_add {K x : ℝ} (hK : 0 < K) :
    ENNReal.ofReal (Real.exp (|x| / K)) =
      ENNReal.ofReal (Real.exp (|x| / K) - 1) + 1 := by
  have h_nonneg : 0 ≤ Real.exp (|x| / K) - 1 :=
    exp_abs_div_sub_one_nonneg (K := K) (x := x) hK
  calc
    ENNReal.ofReal (Real.exp (|x| / K))
        = ENNReal.ofReal ((Real.exp (|x| / K) - 1) + 1) := by ring_nf
    _ = ENNReal.ofReal (Real.exp (|x| / K) - 1) + ENNReal.ofReal (1 : ℝ) :=
        ENNReal.ofReal_add h_nonneg zero_le_one
    _ = ENNReal.ofReal (Real.exp (|x| / K) - 1) + 1 := by simp

/--
A `Psi2Bound` gives the exponential-square moment bound with constant `2`.

The probability assumption is necessary: `Psi2Bound` alone does not control the
mass of the underlying measure when the Orlicz integrand vanishes.

Formula reference: the `psi_2` Orlicz integrand is
`exp ((|X| / K)^2) - 1`; adding the probability mass gives the bound for
`exp ((|X| / K)^2)`.  See
https://en.wikipedia.org/wiki/Orlicz_space
-/
theorem lintegral_exp_sq_div_le_two_of_psi2Bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : RealRandomVariable Ω} {K : ℝ}
    (hψ : Psi2Bound P X K) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2)) ∂P) ≤ (2 : ENNReal) := by
  rcases hψ with ⟨hK, hψ_int⟩
  calc
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2)) ∂P)
        = ∫⁻ ω, ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2) - 1) + 1 ∂P := by
            simp only [ofReal_exp_sq_div_eq_add (K := K)]
    _ = (∫⁻ ω, ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2) - 1) ∂P) + 1 := by
            rw [lintegral_add_right _ measurable_const]
            simp [lintegral_const, measure_univ]
    _ ≤ (1 : ENNReal) + 1 := add_le_add hψ_int le_rfl
    _ = 2 := by norm_num

/--
A `Psi1Bound` gives the exponential-linear moment bound with constant `2`.

The probability assumption is necessary for the same reason as in the `psi_2`
case: the Orlicz bound controls only the shifted exponential integrand.

Formula reference: the `psi_1` Orlicz integrand is
`exp (|X| / K) - 1`; adding the probability mass gives the bound for
`exp (|X| / K)`.  See https://en.wikipedia.org/wiki/Orlicz_space
-/
theorem lintegral_exp_abs_div_le_two_of_psi1Bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : RealRandomVariable Ω} {K : ℝ}
    (hψ : Psi1Bound P X K) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K)) ∂P) ≤ (2 : ENNReal) := by
  rcases hψ with ⟨hK, hψ_int⟩
  calc
    (∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K)) ∂P)
        = ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K) - 1) + 1 ∂P := by
            simp only [ofReal_exp_abs_div_eq_add (K := K) hK]
    _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K) - 1) ∂P) + 1 := by
            rw [lintegral_add_right _ measurable_const]
            simp [lintegral_const, measure_univ]
    _ ≤ (1 : ENNReal) + 1 := add_le_add hψ_int le_rfl
    _ = 2 := by norm_num

-- Formula reference: this is the exponential Markov conversion from a
-- `psi_2` moment bound to `2 * exp (-(t^2 / K^2))`; see Markov's inequality
-- at https://en.wikipedia.org/wiki/Markov%27s_inequality and Orlicz space at
-- https://en.wikipedia.org/wiki/Orlicz_space
private lemma two_div_exp_sq_eq_ofReal (t K : ℝ) :
    (2 : ENNReal) / ENNReal.ofReal (Real.exp ((t / K) ^ 2)) =
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / K ^ 2))) := by
  have hratio : (t / K) ^ 2 = t ^ 2 / K ^ 2 := by ring
  have htwo : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
  rw [htwo]
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos ((t / K) ^ 2))]
  apply congrArg ENNReal.ofReal
  rw [hratio, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

-- Formula reference: this is the exponential Markov conversion from a
-- `psi_1` moment bound to `2 * exp (-(t / K))`; see Markov's inequality
-- at https://en.wikipedia.org/wiki/Markov%27s_inequality and Orlicz space at
-- https://en.wikipedia.org/wiki/Orlicz_space
private lemma two_div_exp_abs_eq_ofReal (t K : ℝ) :
    (2 : ENNReal) / ENNReal.ofReal (Real.exp (t / K)) =
      ENNReal.ofReal (2 * Real.exp (-(t / K))) := by
  have htwo : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
  rw [htwo]
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos (t / K))]
  apply congrArg ENNReal.ofReal
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]

/--
The `psi_2` Orlicz bound implies the HighDimProb two-sided subGaussian tail
bound with the same scale.

Measurability is kept separate because `Psi2Bound` is an integral bound
predicate, not a random-variable predicate.

Formula reference: applying Markov's inequality to
`exp ((|X| / K)^2)` yields a two-sided `psi_2` tail
`2 * exp (-(t^2 / K^2))`; see
https://en.wikipedia.org/wiki/Markov%27s_inequality and
https://en.wikipedia.org/wiki/Orlicz_space
-/
theorem subGaussianTail_of_psi2Bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X) (hψ : Psi2Bound P X K) :
    SubGaussianTail P X K := by
  rcases hψ with ⟨hK, hψ_int⟩
  refine ⟨hK, ?_⟩
  intro t ht
  let f : Ω → ENNReal := fun ω => ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2))
  have h_meas : AEMeasurable f P := by
    have h_real : Measurable fun ω => Real.exp ((|X ω| / K) ^ 2) := by
      have h_abs : Measurable fun ω => |X ω| := by
        simpa [Real.norm_eq_abs] using hX.norm
      exact Real.measurable_exp.comp ((h_abs.div_const K).pow_const 2)
    exact h_real.aemeasurable.ennreal_ofReal
  have h_threshold_ne_zero :
      ENNReal.ofReal (Real.exp ((t / K) ^ 2)) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h_markov :
      P {ω | ENNReal.ofReal (Real.exp ((t / K) ^ 2)) ≤ f ω} ≤
        (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp ((t / K) ^ 2)) :=
    MeasureTheory.meas_ge_le_lintegral_div h_meas h_threshold_ne_zero ENNReal.ofReal_ne_top
  have h_moment :
      (∫⁻ ω, f ω ∂P) ≤ (2 : ENNReal) := by
    simpa [f] using
      (lintegral_exp_sq_div_le_two_of_psi2Bound
        (P := P) (X := X) (K := K) ⟨hK, hψ_int⟩)
  have h_event :
      absTailEvent X t ⊆ {ω | ENNReal.ofReal (Real.exp ((t / K) ^ 2)) ≤ f ω} := by
    intro ω hω
    have hdiv : t / K ≤ |X ω| / K := div_le_div_of_nonneg_right hω hK.le
    have htd : 0 ≤ t / K := div_nonneg ht hK.le
    have hsquare : (t / K) ^ 2 ≤ (|X ω| / K) ^ 2 :=
      pow_le_pow_left₀ htd hdiv 2
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hsquare)
  calc
    absTailProb P X t
        ≤ P {ω | ENNReal.ofReal (Real.exp ((t / K) ^ 2)) ≤ f ω} :=
            measure_mono h_event
    _ ≤ (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp ((t / K) ^ 2)) := h_markov
    _ ≤ (2 : ENNReal) / ENNReal.ofReal (Real.exp ((t / K) ^ 2)) := by
            gcongr
    _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / K ^ 2))) :=
            two_div_exp_sq_eq_ofReal t K

/--
The `psi_1` Orlicz bound implies the HighDimProb two-sided subExponential tail
bound with the same scale.

Measurability is kept separate for the same reason as in
`subGaussianTail_of_psi2Bound`.

Formula reference: applying Markov's inequality to `exp (|X| / K)` yields the
two-sided `psi_1` tail `2 * exp (-(t / K))`; see
https://en.wikipedia.org/wiki/Markov%27s_inequality and
https://en.wikipedia.org/wiki/Orlicz_space
-/
theorem subExponentialTail_of_psi1Bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X) (hψ : Psi1Bound P X K) :
    SubExponentialTail P X K := by
  rcases hψ with ⟨hK, hψ_int⟩
  refine ⟨hK, ?_⟩
  intro t ht
  let f : Ω → ENNReal := fun ω => ENNReal.ofReal (Real.exp (|X ω| / K))
  have h_meas : AEMeasurable f P := by
    have h_real : Measurable fun ω => Real.exp (|X ω| / K) := by
      have h_abs : Measurable fun ω => |X ω| := by
        simpa [Real.norm_eq_abs] using hX.norm
      exact Real.measurable_exp.comp (h_abs.div_const K)
    exact h_real.aemeasurable.ennreal_ofReal
  have h_threshold_ne_zero :
      ENNReal.ofReal (Real.exp (t / K)) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h_markov :
      P {ω | ENNReal.ofReal (Real.exp (t / K)) ≤ f ω} ≤
        (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp (t / K)) :=
    MeasureTheory.meas_ge_le_lintegral_div h_meas h_threshold_ne_zero ENNReal.ofReal_ne_top
  have h_moment :
      (∫⁻ ω, f ω ∂P) ≤ (2 : ENNReal) := by
    simpa [f] using
      (lintegral_exp_abs_div_le_two_of_psi1Bound
        (P := P) (X := X) (K := K) ⟨hK, hψ_int⟩)
  have h_event :
      absTailEvent X t ⊆ {ω | ENNReal.ofReal (Real.exp (t / K)) ≤ f ω} := by
    intro ω hω
    have hdiv : t / K ≤ |X ω| / K := div_le_div_of_nonneg_right hω hK.le
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hdiv)
  calc
    absTailProb P X t
        ≤ P {ω | ENNReal.ofReal (Real.exp (t / K)) ≤ f ω} :=
            measure_mono h_event
    _ ≤ (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp (t / K)) := h_markov
    _ ≤ (2 : ENNReal) / ENNReal.ofReal (Real.exp (t / K)) := by
            gcongr
    _ = ENNReal.ofReal (2 * Real.exp (-(t / K))) :=
            two_div_exp_abs_eq_ofReal t K

end

end HighDimProb
