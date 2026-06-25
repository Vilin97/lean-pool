/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Concentration.SubExponentialSums

/-!
# Bernstein/subExponential concentration scaffold

This file adds the first Bernstein-branch statement layer and local Chernoff
theorems from the proof-friendly subExponential MGF predicate.

Verified Wikipedia references:
* Bernstein inequalities: https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)
* Chernoff bound: https://en.wikipedia.org/wiki/Chernoff_bound
* Markov inequality: https://en.wikipedia.org/wiki/Markov%27s_inequality
* Heavy-tailed/subExponential context: https://en.wikipedia.org/wiki/Heavy-tailed_distribution
-/

namespace HighDimProb

open MeasureTheory

noncomputable section

open scoped BigOperators ENNReal

/--
The Bernstein min-form rate `min (t^2 / varianceProxy) (t / maxScale)`.

Formula reference: Bernstein inequalities interpolate a quadratic small-
deviation regime and a linear large-deviation regime; see
https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)
-/
def subExponentialBernsteinRate (t varianceProxy maxScale : Real) : Real :=
  min (t ^ 2 / varianceProxy) (t / maxScale)

/--
Typed statement for the scalar Bernstein inequality for a finite sum of
centered subExponential variables.

Formula reference: this records a two-sided Bernstein-style tail bound
`P(|sum_i X_i| >= t) <= 2 * exp(-c * min(t^2/V, t/B))`; see
https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)

The positive constant is explicit because this stage does not prove the full
min-form inequality.
-/
abbrev bernsteinSubExponentialSumStatement
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    (P : Measure Omega)
    (X : ι → RealRandomVariable Omega) (K : ι → Real)
    (varianceProxy maxScale cBernstein : Real) : Prop :=
  0 < varianceProxy ∧
    0 < maxScale ∧
      0 < cBernstein ∧
        varianceProxy = ∑ i : ι, (K i) ^ 2 ∧
          (∀ i : ι, K i <= maxScale) ∧
            (∀ i : ι, IsRealRandomVariable P (X i)) ∧
              ProbabilityTheory.iIndepFun X P ∧
                (∀ i : ι, CenteredSubExponentialMGF P (X i) (K i)) ∧
                  ∀ t : Real, 0 <= t →
                    absTailProb P (fun omega => ∑ i : ι, X i omega) t <=
                      ENNReal.ofReal
                        (2 *
                          Real.exp
                            (-(cBernstein *
                              subExponentialBernsteinRate
                                t varianceProxy maxScale)))

/--
Typed statement for a weighted finite subExponential Bernstein inequality.

Formula reference: this is the weighted analogue of the Bernstein min-form
tail bound with weighted variance and max-scale proxies; see
https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)

The variance proxy and max scale are stated explicitly to avoid committing to a
future gauge or finite-maximum API in this scaffold stage.
-/
abbrev bernsteinSubExponentialWeightedSumStatement
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    (P : Measure Omega)
    (X : ι → RealRandomVariable Omega) (K weights : ι → Real)
    (varianceProxy maxScale cBernstein : Real) : Prop :=
  0 < varianceProxy ∧
    0 < maxScale ∧
      0 < cBernstein ∧
        varianceProxy = ∑ i : ι, (weights i * K i) ^ 2 ∧
          (∀ i : ι, |weights i| * K i <= maxScale) ∧
            (∀ i : ι, IsRealRandomVariable P (X i)) ∧
              ProbabilityTheory.iIndepFun X P ∧
                (∀ i : ι, CenteredSubExponentialMGF P (X i) (K i)) ∧
                  ∀ t : Real, 0 <= t →
                    absTailProb P
                        (fun omega => ∑ i : ι, weights i * X i omega) t <=
                      ENNReal.ofReal
                        (2 *
                          Real.exp
                            (-(cBernstein *
                              subExponentialBernsteinRate
                                t varianceProxy maxScale)))

private lemma ofReal_exp_div_exp_eq_ofReal_exp_sub (a b : Real) :
    ENNReal.ofReal (Real.exp a) / ENNReal.ofReal (Real.exp b) =
      ENNReal.ofReal (Real.exp (a - b)) := by
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos b)]
  apply congrArg ENNReal.ofReal
  rw [Real.exp_sub]

private lemma add_two_ofReal_exp (a : Real) :
    ENNReal.ofReal (Real.exp a) + ENNReal.ofReal (Real.exp a) =
      ENNReal.ofReal (2 * Real.exp a) := by
  rw [← ENNReal.ofReal_add (Real.exp_pos a).le (Real.exp_pos a).le]
  congr 1
  ring

private lemma ofReal_exp_le_of_exp_arg_le {a b : Real} (h : a <= b) :
    ENNReal.ofReal (Real.exp a) <= ENNReal.ofReal (Real.exp b) :=
  ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h)

private lemma neg_sq_div_four_le_neg_quarter_bernsteinRate
    {V B t : Real} (hV : 0 < V) (_hB : 0 < B) (_ht : 0 <= t) :
    -(t ^ 2 / (4 * V)) <=
      -((1 / 4) * subExponentialBernsteinRate t V B) := by
  have hrate_le :
      subExponentialBernsteinRate t V B <= t ^ 2 / V := min_le_left _ _
  have hquarter :
      (1 / 4) * subExponentialBernsteinRate t V B <=
        (1 / 4) * (t ^ 2 / V) := by
    exact mul_le_mul_of_nonneg_left hrate_le (by norm_num)
  have hquarter_eq : (1 / 4) * (t ^ 2 / V) = t ^ 2 / (4 * V) := by
    field_simp [hV.ne']
  exact neg_le_neg (hquarter.trans_eq hquarter_eq)

private lemma neg_linear_half_le_neg_quarter_bernsteinRate
    {V B t : Real} (_hV : 0 < V) (hB : 0 < B) (ht : 0 <= t) :
    -(t / (2 * B)) <=
      -((1 / 4) * subExponentialBernsteinRate t V B) := by
  have hrate_le :
      subExponentialBernsteinRate t V B <= t / B := min_le_right _ _
  have hquarter :
      (1 / 4) * subExponentialBernsteinRate t V B <=
        (1 / 4) * (t / B) := by
    exact mul_le_mul_of_nonneg_left hrate_le (by norm_num)
  have hhalf : (1 / 4) * (t / B) <= t / (2 * B) := by
    field_simp [hB.ne']
    nlinarith [mul_nonneg ht hB.le]
  exact neg_le_neg (hquarter.trans hhalf)

/--
Small-deviation upper-tail Chernoff bound from a local lintegral MGF bound
with variance proxy `V` and max-scale domain `B`.

Formula reference: Chernoff uses `P(X >= t) <= E[exp(lambda X)] * exp(-lambda t)`;
the optimizer here gives `exp(-t^2/(4*V))`; see
https://en.wikipedia.org/wiki/Chernoff_bound
-/
theorem upperTailProb_le_exp_neg_sq_div_varianceProxy_of_mgf_bound_of_le
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {V B t : Real}
    (hX : IsRealRandomVariable P X)
    (hV : 0 < V) (_hB : 0 < B)
    (hMGF : ∀ lambda : Real, |lambda| <= 1 / B →
      (∫⁻ omega, ENNReal.ofReal (Real.exp (lambda * X omega)) ∂P) <=
        ENNReal.ofReal (Real.exp (V * lambda ^ 2)))
    (ht : 0 <= t) (htDomain : t <= 2 * V / B) :
    upperTailProb P X t <=
      ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * V)))) := by
  let lambda : Real := t / (2 * V)
  have hden_pos : 0 < 2 * V := mul_pos (by norm_num) hV
  have hlambda_nonneg : 0 <= lambda := by
    exact div_nonneg ht hden_pos.le
  have hlambda_domain : |lambda| <= 1 / B := by
    rw [abs_of_nonneg hlambda_nonneg]
    dsimp [lambda]
    rw [div_le_iff₀ hden_pos]
    rw [one_div, inv_mul_eq_div, mul_comm]
    simpa [mul_comm, mul_left_comm, mul_assoc] using htDomain
  let f : Omega -> ENNReal := fun omega =>
    ENNReal.ofReal (Real.exp (lambda * X omega))
  have h_meas : AEMeasurable f P := by
    have h_real : Measurable fun omega => Real.exp (lambda * X omega) :=
      (hX.const_mul lambda).exp
    exact h_real.aemeasurable.ennreal_ofReal
  have h_threshold_ne_zero :
      ENNReal.ofReal (Real.exp (lambda * t)) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h_markov :
      P {omega | ENNReal.ofReal (Real.exp (lambda * t)) <= f omega} <=
        (∫⁻ omega, f omega ∂P) / ENNReal.ofReal (Real.exp (lambda * t)) :=
    MeasureTheory.meas_ge_le_lintegral_div
      h_meas h_threshold_ne_zero ENNReal.ofReal_ne_top
  have h_event :
      upperTailEvent X t ⊆
        {omega | ENNReal.ofReal (Real.exp (lambda * t)) <= f omega} := by
    intro omega homega
    have hmul : lambda * t <= lambda * X omega :=
      mul_le_mul_of_nonneg_left homega hlambda_nonneg
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hmul)
  calc
    upperTailProb P X t
        <= P {omega | ENNReal.ofReal (Real.exp (lambda * t)) <= f omega} :=
            measure_mono h_event
    _ <= (∫⁻ omega, f omega ∂P) / ENNReal.ofReal (Real.exp (lambda * t)) := h_markov
    _ <= ENNReal.ofReal (Real.exp (V * lambda ^ 2)) /
          ENNReal.ofReal (Real.exp (lambda * t)) := by
            gcongr
            exact hMGF lambda hlambda_domain
    _ = ENNReal.ofReal (Real.exp (V * lambda ^ 2 - lambda * t)) :=
            ofReal_exp_div_exp_eq_ofReal_exp_sub
              (V * lambda ^ 2) (lambda * t)
    _ = ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * V)))) := by
            apply congrArg ENNReal.ofReal
            apply congrArg Real.exp
            simp only [lambda]
            field_simp [hV.ne']
            ring

/--
Small-deviation lower-tail Chernoff bound from a local lintegral MGF bound
with variance proxy `V` and max-scale domain `B`.

Formula reference: lower-tail Chernoff uses the same exponential Markov method
with negative `lambda`; see https://en.wikipedia.org/wiki/Chernoff_bound
-/
theorem lowerTailProb_le_exp_neg_sq_div_varianceProxy_of_mgf_bound_of_le
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {V B t : Real}
    (hX : IsRealRandomVariable P X)
    (hV : 0 < V) (_hB : 0 < B)
    (hMGF : ∀ lambda : Real, |lambda| <= 1 / B →
      (∫⁻ omega, ENNReal.ofReal (Real.exp (lambda * X omega)) ∂P) <=
        ENNReal.ofReal (Real.exp (V * lambda ^ 2)))
    (ht : 0 <= t) (htDomain : t <= 2 * V / B) :
    lowerTailProb P X (-t) <=
      ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * V)))) := by
  let lambda : Real := -t / (2 * V)
  have hden_pos : 0 < 2 * V := mul_pos (by norm_num) hV
  have hlambda_nonpos : lambda <= 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hden_pos.le
  have hlambda_domain : |lambda| <= 1 / B := by
    rw [abs_of_nonpos hlambda_nonpos]
    dsimp [lambda]
    rw [neg_div, neg_neg]
    rw [div_le_iff₀ hden_pos]
    rw [one_div, inv_mul_eq_div, mul_comm]
    simpa [mul_comm, mul_left_comm, mul_assoc] using htDomain
  let f : Omega -> ENNReal := fun omega =>
    ENNReal.ofReal (Real.exp (lambda * X omega))
  have h_meas : AEMeasurable f P := by
    have h_real : Measurable fun omega => Real.exp (lambda * X omega) :=
      (hX.const_mul lambda).exp
    exact h_real.aemeasurable.ennreal_ofReal
  have h_threshold_ne_zero :
      ENNReal.ofReal (Real.exp (lambda * (-t))) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h_markov :
      P {omega | ENNReal.ofReal (Real.exp (lambda * (-t))) <= f omega} <=
        (∫⁻ omega, f omega ∂P) /
          ENNReal.ofReal (Real.exp (lambda * (-t))) :=
    MeasureTheory.meas_ge_le_lintegral_div
      h_meas h_threshold_ne_zero ENNReal.ofReal_ne_top
  have h_event :
      lowerTailEvent X (-t) ⊆
        {omega | ENNReal.ofReal (Real.exp (lambda * (-t))) <= f omega} := by
    intro omega homega
    have hmul : lambda * (-t) <= lambda * X omega :=
      mul_le_mul_of_nonpos_left homega hlambda_nonpos
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hmul)
  calc
    lowerTailProb P X (-t)
        <= P {omega | ENNReal.ofReal (Real.exp (lambda * (-t))) <= f omega} :=
            measure_mono h_event
    _ <= (∫⁻ omega, f omega ∂P) /
          ENNReal.ofReal (Real.exp (lambda * (-t))) := h_markov
    _ <= ENNReal.ofReal (Real.exp (V * lambda ^ 2)) /
          ENNReal.ofReal (Real.exp (lambda * (-t))) := by
            gcongr
            exact hMGF lambda hlambda_domain
    _ = ENNReal.ofReal (Real.exp (V * lambda ^ 2 - lambda * (-t))) :=
            ofReal_exp_div_exp_eq_ofReal_exp_sub
              (V * lambda ^ 2) (lambda * (-t))
    _ = ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * V)))) := by
            apply congrArg ENNReal.ofReal
            apply congrArg Real.exp
            simp only [lambda]
            field_simp [hV.ne']
            ring

/--
Two-sided local Bernstein small-deviation bound from a local lintegral MGF
bound with variance proxy `V` and max-scale domain `B`.

Formula reference: combines upper and lower small-deviation Chernoff bounds into
`P(|X| >= t) <= 2 * exp(-t^2/(4*V))`; see
https://en.wikipedia.org/wiki/Chernoff_bound
-/
theorem absTailProb_le_two_mul_exp_neg_sq_div_varianceProxy_of_mgf_bound_of_le
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {V B t : Real}
    (hX : IsRealRandomVariable P X)
    (hV : 0 < V) (hB : 0 < B)
    (hMGF : ∀ lambda : Real, |lambda| <= 1 / B →
      (∫⁻ omega, ENNReal.ofReal (Real.exp (lambda * X omega)) ∂P) <=
        ENNReal.ofReal (Real.exp (V * lambda ^ 2)))
    (ht : 0 <= t) (htDomain : t <= 2 * V / B) :
    absTailProb P X t <=
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (4 * V)))) := by
  have hupper :=
    upperTailProb_le_exp_neg_sq_div_varianceProxy_of_mgf_bound_of_le
      (P := P) (X := X) (V := V) (B := B) (t := t)
      hX hV hB hMGF ht htDomain
  have hlower :=
    lowerTailProb_le_exp_neg_sq_div_varianceProxy_of_mgf_bound_of_le
      (P := P) (X := X) (V := V) (B := B) (t := t)
      hX hV hB hMGF ht htDomain
  let a : Real := -(t ^ 2 / (4 * V))
  calc
    absTailProb P X t
        <= P (upperTailEvent X t ∪ lowerTailEvent X (-t)) :=
            measure_mono (absTailEvent_subset_upperTailEvent_union_lowerTailEvent_neg X t)
    _ <= P (upperTailEvent X t) + P (lowerTailEvent X (-t)) :=
            measure_union_le _ _
    _ <= ENNReal.ofReal (Real.exp a) + ENNReal.ofReal (Real.exp a) := by
            simpa [a] using add_le_add hupper hlower
    _ = ENNReal.ofReal (2 * Real.exp a) :=
            add_two_ofReal_exp a
    _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (4 * V)))) := by
            rfl

/--
Large-deviation upper-tail Chernoff bound from a local lintegral MGF bound
with variance proxy `V` and max-scale domain `B`.

Formula reference: this is the linear Bernstein regime
`exp(-t/(2*B))`, obtained by choosing the boundary MGF parameter; see
https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)
-/
theorem upperTailProb_le_exp_neg_linear_div_maxScale_of_mgf_bound_of_ge
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {V B t : Real}
    (hX : IsRealRandomVariable P X)
    (_hV : 0 < V) (hB : 0 < B)
    (hMGF : ∀ lambda : Real, |lambda| <= 1 / B →
      (∫⁻ omega, ENNReal.ofReal (Real.exp (lambda * X omega)) ∂P) <=
        ENNReal.ofReal (Real.exp (V * lambda ^ 2)))
    (_ht : 0 <= t) (htDomain : 2 * V / B <= t) :
    upperTailProb P X t <=
      ENNReal.ofReal (Real.exp (-(t / (2 * B)))) := by
  let lambda : Real := 1 / B
  have hlambda_pos : 0 < lambda := by
    exact one_div_pos.mpr hB
  have hlambda_nonneg : 0 <= lambda := hlambda_pos.le
  have hlambda_domain : |lambda| <= 1 / B := by
    rw [abs_of_pos hlambda_pos]
  let f : Omega -> ENNReal := fun omega =>
    ENNReal.ofReal (Real.exp (lambda * X omega))
  have h_meas : AEMeasurable f P := by
    have h_real : Measurable fun omega => Real.exp (lambda * X omega) :=
      (hX.const_mul lambda).exp
    exact h_real.aemeasurable.ennreal_ofReal
  have h_threshold_ne_zero :
      ENNReal.ofReal (Real.exp (lambda * t)) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h_markov :
      P {omega | ENNReal.ofReal (Real.exp (lambda * t)) <= f omega} <=
        (∫⁻ omega, f omega ∂P) / ENNReal.ofReal (Real.exp (lambda * t)) :=
    MeasureTheory.meas_ge_le_lintegral_div
      h_meas h_threshold_ne_zero ENNReal.ofReal_ne_top
  have h_event :
      upperTailEvent X t ⊆
        {omega | ENNReal.ofReal (Real.exp (lambda * t)) <= f omega} := by
    intro omega homega
    have hmul : lambda * t <= lambda * X omega :=
      mul_le_mul_of_nonneg_left homega hlambda_nonneg
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hmul)
  have h_exp_arg :
      V * lambda ^ 2 - lambda * t <= -(t / (2 * B)) := by
    have h2V_le_tB : 2 * V <= t * B := by
      have hmul := mul_le_mul_of_nonneg_right htDomain hB.le
      field_simp [hB.ne'] at hmul
      nlinarith
    simp only [lambda]
    field_simp [hB.ne']
    nlinarith
  calc
    upperTailProb P X t
        <= P {omega | ENNReal.ofReal (Real.exp (lambda * t)) <= f omega} :=
            measure_mono h_event
    _ <= (∫⁻ omega, f omega ∂P) / ENNReal.ofReal (Real.exp (lambda * t)) := h_markov
    _ <= ENNReal.ofReal (Real.exp (V * lambda ^ 2)) /
          ENNReal.ofReal (Real.exp (lambda * t)) := by
            gcongr
            exact hMGF lambda hlambda_domain
    _ = ENNReal.ofReal (Real.exp (V * lambda ^ 2 - lambda * t)) :=
            ofReal_exp_div_exp_eq_ofReal_exp_sub
              (V * lambda ^ 2) (lambda * t)
    _ <= ENNReal.ofReal (Real.exp (-(t / (2 * B)))) :=
            ofReal_exp_le_of_exp_arg_le h_exp_arg

/--
Large-deviation lower-tail Chernoff bound from a local lintegral MGF bound
with variance proxy `V` and max-scale domain `B`.

Formula reference: lower-tail version of the linear Bernstein regime; see
https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)
-/
theorem lowerTailProb_le_exp_neg_linear_div_maxScale_of_mgf_bound_of_ge
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {V B t : Real}
    (hX : IsRealRandomVariable P X)
    (_hV : 0 < V) (hB : 0 < B)
    (hMGF : ∀ lambda : Real, |lambda| <= 1 / B →
      (∫⁻ omega, ENNReal.ofReal (Real.exp (lambda * X omega)) ∂P) <=
        ENNReal.ofReal (Real.exp (V * lambda ^ 2)))
    (_ht : 0 <= t) (htDomain : 2 * V / B <= t) :
    lowerTailProb P X (-t) <=
      ENNReal.ofReal (Real.exp (-(t / (2 * B)))) := by
  let lambda : Real := -(1 / B)
  have h_inv_pos : 0 < 1 / B := one_div_pos.mpr hB
  have hlambda_nonpos : lambda <= 0 := by
    dsimp [lambda]
    exact neg_nonpos.mpr h_inv_pos.le
  have hlambda_domain : |lambda| <= 1 / B := by
    rw [abs_of_nonpos hlambda_nonpos]
    simp [lambda]
  let f : Omega -> ENNReal := fun omega =>
    ENNReal.ofReal (Real.exp (lambda * X omega))
  have h_meas : AEMeasurable f P := by
    have h_real : Measurable fun omega => Real.exp (lambda * X omega) :=
      (hX.const_mul lambda).exp
    exact h_real.aemeasurable.ennreal_ofReal
  have h_threshold_ne_zero :
      ENNReal.ofReal (Real.exp (lambda * (-t))) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h_markov :
      P {omega | ENNReal.ofReal (Real.exp (lambda * (-t))) <= f omega} <=
        (∫⁻ omega, f omega ∂P) /
          ENNReal.ofReal (Real.exp (lambda * (-t))) :=
    MeasureTheory.meas_ge_le_lintegral_div
      h_meas h_threshold_ne_zero ENNReal.ofReal_ne_top
  have h_event :
      lowerTailEvent X (-t) ⊆
        {omega | ENNReal.ofReal (Real.exp (lambda * (-t))) <= f omega} := by
    intro omega homega
    have hmul : lambda * (-t) <= lambda * X omega :=
      mul_le_mul_of_nonpos_left homega hlambda_nonpos
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hmul)
  have h_exp_arg :
      V * lambda ^ 2 - lambda * (-t) <= -(t / (2 * B)) := by
    have h2V_le_tB : 2 * V <= t * B := by
      have hmul := mul_le_mul_of_nonneg_right htDomain hB.le
      field_simp [hB.ne'] at hmul
      nlinarith
    simp only [lambda]
    field_simp [hB.ne']
    nlinarith
  calc
    lowerTailProb P X (-t)
        <= P {omega | ENNReal.ofReal (Real.exp (lambda * (-t))) <= f omega} :=
            measure_mono h_event
    _ <= (∫⁻ omega, f omega ∂P) /
          ENNReal.ofReal (Real.exp (lambda * (-t))) := h_markov
    _ <= ENNReal.ofReal (Real.exp (V * lambda ^ 2)) /
          ENNReal.ofReal (Real.exp (lambda * (-t))) := by
            gcongr
            exact hMGF lambda hlambda_domain
    _ = ENNReal.ofReal (Real.exp (V * lambda ^ 2 - lambda * (-t))) :=
            ofReal_exp_div_exp_eq_ofReal_exp_sub
              (V * lambda ^ 2) (lambda * (-t))
    _ <= ENNReal.ofReal (Real.exp (-(t / (2 * B)))) :=
            ofReal_exp_le_of_exp_arg_le h_exp_arg

/--
Two-sided large-deviation Bernstein bound from a local lintegral MGF bound
with variance proxy `V` and max-scale domain `B`.

Formula reference: combines the upper/lower linear Bernstein regimes into
`P(|X| >= t) <= 2 * exp(-t/(2*B))`; see
https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)
-/
theorem absTailProb_le_two_mul_exp_neg_linear_div_maxScale_of_mgf_bound_of_ge
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {V B t : Real}
    (hX : IsRealRandomVariable P X)
    (hV : 0 < V) (hB : 0 < B)
    (hMGF : ∀ lambda : Real, |lambda| <= 1 / B →
      (∫⁻ omega, ENNReal.ofReal (Real.exp (lambda * X omega)) ∂P) <=
        ENNReal.ofReal (Real.exp (V * lambda ^ 2)))
    (ht : 0 <= t) (htDomain : 2 * V / B <= t) :
    absTailProb P X t <=
      ENNReal.ofReal (2 * Real.exp (-(t / (2 * B)))) := by
  have hupper :=
    upperTailProb_le_exp_neg_linear_div_maxScale_of_mgf_bound_of_ge
      (P := P) (X := X) (V := V) (B := B) (t := t)
      hX hV hB hMGF ht htDomain
  have hlower :=
    lowerTailProb_le_exp_neg_linear_div_maxScale_of_mgf_bound_of_ge
      (P := P) (X := X) (V := V) (B := B) (t := t)
      hX hV hB hMGF ht htDomain
  let a : Real := -(t / (2 * B))
  calc
    absTailProb P X t
        <= P (upperTailEvent X t ∪ lowerTailEvent X (-t)) :=
            measure_mono (absTailEvent_subset_upperTailEvent_union_lowerTailEvent_neg X t)
    _ <= P (upperTailEvent X t) + P (lowerTailEvent X (-t)) :=
            measure_union_le _ _
    _ <= ENNReal.ofReal (Real.exp a) + ENNReal.ofReal (Real.exp a) := by
            simpa [a] using add_le_add hupper hlower
    _ = ENNReal.ofReal (2 * Real.exp a) :=
            add_two_ofReal_exp a
    _ = ENNReal.ofReal (2 * Real.exp (-(t / (2 * B)))) := by
            rfl

/--
One-sided upper-tail Bernstein min-form bound from a local lintegral MGF
bound.  The universal constant is the conservative value `1/4`.

Formula reference: this packages the quadratic and linear regimes as
`exp(-c * min(t^2/V, t/B))`; see
https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)
-/
theorem upperTailProb_le_exp_neg_quarter_bernsteinRate_of_mgf_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {V B t : Real}
    (hX : IsRealRandomVariable P X)
    (hV : 0 < V) (hB : 0 < B)
    (hMGF : ∀ lambda : Real, |lambda| <= 1 / B →
      (∫⁻ omega, ENNReal.ofReal (Real.exp (lambda * X omega)) ∂P) <=
        ENNReal.ofReal (Real.exp (V * lambda ^ 2)))
    (ht : 0 <= t) :
    upperTailProb P X t <=
      ENNReal.ofReal
        (Real.exp (-((1 / 4) * subExponentialBernsteinRate t V B))) := by
  by_cases hsmall : t <= 2 * V / B
  · have hupper :=
      upperTailProb_le_exp_neg_sq_div_varianceProxy_of_mgf_bound_of_le
        (P := P) (X := X) (V := V) (B := B) (t := t)
        hX hV hB hMGF ht hsmall
    exact
      hupper.trans
        (ofReal_exp_le_of_exp_arg_le
          (neg_sq_div_four_le_neg_quarter_bernsteinRate hV hB ht))
  · have hlarge : 2 * V / B <= t := (lt_of_not_ge hsmall).le
    have hupper :=
      upperTailProb_le_exp_neg_linear_div_maxScale_of_mgf_bound_of_ge
        (P := P) (X := X) (V := V) (B := B) (t := t)
        hX hV hB hMGF ht hlarge
    exact
      hupper.trans
        (ofReal_exp_le_of_exp_arg_le
          (neg_linear_half_le_neg_quarter_bernsteinRate hV hB ht))

/--
One-sided lower-tail Bernstein min-form bound from a local lintegral MGF
bound.  The universal constant is the conservative value `1/4`.

Formula reference: lower-tail min-form Bernstein bound; see
https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)
-/
theorem lowerTailProb_le_exp_neg_quarter_bernsteinRate_of_mgf_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {V B t : Real}
    (hX : IsRealRandomVariable P X)
    (hV : 0 < V) (hB : 0 < B)
    (hMGF : ∀ lambda : Real, |lambda| <= 1 / B →
      (∫⁻ omega, ENNReal.ofReal (Real.exp (lambda * X omega)) ∂P) <=
        ENNReal.ofReal (Real.exp (V * lambda ^ 2)))
    (ht : 0 <= t) :
    lowerTailProb P X (-t) <=
      ENNReal.ofReal
        (Real.exp (-((1 / 4) * subExponentialBernsteinRate t V B))) := by
  by_cases hsmall : t <= 2 * V / B
  · have hlower :=
      lowerTailProb_le_exp_neg_sq_div_varianceProxy_of_mgf_bound_of_le
        (P := P) (X := X) (V := V) (B := B) (t := t)
        hX hV hB hMGF ht hsmall
    exact
      hlower.trans
        (ofReal_exp_le_of_exp_arg_le
          (neg_sq_div_four_le_neg_quarter_bernsteinRate hV hB ht))
  · have hlarge : 2 * V / B <= t := (lt_of_not_ge hsmall).le
    have hlower :=
      lowerTailProb_le_exp_neg_linear_div_maxScale_of_mgf_bound_of_ge
        (P := P) (X := X) (V := V) (B := B) (t := t)
        hX hV hB hMGF ht hlarge
    exact
      hlower.trans
        (ofReal_exp_le_of_exp_arg_le
          (neg_linear_half_le_neg_quarter_bernsteinRate hV hB ht))

/--
Two-sided Bernstein min-form bound from a local lintegral MGF bound.  The
universal constant is the conservative value `1/4`.

Formula reference: two-sided min-form Bernstein bound
`P(|X| >= t) <= 2 * exp(-c * min(t^2/V, t/B))`; see
https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)
-/
theorem absTailProb_le_two_mul_exp_neg_quarter_bernsteinRate_of_mgf_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {V B t : Real}
    (hX : IsRealRandomVariable P X)
    (hV : 0 < V) (hB : 0 < B)
    (hMGF : ∀ lambda : Real, |lambda| <= 1 / B →
      (∫⁻ omega, ENNReal.ofReal (Real.exp (lambda * X omega)) ∂P) <=
        ENNReal.ofReal (Real.exp (V * lambda ^ 2)))
    (ht : 0 <= t) :
    absTailProb P X t <=
      ENNReal.ofReal
        (2 * Real.exp (-((1 / 4) * subExponentialBernsteinRate t V B))) := by
  have hupper :=
    upperTailProb_le_exp_neg_quarter_bernsteinRate_of_mgf_bound
      (P := P) (X := X) (V := V) (B := B) (t := t)
      hX hV hB hMGF ht
  have hlower :=
    lowerTailProb_le_exp_neg_quarter_bernsteinRate_of_mgf_bound
      (P := P) (X := X) (V := V) (B := B) (t := t)
      hX hV hB hMGF ht
  let a : Real := -((1 / 4) * subExponentialBernsteinRate t V B)
  calc
    absTailProb P X t
        <= P (upperTailEvent X t ∪ lowerTailEvent X (-t)) :=
            measure_mono (absTailEvent_subset_upperTailEvent_union_lowerTailEvent_neg X t)
    _ <= P (upperTailEvent X t) + P (lowerTailEvent X (-t)) :=
            measure_union_le _ _
    _ <= ENNReal.ofReal (Real.exp a) + ENNReal.ofReal (Real.exp a) := by
            simpa [a] using add_le_add hupper hlower
    _ = ENNReal.ofReal (2 * Real.exp a) :=
            add_two_ofReal_exp a
    _ = ENNReal.ofReal
          (2 * Real.exp (-((1 / 4) * subExponentialBernsteinRate t V B))) := by
            rfl

/--
Local Bernstein small-deviation bound for a finite independent sum satisfying
the proof-facing subExponential MGF assumptions.

Formula reference: finite-sum version of the small-deviation Bernstein regime;
see https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)
-/
theorem
  absTailProb_le_two_mul_exp_neg_sq_div_varianceProxy_of_centeredSubExponentialMGFLIntegral_sum
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Omega} {K : ι → Real}
    (hV : 0 < varianceProxy K)
    (hB : 0 < maxScale K)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hMGF : ∀ i : ι, CenteredSubExponentialMGFLIntegral P (X i) (K i))
    {t : Real} (ht : 0 <= t)
    (htDomain : t <= 2 * varianceProxy K / maxScale K) :
    absTailProb P (fun omega => ∑ i : ι, X i omega) t <=
      ENNReal.ofReal
        (2 * Real.exp (-(t ^ 2 / (4 * varianceProxy K)))) := by
  have hXsum : IsRealRandomVariable P (fun omega => ∑ i : ι, X i omega) := by
    dsimp [IsRealRandomVariable, IsRandomVariable]
    exact Finset.measurable_sum (Finset.univ : Finset ι) (fun i _hi => (hMGF i).1)
  have hsum_mgf :=
    centeredSubExponentialMGFLIntegral_sum_mgf_bound_of_iIndepFun_maxScale
      (P := P) (X := X) (K := K) hB hIndep hMGF
  exact
    absTailProb_le_two_mul_exp_neg_sq_div_varianceProxy_of_mgf_bound_of_le
      (P := P) (X := fun omega => ∑ i : ι, X i omega)
      (V := varianceProxy K) (B := maxScale K) (t := t)
      hXsum hV hB hsum_mgf ht htDomain

/--
One-sided upper-tail scalar Bernstein min-form bound for a finite independent
sum satisfying the proof-facing subExponential MGF assumptions.

Formula reference: finite independent-sum Bernstein min-form upper tail; see
https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)
-/
theorem upperTailProb_le_exp_neg_quarter_bernsteinRate_of_centeredSubExponentialMGFLIntegral_sum
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Omega} {K : ι → Real}
    (hV : 0 < varianceProxy K)
    (hB : 0 < maxScale K)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hMGF : ∀ i : ι, CenteredSubExponentialMGFLIntegral P (X i) (K i))
    {t : Real} (ht : 0 <= t) :
    upperTailProb P (fun omega => ∑ i : ι, X i omega) t <=
      ENNReal.ofReal
        (Real.exp
          (-((1 / 4) *
            subExponentialBernsteinRate t (varianceProxy K) (maxScale K)))) := by
  have hXsum : IsRealRandomVariable P (fun omega => ∑ i : ι, X i omega) := by
    dsimp [IsRealRandomVariable, IsRandomVariable]
    exact Finset.measurable_sum (Finset.univ : Finset ι) (fun i _hi => (hMGF i).1)
  have hsum_mgf :=
    centeredSubExponentialMGFLIntegral_sum_mgf_bound_of_iIndepFun_maxScale
      (P := P) (X := X) (K := K) hB hIndep hMGF
  exact
    upperTailProb_le_exp_neg_quarter_bernsteinRate_of_mgf_bound
      (P := P) (X := fun omega => ∑ i : ι, X i omega)
      (V := varianceProxy K) (B := maxScale K) (t := t)
      hXsum hV hB hsum_mgf ht

/--
One-sided lower-tail scalar Bernstein min-form bound for a finite independent
sum satisfying the proof-facing subExponential MGF assumptions.

Formula reference: finite independent-sum Bernstein min-form lower tail; see
https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)
-/
theorem lowerTailProb_le_exp_neg_quarter_bernsteinRate_of_centeredSubExponentialMGFLIntegral_sum
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Omega} {K : ι → Real}
    (hV : 0 < varianceProxy K)
    (hB : 0 < maxScale K)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hMGF : ∀ i : ι, CenteredSubExponentialMGFLIntegral P (X i) (K i))
    {t : Real} (ht : 0 <= t) :
    lowerTailProb P (fun omega => ∑ i : ι, X i omega) (-t) <=
      ENNReal.ofReal
        (Real.exp
          (-((1 / 4) *
            subExponentialBernsteinRate t (varianceProxy K) (maxScale K)))) := by
  have hXsum : IsRealRandomVariable P (fun omega => ∑ i : ι, X i omega) := by
    dsimp [IsRealRandomVariable, IsRandomVariable]
    exact Finset.measurable_sum (Finset.univ : Finset ι) (fun i _hi => (hMGF i).1)
  have hsum_mgf :=
    centeredSubExponentialMGFLIntegral_sum_mgf_bound_of_iIndepFun_maxScale
      (P := P) (X := X) (K := K) hB hIndep hMGF
  exact
    lowerTailProb_le_exp_neg_quarter_bernsteinRate_of_mgf_bound
      (P := P) (X := fun omega => ∑ i : ι, X i omega)
      (V := varianceProxy K) (B := maxScale K) (t := t)
      hXsum hV hB hsum_mgf ht

/--
Full scalar Bernstein min-form tail bound for a finite independent sum
satisfying the proof-facing centered subExponential MGF assumptions.

Formula reference: two-sided finite independent-sum Bernstein min-form tail
bound; see
https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)

The constant is the conservative universal value `1/4`.
-/
theorem bernstein_sum_subExponential
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Omega} {K : ι → Real}
    (hV : 0 < varianceProxy K)
    (hB : 0 < maxScale K)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hMGF : ∀ i : ι, CenteredSubExponentialMGFLIntegral P (X i) (K i))
    {t : Real} (ht : 0 <= t) :
    absTailProb P (fun omega => ∑ i : ι, X i omega) t <=
      ENNReal.ofReal
        (2 * Real.exp
          (-((1 / 4) *
            subExponentialBernsteinRate t (varianceProxy K) (maxScale K)))) := by
  have hXsum : IsRealRandomVariable P (fun omega => ∑ i : ι, X i omega) := by
    dsimp [IsRealRandomVariable, IsRandomVariable]
    exact Finset.measurable_sum (Finset.univ : Finset ι) (fun i _hi => (hMGF i).1)
  have hsum_mgf :=
    centeredSubExponentialMGFLIntegral_sum_mgf_bound_of_iIndepFun_maxScale
      (P := P) (X := X) (K := K) hB hIndep hMGF
  exact
    absTailProb_le_two_mul_exp_neg_quarter_bernsteinRate_of_mgf_bound
      (P := P) (X := fun omega => ∑ i : ι, X i omega)
      (V := varianceProxy K) (B := maxScale K) (t := t)
      hXsum hV hB hsum_mgf ht

/--
Deterministic weighted scalar Bernstein min-form tail bound for a finite
independent sum satisfying the proof-facing centered subExponential MGF
assumptions.

Formula reference: weighted two-sided Bernstein min-form tail bound with
variance proxy `sum_i c_i^2 * K_i^2` and max scale `max_i |c_i| * K_i`; see
https://en.wikipedia.org/wiki/Bernstein_inequalities_(probability_theory)

The weighted variance proxy is `sum_i c_i^2 * K_i^2`, and the weighted max
scale is `max_i |c_i| * K_i`.  The positive weighted denominators are explicit,
so zero weights are allowed as long as the total weighted proxies are positive.
-/
theorem bernstein_weighted_sum_subExponential
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {X : ι -> RealRandomVariable Omega} {K c : ι -> Real}
    (hV : 0 < weightedVarianceProxy c K)
    (hB : 0 < weightedMaxScale c K)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hMGF : ∀ i : ι, CenteredSubExponentialMGFLIntegral P (X i) (K i))
    {t : Real} (ht : 0 <= t) :
    absTailProb P (fun omega => ∑ i : ι, c i * X i omega) t <=
      ENNReal.ofReal
        (2 * Real.exp
          (-((1 / 4) *
            subExponentialBernsteinRate
              t (weightedVarianceProxy c K) (weightedMaxScale c K)))) := by
  have hXsum :
      IsRealRandomVariable P (fun omega => ∑ i : ι, c i * X i omega) := by
    exact
      isRealRandomVariable_finset_weighted_sum
        (P := P) (s := Finset.univ) c (X := X)
        (fun i _hi => (hMGF i).1)
  have hsum_mgf :=
    centeredSubExponentialMGFLIntegral_weighted_sum_mgf_bound_of_iIndepFun_maxScale
      (P := P) (X := X) (K := K) (c := c) hB hIndep hMGF
  exact
    absTailProb_le_two_mul_exp_neg_quarter_bernsteinRate_of_mgf_bound
      (P := P) (X := fun omega => ∑ i : ι, c i * X i omega)
      (V := weightedVarianceProxy c K) (B := weightedMaxScale c K) (t := t)
      hXsum hV hB hsum_mgf ht

/--
Small-deviation upper-tail Chernoff bound from the lintegral local MGF
predicate.

Formula reference: local subExponential MGF plus Chernoff yields
`exp(-t^2/(4*K^2))` in the small-deviation range; see
https://en.wikipedia.org/wiki/Chernoff_bound

The optimizer `lambda = t / (2*K^2)` is inside the local MGF domain under the
visible assumption `t <= K`.
-/
theorem upperTailProb_le_exp_neg_sq_of_centeredSubExponentialMGFLIntegral_of_le
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {K t : Real}
    (hMGF : CenteredSubExponentialMGFLIntegral P X K)
    (ht : 0 <= t) (htK : t <= K) :
    upperTailProb P X t <=
      ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * K ^ 2)))) := by
  rcases hMGF with ⟨hX, hK, hbound⟩
  let lambda : Real := t / (2 * K ^ 2)
  have hKsq_pos : 0 < K ^ 2 := sq_pos_of_pos hK
  have hden_pos : 0 < 2 * K ^ 2 := mul_pos (by norm_num) hKsq_pos
  have hlambda_nonneg : 0 <= lambda := by
    exact div_nonneg ht hden_pos.le
  have hlambda_domain : |lambda| <= 1 / K := by
    rw [abs_of_nonneg hlambda_nonneg]
    have ht_twoK : t <= 2 * K := by nlinarith [htK, hK]
    dsimp [lambda]
    rw [div_le_iff₀ hden_pos]
    field_simp [hK.ne']
    nlinarith [ht_twoK]
  let f : Omega → ENNReal := fun omega =>
    ENNReal.ofReal (Real.exp (lambda * X omega))
  have h_meas : AEMeasurable f P := by
    have h_real : Measurable fun omega => Real.exp (lambda * X omega) :=
      (hX.const_mul lambda).exp
    exact h_real.aemeasurable.ennreal_ofReal
  have h_threshold_ne_zero :
      ENNReal.ofReal (Real.exp (lambda * t)) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h_markov :
      P {omega | ENNReal.ofReal (Real.exp (lambda * t)) <= f omega} <=
        (∫⁻ omega, f omega ∂P) / ENNReal.ofReal (Real.exp (lambda * t)) :=
    MeasureTheory.meas_ge_le_lintegral_div
      h_meas h_threshold_ne_zero ENNReal.ofReal_ne_top
  have h_event :
      upperTailEvent X t ⊆
        {omega | ENNReal.ofReal (Real.exp (lambda * t)) <= f omega} := by
    intro omega homega
    have hmul : lambda * t <= lambda * X omega :=
      mul_le_mul_of_nonneg_left homega hlambda_nonneg
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hmul)
  calc
    upperTailProb P X t
        <= P {omega | ENNReal.ofReal (Real.exp (lambda * t)) <= f omega} :=
            measure_mono h_event
    _ <= (∫⁻ omega, f omega ∂P) / ENNReal.ofReal (Real.exp (lambda * t)) := h_markov
    _ <= ENNReal.ofReal (Real.exp (K ^ 2 * lambda ^ 2)) /
          ENNReal.ofReal (Real.exp (lambda * t)) := by
            gcongr
            exact hbound lambda hlambda_domain
    _ = ENNReal.ofReal (Real.exp (K ^ 2 * lambda ^ 2 - lambda * t)) :=
            ofReal_exp_div_exp_eq_ofReal_exp_sub
              (K ^ 2 * lambda ^ 2) (lambda * t)
    _ = ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * K ^ 2)))) := by
            apply congrArg ENNReal.ofReal
            apply congrArg Real.exp
            simp only [lambda]
            field_simp [hK.ne']
            ring

/--
Small-deviation lower-tail Chernoff bound from the lintegral local MGF predicate.

Formula reference: lower-tail local subExponential Chernoff bound with the same
`exp(-t^2/(4*K^2))` exponent; see
https://en.wikipedia.org/wiki/Chernoff_bound
-/
theorem lowerTailProb_le_exp_neg_sq_of_centeredSubExponentialMGFLIntegral_of_le
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {K t : Real}
    (hMGF : CenteredSubExponentialMGFLIntegral P X K)
    (ht : 0 <= t) (htK : t <= K) :
    lowerTailProb P X (-t) <=
      ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * K ^ 2)))) := by
  rcases hMGF with ⟨hX, hK, hbound⟩
  let lambda : Real := -t / (2 * K ^ 2)
  have hKsq_pos : 0 < K ^ 2 := sq_pos_of_pos hK
  have hden_pos : 0 < 2 * K ^ 2 := mul_pos (by norm_num) hKsq_pos
  have hlambda_nonpos : lambda <= 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hden_pos.le
  have hlambda_domain : |lambda| <= 1 / K := by
    rw [abs_of_nonpos hlambda_nonpos]
    have ht_twoK : t <= 2 * K := by nlinarith [htK, hK]
    dsimp [lambda]
    rw [neg_div, neg_neg]
    rw [div_le_iff₀ hden_pos]
    field_simp [hK.ne']
    nlinarith [ht_twoK]
  let f : Omega → ENNReal := fun omega =>
    ENNReal.ofReal (Real.exp (lambda * X omega))
  have h_meas : AEMeasurable f P := by
    have h_real : Measurable fun omega => Real.exp (lambda * X omega) :=
      (hX.const_mul lambda).exp
    exact h_real.aemeasurable.ennreal_ofReal
  have h_threshold_ne_zero :
      ENNReal.ofReal (Real.exp (lambda * (-t))) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h_markov :
      P {omega | ENNReal.ofReal (Real.exp (lambda * (-t))) <= f omega} <=
        (∫⁻ omega, f omega ∂P) /
          ENNReal.ofReal (Real.exp (lambda * (-t))) :=
    MeasureTheory.meas_ge_le_lintegral_div
      h_meas h_threshold_ne_zero ENNReal.ofReal_ne_top
  have h_event :
      lowerTailEvent X (-t) ⊆
        {omega | ENNReal.ofReal (Real.exp (lambda * (-t))) <= f omega} := by
    intro omega homega
    have hmul : lambda * (-t) <= lambda * X omega :=
      mul_le_mul_of_nonpos_left homega hlambda_nonpos
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hmul)
  calc
    lowerTailProb P X (-t)
        <= P {omega | ENNReal.ofReal (Real.exp (lambda * (-t))) <= f omega} :=
            measure_mono h_event
    _ <= (∫⁻ omega, f omega ∂P) /
          ENNReal.ofReal (Real.exp (lambda * (-t))) := h_markov
    _ <= ENNReal.ofReal (Real.exp (K ^ 2 * lambda ^ 2)) /
          ENNReal.ofReal (Real.exp (lambda * (-t))) := by
            gcongr
            exact hbound lambda hlambda_domain
    _ = ENNReal.ofReal (Real.exp (K ^ 2 * lambda ^ 2 - lambda * (-t))) :=
            ofReal_exp_div_exp_eq_ofReal_exp_sub
              (K ^ 2 * lambda ^ 2) (lambda * (-t))
    _ = ENNReal.ofReal (Real.exp (-(t ^ 2 / (4 * K ^ 2)))) := by
            apply congrArg ENNReal.ofReal
            apply congrArg Real.exp
            simp only [lambda]
            field_simp [hK.ne']
            ring

/--
Two-sided local small-deviation tail bound from the lintegral local MGF predicate.

Formula reference: combines the local upper/lower Chernoff bounds into
`P(|X| >= t) <= 2 * exp(-t^2/(4*K^2))`; see
https://en.wikipedia.org/wiki/Chernoff_bound
-/
theorem absTailProb_le_two_mul_exp_neg_sq_of_centeredSubExponentialMGFLIntegral_of_le
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {K t : Real}
    (hMGF : CenteredSubExponentialMGFLIntegral P X K)
    (ht : 0 <= t) (htK : t <= K) :
    absTailProb P X t <=
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (4 * K ^ 2)))) := by
  have hupper :=
    upperTailProb_le_exp_neg_sq_of_centeredSubExponentialMGFLIntegral_of_le
      (P := P) (X := X) (K := K) (t := t) hMGF ht htK
  have hlower :=
    lowerTailProb_le_exp_neg_sq_of_centeredSubExponentialMGFLIntegral_of_le
      (P := P) (X := X) (K := K) (t := t) hMGF ht htK
  let a : Real := -(t ^ 2 / (4 * K ^ 2))
  calc
    absTailProb P X t
        <= P (upperTailEvent X t ∪ lowerTailEvent X (-t)) :=
            measure_mono (absTailEvent_subset_upperTailEvent_union_lowerTailEvent_neg X t)
    _ <= P (upperTailEvent X t) + P (lowerTailEvent X (-t)) :=
            measure_union_le _ _
    _ <= ENNReal.ofReal (Real.exp a) + ENNReal.ofReal (Real.exp a) := by
            simpa [a] using add_le_add hupper hlower
    _ = ENNReal.ofReal (2 * Real.exp a) :=
            add_two_ofReal_exp a
    _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (4 * K ^ 2)))) := by
            rfl

end

end HighDimProb
