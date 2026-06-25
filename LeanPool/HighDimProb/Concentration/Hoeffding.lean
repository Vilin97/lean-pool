/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Concentration.SubGaussianSums

/-!
# Hoeffding bounds for bounded variables

This file packages Mathlib's one-variable Hoeffding lemma for bounded centered
real random variables with the existing HighDimProb finite independent-sum MGF
and tail infrastructure, including sharp centered, non-centered, and
deterministic weighted finite-sum forms.

Verified Wikipedia references:
* Hoeffding inequality: https://en.wikipedia.org/wiki/Hoeffding%27s_inequality
* Chernoff bound: https://en.wikipedia.org/wiki/Chernoff_bound
* Sub-Gaussian distribution: https://en.wikipedia.org/wiki/Sub-Gaussian_distribution
-/

namespace HighDimProb

open MeasureTheory ProbabilityTheory

noncomputable section

open scoped BigOperators NNReal

private lemma ofReal_exp_div_exp_eq_ofReal_exp_sub_local (a b : ℝ) :
    ENNReal.ofReal (Real.exp a) / ENNReal.ofReal (Real.exp b) =
      ENNReal.ofReal (Real.exp (a - b)) := by
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos b)]
  apply congrArg ENNReal.ofReal
  rw [Real.exp_sub]

private lemma add_two_ofReal_exp_local (a : ℝ) :
    ENNReal.ofReal (Real.exp a) + ENNReal.ofReal (Real.exp a) =
      ENNReal.ofReal (2 * Real.exp a) := by
  rw [← ENNReal.ofReal_add (Real.exp_pos a).le (Real.exp_pos a).le]
  congr 1
  ring

/-- Expectation commutes with finite sums of integrable real random variables. -/
theorem expect_finset_sum {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {s : Finset ι} {X : ι → RealRandomVariable Ω}
    (hX : ∀ i, i ∈ s → IntegrableRealRandomVariable P (X i)) :
    expect P (fun ω => ∑ i ∈ s, X i ω) =
      ∑ i ∈ s, expect P (X i) := by
  change (∫ ω, ∑ i ∈ s, X i ω ∂P) =
    ∑ i ∈ s, ∫ ω, X i ω ∂P
  exact MeasureTheory.integral_finsetSum s hX

/-- Independent real variables remain independent after subtracting their means. -/
theorem iIndepFun_centered_of_iIndepFun {Ω ι : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {X : ι → RealRandomVariable Ω}
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    ProbabilityTheory.iIndepFun (fun i : ι => centered P (X i)) P := by
  have h :=
    hIndep.comp
      (fun i : ι => fun x : ℝ => x - mean P (X i))
      (by
        intro i
        fun_prop)
  change
    ProbabilityTheory.iIndepFun
      (fun i : ι => (fun x : ℝ => x - mean P (X i)) ∘ X i) P
  exact h

/--
If `X` is a.e. bounded in `[a,b]`, then its centered version is a.e. bounded
in the shifted interval `[a - mean X, b - mean X]`.
-/
theorem ae_mem_Icc_centered_of_ae_mem_Icc {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : RealRandomVariable Ω} {a b : ℝ}
    (hmem : ∀ᵐ ω ∂P, X ω ∈ Set.Icc a b) :
    ∀ᵐ ω ∂P, centered P X ω ∈
      Set.Icc (a - mean P X) (b - mean P X) := by
  exact hmem.mono fun ω hω => by
    change X ω - mean P X ∈ Set.Icc (a - mean P X) (b - mean P X)
    exact ⟨sub_le_sub_right hω.1 _, sub_le_sub_right hω.2 _⟩

/--
The sum of centered variables is the original sum minus the expectation of the
sum, for finite integrable families.
-/
theorem sum_centered_eq_sum_sub_expect_sum {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}
    {X : ι → RealRandomVariable Ω}
    (hX : ∀ i : ι, IntegrableRealRandomVariable P (X i)) :
    (fun ω => ∑ i : ι, centered P (X i) ω) =
      fun ω => (∑ i : ι, X i ω) -
        expect P (fun ω => ∑ i : ι, X i ω) := by
  have hsum_expect :
      expect P (fun ω => ∑ i : ι, X i ω) =
        ∑ i : ι, mean P (X i) := by
    calc
      expect P (fun ω => ∑ i : ι, X i ω)
          = ∑ i : ι, expect P (X i) :=
              expect_finset_sum (P := P) (s := Finset.univ) (X := X)
                (fun i _hi => hX i)
      _ = ∑ i : ι, mean P (X i) := by
              rfl
  funext ω
  calc
    (∑ i : ι, centered P (X i) ω)
        = ∑ i : ι, (X i ω - mean P (X i)) := by
            rfl
    _ = (∑ i : ι, X i ω) - ∑ i : ι, mean P (X i) := by
            rw [Finset.sum_sub_distrib]
    _ = (∑ i : ι, X i ω) -
        expect P (fun ω => ∑ i : ι, X i ω) := by
            rw [hsum_expect]

/--
The weighted sum of centered variables is the weighted sum minus its
expectation, for finite integrable families.
-/
theorem sum_weighted_centered_eq_weighted_sum_sub_expect_weighted_sum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}
    {X : ι → RealRandomVariable Ω} (c : ι → ℝ)
    (hX : ∀ i : ι, IntegrableRealRandomVariable P (X i)) :
    (fun ω => ∑ i : ι, c i * centered P (X i) ω) =
      fun ω => (∑ i : ι, c i * X i ω) -
        expect P (fun ω => ∑ i : ι, c i * X i ω) := by
  have hsum_expect :
      expect P (fun ω => ∑ i : ι, c i * X i ω) =
        ∑ i : ι, c i * mean P (X i) := by
    calc
      expect P (fun ω => ∑ i : ι, c i * X i ω)
          = ∑ i : ι, ∫ ω, c i * X i ω ∂P := by
              change (∫ ω, ∑ i : ι, c i * X i ω ∂P) =
                ∑ i : ι, ∫ ω, c i * X i ω ∂P
              exact MeasureTheory.integral_finsetSum Finset.univ
                (fun i _hi => (hX i).const_mul (c i))
      _ = ∑ i : ι, c i * mean P (X i) := by
              apply Finset.sum_congr rfl
              intro i _hi
              change (∫ ω, c i * X i ω ∂P) = c i * (∫ ω, X i ω ∂P)
              rw [MeasureTheory.integral_const_mul]
  funext ω
  calc
    (∑ i : ι, c i * centered P (X i) ω)
        = ∑ i : ι, (c i * X i ω - c i * mean P (X i)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            change c i * (X i ω - mean P (X i)) =
              c i * X i ω - c i * mean P (X i)
            ring
    _ = (∑ i : ι, c i * X i ω) -
        ∑ i : ι, c i * mean P (X i) := by
            rw [Finset.sum_sub_distrib]
    _ = (∑ i : ι, c i * X i ω) -
        expect P (fun ω => ∑ i : ι, c i * X i ω) := by
            rw [hsum_expect]

/--
Sharp one-sided Chernoff bound from an eighth-variance MGF estimate.

Formula reference: Chernoff bounds apply Markov to `exp(lambda * Y)` and
optimize the exponential moment bound; see
https://en.wikipedia.org/wiki/Chernoff_bound

The hypothesis is the Hoeffding-specific normal form
`E exp(lambda * Y) <= exp(lambda^2 * V / 8)`. Optimizing at
`lambda = 4*t/V` gives the classical exponent `-2*t^2/V`.
-/
theorem upperTailProb_le_exp_neg_two_mul_sq_div_of_mgf_eighth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : RealRandomVariable Ω} {V t : ℝ}
    (hY : IsRealRandomVariable P Y)
    (hV : 0 < V)
    (hmgf : ∀ lambda : ℝ,
      (∫⁻ ω, ENNReal.ofReal (Real.exp (lambda * Y ω)) ∂P) ≤
        ENNReal.ofReal (Real.exp (lambda ^ 2 * V / 8)))
    (ht : 0 ≤ t) :
    upperTailProb P Y t ≤
      ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / V))) := by
  let lambda : ℝ := 4 * t / V
  have hlambda_nonneg : 0 ≤ lambda := by
    exact div_nonneg (mul_nonneg (by norm_num) ht) hV.le
  let f : Ω → ENNReal := fun ω => ENNReal.ofReal (Real.exp (lambda * Y ω))
  have h_meas : AEMeasurable f P := by
    have h_real : Measurable fun ω => Real.exp (lambda * Y ω) :=
      (hY.const_mul lambda).exp
    exact h_real.aemeasurable.ennreal_ofReal
  have h_threshold_ne_zero :
      ENNReal.ofReal (Real.exp (lambda * t)) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h_markov :
      P {ω | ENNReal.ofReal (Real.exp (lambda * t)) ≤ f ω} ≤
        (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp (lambda * t)) :=
    MeasureTheory.meas_ge_le_lintegral_div h_meas h_threshold_ne_zero ENNReal.ofReal_ne_top
  have h_event :
      upperTailEvent Y t ⊆
        {ω | ENNReal.ofReal (Real.exp (lambda * t)) ≤ f ω} := by
    intro ω hω
    have hmul : lambda * t ≤ lambda * Y ω :=
      mul_le_mul_of_nonneg_left hω hlambda_nonneg
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hmul)
  calc
    upperTailProb P Y t
        ≤ P {ω | ENNReal.ofReal (Real.exp (lambda * t)) ≤ f ω} :=
            measure_mono h_event
    _ ≤ (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp (lambda * t)) := h_markov
    _ ≤ ENNReal.ofReal (Real.exp (lambda ^ 2 * V / 8)) /
          ENNReal.ofReal (Real.exp (lambda * t)) := by
            gcongr
            exact hmgf lambda
    _ = ENNReal.ofReal (Real.exp (lambda ^ 2 * V / 8 - lambda * t)) :=
            ofReal_exp_div_exp_eq_ofReal_exp_sub_local
              (lambda ^ 2 * V / 8) (lambda * t)
    _ = ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / V))) := by
            apply congrArg ENNReal.ofReal
            apply congrArg Real.exp
            simp only [lambda]
            field_simp [hV.ne']
            ring

/--
Sharp lower-tail Chernoff bound from an eighth-variance MGF estimate.

Formula reference: this is the lower-tail counterpart of the same Chernoff
optimization used for Hoeffding-type bounds; see
https://en.wikipedia.org/wiki/Chernoff_bound
-/
theorem lowerTailProb_le_exp_neg_two_mul_sq_div_of_mgf_eighth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : RealRandomVariable Ω} {V t : ℝ}
    (hY : IsRealRandomVariable P Y)
    (hV : 0 < V)
    (hmgf : ∀ lambda : ℝ,
      (∫⁻ ω, ENNReal.ofReal (Real.exp (lambda * Y ω)) ∂P) ≤
        ENNReal.ofReal (Real.exp (lambda ^ 2 * V / 8)))
    (ht : 0 ≤ t) :
    lowerTailProb P Y (-t) ≤
      ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / V))) := by
  let lambda : ℝ := -(4 * t / V)
  have hbase_nonneg : 0 ≤ 4 * t / V := by
    exact div_nonneg (mul_nonneg (by norm_num) ht) hV.le
  have hlambda_nonpos : lambda ≤ 0 := by
    exact neg_nonpos.mpr hbase_nonneg
  let f : Ω → ENNReal := fun ω => ENNReal.ofReal (Real.exp (lambda * Y ω))
  have h_meas : AEMeasurable f P := by
    have h_real : Measurable fun ω => Real.exp (lambda * Y ω) :=
      (hY.const_mul lambda).exp
    exact h_real.aemeasurable.ennreal_ofReal
  have h_threshold_ne_zero :
      ENNReal.ofReal (Real.exp (lambda * (-t))) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have h_markov :
      P {ω | ENNReal.ofReal (Real.exp (lambda * (-t))) ≤ f ω} ≤
        (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp (lambda * (-t))) :=
    MeasureTheory.meas_ge_le_lintegral_div h_meas h_threshold_ne_zero ENNReal.ofReal_ne_top
  have h_event :
      lowerTailEvent Y (-t) ⊆
        {ω | ENNReal.ofReal (Real.exp (lambda * (-t))) ≤ f ω} := by
    intro ω hω
    have hmul : lambda * (-t) ≤ lambda * Y ω :=
      mul_le_mul_of_nonpos_left hω hlambda_nonpos
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hmul)
  calc
    lowerTailProb P Y (-t)
        ≤ P {ω | ENNReal.ofReal (Real.exp (lambda * (-t))) ≤ f ω} :=
            measure_mono h_event
    _ ≤ (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp (lambda * (-t))) := h_markov
    _ ≤ ENNReal.ofReal (Real.exp (lambda ^ 2 * V / 8)) /
          ENNReal.ofReal (Real.exp (lambda * (-t))) := by
            gcongr
            exact hmgf lambda
    _ = ENNReal.ofReal (Real.exp (lambda ^ 2 * V / 8 - lambda * (-t))) :=
            ofReal_exp_div_exp_eq_ofReal_exp_sub_local
              (lambda ^ 2 * V / 8) (lambda * (-t))
    _ = ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / V))) := by
            apply congrArg ENNReal.ofReal
            apply congrArg Real.exp
            simp only [lambda]
            field_simp [hV.ne']
            ring

/--
Sharp two-sided absolute-tail bound from an eighth-variance MGF estimate.

Formula reference: combines one-sided Chernoff bounds into the two-sided
Hoeffding-style form `P(|Y| >= t) <= 2 * exp(-2*t^2/V)`; see
https://en.wikipedia.org/wiki/Hoeffding%27s_inequality
-/
theorem absTailProb_le_two_mul_exp_neg_two_mul_sq_div_of_mgf_eighth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : RealRandomVariable Ω} {V t : ℝ}
    (hY : IsRealRandomVariable P Y)
    (hV : 0 < V)
    (hmgf : ∀ lambda : ℝ,
      (∫⁻ ω, ENNReal.ofReal (Real.exp (lambda * Y ω)) ∂P) ≤
        ENNReal.ofReal (Real.exp (lambda ^ 2 * V / 8)))
    (ht : 0 ≤ t) :
    absTailProb P Y t ≤
      ENNReal.ofReal (2 * Real.exp (-(2 * t ^ 2 / V))) := by
  have hupper :=
    upperTailProb_le_exp_neg_two_mul_sq_div_of_mgf_eighth
      (P := P) (Y := Y) (V := V) (t := t) hY hV hmgf ht
  have hlower :=
    lowerTailProb_le_exp_neg_two_mul_sq_div_of_mgf_eighth
      (P := P) (Y := Y) (V := V) (t := t) hY hV hmgf ht
  let exponent : ℝ := -(2 * t ^ 2 / V)
  calc
    absTailProb P Y t
        ≤ P (upperTailEvent Y t ∪ lowerTailEvent Y (-t)) :=
            measure_mono (absTailEvent_subset_upperTailEvent_union_lowerTailEvent_neg Y t)
    _ ≤ P (upperTailEvent Y t) + P (lowerTailEvent Y (-t)) :=
            measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp exponent) + ENNReal.ofReal (Real.exp exponent) := by
            simpa [exponent] using add_le_add hupper hlower
    _ = ENNReal.ofReal (2 * Real.exp exponent) :=
            add_two_ofReal_exp_local exponent

/--
A bounded centered real random variable is centered subGaussian.

Formula reference: bounded variables are sub-Gaussian via Hoeffding's lemma;
see the sub-Gaussian generalization discussion at
https://en.wikipedia.org/wiki/Hoeffding%27s_inequality

This a.e.-bounded wrapper reuses Mathlib's Hoeffding lemma
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` with
HighDimProb's `Centered` and `CenteredSubGaussianMGF` interfaces. The scale is
the half-width `(b - a) / 2`.
-/
theorem centeredSubGaussianMGF_of_ae_mem_Icc_of_centered
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {a b : ℝ}
    (hX : IsRealRandomVariable P X)
    (hmem : ∀ᵐ ω ∂P, X ω ∈ Set.Icc a b)
    (hcentered : Centered P X)
    (hwidth : 0 < b - a) :
    CenteredSubGaussianMGF P X ((b - a) / 2) := by
  refine ⟨div_pos hwidth two_pos, ?_⟩
  have hzero : ∫ ω, X ω ∂P = 0 := by
    exact hcentered
  have hsub :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (X := X) (a := a) (b := b) hX.aemeasurable hmem hzero
  convert hsub using 1
  apply Subtype.ext
  simp [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hwidth)]

/--
Pointwise-bounded version of
`centeredSubGaussianMGF_of_ae_mem_Icc_of_centered`.
-/
theorem centeredSubGaussianMGF_of_forall_mem_Icc_of_centered
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {a b : ℝ}
    (hX : IsRealRandomVariable P X)
    (hmem : ∀ ω, X ω ∈ Set.Icc a b)
    (hcentered : Centered P X)
    (hwidth : 0 < b - a) :
    CenteredSubGaussianMGF P X ((b - a) / 2) :=
  centeredSubGaussianMGF_of_ae_mem_Icc_of_centered
    (P := P) (X := X) (a := a) (b := b)
    hX (ae_of_all P hmem) hcentered hwidth

/--
Finite independent sums of bounded centered variables are centered
subGaussian.

Formula reference: the sum proxy is the square-root of the sum of squared
half-widths, matching the MGF route behind Hoeffding bounds; see
https://en.wikipedia.org/wiki/Hoeffding%27s_inequality

The scale is `sqrt (sum_i ((b_i - a_i) / 2)^2)`, inherited directly from the
one-variable half-width MGF scale and the existing independent finite-sum MGF
closure theorem.
-/
theorem centeredSubGaussianMGF_sum_of_iIndepFun_bounded_centered
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Ω} {a b : ι → ℝ}
    (hpos : 0 < ∑ i : ι, ((b i - a i) / 2) ^ 2)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hX : ∀ i : ι, IsRealRandomVariable P (X i))
    (hmem : ∀ i : ι, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (a i) (b i))
    (hcentered : ∀ i : ι, Centered P (X i))
    (hwidth : ∀ i : ι, 0 < b i - a i) :
    CenteredSubGaussianMGF P
      (fun ω => ∑ i : ι, X i ω)
      (Real.sqrt (∑ i : ι, ((b i - a i) / 2) ^ 2)) := by
  exact
    centeredSubGaussianMGF_sum_of_iIndepFun_of_pos
      (P := P) (X := X) (K := fun i : ι => (b i - a i) / 2)
      hpos hIndep
      (fun i =>
        centeredSubGaussianMGF_of_ae_mem_Icc_of_centered
          (P := P) (X := X i) (a := a i) (b := b i)
          (hX i) (hmem i) (hcentered i) (hwidth i))

/--
Two-sided subGaussian tail corollary for finite independent sums of bounded
centered variables.

Formula reference: this is the sub-Gaussian tail form
`P(|sum_i X_i| >= t) <= 2 * exp(-c*t^2 / sum_i ||X_i||_psi2^2)`; see
https://en.wikipedia.org/wiki/Hoeffding%27s_inequality

The tail scale doubles the MGF scale through
`subGaussianTail_of_centeredSubGaussianMGF`.
-/
theorem subGaussianTail_sum_of_iIndepFun_bounded_centered
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Ω} {a b : ι → ℝ}
    (hpos : 0 < ∑ i : ι, ((b i - a i) / 2) ^ 2)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hX : ∀ i : ι, IsRealRandomVariable P (X i))
    (hmem : ∀ i : ι, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (a i) (b i))
    (hcentered : ∀ i : ι, Centered P (X i))
    (hwidth : ∀ i : ι, 0 < b i - a i) :
    SubGaussianTail P
      (fun ω => ∑ i : ι, X i ω)
      (2 * Real.sqrt (∑ i : ι, ((b i - a i) / 2) ^ 2)) := by
  exact
    subGaussianTail_sum_of_iIndepFun_of_pos
      (P := P) (X := X) (K := fun i : ι => (b i - a i) / 2)
      hX hpos hIndep
      (fun i =>
        centeredSubGaussianMGF_of_ae_mem_Icc_of_centered
          (P := P) (X := X i) (a := a i) (b := b i)
          (hX i) (hmem i) (hcentered i) (hwidth i))

/--
Conservative, non-sharp HighDimProb-facing Hoeffding bound for finite
independent sums of bounded centered variables.

Formula reference: compare the classical two-sided Hoeffding formula
`P(|sum_i X_i - E[sum_i X_i]| >= t) <=
2 * exp(-2*t^2 / sum_i (b_i-a_i)^2)` at
https://en.wikipedia.org/wiki/Hoeffding%27s_inequality

The denominator is `sum_i (b_i - a_i)^2`. This follows from the half-width MGF
scale and the existing MGF-to-tail bridge, so it is a conservative two-sided
constant rather than the sharp classical `2` in the exponent.
-/
theorem hoeffding_sum_bounded_centered
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Ω} {a b : ι → ℝ}
    (hpos : 0 < ∑ i : ι, ((b i - a i) / 2) ^ 2)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hX : ∀ i : ι, IsRealRandomVariable P (X i))
    (hmem : ∀ i : ι, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (a i) (b i))
    (hcentered : ∀ i : ι, Centered P (X i))
    (hwidth : ∀ i : ι, 0 < b i - a i)
    {t : ℝ} (ht : 0 ≤ t) :
    absTailProb P (fun ω => ∑ i : ι, X i ω) t ≤
      ENNReal.ofReal
        (2 * Real.exp (-(t ^ 2 / ∑ i : ι, (b i - a i) ^ 2))) := by
  have htail :=
    (subGaussianTail_sum_of_iIndepFun_bounded_centered
      (P := P) (X := X) (a := a) (b := b)
      hpos hIndep hX hmem hcentered hwidth).2 t ht
  have hsum_nonneg :
      0 ≤ ∑ i : ι, ((b i - a i) / 2) ^ 2 :=
    le_of_lt hpos
  have hden :
      (2 * Real.sqrt (∑ i : ι, ((b i - a i) / 2) ^ 2)) ^ 2 =
        ∑ i : ι, (b i - a i) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hsum_nonneg]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  simpa [hden] using htail

/--
Sharp centered Hoeffding bound for finite independent sums of bounded centered
variables.

Formula reference: this proves the classical two-sided exponent
`-2*t^2 / sum_i (b_i-a_i)^2`; see
https://en.wikipedia.org/wiki/Hoeffding%27s_inequality

This theorem keeps the existing conservative `SubGaussianTail` API unchanged.
It uses the sharper Hoeffding-specific MGF constant, optimizing
`E exp(lambda * sum_i X_i) <= exp(lambda^2 * sum_i (b_i-a_i)^2 / 8)`
directly.
-/
theorem hoeffding_sum_bounded_centered_sharp
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Ω} {a b : ι → ℝ}
    (hpos : 0 < ∑ i : ι, (b i - a i) ^ 2)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hX : ∀ i : ι, IsRealRandomVariable P (X i))
    (hmem : ∀ i : ι, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (a i) (b i))
    (hcentered : ∀ i : ι, Centered P (X i))
    (hwidth : ∀ i : ι, 0 < b i - a i)
    {t : ℝ} (ht : 0 ≤ t) :
    absTailProb P (fun ω => ∑ i : ι, X i ω) t ≤
      ENNReal.ofReal
        (2 * Real.exp (-(2 * t ^ 2 / ∑ i : ι, (b i - a i) ^ 2))) := by
  have hhalf_eq :
      (∑ i : ι, ((b i - a i) / 2) ^ 2) =
        (∑ i : ι, (b i - a i) ^ 2) / 4 := by
    calc
      (∑ i : ι, ((b i - a i) / 2) ^ 2)
          = ∑ i : ι, (b i - a i) ^ 2 / 4 := by
              apply Finset.sum_congr rfl
              intro i _hi
              ring
      _ = (∑ i : ι, (b i - a i) ^ 2) / 4 := by
              rw [Finset.sum_div]
  have hhalf_pos :
      0 < ∑ i : ι, ((b i - a i) / 2) ^ 2 := by
    rw [hhalf_eq]
    exact div_pos hpos (by norm_num)
  have hMGF :=
    centeredSubGaussianMGF_sum_of_iIndepFun_bounded_centered
      (P := P) (X := X) (a := a) (b := b)
      hhalf_pos hIndep hX hmem hcentered hwidth
  have hsumX : IsRealRandomVariable P (fun ω => ∑ i : ι, X i ω) :=
    isRealRandomVariable_finset_sum
      (P := P) (s := Finset.univ) (X := X)
      (fun i _hi => hX i)
  have hsharp_mgf :
      ∀ lambda : ℝ,
        (∫⁻ ω, ENNReal.ofReal (Real.exp (lambda * (∑ i : ι, X i ω))) ∂P) ≤
          ENNReal.ofReal
            (Real.exp (lambda ^ 2 * (∑ i : ι, (b i - a i) ^ 2) / 8)) := by
    intro lambda
    have h_nonneg :
        0 ≤ᵐ[P] fun ω => Real.exp (lambda * (∑ i : ι, X i ω)) :=
      ae_of_all P fun _ => (Real.exp_pos _).le
    have h_lintegral :
        (∫⁻ ω, ENNReal.ofReal (Real.exp (lambda * (∑ i : ι, X i ω))) ∂P) =
          ENNReal.ofReal
            (ProbabilityTheory.mgf (fun ω => ∑ i : ι, X i ω) P lambda) := by
      rw [ProbabilityTheory.mgf]
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hMGF.2.integrable_exp_mul lambda) h_nonneg).symm
    have hS_nonneg :
        0 ≤ ∑ i : ι, ((b i - a i) / 2) ^ 2 :=
      le_of_lt hhalf_pos
    have h_exp_arg :
        (Real.sqrt (∑ i : ι, ((b i - a i) / 2) ^ 2)) ^ 2 *
            lambda ^ 2 / 2 ≤
          lambda ^ 2 * (∑ i : ι, (b i - a i) ^ 2) / 8 := by
      rw [Real.sq_sqrt hS_nonneg, hhalf_eq]
      ring_nf
      exact le_rfl
    rw [h_lintegral]
    exact ENNReal.ofReal_le_ofReal
      ((hMGF.2.mgf_le lambda).trans (Real.exp_le_exp.mpr h_exp_arg))
  exact
    absTailProb_le_two_mul_exp_neg_two_mul_sq_div_of_mgf_eighth
      (P := P) (Y := fun ω => ∑ i : ι, X i ω)
      (V := ∑ i : ι, (b i - a i) ^ 2) (t := t)
      hsumX hpos hsharp_mgf ht

/--
Sharp centered weighted Hoeffding bound for finite independent sums of bounded
centered variables with deterministic real weights.

Formula reference: this is the weighted analogue of the two-sided Hoeffding
bound, replacing `sum_i (b_i-a_i)^2` by
`sum_i c_i^2 * (b_i-a_i)^2`; see
https://en.wikipedia.org/wiki/Hoeffding%27s_inequality

The denominator is `sum_i c_i^2 * (b_i-a_i)^2`. Negative and zero weights are
handled through the existing weighted finite-sum MGF theorem, whose proxy uses
the squared weighted half-widths.
-/
theorem hoeffding_weighted_sum_bounded_centered_sharp
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Ω} {a b c : ι → ℝ}
    (hpos : 0 < ∑ i : ι, (c i) ^ 2 * (b i - a i) ^ 2)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hX : ∀ i : ι, IsRealRandomVariable P (X i))
    (hmem : ∀ i : ι, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (a i) (b i))
    (hcentered : ∀ i : ι, Centered P (X i))
    (hwidth : ∀ i : ι, 0 < b i - a i)
    {t : ℝ} (ht : 0 ≤ t) :
    absTailProb P (fun ω => ∑ i : ι, c i * X i ω) t ≤
      ENNReal.ofReal
        (2 * Real.exp
          (-(2 * t ^ 2 / ∑ i : ι, (c i) ^ 2 * (b i - a i) ^ 2))) := by
  have hhalf_eq :
      (∑ i : ι, (c i * ((b i - a i) / 2)) ^ 2) =
        (∑ i : ι, (c i) ^ 2 * (b i - a i) ^ 2) / 4 := by
    calc
      (∑ i : ι, (c i * ((b i - a i) / 2)) ^ 2)
          = ∑ i : ι, ((c i) ^ 2 * (b i - a i) ^ 2) / 4 := by
              apply Finset.sum_congr rfl
              intro i _hi
              ring
      _ = (∑ i : ι, (c i) ^ 2 * (b i - a i) ^ 2) / 4 := by
              rw [Finset.sum_div]
  have hhalf_pos :
      0 < ∑ i : ι, (c i * ((b i - a i) / 2)) ^ 2 := by
    rw [hhalf_eq]
    exact div_pos hpos (by norm_num)
  have hMGF :=
    centeredSubGaussianMGF_weighted_sum_of_iIndepFun_of_pos
      (P := P) (X := X) (K := fun i : ι => (b i - a i) / 2) c
      hhalf_pos hIndep
      (fun i =>
        centeredSubGaussianMGF_of_ae_mem_Icc_of_centered
          (P := P) (X := X i) (a := a i) (b := b i)
          (hX i) (hmem i) (hcentered i) (hwidth i))
  have hsumX : IsRealRandomVariable P (fun ω => ∑ i : ι, c i * X i ω) :=
    isRealRandomVariable_finset_weighted_sum
      (P := P) (s := Finset.univ) c (X := X)
      (fun i _hi => hX i)
  have hsharp_mgf :
      ∀ lambda : ℝ,
        (∫⁻ ω, ENNReal.ofReal
          (Real.exp (lambda * (∑ i : ι, c i * X i ω))) ∂P) ≤
          ENNReal.ofReal
            (Real.exp
              (lambda ^ 2 * (∑ i : ι, (c i) ^ 2 * (b i - a i) ^ 2) / 8)) := by
    intro lambda
    have h_nonneg :
        0 ≤ᵐ[P] fun ω => Real.exp (lambda * (∑ i : ι, c i * X i ω)) :=
      ae_of_all P fun _ => (Real.exp_pos _).le
    have h_lintegral :
        (∫⁻ ω, ENNReal.ofReal
          (Real.exp (lambda * (∑ i : ι, c i * X i ω))) ∂P) =
          ENNReal.ofReal
            (ProbabilityTheory.mgf
              (fun ω => ∑ i : ι, c i * X i ω) P lambda) := by
      rw [ProbabilityTheory.mgf]
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hMGF.2.integrable_exp_mul lambda) h_nonneg).symm
    have hS_nonneg :
        0 ≤ ∑ i : ι, (c i * ((b i - a i) / 2)) ^ 2 :=
      le_of_lt hhalf_pos
    have h_exp_arg :
        (Real.sqrt (∑ i : ι, (c i * ((b i - a i) / 2)) ^ 2)) ^ 2 *
            lambda ^ 2 / 2 ≤
          lambda ^ 2 * (∑ i : ι, (c i) ^ 2 * (b i - a i) ^ 2) / 8 := by
      rw [Real.sq_sqrt hS_nonneg, hhalf_eq]
      ring_nf
      exact le_rfl
    rw [h_lintegral]
    exact ENNReal.ofReal_le_ofReal
      ((hMGF.2.mgf_le lambda).trans (Real.exp_le_exp.mpr h_exp_arg))
  exact
    absTailProb_le_two_mul_exp_neg_two_mul_sq_div_of_mgf_eighth
      (P := P) (Y := fun ω => ∑ i : ι, c i * X i ω)
      (V := ∑ i : ι, (c i) ^ 2 * (b i - a i) ^ 2) (t := t)
      hsumX hpos hsharp_mgf ht

/--
Non-centered classical/Wikipedia-style finite Hoeffding inequality for finite
independent bounded real variables.

Formula reference: Wikipedia states the deviation-from-expectation form
`P(|S_n - E[S_n]| >= t) <=
2 * exp(-2*t^2 / sum_i (b_i-a_i)^2)`; see
https://en.wikipedia.org/wiki/Hoeffding%27s_inequality

This is the classical/Wikipedia form: the deviation is measured from
`E[sum_i X_i]`. The proof centers each variable, applies
`hoeffding_sum_bounded_centered_sharp`, and uses finite expectation linearity to
identify `sum_i (X_i - E X_i)` with `sum_i X_i - E[sum_i X_i]`.
-/
theorem hoeffding_sum_bounded
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Ω} {a b : ι → ℝ}
    (hpos : 0 < ∑ i : ι, (b i - a i) ^ 2)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hX : ∀ i : ι, IsRealRandomVariable P (X i))
    (hInt : ∀ i : ι, IntegrableRealRandomVariable P (X i))
    (hmem : ∀ i : ι, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (a i) (b i))
    (hwidth : ∀ i : ι, 0 < b i - a i)
    {t : ℝ} (ht : 0 ≤ t) :
    absTailProb P
      (fun ω => (∑ i : ι, X i ω) -
        expect P (fun ω => ∑ i : ι, X i ω)) t ≤
      ENNReal.ofReal
        (2 * Real.exp (-(2 * t ^ 2 / ∑ i : ι, (b i - a i) ^ 2))) := by
  have hden_centered :
      (∑ i : ι,
          ((b i - mean P (X i)) - (a i - mean P (X i))) ^ 2) =
        ∑ i : ι, (b i - a i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hpos_centered :
      0 < ∑ i : ι,
        ((b i - mean P (X i)) - (a i - mean P (X i))) ^ 2 := by
    rw [hden_centered]
    exact hpos
  have hwidth_centered :
      ∀ i : ι, 0 < (b i - mean P (X i)) - (a i - mean P (X i)) := by
    intro i
    have hdiff :
        (b i - mean P (X i)) - (a i - mean P (X i)) = b i - a i := by
      ring
    rw [hdiff]
    exact hwidth i
  have hcentered_bound :=
    hoeffding_sum_bounded_centered_sharp
      (P := P) (X := fun i : ι => centered P (X i))
      (a := fun i : ι => a i - mean P (X i))
      (b := fun i : ι => b i - mean P (X i))
      hpos_centered
      (iIndepFun_centered_of_iIndepFun (P := P) (X := X) hIndep)
      (fun i => isRealRandomVariable_centered (P := P) (X := X i) (hX i))
      (fun i =>
        ae_mem_Icc_centered_of_ae_mem_Icc
          (P := P) (X := X i) (a := a i) (b := b i) (hmem i))
      (fun i => centered_centered (P := P) (X i) (hInt i))
      hwidth_centered
      ht
  have hsum_centered :=
    sum_centered_eq_sum_sub_expect_sum (P := P) (X := X) hInt
  rw [hsum_centered] at hcentered_bound
  rw [hden_centered] at hcentered_bound
  exact hcentered_bound

/--
Sharp non-centered weighted Hoeffding inequality for finite independent bounded
real variables with deterministic real weights.

Formula reference: this is the weighted deviation-from-expectation analogue
of the Wikipedia two-sided Hoeffding bound; see
https://en.wikipedia.org/wiki/Hoeffding%27s_inequality

This is the weighted classical/Wikipedia form around
`E[sum_i c_i X_i]`, with denominator `sum_i c_i^2 * (b_i-a_i)^2`.
-/
theorem hoeffding_weighted_sum_bounded
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Ω} {a b c : ι → ℝ}
    (hpos : 0 < ∑ i : ι, (c i) ^ 2 * (b i - a i) ^ 2)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hX : ∀ i : ι, IsRealRandomVariable P (X i))
    (hInt : ∀ i : ι, IntegrableRealRandomVariable P (X i))
    (hmem : ∀ i : ι, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (a i) (b i))
    (hwidth : ∀ i : ι, 0 < b i - a i)
    {t : ℝ} (ht : 0 ≤ t) :
    absTailProb P
      (fun ω => (∑ i : ι, c i * X i ω) -
        expect P (fun ω => ∑ i : ι, c i * X i ω)) t ≤
      ENNReal.ofReal
        (2 * Real.exp
          (-(2 * t ^ 2 / ∑ i : ι, (c i) ^ 2 * (b i - a i) ^ 2))) := by
  have hden_centered :
      (∑ i : ι, (c i) ^ 2 *
          ((b i - mean P (X i)) - (a i - mean P (X i))) ^ 2) =
        ∑ i : ι, (c i) ^ 2 * (b i - a i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hpos_centered :
      0 < ∑ i : ι, (c i) ^ 2 *
          ((b i - mean P (X i)) - (a i - mean P (X i))) ^ 2 := by
    rw [hden_centered]
    exact hpos
  have hwidth_centered :
      ∀ i : ι, 0 < (b i - mean P (X i)) - (a i - mean P (X i)) := by
    intro i
    have hdiff :
        (b i - mean P (X i)) - (a i - mean P (X i)) = b i - a i := by
      ring
    rw [hdiff]
    exact hwidth i
  have hcentered_bound :=
    hoeffding_weighted_sum_bounded_centered_sharp
      (P := P) (X := fun i : ι => centered P (X i))
      (a := fun i : ι => a i - mean P (X i))
      (b := fun i : ι => b i - mean P (X i))
      (c := c)
      hpos_centered
      (iIndepFun_centered_of_iIndepFun (P := P) (X := X) hIndep)
      (fun i => isRealRandomVariable_centered (P := P) (X := X i) (hX i))
      (fun i =>
        ae_mem_Icc_centered_of_ae_mem_Icc
          (P := P) (X := X i) (a := a i) (b := b i) (hmem i))
      (fun i => centered_centered (P := P) (X i) (hInt i))
      hwidth_centered
      ht
  have hsum_centered :=
    sum_weighted_centered_eq_weighted_sum_sub_expect_weighted_sum
      (P := P) (X := X) c hInt
  rw [hsum_centered] at hcentered_bound
  rw [hden_centered] at hcentered_bound
  exact hcentered_bound

end

end HighDimProb
