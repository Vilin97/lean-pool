/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Distributions.RademacherFamily

/-!
# Weighted finite Rademacher sums

This file packages the finite product Rademacher family into the first reusable
weighted-sum MGF theorem for the Hoeffding branch.

Verified Wikipedia reference:
* Rademacher distribution:
  https://en.wikipedia.org/wiki/Rademacher_distribution
-/

namespace HighDimProb

open MeasureTheory ProbabilityTheory

noncomputable section

open scoped BigOperators NNReal

/--
The finite weighted sum `sum_i a_i eps_i` on the product Rademacher space.

Formula reference: this is the random variable
`S(omega) = sum_i a_i * eps_i(omega)`, where each `eps_i` is a Rademacher
sign. Wikipedia states concentration bounds for weighted sums of this form;
see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
def weightedRademacherSum {n : ℕ} (a : Fin n → ℝ) :
    RealRandomVariable (Fin n → Bool) :=
  fun ω => ∑ i : Fin n, a i * rademacherCoord i ω

/--
The weighted Rademacher sum is measurable.

Formula reference: this proves measurability of
`omega |-> sum_i a_i * eps_i(omega)` before applying MGF and tail bounds; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem isRealRandomVariable_weightedRademacherSum {n : ℕ} (a : Fin n → ℝ) :
    IsRealRandomVariable (rademacherVectorMeasure n) (weightedRademacherSum a) := by
  unfold IsRealRandomVariable IsRandomVariable weightedRademacherSum rademacherCoord rademacher
  fun_prop

/--
If all deterministic weights vanish, the weighted Rademacher sum vanishes.

Formula reference: setting all weights `a_i = 0` makes
`sum_i a_i eps_i = 0`; see the weighted-sum setup at
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem weightedRademacherSum_eq_zero_of_forall_eq_zero {n : ℕ}
    {a : Fin n → ℝ} (ha : ∀ i : Fin n, a i = 0) :
    weightedRademacherSum a = fun _ => 0 := by
  funext ω
  simp [weightedRademacherSum, ha]

/--
If the finite sum of squared weights is zero, the weighted Rademacher sum
vanishes.  This is the zero-variance edge case for the Rademacher Hoeffding
API.

Formula reference: the squared subGaussian proxy for
`S = sum_i a_i eps_i` is `sum_i a_i^2`; when this is zero, every `a_i` is
zero and `S = 0`; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem weightedRademacherSum_eq_zero_of_sum_sq_eq_zero {n : ℕ}
    {a : Fin n → ℝ} (ha : (∑ i : Fin n, (a i) ^ 2) = 0) :
    weightedRademacherSum a = fun _ => 0 := by
  apply weightedRademacherSum_eq_zero_of_forall_eq_zero
  intro i
  have hterm :
      (a i) ^ 2 = 0 := by
    have hall :
        ∀ j ∈ (Finset.univ : Finset (Fin n)), (a j) ^ 2 = 0 := by
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _hj => sq_nonneg (a j))).1 ha
    exact hall i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hterm

/--
For zero weights, the absolute tail is empty at every strictly positive
threshold.

At threshold `0` the absolute-tail event is the whole space, so the strict
positivity assumption on `t` is necessary.

Formula reference: for `S = 0`, the event `{|S| >= t}` is empty for `t > 0`,
so `P(|sum_i a_i eps_i| >= t) = 0`; compare the Rademacher-sum tail form at
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem absTailProb_weightedRademacherSum_eq_zero_of_forall_eq_zero_of_pos {n : ℕ}
    {a : Fin n → ℝ} (ha : ∀ i : Fin n, a i = 0) {t : ℝ} (ht : 0 < t) :
    absTailProb (rademacherVectorMeasure n) (weightedRademacherSum a) t = 0 := by
  have hsum : weightedRademacherSum a = fun _ => 0 :=
    weightedRademacherSum_eq_zero_of_forall_eq_zero ha
  have h_event : absTailEvent (weightedRademacherSum a) t = ∅ := by
    ext ω
    simp [absTailEvent, hsum, not_le.mpr ht]
  simp [absTailProb, h_event]

/--
Zero-square-sum version of the strictly positive threshold zero-tail theorem.

Formula reference: `sum_i a_i^2 = 0` gives `||a||_2 = 0`, hence the zero-tail
edge case for the weighted Rademacher concentration formula; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem absTailProb_weightedRademacherSum_eq_zero_of_sum_sq_eq_zero_of_pos {n : ℕ}
    {a : Fin n → ℝ} (ha : (∑ i : Fin n, (a i) ^ 2) = 0)
    {t : ℝ} (ht : 0 < t) :
    absTailProb (rademacherVectorMeasure n) (weightedRademacherSum a) t = 0 := by
  have hsum : weightedRademacherSum a = fun _ => 0 :=
    weightedRademacherSum_eq_zero_of_sum_sq_eq_zero ha
  have h_event : absTailEvent (weightedRademacherSum a) t = ∅ := by
    ext ω
    simp [absTailEvent, hsum, not_le.mpr ht]
  simp [absTailProb, h_event]

/--
A single coordinate Rademacher variable has Mathlib subGaussian MGF proxy `1`.

Formula reference: a single Rademacher sign `eps` has
`E[exp(lambda eps)] = cosh(lambda) <= exp(lambda^2 / 2)`, giving Mathlib proxy
`1`; see https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem hasSubgaussianMGF_rademacherCoord {n : ℕ} (i : Fin n) :
    ProbabilityTheory.HasSubgaussianMGF
      (rademacherCoord i) (1 : ℝ≥0) (rademacherVectorMeasure n) := by
  have hm : AEMeasurable (rademacherCoord i) (rademacherVectorMeasure n) :=
    (isRealRandomVariable_rademacherCoord i).aemeasurable
  have hb :
      ∀ᵐ ω ∂rademacherVectorMeasure n,
        rademacherCoord i ω ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ae_of_all _ (rademacherCoord_mem_Icc i)
  have hsub :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (X := rademacherCoord i) (a := (-1 : ℝ)) (b := 1) hm hb
      (integral_rademacherCoord i)
  convert hsub using 1
  ext
  norm_num [Real.norm_eq_abs]

/--
Weighted coordinate terms remain independent.

Formula reference: independence is preserved when replacing each sign
`eps_i` by the deterministic multiple `a_i * eps_i`, so MGF proxies can be
multiplied and then added; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem iIndepFun_weightedRademacherTerms {n : ℕ} (a : Fin n → ℝ) :
    ProbabilityTheory.iIndepFun
      (fun i : Fin n => fun ω : Fin n → Bool => a i * rademacherCoord i ω)
      (rademacherVectorMeasure n) := by
  have h :=
    (iIndepFun_rademacherCoord n).comp
      (fun i : Fin n => fun x : ℝ => a i * x)
      (by
        intro i
        fun_prop)
  simpa [Function.comp_def] using h

/--
A weighted coordinate term has MGF proxy `a_i^2`.

Formula reference: scaling `eps_i` by `a_i` changes the proxy from `1` to
`a_i^2`, matching the squared Euclidean weight contribution; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem hasSubgaussianMGF_weightedRademacherTerm {n : ℕ}
    (a : Fin n → ℝ) (i : Fin n) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun ω : Fin n → Bool => a i * rademacherCoord i ω)
      (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : ℝ≥0) (rademacherVectorMeasure n) := by
  have h := (hasSubgaussianMGF_rademacherCoord i).const_mul (a i)
  simpa using h

/--
Mathlib MGF proxy for the weighted Rademacher sum:
the independent coordinate proxies add to `sum_i a_i^2`.

Formula reference: independence multiplies MGFs, so the weighted sum has proxy
`sum_i a_i^2 = ||a||_2^2`, the scale appearing in Wikipedia's weighted
Rademacher concentration statement; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem hasSubgaussianMGF_weightedRademacherSum {n : ℕ} (a : Fin n → ℝ) :
    ProbabilityTheory.HasSubgaussianMGF
      (weightedRademacherSum a)
      (∑ i : Fin n, (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : ℝ≥0))
      (rademacherVectorMeasure n) := by
  have hsum :=
    ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
      (iIndepFun_weightedRademacherTerms a)
      (s := Finset.univ)
      (c := fun i : Fin n => (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : ℝ≥0))
      (by
        intro i _hi
        exact hasSubgaussianMGF_weightedRademacherTerm a i)
  change ProbabilityTheory.HasSubgaussianMGF
    (fun ω : Fin n → Bool => ∑ i : Fin n, a i * rademacherCoord i ω)
    (∑ i : Fin n, (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : ℝ≥0))
    (rademacherVectorMeasure n)
  exact hsum

/--
The weighted Rademacher sum is centered subGaussian with exact scale
`sqrt (sum_i a_i^2)` whenever that scale is positive.

The positivity assumption only excludes the all-zero weight vector; the current
`CenteredSubGaussianMGF` predicate requires a strictly positive scale.

Formula reference: the MGF proxy `sum_i a_i^2` is converted to the
HighDimProb scale `K = sqrt (sum_i a_i^2)` for the centered subGaussian
predicate; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem centeredSubGaussianMGF_weightedRademacherSum {n : ℕ}
    (a : Fin n → ℝ) (ha : 0 < ∑ i : Fin n, (a i) ^ 2) :
    CenteredSubGaussianMGF
      (rademacherVectorMeasure n) (weightedRademacherSum a)
      (Real.sqrt (∑ i : Fin n, (a i) ^ 2)) := by
  refine ⟨Real.sqrt_pos.2 ha, ?_⟩
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, (a i) ^ 2 := by
    exact Finset.sum_nonneg fun i _hi => sq_nonneg (a i)
  have hproxy :
      (⟨(Real.sqrt (∑ i : Fin n, (a i) ^ 2)) ^ 2,
          sq_nonneg (Real.sqrt (∑ i : Fin n, (a i) ^ 2))⟩ : ℝ≥0)
        = ∑ i : Fin n, (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : ℝ≥0) := by
    have hcoe :
        ((↑(∑ i : Fin n, (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : ℝ≥0)) : ℝ))
          = ∑ i : Fin n, (a i) ^ 2 := by
      exact
        (NNReal.coe_sum (Finset.univ : Finset (Fin n))
          (fun i : Fin n => (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : ℝ≥0)))
    ext
    simp only [Real.sq_sqrt hsum_nonneg]
    exact hcoe.symm
  rw [hproxy]
  exact hasSubgaussianMGF_weightedRademacherSum a

/--
Weighted Rademacher sums satisfy the existing two-sided subGaussian-tail
predicate with scale `2 * sqrt (sum_i a_i^2)`, provided that scale is positive.

The positive-square-sum assumption excludes only the all-zero weight vector;
the `SubGaussianTail` predicate itself requires a strictly positive scale.

Formula reference: this packages the MGF scale into the existing two-sided
tail predicate with `K = 2 * sqrt (sum_i a_i^2)`, so its tail formula becomes
`P(|S| >= t) <= 2 * exp(-(t^2 / (4 * sum_i a_i^2)))`; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem subGaussianTail_weightedRademacherSum {n : ℕ}
    (a : Fin n → ℝ) (ha : 0 < ∑ i : Fin n, (a i) ^ 2) :
    SubGaussianTail
      (rademacherVectorMeasure n) (weightedRademacherSum a)
      (2 * Real.sqrt (∑ i : Fin n, (a i) ^ 2)) := by
  exact
    subGaussianTail_of_centeredSubGaussianMGF
      (P := rademacherVectorMeasure n)
      (X := weightedRademacherSum a)
      (K := Real.sqrt (∑ i : Fin n, (a i) ^ 2))
      (isRealRandomVariable_weightedRademacherSum a)
      (centeredSubGaussianMGF_weightedRademacherSum a ha)

/--
Finite weighted Rademacher Hoeffding tail bound, in explicit probability form.

The denominator is positive by assumption; the all-zero weight vector is a
separate edge case because the current subGaussian-tail predicate uses strictly
positive scales.

Formula reference: this theorem states the concrete HighDimProb bound
`P(|sum_i a_i eps_i| >= t) <= 2 * exp(-(t^2 / (4 * sum_i a_i^2)))`.
Wikipedia's normalized one-sided form is
`P(sum_i x_i a_i > t ||a||_2) <= exp(-t^2 / 2)`, so the constants differ
because this file uses an existing two-sided subGaussian-tail wrapper:
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem hoeffding_rademacher_sum {n : ℕ}
    (a : Fin n → ℝ) (ha : 0 < ∑ i : Fin n, (a i) ^ 2)
    {t : ℝ} (ht : 0 ≤ t) :
    absTailProb (rademacherVectorMeasure n) (weightedRademacherSum a) t ≤
      ENNReal.ofReal
        (2 * Real.exp (-(t ^ 2 / (4 * ∑ i : Fin n, (a i) ^ 2)))) := by
  have htail :=
    (subGaussianTail_weightedRademacherSum a ha).2 t ht
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, (a i) ^ 2 := le_of_lt ha
  have hden :
      (2 * Real.sqrt (∑ i : Fin n, (a i) ^ 2)) ^ 2 =
        4 * ∑ i : Fin n, (a i) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hsum_nonneg]
    ring
  simpa [hden] using htail

/--
Alias for the positive-variance form of the weighted Rademacher Hoeffding
bound.  The statement is definitionally the same as `hoeffding_rademacher_sum`,
but the name makes the required assumption explicit for downstream users.

Formula reference: alias for the same explicit bound
`P(|sum_i a_i eps_i| >= t) <= 2 * exp(-(t^2 / (4 * sum_i a_i^2)))`; see
https://en.wikipedia.org/wiki/Rademacher_distribution
-/
theorem hoeffding_rademacher_sum_of_pos_variance {n : ℕ}
    (a : Fin n → ℝ) (ha : 0 < ∑ i : Fin n, (a i) ^ 2)
    {t : ℝ} (ht : 0 ≤ t) :
    absTailProb (rademacherVectorMeasure n) (weightedRademacherSum a) t ≤
      ENNReal.ofReal
        (2 * Real.exp (-(t ^ 2 / (4 * ∑ i : Fin n, (a i) ^ 2)))) :=
  hoeffding_rademacher_sum a ha ht

end

end HighDimProb
