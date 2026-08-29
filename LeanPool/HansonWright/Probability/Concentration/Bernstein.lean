/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu, Kazuki Uesugi
-/
import LeanPool.HansonWright.Probability.Concentration.Chernoff
import LeanPool.HansonWright.Probability.Moments.Cumulant
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Scalar Bernstein Inequality

This file contains generic scalar Bernstein CGF-to-tail infrastructure and the
classical Bernstein inequality for finite independent sums of centered bounded
real random variables.

## Main results

* `bernstein_one_sided_of_cgf_bound`: a coarse one-sided sub-exponential tail
  bound from a local quadratic CGF estimate.
* `bernstein_two_sided_of_cgf_bound`: the corresponding two-sided bound.
* `bernstein_mgf_le_of_centered_abs_le`: one-variable Bernstein MGF bound.
* `bernstein_cgf_le_of_centered_abs_le`: one-variable Bernstein CGF bound.
* `bernstein_cgf_sum_le`: rational CGF bound for a finite independent sum.
* `bernstein_one_sided_of_rational_cgf_bound`: exact optimized Bernstein tail
  from a rational CGF estimate.
* `bernstein_inequality_finset`: scalar Bernstein inequality for a `Finset`.
* `bernstein_inequality`: `[Fintype]` convenience wrapper.

-/

namespace LeanPool

open MeasureTheory Real Set Metric Filter
open _root_.ProbabilityTheory
open _root_.LeanPool.ProbabilityTheory
open scoped ENNReal BigOperators NNReal Topology

noncomputable section

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A one-sided Bernstein tail bound from a local quadratic CGF estimate. -/
theorem bernstein_one_sided_of_cgf_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ} {v b C t : ℝ}
    (hC : 0 < C) (hv : 0 < v) (hb : 0 < b)
    (hcgf : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ → cgf Y μ l ≤ C * l ^ 2 * v)
    (hint : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ →
      Integrable (fun ω => exp (l * Y ω)) μ) (ht : 0 ≤ t) :
    (μ {ω | t ≤ Y ω}).toReal ≤
      exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · calc (μ {ω | 0 ≤ Y ω}).toReal
      _ ≤ (1 : ℝ) := ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
      _ = exp (-(1 / (4 * C)) * min (0 ^ 2 / v) (0 / b)) := by simp
  · set l : ℝ := min (t / (2 * C * v)) ((2 * C * b)⁻¹) with hl_def
    have hden_v : 0 < 2 * C * v := by positivity
    have hden_b : 0 < 2 * C * b := by positivity
    have hl_nonneg : 0 ≤ l := by
      rw [hl_def]
      exact le_min (div_nonneg ht (le_of_lt hden_v)) (inv_nonneg.mpr (le_of_lt hden_b))
    have hl_domain : |l| ≤ (2 * C * b)⁻¹ := by
      rw [abs_of_nonneg hl_nonneg, hl_def]
      exact min_le_right _ _
    have hl_le_v : l ≤ t / (2 * C * v) := by
      rw [hl_def]
      exact min_le_left _ _
    have hl_mul_le_t : l * (2 * C * v) ≤ t := by
      rwa [le_div_iff₀ hden_v] at hl_le_v
    have hquad_le : C * l ^ 2 * v ≤ l * t / 2 := by
      nlinarith [hl_mul_le_t, hl_nonneg, hC.le, hv.le]
    have h_exp_to_half : -l * t + C * l ^ 2 * v ≤ -(l * t / 2) := by
      linarith
    have h_rate :
        l * t / 2 = (1 / (4 * C)) * min (t ^ 2 / v) (t / b) := by
      by_cases hcase : t / (2 * C * v) ≤ (2 * C * b)⁻¹
      · have htb_le_v : t * b ≤ v := by
          rw [inv_eq_one_div] at hcase
          rw [div_le_div_iff₀ hden_v hden_b] at hcase
          nlinarith [hcase, hC, hb]
        have hmin : min (t ^ 2 / v) (t / b) = t ^ 2 / v := by
          rw [min_eq_left]
          rw [div_le_div_iff₀ hv hb]
          nlinarith [htb_le_v, ht_pos]
        rw [hl_def, min_eq_left hcase, hmin]
        field_simp [hC.ne', hv.ne']
        ring
      · have hcase' : (2 * C * b)⁻¹ ≤ t / (2 * C * v) := le_of_not_ge hcase
        have hv_le_tb : v ≤ t * b := by
          rw [inv_eq_one_div] at hcase'
          rw [div_le_div_iff₀ hden_b hden_v] at hcase'
          nlinarith [hcase', hC, hv]
        have hmin : min (t ^ 2 / v) (t / b) = t / b := by
          rw [min_eq_right]
          rw [div_le_div_iff₀ hb hv]
          nlinarith [hv_le_tb, ht_pos]
        rw [hl_def, min_eq_right hcase', hmin]
        field_simp [hC.ne', hb.ne']
        ring
    have h_chernoff := chernoff_bound_cgf hl_nonneg (hint l hl_domain)
      (μ := μ) (X := Y) (ε := t)
    calc (μ {ω | t ≤ Y ω}).toReal
      _ ≤ exp (-l * t + cgf Y μ l) := h_chernoff
      _ ≤ exp (-l * t + C * l ^ 2 * v) := by
        exact exp_le_exp.mpr (by linarith [hcgf l hl_domain])
      _ ≤ exp (-(l * t / 2)) := exp_le_exp.mpr h_exp_to_half
      _ = exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by
        rw [h_rate]
        ring_nf

/-- A two-sided Bernstein tail bound from a local quadratic CGF estimate. -/
theorem bernstein_two_sided_of_cgf_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ} {v b C t : ℝ}
    (hC : 0 < C) (hv : 0 < v) (hb : 0 < b)
    (hcgf : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ → cgf Y μ l ≤ C * l ^ 2 * v)
    (hint : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ →
      Integrable (fun ω => exp (l * Y ω)) μ) (ht : 0 ≤ t) :
    (μ {ω | t ≤ |Y ω|}).toReal ≤
      2 * exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by
  have hpos := bernstein_one_sided_of_cgf_bound hC hv hb hcgf hint ht
  have hcgf_neg :
      ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ →
        cgf (fun ω => -Y ω) μ l ≤ C * l ^ 2 * v := by
    intro l hl
    have h_eq : cgf (fun ω => -Y ω) μ l = cgf Y μ (-l) := by
      unfold cgf mgf
      congr 1
      apply integral_congr_ae
      filter_upwards with ω
      congr 1
      ring
    rw [h_eq]
    have hl' : |-l| ≤ (2 * C * b)⁻¹ := by simpa [abs_neg] using hl
    simpa using hcgf (-l) hl'
  have hint_neg : ∀ l : ℝ, |l| ≤ (2 * C * b)⁻¹ →
      Integrable (fun ω => exp (l * (-Y ω))) μ := by
    intro l hl
    convert hint (-l) (by simpa [abs_neg] using hl) using 1
    ext ω
    ring_nf
  have hneg := bernstein_one_sided_of_cgf_bound hC hv hb hcgf_neg hint_neg ht
  have h_subset :
      {ω | t ≤ |Y ω|} ⊆ {ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    rcases le_or_gt 0 (Y ω) with hY | hY
    · left
      simpa [abs_of_nonneg hY] using hω
    · right
      simpa [abs_of_neg hY] using hω
  calc (μ {ω | t ≤ |Y ω|}).toReal
      ≤ (μ ({ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω})).toReal := by
        exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono h_subset)
    _ ≤ (μ {ω | t ≤ Y ω}).toReal + (μ {ω | t ≤ -Y ω}).toReal := by
        rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
        exact ENNReal.toReal_mono
          (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩)
          (measure_union_le _ _)
    _ ≤ exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) +
        exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by
        exact add_le_add hpos hneg
    _ = 2 * exp (-(1 / (4 * C)) * min (t ^ 2 / v) (t / b)) := by ring

/-! ## Exact scalar Bernstein CGF and tail infrastructure -/

private def scalarBernsteinMgfRate (b l : ℝ) : ℝ :=
  (l ^ 2 / 2) / (1 - l * b / 3)

private lemma scalarBernstein_exp_le_taylor_four_add_abs_fifth_of_abs_le_three
    {u : ℝ} (hu : |u| ≤ 3) :
    Real.exp u ≤
      (∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℝ)) + |u| ^ 5 / 60 := by
  have hcomplex :
      ‖Complex.exp (u : ℂ) -
          ∑ m ∈ Finset.range 5, (u : ℂ) ^ m / (m.factorial : ℂ)‖ ≤
        ‖(u : ℂ)‖ ^ 5 / (Nat.factorial 5 : ℝ) * 2 := by
    apply Complex.exp_bound'
    rw [Complex.norm_real, Real.norm_eq_abs]
    norm_num
    nlinarith [abs_nonneg u, hu]
  have hcast :
      ((Real.exp u -
          ∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℝ) : ℝ) : ℂ) =
        Complex.exp (u : ℂ) -
          ∑ m ∈ Finset.range 5, (u : ℂ) ^ m / (m.factorial : ℂ) := by
    simp [Complex.ofReal_exp, Complex.ofReal_sum, Complex.ofReal_pow]
  have hreal_abs :
      |Real.exp u - ∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℝ)| ≤
        |u| ^ 5 / (Nat.factorial 5 : ℝ) * 2 := by
    rw [← Real.norm_eq_abs]
    rw [← Complex.norm_real
      (Real.exp u - ∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℝ))]
    rw [hcast]
    simpa [Complex.norm_real, Real.norm_eq_abs] using hcomplex
  have hupper := (abs_sub_le_iff.mp hreal_abs).1
  calc
    Real.exp u ≤
        (∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℝ)) +
          |u| ^ 5 / (Nat.factorial 5 : ℝ) * 2 := by
      linarith
    _ = (∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℝ)) + |u| ^ 5 / 60 := by
      ring

private lemma scalarBernstein_exp_le_quadratic_of_abs_lt_three
    {u : ℝ} (hu : |u| < 3) :
    Real.exp u ≤ 1 + u + (u ^ 2 / 2) / (1 - |u| / 3) := by
  have htaylor :=
    scalarBernstein_exp_le_taylor_four_add_abs_fifth_of_abs_le_three (le_of_lt hu)
  have hpoly :
      (∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℝ)) + |u| ^ 5 / 60 ≤
        1 + u + (u ^ 2 / 2) / (1 - |u| / 3) := by
    by_cases hu_nonneg : 0 ≤ u
    · have habs : |u| = u := abs_of_nonneg hu_nonneg
      have hdenpos : 0 < 1 - u / 3 := by
        have hu_lt : u < 3 := by simpa [habs] using hu
        linarith
      rw [habs]
      norm_num [Finset.sum_range_succ, Nat.factorial]
      have htail :
          u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 60 ≤
            (u ^ 2 / 2) / (1 - u / 3) := by
        rw [le_div_iff₀ hdenpos]
        ring_nf
        have hquad : 0 ≤ 5 - u + 2 * u ^ 2 := by
          nlinarith [sq_nonneg (u - 1 / 4)]
        nlinarith [mul_nonneg (sq_nonneg (u ^ 2)) hquad]
      linarith
    · have hu_nonpos : u ≤ 0 := le_of_lt (not_le.mp hu_nonneg)
      have habs : |u| = -u := abs_of_nonpos hu_nonpos
      have hneg_lt : -u < 3 := by
        have h := (abs_lt.mp hu).1
        linarith
      rw [habs]
      norm_num [Finset.sum_range_succ, Nat.factorial]
      let w : ℝ := -u
      have hw_nonneg : 0 ≤ w := by simp [w, hu_nonpos]
      have hw_lt : w < 3 := by simpa [w] using hneg_lt
      have hw_le : w ≤ 3 := hw_lt.le
      have hdenpos_w : 0 < 1 - w / 3 := by linarith
      have htail_w :
          w ^ 2 / 2 - w ^ 3 / 6 + w ^ 4 / 24 + w ^ 5 / 60 ≤
            (w ^ 2 / 2) / (1 - w / 3) := by
        rw [le_div_iff₀ hdenpos_w]
        ring_nf
        have hw_sq_le_three_mul : w ^ 2 ≤ 3 * w := by
          nlinarith [mul_nonneg hw_nonneg (sub_nonneg.mpr hw_le)]
        have hw_sq_le : w ^ 2 ≤ 9 := by nlinarith
        have hw_cube_nonneg : 0 ≤ w ^ 3 := by
          nlinarith [mul_nonneg hw_nonneg (sq_nonneg w)]
        have hfactor : 0 ≤ 120 - 35 * w - w ^ 2 + 2 * w ^ 3 := by
          nlinarith
        nlinarith [mul_nonneg (mul_nonneg hw_nonneg (sq_nonneg w)) hfactor]
      have htail_raw :
          (-u) ^ 2 / 2 - (-u) ^ 3 / 6 + (-u) ^ 4 / 24 + (-u) ^ 5 / 60 ≤
            ((-u) ^ 2 / 2) / (1 - (-u) / 3) := by
        simpa [w] using htail_w
      have htail_simpl :
          u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + (-u) ^ 5 / 60 ≤
            (u ^ 2 / 2) / (1 - -u / 3) := by
        ring_nf at htail_raw ⊢
        exact htail_raw
      nlinarith [htail_simpl]
  exact htaylor.trans hpoly

private lemma scalarBernstein_exp_mul_le_quadratic
    {b l x : ℝ} (hl : 0 ≤ l) (hden : 0 < 1 - l * b / 3)
    (hx : |x| ≤ b) :
    Real.exp (l * x) ≤
      1 + l * x + scalarBernsteinMgfRate b l * x ^ 2 := by
  have h_abs_lx_le : |l * x| ≤ l * b := by
    rw [abs_mul, abs_of_nonneg hl]
    exact mul_le_mul_of_nonneg_left hx hl
  have hlb_lt : l * b < 3 := by nlinarith
  have hlocal_lt : |l * x| < 3 := h_abs_lx_le.trans_lt hlb_lt
  have hbase := scalarBernstein_exp_le_quadratic_of_abs_lt_three hlocal_lt
  have hlocal_den_pos : 0 < 1 - |l * x| / 3 := by nlinarith
  have hden_le : 1 - l * b / 3 ≤ 1 - |l * x| / 3 := by nlinarith
  have hnum_nonneg : 0 ≤ (l * x) ^ 2 / 2 :=
    div_nonneg (sq_nonneg _) (by norm_num)
  have hquad_le :
      ((l * x) ^ 2 / 2) / (1 - |l * x| / 3) ≤
        ((l * x) ^ 2 / 2) / (1 - l * b / 3) :=
    div_le_div_of_nonneg_left hnum_nonneg hden hden_le
  have hquad_eq :
      ((l * x) ^ 2 / 2) / (1 - l * b / 3) =
        scalarBernsteinMgfRate b l * x ^ 2 := by
    simp [scalarBernsteinMgfRate]
    ring
  nlinarith

private lemma scalarBernstein_integrable_exp_mul_of_abs_le
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {b l : ℝ}
    (hX : AEMeasurable X μ) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    Integrable (fun ω => exp (l * X ω)) μ := by
  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-b) b := by
    filter_upwards [hbound] with ω hω
    exact (abs_le.mp hω)
  exact integrable_expt_bound hX hIcc

lemma iIndepFun.integrable_exp_mul_finsetSum
    {ι : Type*} {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    {s : Finset ι} {t : ℝ}
    (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ) :
    Integrable (fun ω => exp (t * (∑ i ∈ s, X i) ω)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_apply, Finset.sum_empty, mul_zero, exp_zero]
      exact integrable_const _
  | insert i s hi h_rec =>
      have hs :
          ∀ j ∈ s, Integrable (fun ω => exp (t * X j ω)) μ := by
        intro j hj
        exact h_int j (Finset.mem_insert_of_mem hj)
      specialize h_rec hs
      rw [Finset.sum_insert hi]
      refine IndepFun.integrable_exp_mul_add ?_
        (h_int i (Finset.mem_insert_self i s)) h_rec
      exact (h_indep.indepFun_finsetSum_of_notMem₀ h_meas hi).symm

/--
Bernstein MGF bound for one centered, almost surely bounded real random variable.
-/
theorem bernstein_mgf_le_of_centered_abs_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {b l : ℝ}
    (hX : AEMeasurable X μ)
    (hcenter : ∫ ω, X ω ∂μ = 0)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (hl : 0 ≤ l) (hbl : b * l < 3) :
    mgf X μ l ≤
      exp (variance X μ * l ^ 2 / (2 * (1 - b * l / 3))) := by
  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-b) b := by
    filter_upwards [hbound] with ω hω
    exact (abs_le.mp hω)
  have hX_int : Integrable X μ :=
    integrable_bounded (-b) b hX hIcc
  have hX_norm_bound : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ b := by
    filter_upwards [hbound] with ω hω
    simpa [Real.norm_eq_abs] using hω
  have hX2_int : Integrable (fun ω => X ω ^ 2) μ := by
    have hmul : Integrable (fun ω => X ω * X ω) μ :=
      hX_int.bdd_mul hX.aestronglyMeasurable hX_norm_bound
    simpa [pow_two] using hmul
  have hexp_int : Integrable (fun ω => exp (l * X ω)) μ :=
    scalarBernstein_integrable_exp_mul_of_abs_le hX hbound
  have hden : 0 < 1 - l * b / 3 := by
    nlinarith [hbl]
  have hden' : 0 < 1 - b * l / 3 := by
    nlinarith [hbl]
  let g : ℝ := scalarBernsteinMgfRate b l
  have henv :
      ∀ᵐ ω ∂μ,
        exp (l * X ω) ≤ 1 + l * X ω + g * X ω ^ 2 := by
    filter_upwards [hbound] with ω hω
    simpa [g] using
      scalarBernstein_exp_mul_le_quadratic
        (b := b) (l := l) (x := X ω) hl hden hω
  have hQ_int :
      Integrable (fun ω => 1 + l * X ω + g * X ω ^ 2) μ := by
    exact
      ((integrable_const (μ := μ) (1 : ℝ)).add (hX_int.const_mul l)).add
        (hX2_int.const_mul g)
  have hconst_int : Integrable (fun _ : Ω => (1 : ℝ)) μ :=
    integrable_const (1 : ℝ)
  have hlin_int : Integrable (fun ω => l * X ω) μ := hX_int.const_mul l
  have hquad_int : Integrable (fun ω => g * X ω ^ 2) μ := hX2_int.const_mul g
  have hQ_integral :
      ∫ ω, (1 + l * X ω + g * X ω ^ 2) ∂μ =
        1 + g * ∫ ω, X ω ^ 2 ∂μ := by
    calc
      ∫ ω, (1 + l * X ω + g * X ω ^ 2) ∂μ =
          (∫ ω, 1 + l * X ω ∂μ) + ∫ ω, g * X ω ^ 2 ∂μ := by
        exact integral_add (hconst_int.add hlin_int) hquad_int
      _ = ((∫ _ω, (1 : ℝ) ∂μ) + ∫ ω, l * X ω ∂μ) +
          ∫ ω, g * X ω ^ 2 ∂μ := by
        rw [show (∫ ω, 1 + l * X ω ∂μ) =
            (∫ _ω, (1 : ℝ) ∂μ) + ∫ ω, l * X ω ∂μ from
          integral_add hconst_int hlin_int]
      _ = 1 + l * (∫ ω, X ω ∂μ) + g * ∫ ω, X ω ^ 2 ∂μ := by
        rw [integral_const, probReal_univ, one_smul,
          integral_const_mul, integral_const_mul]
      _ = 1 + g * ∫ ω, X ω ^ 2 ∂μ := by rw [hcenter]; ring
  have hvar :
      variance X μ = ∫ ω, X ω ^ 2 ∂μ :=
    variance_of_integral_eq_zero hX hcenter
  have hmgf_le :
      mgf X μ l ≤ 1 + g * variance X μ := by
    calc
      mgf X μ l = ∫ ω, exp (l * X ω) ∂μ := rfl
      _ ≤ ∫ ω, (1 + l * X ω + g * X ω ^ 2) ∂μ :=
        integral_mono_ae hexp_int hQ_int henv
      _ = 1 + g * ∫ ω, X ω ^ 2 ∂μ := hQ_integral
      _ = 1 + g * variance X μ := by rw [← hvar]
  calc
    mgf X μ l ≤ 1 + g * variance X μ := hmgf_le
    _ ≤ exp (g * variance X μ) := by
      simpa [add_comm] using Real.add_one_le_exp (g * variance X μ)
    _ = exp (variance X μ * l ^ 2 / (2 * (1 - b * l / 3))) := by
      congr 1
      dsimp [g, scalarBernsteinMgfRate]
      field_simp [hden.ne', hden'.ne']

/--
Bernstein CGF bound for one centered, almost surely bounded real random variable.
-/
theorem bernstein_cgf_le_of_centered_abs_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {b l : ℝ}
    (hX : AEMeasurable X μ)
    (hcenter : ∫ ω, X ω ∂μ = 0)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (hl : 0 ≤ l) (hbl : b * l < 3) :
    cgf X μ l ≤
      variance X μ * l ^ 2 / (2 * (1 - b * l / 3)) := by
  have hexp_int : Integrable (fun ω => exp (l * X ω)) μ :=
    scalarBernstein_integrable_exp_mul_of_abs_le hX hbound
  have hmgf :=
    bernstein_mgf_le_of_centered_abs_le hX hcenter hbound hl hbl
  have hmgf_pos : 0 < mgf X μ l := mgf_pos hexp_int
  calc
    cgf X μ l = log (mgf X μ l) := rfl
    _ ≤ log (exp (variance X μ * l ^ 2 / (2 * (1 - b * l / 3)))) :=
      log_le_log hmgf_pos hmgf
    _ = variance X μ * l ^ 2 / (2 * (1 - b * l / 3)) := log_exp _

/--
The CGF of a finite independent sum satisfies the rational Bernstein bound.
-/
theorem bernstein_cgf_sum_le
    {ι : Type*} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Finset ι) {X : ι → Ω → ℝ} {b v l : ℝ}
    (h_indep : iIndepFun X μ)
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (hvar : ∑ i ∈ s, variance (X i) μ ≤ v)
    (hl : 0 ≤ l) (hbl : b * l < 3) :
    cgf (∑ i ∈ s, X i) μ l ≤
      v * l ^ 2 / (2 * (1 - b * l / 3)) := by
  classical
  have hint :
      ∀ i ∈ s, Integrable (fun ω => exp (l * X i ω)) μ := by
    intro i hi
    exact scalarBernstein_integrable_exp_mul_of_abs_le
      (hX i) (hbound i hi)
  have hcgf_sum :=
    h_indep.cgf_sum₀ hX (s := s) hint
  let c : ℝ := l ^ 2 / (2 * (1 - b * l / 3))
  have hden : 0 < 2 * (1 - b * l / 3) := by
    nlinarith [hbl]
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (sq_nonneg l) hden.le
  have hterm :
      ∀ i ∈ s, cgf (X i) μ l ≤ variance (X i) μ * c := by
    intro i hi
    have hi_bound :=
      bernstein_cgf_le_of_centered_abs_le
        (hX i) (hcenter i hi) (hbound i hi) hl hbl
    dsimp [c]
    convert hi_bound using 1
    ring
  calc
    cgf (∑ i ∈ s, X i) μ l =
        ∑ i ∈ s, cgf (X i) μ l := hcgf_sum
    _ ≤ ∑ i ∈ s, variance (X i) μ * c :=
      Finset.sum_le_sum fun i hi => hterm i hi
    _ = (∑ i ∈ s, variance (X i) μ) * c := by
      rw [Finset.sum_mul]
    _ ≤ v * c := mul_le_mul_of_nonneg_right hvar hc
    _ = v * l ^ 2 / (2 * (1 - b * l / 3)) := by
      dsimp [c]
      ring

/--
Exact one-sided Bernstein tail bound from a rational Bernstein CGF estimate.
-/
theorem bernstein_one_sided_of_rational_cgf_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {v b t : ℝ}
    (hv : 0 < v) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hcgf : ∀ l : ℝ, 0 ≤ l → b * l < 3 →
      cgf Y μ l ≤ v * l ^ 2 / (2 * (1 - b * l / 3)))
    (hint : ∀ l : ℝ, 0 ≤ l → b * l < 3 →
      Integrable (fun ω => exp (l * Y ω)) μ) :
    (μ {ω | t ≤ Y ω}).toReal ≤
      exp (-(t ^ 2) / (2 * (v + b * t / 3))) := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · calc
      (μ {ω | 0 ≤ Y ω}).toReal ≤ (1 : ℝ) :=
        ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
      _ = exp (-(0 ^ 2) / (2 * (v + b * 0 / 3))) := by simp
  · let d : ℝ := v + b * t / 3
    let l : ℝ := t / d
    have hd : 0 < d := by
      dsimp [d]
      positivity
    have hl : 0 ≤ l := by
      dsimp [l]
      exact div_nonneg ht hd.le
    have hbl : b * l < 3 := by
      have hnum : b * t < 3 * d := by
        dsimp [d]
        nlinarith [hv]
      calc
        b * l = (b * t) / d := by
          dsimp [l]
          ring
        _ < 3 := (div_lt_iff₀ hd).2 hnum
    have hden_eq : 1 - b * l / 3 = v / d := by
      dsimp [l, d]
      field_simp [hd.ne']
      ring
    have hrate :
        -l * t + v * l ^ 2 / (2 * (1 - b * l / 3)) =
          -(t ^ 2) / (2 * d) := by
      rw [hden_eq]
      dsimp [l]
      field_simp [hv.ne', hd.ne']
      ring
    have hchernoff :=
      chernoff_bound_cgf hl (hint l hl hbl)
        (μ := μ) (X := Y) (ε := t)
    calc
      (μ {ω | t ≤ Y ω}).toReal
          ≤ exp (-l * t + cgf Y μ l) := hchernoff
      _ ≤ exp (-l * t + v * l ^ 2 / (2 * (1 - b * l / 3))) := by
        exact exp_le_exp.mpr (by linarith [hcgf l hl hbl])
      _ = exp (-(t ^ 2) / (2 * (v + b * t / 3))) := by
        rw [hrate]

/--
Scalar Bernstein inequality for a finite set of independent centered bounded summands.
-/
theorem bernstein_inequality_finset
    {ι : Type*} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Finset ι) {X : ι → Ω → ℝ} {b v t : ℝ}
    (hb : 0 ≤ b) (hv : 0 < v) (ht : 0 ≤ t)
    (h_indep : iIndepFun X μ)
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (hvar : ∑ i ∈ s, variance (X i) μ ≤ v) :
    (μ {ω | t ≤ (∑ i ∈ s, X i) ω}).toReal ≤
      exp (-(t ^ 2) / (2 * (v + b * t / 3))) := by
  classical
  let S : Ω → ℝ := ∑ i ∈ s, X i
  have htail :
      (μ {ω | t ≤ S ω}).toReal ≤
        exp (-(t ^ 2) / (2 * (v + b * t / 3))) := by
    apply bernstein_one_sided_of_rational_cgf_bound
      (Y := S) hv hb ht
    · intro l hl hbl
      simpa [S] using
        bernstein_cgf_sum_le s h_indep hX hcenter hbound hvar hl hbl
    · intro l _hl _hbl
      have hint :
          ∀ i ∈ s, Integrable (fun ω => exp (l * X i ω)) μ := by
        intro i hi
        exact scalarBernstein_integrable_exp_mul_of_abs_le
          (hX i) (hbound i hi)
      simpa [S] using
        (iIndepFun.integrable_exp_mul_finsetSum h_indep hX (s := s) hint)
  simpa [S] using htail

/--
Convenience `[Fintype ι]` wrapper for the scalar Bernstein inequality.
-/
theorem bernstein_inequality
    {ι : Type*} [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {b v t : ℝ}
    (hb : 0 ≤ b) (hv : 0 < v) (ht : 0 ≤ t)
    (h_indep : iIndepFun X μ)
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (hvar : ∑ i, variance (X i) μ ≤ v) :
    (μ {ω | t ≤ (∑ i, X i) ω}).toReal ≤
      exp (-(t ^ 2) / (2 * (v + b * t / 3))) := by
  classical
  simpa using
    (bernstein_inequality_finset
      (s := (Finset.univ : Finset ι))
      (X := X) (b := b) (v := v) (t := t)
      hb hv ht h_indep hX
      (fun i _ => hcenter i)
      (fun i _ => hbound i)
      (by simpa using hvar))

end

end LeanPool
