/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.GammaSigmaExpRegime.Preliminaries

/-! # One Variable -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

private lemma exp_mul_mul_le_half_of_le_inv_two_exp_mul {M l : ℝ}
    (hM : 0 ≤ M) (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹) :
    Real.exp 1 * M * l ≤ (1 / 2 : ℝ) := by
  by_cases hM0 : M = 0
  · simp [hM0]
  · let C : ℝ := 2 * Real.exp 1 * M
    have hM_pos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (Real.exp_pos 1).le)
        hM
    have htmp := mul_le_mul_of_nonneg_left hl_small hC_nonneg
    have hC_ne : C ≠ 0 := by
      dsimp [C]
      positivity
    have hbound : C * l ≤ 1 := by
      calc
        C * l ≤ C * C⁻¹ := by simpa [C] using htmp
        _ = 1 := by field_simp [hC_ne]
    dsimp [C] at hbound ⊢
    linarith

private lemma exp_mul_mul_le_quarter_of_le_inv_four_exp_mul {M l : ℝ}
    (hM : 0 ≤ M) (hl_small : l ≤ (4 * Real.exp 1 * M)⁻¹) :
    Real.exp 1 * M * l ≤ (1 / 4 : ℝ) := by
  by_cases hM0 : M = 0
  · simp [hM0]
  · let C : ℝ := 4 * Real.exp 1 * M
    have hM_pos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (4 : ℝ)) (Real.exp_pos 1).le)
        hM
    have htmp := mul_le_mul_of_nonneg_left hl_small hC_nonneg
    have hC_ne : C ≠ 0 := by
      dsimp [C]
      positivity
    have hbound : C * l ≤ 1 := by
      calc
        C * l ≤ C * C⁻¹ := by simpa [C] using htmp
        _ = 1 := by field_simp [hC_ne]
    dsimp [C] at hbound ⊢
    linarith

/-- Small-`λ` mgf bound for a centered `Γ_σ` random variable, in the raw
geometric-tail form that comes directly from the exponential power series. -/
theorem mgf_le_one_add_tsum_geometric_of_gammaMomentGrowth_small_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹)
    (hXmean : ∫ ω, X ω ∂μ = 0)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    mgf X μ l ≤ 1 + ∑' n : ℕ, (Real.exp 1 * M * l) ^ (n + 2) := by
  let F : ℕ → Ω → ℝ := gammaExpSeriesTerm l X
  let r : ℝ := Real.exp 1 * M * l
  have hF_int : ∀ n : ℕ, Integrable (F n) μ := by
    intro n
    exact integrable_gammaExpSeriesTerm
      (μ := μ) (X := X) (σ := σ) (M := M) (l := l) n hXm hl hXmom
  have hF_sum_norm : Summable (fun n : ℕ => ∫ ω, ‖F n ω‖ ∂μ) := by
    simpa [F] using summable_integral_norm_gammaExpSeriesTerm
      (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
      hσ hM hl hl_small hXmom
  have hF_sum_int : Summable (fun n : ℕ => ∫ ω, F n ω ∂μ) := by
    exact hF_sum_norm.of_norm_bounded (fun n => norm_integral_le_integral_norm _)
  have h_exp_series :
      (fun ω => Real.exp (l * X ω)) = fun ω => ∑' n : ℕ, F n ω := by
    funext ω
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    simp [F, gammaExpSeriesTerm]
  have hmgf_series :
      mgf X μ l = ∑' n : ℕ, ∫ ω, F n ω ∂μ := by
    rw [mgf, h_exp_series]
    symm
    exact integral_tsum_of_summable_integral_norm hF_int hF_sum_norm
  have hhead0 : ∫ ω, F 0 ω ∂μ = 1 := by
    simp [F, gammaExpSeriesTerm]
  have hhead1 : ∫ ω, F 1 ω ∂μ = 0 := by
    calc
      ∫ ω, F 1 ω ∂μ = l * (∫ ω, X ω ∂μ) := by
          simpa [F, gammaExpSeriesTerm] using integral_const_mul l X
      _ = 0 := by rw [hXmean]; ring
  have htail_sum_int : Summable (fun n : ℕ => ∫ ω, F (n + 2) ω ∂μ) := by
    exact (summable_nat_add_iff (f := fun n : ℕ => ∫ ω, F n ω ∂μ) 2).2 hF_sum_int
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_le_half : r ≤ 1 / 2 := by
    dsimp [r]
    exact exp_mul_mul_le_half_of_le_inv_two_exp_mul hM hl_small
  have hr_lt_one : r < 1 := lt_of_le_of_lt hr_le_half (by norm_num)
  have hgeom : Summable (fun n : ℕ => r ^ (n + 2)) := by
    have hs : Summable (fun n : ℕ => r ^ n) :=
      summable_geometric_of_lt_one hr_nonneg hr_lt_one
    simpa [pow_add, pow_two, mul_assoc, mul_left_comm, mul_comm] using
      hs.mul_left (r ^ (2 : ℕ))
  have htail_le :
      ∑' n : ℕ, ∫ ω, F (n + 2) ω ∂μ ≤ ∑' n : ℕ, r ^ (n + 2) := by
    refine htail_sum_int.tsum_le_tsum (fun n => ?_) hgeom
    have hnorm_le : ∫ ω, F (n + 2) ω ∂μ ≤ ∫ ω, ‖F (n + 2) ω‖ ∂μ := by
      calc
        ∫ ω, F (n + 2) ω ∂μ ≤ |∫ ω, F (n + 2) ω ∂μ| := by
          exact le_abs_self _
        _ = ‖∫ ω, F (n + 2) ω ∂μ‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∫ ω, ‖F (n + 2) ω‖ ∂μ := norm_integral_le_integral_norm _
    have hgeom_le : ∫ ω, ‖F (n + 2) ω‖ ∂μ ≤ r ^ (n + 2) := by
      simpa [F, r, gammaExpTaylorTail_eq_gammaExpSeriesTerm_add_two] using
        integral_norm_gammaExpTaylorTail_le_geometric
          (μ := μ) (X := X) (σ := σ) (M := M) (l := l) n hσ hM hl hXmom
    exact hnorm_le.trans hgeom_le
  calc
    mgf X μ l
      = (∑ i ∈ Finset.range 2, ∫ ω, F i ω ∂μ) +
          ∑' n : ℕ, ∫ ω, F (n + 2) ω ∂μ := by
            rw [hmgf_series, ← hF_sum_int.sum_add_tsum_nat_add 2]
    _ = 1 + ∑' n : ℕ, ∫ ω, F (n + 2) ω ∂μ := by
          rw [Finset.sum_range_succ, Finset.sum_range_one, hhead0, hhead1]
          ring
    _ ≤ 1 + ∑' n : ℕ, r ^ (n + 2) := by
          gcongr
    _ = 1 + ∑' n : ℕ, (Real.exp 1 * M * l) ^ (n + 2) := by
          simp [r]

/-- Small-`λ` mgf bound without the centering hypothesis. The linear term is
controlled by the first absolute moment. -/
theorem mgf_le_one_add_linear_add_tsum_geometric_of_gammaMomentGrowth_small
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    mgf X μ l ≤ 1 + l * M + ∑' n : ℕ, (Real.exp 1 * M * l) ^ (n + 2) := by
  let F : ℕ → Ω → ℝ := gammaExpSeriesTerm l X
  let r : ℝ := Real.exp 1 * M * l
  have hF_int : ∀ n : ℕ, Integrable (F n) μ := by
    intro n
    exact integrable_gammaExpSeriesTerm
      (μ := μ) (X := X) (σ := σ) (M := M) (l := l) n hXm hl hXmom
  have hF_sum_norm : Summable (fun n : ℕ => ∫ ω, ‖F n ω‖ ∂μ) := by
    simpa [F] using summable_integral_norm_gammaExpSeriesTerm
      (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
      hσ hM hl hl_small hXmom
  have hF_sum_int : Summable (fun n : ℕ => ∫ ω, F n ω ∂μ) := by
    exact hF_sum_norm.of_norm_bounded (fun n => norm_integral_le_integral_norm _)
  have h_exp_series :
      (fun ω => Real.exp (l * X ω)) = fun ω => ∑' n : ℕ, F n ω := by
    funext ω
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    simp [F, gammaExpSeriesTerm]
  have hmgf_series :
      mgf X μ l = ∑' n : ℕ, ∫ ω, F n ω ∂μ := by
    rw [mgf, h_exp_series]
    symm
    exact integral_tsum_of_summable_integral_norm hF_int hF_sum_norm
  have hhead0 : ∫ ω, F 0 ω ∂μ = 1 := by
    simp [F, gammaExpSeriesTerm]
  have hXone :=
    gammaMomentGrowth_natCast_bound
      (μ := μ) (X := X) (σ := σ) (M := M) (n := 1) (by norm_num) hXmom
  have hX_abs_int : Integrable (fun ω => |X ω|) μ := by
    simpa using hXone.1
  have hX_int : Integrable X μ := by
    have hX_norm_int : Integrable (fun ω => ‖X ω‖) μ := by
      simpa [Real.norm_eq_abs] using hX_abs_int
    exact (integrable_norm_iff hXm.aestronglyMeasurable).1 hX_norm_int
  have hX_abs_bound : ∫ ω, |X ω| ∂μ ≤ M := by
    simpa using hXone.2
  have hhead1_le : ∫ ω, F 1 ω ∂μ ≤ l * M := by
    calc
      ∫ ω, F 1 ω ∂μ = l * (∫ ω, X ω ∂μ) := by
          simpa [F, gammaExpSeriesTerm] using integral_const_mul l X
      _ ≤ l * (∫ ω, |X ω| ∂μ) := by
          exact mul_le_mul_of_nonneg_left
            (integral_mono_ae hX_int hX_abs_int
              (Filter.Eventually.of_forall fun ω => le_abs_self (X ω))) hl
      _ ≤ l * M := by
          gcongr
  have htail_sum_int : Summable (fun n : ℕ => ∫ ω, F (n + 2) ω ∂μ) := by
    exact (summable_nat_add_iff (f := fun n : ℕ => ∫ ω, F n ω ∂μ) 2).2 hF_sum_int
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_le_half : r ≤ 1 / 2 := by
    dsimp [r]
    exact exp_mul_mul_le_half_of_le_inv_two_exp_mul hM hl_small
  have hr_lt_one : r < 1 := lt_of_le_of_lt hr_le_half (by norm_num)
  have hgeom : Summable (fun n : ℕ => r ^ (n + 2)) := by
    have hs : Summable (fun n : ℕ => r ^ n) :=
      summable_geometric_of_lt_one hr_nonneg hr_lt_one
    simpa [pow_add, pow_two, mul_assoc, mul_left_comm, mul_comm] using
      hs.mul_left (r ^ (2 : ℕ))
  have htail_le :
      ∑' n : ℕ, ∫ ω, F (n + 2) ω ∂μ ≤ ∑' n : ℕ, r ^ (n + 2) := by
    refine htail_sum_int.tsum_le_tsum (fun n => ?_) hgeom
    have hnorm_le : ∫ ω, F (n + 2) ω ∂μ ≤ ∫ ω, ‖F (n + 2) ω‖ ∂μ := by
      calc
        ∫ ω, F (n + 2) ω ∂μ ≤ |∫ ω, F (n + 2) ω ∂μ| := by
          exact le_abs_self _
        _ = ‖∫ ω, F (n + 2) ω ∂μ‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∫ ω, ‖F (n + 2) ω‖ ∂μ := norm_integral_le_integral_norm _
    have hgeom_le : ∫ ω, ‖F (n + 2) ω‖ ∂μ ≤ r ^ (n + 2) := by
      simpa [F, r, gammaExpTaylorTail_eq_gammaExpSeriesTerm_add_two] using
        integral_norm_gammaExpTaylorTail_le_geometric
          (μ := μ) (X := X) (σ := σ) (M := M) (l := l) n hσ hM hl hXmom
    exact hnorm_le.trans hgeom_le
  calc
    mgf X μ l
      = (∑ i ∈ Finset.range 2, ∫ ω, F i ω ∂μ) +
          ∑' n : ℕ, ∫ ω, F (n + 2) ω ∂μ := by
            rw [hmgf_series, ← hF_sum_int.sum_add_tsum_nat_add 2]
    _ = 1 + ∫ ω, F 1 ω ∂μ + ∑' n : ℕ, ∫ ω, F (n + 2) ω ∂μ := by
          rw [Finset.sum_range_succ, Finset.sum_range_one, hhead0]
    _ ≤ 1 + l * M + ∑' n : ℕ, ∫ ω, F (n + 2) ω ∂μ := by
          gcongr
    _ ≤ 1 + l * M + ∑' n : ℕ, r ^ (n + 2) := by
          gcongr
    _ = 1 + l * M + ∑' n : ℕ, (Real.exp 1 * M * l) ^ (n + 2) := by
          simp [r]

/-- Clean small-`λ` mgf estimate for centered `Γ_σ` random variables in the
exponential regime `σ ≥ 1`. -/
theorem mgf_le_one_add_two_mul_sq_of_gammaMomentGrowth_small_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹)
    (hXmean : ∫ ω, X ω ∂μ = 0)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    mgf X μ l ≤ 1 + 2 * (Real.exp 1 * M * l) ^ (2 : ℕ) := by
  let r : ℝ := Real.exp 1 * M * l
  have hbase :=
    mgf_le_one_add_tsum_geometric_of_gammaMomentGrowth_small_of_integral_eq_zero
      (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
      hXm hσ hM hl hl_small hXmean hXmom
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_le_half : r ≤ 1 / 2 := by
    dsimp [r]
    exact exp_mul_mul_le_half_of_le_inv_two_exp_mul hM hl_small
  have hr_lt_one : r < 1 := lt_of_le_of_lt hr_le_half (by norm_num)
  have hsum :
      ∑' n : ℕ, r ^ (n + 2) = r ^ (2 : ℕ) * (1 - r)⁻¹ := by
    calc
      ∑' n : ℕ, r ^ (n + 2) = ∑' n : ℕ, (r ^ (2 : ℕ)) * r ^ n := by
            congr with n
            rw [pow_add, pow_two]
            ring
      _ = r ^ (2 : ℕ) * ∑' n : ℕ, r ^ n := by rw [tsum_mul_left]
      _ = r ^ (2 : ℕ) * (1 - r)⁻¹ := by
            rw [tsum_geometric_of_lt_one hr_nonneg hr_lt_one]
  have hgeom_le : ∑' n : ℕ, r ^ (n + 2) ≤ 2 * r ^ (2 : ℕ) := by
    rw [hsum]
    have hhalf_le : (1 : ℝ) / 2 ≤ 1 - r := by
      linarith
    have hden_pos : 0 < 1 - r := by
      linarith
    have hinv_le : (1 - r)⁻¹ ≤ 2 := by
      have := one_div_le_one_div_of_le (by norm_num : 0 < (1 : ℝ) / 2) hhalf_le
      simpa using this
    calc
      r ^ (2 : ℕ) * (1 - r)⁻¹ ≤ r ^ (2 : ℕ) * 2 := by
            gcongr
      _ = 2 * r ^ (2 : ℕ) := by ring
  calc
    mgf X μ l ≤ 1 + ∑' n : ℕ, r ^ (n + 2) := by
      simpa [r] using hbase
    _ ≤ 1 + 2 * r ^ (2 : ℕ) := by
      gcongr
    _ = 1 + 2 * (Real.exp 1 * M * l) ^ (2 : ℕ) := by
      simp [r]

/-- Exponential small-`λ` mgf estimate for centered `Γ_σ` random variables in
the regime `σ ≥ 1`. -/
theorem mgf_le_exp_two_mul_sq_of_gammaMomentGrowth_small_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹)
    (hXmean : ∫ ω, X ω ∂μ = 0)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    mgf X μ l ≤ Real.exp (2 * (Real.exp 1 * M * l) ^ (2 : ℕ)) := by
  calc
    mgf X μ l ≤ 1 + 2 * (Real.exp 1 * M * l) ^ (2 : ℕ) := by
      exact mgf_le_one_add_two_mul_sq_of_gammaMomentGrowth_small_of_integral_eq_zero
        (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
        hXm hσ hM hl hl_small hXmean hXmom
    _ ≤ Real.exp (2 * (Real.exp 1 * M * l) ^ (2 : ℕ)) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * (Real.exp 1 * M * l) ^ (2 : ℕ))

/-- Under the stronger quarter-scale hypothesis `e M λ ≤ 1/4`, the small-`λ`
mgf is universally bounded by `2`. -/
theorem mgf_le_two_of_gammaMomentGrowth_quarter_small
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 ≤ σ) (hM : 0 < M) (hl : 0 ≤ l)
    (hl_quarter : l ≤ (4 * Real.exp 1 * M)⁻¹)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    mgf X μ l ≤ 2 := by
  have hsmall :
      l ≤ (2 * Real.exp 1 * M)⁻¹ := by
    have hden :
        0 < 2 * Real.exp 1 * M := by
      positivity
    have hfour_le :
        (4 * Real.exp 1 * M)⁻¹ ≤ (2 * Real.exp 1 * M)⁻¹ := by
      have haux : 2 * Real.exp 1 * M ≤ 4 * Real.exp 1 * M := by
        have hbase_nonneg : 0 ≤ Real.exp 1 * M :=
          mul_nonneg (Real.exp_pos 1).le hM.le
        calc
          2 * Real.exp 1 * M = 2 * (Real.exp 1 * M) := by ring
          _ ≤ 4 * (Real.exp 1 * M) :=
            mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) hbase_nonneg
          _ = 4 * Real.exp 1 * M := by ring
      simpa [one_div] using (one_div_le_one_div_of_le hden haux)
    exact hl_quarter.trans hfour_le
  have hmain :=
    mgf_le_one_add_linear_add_tsum_geometric_of_gammaMomentGrowth_small
      (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
      hXm hσ hM.le hl hsmall hXmom
  let r : ℝ := Real.exp 1 * M * l
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_le_quarter : r ≤ (1 / 4 : ℝ) := by
    dsimp [r]
    exact exp_mul_mul_le_quarter_of_le_inv_four_exp_mul hM.le hl_quarter
  have hr_lt_one : r < 1 := lt_of_le_of_lt hr_le_quarter (by norm_num)
  have hsum :
      ∑' n : ℕ, r ^ (n + 2) = r ^ (2 : ℕ) * (1 - r)⁻¹ := by
    calc
      ∑' n : ℕ, r ^ (n + 2) = ∑' n : ℕ, (r ^ (2 : ℕ)) * r ^ n := by
            congr with n
            rw [pow_add, pow_two]
            ring
      _ = r ^ (2 : ℕ) * ∑' n : ℕ, r ^ n := by rw [tsum_mul_left]
      _ = r ^ (2 : ℕ) * (1 - r)⁻¹ := by
            rw [tsum_geometric_of_lt_one hr_nonneg hr_lt_one]
  have htail_le : ∑' n : ℕ, r ^ (n + 2) ≤ 1 / 2 := by
    rw [hsum]
    have hhalf_le : (1 : ℝ) / 2 ≤ 1 - r := by
      linarith
    have hinv_le : (1 - r)⁻¹ ≤ 2 := by
      have := one_div_le_one_div_of_le (by norm_num : 0 < (1 : ℝ) / 2) hhalf_le
      simpa using this
    have hr_sq_le : r ^ (2 : ℕ) ≤ (1 / 4 : ℝ) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ hr_nonneg hr_le_quarter 2
    calc
      r ^ (2 : ℕ) * (1 - r)⁻¹ ≤ r ^ (2 : ℕ) * 2 := by
            gcongr
      _ ≤ (1 / 4 : ℝ) ^ (2 : ℕ) * 2 := by
            gcongr
      _ ≤ 1 / 2 := by norm_num
  have hlin_le : l * M ≤ 1 / 2 := by
    have htmp := mul_le_mul_of_nonneg_left hl_quarter hM.le
    have hcalc : M * (4 * Real.exp 1 * M)⁻¹ = (4 * Real.exp 1)⁻¹ := by
      field_simp [hM.ne', Real.exp_ne_zero]
    calc
      l * M = M * l := by ring
      _ ≤ M * (4 * Real.exp 1 * M)⁻¹ := htmp
      _ = (4 * Real.exp 1)⁻¹ := hcalc
      _ ≤ 1 / 2 := by
            have hexp : (1 : ℝ) ≤ Real.exp 1 := by
              exact Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
            have hden : (2 : ℝ) ≤ 4 * Real.exp 1 := by
              calc
                (2 : ℝ) = 2 * 1 := by ring
                _ ≤ 2 * Real.exp 1 :=
                  mul_le_mul_of_nonneg_left hexp (by norm_num : 0 ≤ (2 : ℝ))
                _ ≤ 4 * Real.exp 1 :=
                  mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4)
                    (Real.exp_pos 1).le
            have hinv : (4 * Real.exp 1)⁻¹ ≤ (2 : ℝ)⁻¹ := by
              simpa [one_div] using
                (one_div_le_one_div_of_le (show 0 < (2 : ℝ) by norm_num) hden)
            simpa using hinv
  calc
    mgf X μ l ≤ 1 + l * M + ∑' n : ℕ, (Real.exp 1 * M * l) ^ (n + 2) := hmain
    _ = 1 + l * M + ∑' n : ℕ, r ^ (n + 2) := by simp [r]
    _ ≤ 2 := by
          have hsum_le :
              l * M + (∑' n : ℕ, r ^ (n + 2)) ≤ (1 / 2 : ℝ) + 1 / 2 :=
            add_le_add hlin_le htail_le
          calc
            1 + l * M + (∑' n : ℕ, r ^ (n + 2))
                ≤ 1 + ((1 / 2 : ℝ) + 1 / 2) :=
              by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_left hsum_le (1 : ℝ)
            _ = 2 := by norm_num

private theorem gammaExpLargeLambdaControl
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 < σ) (hM : 0 < M) (hl : 0 ≤ l)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    let B : ℝ := Real.exp 1 * M
    let Y : Ω → ℝ := fun ω => |B⁻¹ * X ω| ^ σ
    let δ : ℝ := (4 * Real.exp 1 * gammaMomentConst 1)⁻¹
    let C : ℝ := gammaExpLargeLambdaConst σ * (B * l) ^ gammaExpConjExponent σ
    Integrable (fun ω => Real.exp (C + δ * Y ω)) μ ∧
      (∀ ω, l * X ω ≤ C + δ * Y ω) ∧
        mgf Y μ δ ≤ 2 := by
  let B : ℝ := Real.exp 1 * M
  let Y : Ω → ℝ := fun ω => |B⁻¹ * X ω| ^ σ
  let δ : ℝ := (4 * Real.exp 1 * gammaMomentConst 1)⁻¹
  let C : ℝ := gammaExpLargeLambdaConst σ * (B * l) ^ gammaExpConjExponent σ
  change
      Integrable (fun ω => Real.exp (C + δ * Y ω)) μ ∧
        (∀ ω, l * X ω ≤ C + δ * Y ω) ∧
          mgf Y μ δ ≤ 2
  have hσ_pos : 0 < σ := by linarith
  have hσ_ne : σ ≠ 0 := by linarith
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hscaled : IsBigO μ (gammaSigma σ) (fun ω => B⁻¹ * X ω) 1 := by
    have hX_bigO :
        IsBigO μ (gammaSigma σ) X B := by
      exact isBigO_gammaSigma_of_hasGammaMomentGrowthWith
        (μ := μ) (X := X) (M := M) (σ := σ) hσ_pos hM hXmom
    have hscaled' :=
      IsBigO.const_mul (μ := μ) (Ψ := gammaSigma σ) (X := X) (A := B) (c := B⁻¹)
        (inv_nonneg.mpr hB_pos.le) hX_bigO
    have hscale : B⁻¹ * B = (1 : ℝ) := by
      field_simp [hB_pos.ne']
    simpa [hscale] using hscaled'
  have hYm : AEMeasurable Y μ := by
    dsimp [Y]
    have hscaledm : AEMeasurable (fun ω => B⁻¹ * X ω) μ := by
      simpa [mul_comm] using hXm.const_mul B⁻¹
    exact (Real.continuous_rpow_const hσ_pos.le).measurable.comp_aemeasurable
      (continuous_abs.measurable.comp_aemeasurable hscaledm)
  have hY_bigO : IsBigO μ (gammaSigma 1) Y 1 := by
    have hpow_bigO :=
      (isBigO_gammaSigma_rpow_iff
        (μ := μ) (X := fun ω => B⁻¹ * X ω) (A := 1) (σ := σ) (p := σ)
        hσ_pos (by norm_num : 0 ≤ (1 : ℝ))).1 hscaled
    have hσ_div : σ / σ = (1 : ℝ) := by
      field_simp [hσ_ne]
    simpa [Y, hσ_div] using hpow_bigO
  have hYmom : HasGammaMomentGrowthWith μ 1 Y (gammaMomentConst 1) := by
    simpa using hasGammaMomentGrowthWith_of_isBigO_gammaSigma
      (μ := μ) (X := Y) (K := 1) (σ := 1)
      zero_lt_one zero_lt_one hYm hY_bigO
  have hγone_pos : 0 < gammaMomentConst 1 := gammaMomentConst_pos zero_lt_one
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    have hden_pos : 0 < 4 * Real.exp 1 * gammaMomentConst 1 := by
      positivity
    exact inv_pos.mpr hden_pos
  have hδ_small : δ ≤ (2 * Real.exp 1 * gammaMomentConst 1)⁻¹ := by
    have hden : 0 < 2 * Real.exp 1 * gammaMomentConst 1 := by
      positivity
    have haux : 2 * Real.exp 1 * gammaMomentConst 1 ≤ 4 * Real.exp 1 * gammaMomentConst 1 := by
      have hbase_nonneg : 0 ≤ Real.exp 1 * gammaMomentConst 1 :=
        mul_nonneg (Real.exp_pos 1).le hγone_pos.le
      calc
        2 * Real.exp 1 * gammaMomentConst 1 = 2 * (Real.exp 1 * gammaMomentConst 1) := by
          ring
        _ ≤ 4 * (Real.exp 1 * gammaMomentConst 1) :=
          mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) hbase_nonneg
        _ = 4 * Real.exp 1 * gammaMomentConst 1 := by ring
    simpa [δ, one_div] using (one_div_le_one_div_of_le hden haux)
  have hYint : Integrable (fun ω => Real.exp (δ * Y ω)) μ := by
    exact integrable_exp_mul_of_gammaMomentGrowth_small
      (μ := μ) (X := Y) (σ := 1) (M := gammaMomentConst 1) (l := δ)
      hYm (by norm_num) hγone_pos.le hδ_pos.le hδ_small hYmom
  have hYmgf : mgf Y μ δ ≤ 2 := by
    exact mgf_le_two_of_gammaMomentGrowth_quarter_small
      (μ := μ) (X := Y) (σ := 1) (M := gammaMomentConst 1) (l := δ)
      hYm (by norm_num) hγone_pos hδ_pos.le (by simp [δ]) hYmom
  have hpointwise : ∀ ω, l * X ω ≤ C + δ * Y ω := by
    intro ω
    have habs : l * X ω ≤ l * |X ω| := by
      exact mul_le_mul_of_nonneg_left (le_abs_self (X ω)) hl
    have hyoung :=
      gammaExp_young_scale_delta (σ := σ) (B := B) (l := l)
        (t := |B⁻¹ * X ω|) (δ := δ) hσ hB_pos.le hl (abs_nonneg _) hδ_pos
    have habs_scaled : B * |B⁻¹ * X ω| = |X ω| := by
      calc
        B * |B⁻¹ * X ω| = B * (|B⁻¹| * |X ω|) := by rw [abs_mul]
        _ = B * (B⁻¹ * |X ω|) := by
          rw [abs_of_nonneg (inv_nonneg.mpr hB_pos.le)]
        _ = (B * B⁻¹) * |X ω| := by ring
        _ = |X ω| := by rw [mul_inv_cancel₀ hB_pos.ne', one_mul]
    have hyoung1 : l * (B * |B⁻¹ * X ω|) ≤ δ * Y ω + C := by
      simpa [C, Y, δ, gammaExpLargeLambdaConst, add_comm, add_left_comm, add_assoc] using hyoung
    have hyoung' : l * |X ω| ≤ C + δ * Y ω := by
      calc
        l * |X ω| = l * (B * |B⁻¹ * X ω|) := by rw [habs_scaled]
        _ ≤ δ * Y ω + C := hyoung1
        _ = C + δ * Y ω := by ring
    exact le_trans habs hyoung'
  have hUpperInt : Integrable (fun ω => Real.exp (C + δ * Y ω)) μ := by
    have hmul : Integrable (fun ω => Real.exp C * Real.exp (δ * Y ω)) μ := by
      exact hYint.const_mul (Real.exp C)
    simpa [Real.exp_add, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hmul
  exact ⟨hUpperInt, hpointwise, hYmgf⟩

/-- One-variable exponential mgf bound in the Chapter 4 regime `σ > 1`.
The proof reduces `|X|^σ` to a unit-scale `Γ₁` random variable and feeds it
through the small-parameter `Γ₁` mgf estimate. -/
theorem mgf_le_two_mul_exp_of_gammaMomentGrowth_of_one_lt
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 < σ) (hM : 0 < M) (hl : 0 ≤ l)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    mgf X μ l ≤
      2 * Real.exp
        (gammaExpLargeLambdaConst σ *
          (Real.exp 1 * M * l) ^ gammaExpConjExponent σ) := by
  let B : ℝ := Real.exp 1 * M
  let Y : Ω → ℝ := fun ω => |B⁻¹ * X ω| ^ σ
  let δ : ℝ := (4 * Real.exp 1 * gammaMomentConst 1)⁻¹
  let C : ℝ := gammaExpLargeLambdaConst σ * (B * l) ^ gammaExpConjExponent σ
  have hcontrol := gammaExpLargeLambdaControl
    (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
    hXm hσ hM hl hXmom
  change
      Integrable (fun ω => Real.exp (C + δ * Y ω)) μ ∧
        (∀ ω, l * X ω ≤ C + δ * Y ω) ∧
          mgf Y μ δ ≤ 2 at hcontrol
  obtain ⟨hUpperInt, hpointwise, hYmgf⟩ := hcontrol
  have hUpperInt' : Integrable (fun ω => Real.exp (1 * (C + δ * Y ω))) μ := by
    simpa using hUpperInt
  have hmgf_le :
      mgf (fun ω => l * X ω) μ 1 ≤ mgf (fun ω => C + δ * Y ω) μ 1 := by
    exact mgf_mono_of_nonneg
      (μ := μ) (X := fun ω => l * X ω) (Y := fun ω => C + δ * Y ω)
      (Filter.Eventually.of_forall hpointwise) (by norm_num) hUpperInt'
  calc
    mgf X μ l = mgf (fun ω => l * X ω) μ 1 := by
      simpa using (mgf_const_mul (X := X) (μ := μ) (t := (1 : ℝ)) l).symm
    _ ≤ mgf (fun ω => C + δ * Y ω) μ 1 := hmgf_le
    _ = Real.exp C * mgf Y μ δ := by
      rw [mgf_const_add, mgf_const_mul]
      simp
    _ ≤ Real.exp C * 2 := by
      gcongr
    _ = 2 * Real.exp C := by ring
    _ = 2 * Real.exp
        (gammaExpLargeLambdaConst σ *
          (Real.exp 1 * M * l) ^ gammaExpConjExponent σ) := by
            simp [C, B]

/-- Exponential integrability in the Chapter 4 large-`λ` regime `σ > 1`. -/
theorem integrable_exp_mul_of_gammaMomentGrowth_of_one_lt
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 < σ) (hM : 0 < M) (hl : 0 ≤ l)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    Integrable (fun ω => Real.exp (l * X ω)) μ := by
  let B : ℝ := Real.exp 1 * M
  let Y : Ω → ℝ := fun ω => |B⁻¹ * X ω| ^ σ
  let δ : ℝ := (4 * Real.exp 1 * gammaMomentConst 1)⁻¹
  let C : ℝ := gammaExpLargeLambdaConst σ * (B * l) ^ gammaExpConjExponent σ
  have hcontrol := gammaExpLargeLambdaControl
    (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
    hXm hσ hM hl hXmom
  change
      Integrable (fun ω => Real.exp (C + δ * Y ω)) μ ∧
        (∀ ω, l * X ω ≤ C + δ * Y ω) ∧
          mgf Y μ δ ≤ 2 at hcontrol
  obtain ⟨hUpperInt, hpointwise, _hYmgf⟩ := hcontrol
  have hExpMeas : AEStronglyMeasurable (fun ω => Real.exp (l * X ω)) μ := by
    have hmul : AEMeasurable (fun ω => l * X ω) μ := by
      simpa [mul_comm] using hXm.const_mul l
    exact hmul.exp.aestronglyMeasurable
  refine Integrable.mono' hUpperInt hExpMeas ?_
  refine Filter.Eventually.of_forall ?_
  intro ω
  have hle : l * X ω ≤ C + δ * Y ω := hpointwise ω
  have hexp_le : Real.exp (l * X ω) ≤ Real.exp (C + δ * Y ω) := by
    exact Real.exp_le_exp.2 hle
  have hleft_nonneg : 0 ≤ Real.exp (l * X ω) := by positivity
  have hright_nonneg : 0 ≤ Real.exp (C + δ * Y ω) := by positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using
    hexp_le

/-- Explicit coefficient after pushing the large-`λ` mgf estimate from
moment-growth witnesses back to the note-facing `O_{Γ_σ}` scale. -/
noncomputable def gammaSigmaLargeMgfConst (σ : ℝ) : ℝ :=
  gammaExpLargeLambdaConst σ *
    (Real.exp 1 * gammaMomentConst σ) ^ gammaExpConjExponent σ

/-- Large-`λ` one-variable mgf bound stated directly for `O_{Γ_σ}` random
variables with `σ > 1`. -/
theorem mgf_le_two_mul_exp_of_isBigO_gammaSigma_of_one_lt
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ K l : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 < σ) (hK : 0 < K) (hl : 0 ≤ l)
    (hX : IsBigO μ (gammaSigma σ) X K) :
    mgf X μ l ≤
      2 * Real.exp
        (gammaSigmaLargeMgfConst σ * (K * l) ^ gammaExpConjExponent σ) := by
  have hσ_pos : 0 < σ := by linarith
  have hmom :
      HasGammaMomentGrowthWith μ σ X (gammaMomentConst σ * K) := by
    exact hasGammaMomentGrowthWith_of_isBigO_gammaSigma
      (μ := μ) (X := X) (K := K) (σ := σ) hσ_pos hK hXm hX
  have hM_pos : 0 < gammaMomentConst σ * K := by
    exact mul_pos (gammaMomentConst_pos hσ_pos) hK
  have hmain :=
    mgf_le_two_mul_exp_of_gammaMomentGrowth_of_one_lt
      (μ := μ) (X := X) (σ := σ) (M := gammaMomentConst σ * K) (l := l)
      hXm hσ hM_pos hl hmom
  have hscale :
      gammaExpLargeLambdaConst σ *
          (Real.exp 1 * (gammaMomentConst σ * K) * l) ^ gammaExpConjExponent σ =
        gammaSigmaLargeMgfConst σ * (K * l) ^ gammaExpConjExponent σ := by
    let q : ℝ := gammaExpConjExponent σ
    have hconst_pos : 0 < Real.exp 1 * gammaMomentConst σ := by
      exact mul_pos (Real.exp_pos 1) (gammaMomentConst_pos hσ_pos)
    have hKl_nonneg : 0 ≤ K * l := mul_nonneg hK.le hl
    calc
      gammaExpLargeLambdaConst σ *
          (Real.exp 1 * (gammaMomentConst σ * K) * l) ^ q
        = gammaExpLargeLambdaConst σ *
            (((Real.exp 1 * gammaMomentConst σ) * (K * l)) ^ q) := by
              congr 2
              ring
      _ = gammaExpLargeLambdaConst σ *
            ((Real.exp 1 * gammaMomentConst σ) ^ q * (K * l) ^ q) := by
              rw [Real.mul_rpow hconst_pos.le hKl_nonneg]
      _ = gammaSigmaLargeMgfConst σ * (K * l) ^ q := by
              dsimp [gammaSigmaLargeMgfConst, q]
              ring
  simpa [hscale] using hmain

/-- Exponential integrability in the note-facing `O_{Γ_σ}` language for
`σ > 1`. -/
theorem integrable_exp_mul_of_isBigO_gammaSigma_of_one_lt
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ K l : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 < σ) (hK : 0 < K) (hl : 0 ≤ l)
    (hX : IsBigO μ (gammaSigma σ) X K) :
    Integrable (fun ω => Real.exp (l * X ω)) μ := by
  have hσ_pos : 0 < σ := by linarith
  have hmom :
      HasGammaMomentGrowthWith μ σ X (gammaMomentConst σ * K) := by
    exact hasGammaMomentGrowthWith_of_isBigO_gammaSigma
      (μ := μ) (X := X) (K := K) (σ := σ) hσ_pos hK hXm hX
  have hM_pos : 0 < gammaMomentConst σ * K := by
    exact mul_pos (gammaMomentConst_pos hσ_pos) hK
  exact integrable_exp_mul_of_gammaMomentGrowth_of_one_lt
    (μ := μ) (X := X) (σ := σ) (M := gammaMomentConst σ * K) (l := l)
    hXm hσ hM_pos hl hmom

/-- Chernoff upper-tail estimate coming from the small-`λ` `Γ_σ` mgf bound. -/
theorem measureReal_upperTailEvent_le_exp_of_gammaMomentGrowth_small_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l a : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹)
    (hXmean : ∫ ω, X ω ∂μ = 0)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    μ.real (upperTailEvent X a) ≤
      Real.exp (-l * a + 2 * (Real.exp 1 * M * l) ^ (2 : ℕ)) := by
  have hsubset : upperTailEvent X a ⊆ {ω | a ≤ X ω} := by
    intro ω hω
    simpa [upperTailEvent] using le_of_lt hω
  refine (measureReal_mono (s₂ := {ω | a ≤ X ω}) hsubset).trans ?_
  calc
    μ.real {ω | a ≤ X ω}
      ≤ Real.exp (-l * a) * mgf X μ l := by
          exact measure_ge_le_exp_mul_mgf
            (μ := μ) (X := X) (ε := a) (t := l) hl
            (integrable_exp_mul_of_gammaMomentGrowth_small
              (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
              hXm hσ hM hl hl_small hXmom)
    _ ≤ Real.exp (-l * a) * Real.exp (2 * (Real.exp 1 * M * l) ^ (2 : ℕ)) := by
          gcongr
          exact mgf_le_exp_two_mul_sq_of_gammaMomentGrowth_small_of_integral_eq_zero
            (μ := μ) (X := X) (σ := σ) (M := M) (l := l)
            hXm hσ hM hl hl_small hXmean hXmom
    _ = Real.exp (-l * a + 2 * (Real.exp 1 * M * l) ^ (2 : ℕ)) := by
          rw [← Real.exp_add]

/-- Absolute-tail version of the small-`λ` `Γ_σ` Chernoff estimate. -/
theorem measureReal_absTailEvent_le_two_mul_exp_of_gammaMomentGrowth_small_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ M l a : ℝ}
    (hXm : AEMeasurable X μ)
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹)
    (hXmean : ∫ ω, X ω ∂μ = 0)
    (hXmom : HasGammaMomentGrowthWith μ σ X M) :
    μ.real (absTailEvent X a) ≤
      2 * Real.exp (-l * a + 2 * (Real.exp 1 * M * l) ^ (2 : ℕ)) := by
  let B : ℝ := Real.exp (-l * a + 2 * (Real.exp 1 * M * l) ^ (2 : ℕ))
  have hsubset :
      absTailEvent X a ⊆ upperTailEvent X a ∪ upperTailEvent (fun ω => -X ω) a := by
    intro ω hω
    rw [Set.mem_union, mem_upperTailEvent, mem_upperTailEvent]
    exact lt_abs.mp (by simpa [absTailEvent, upperTailEvent] using hω)
  have hXmean_neg : ∫ ω, -X ω ∂μ = 0 := by
    calc
      ∫ ω, -X ω ∂μ = -∫ ω, X ω ∂μ := by simpa using integral_neg X
      _ = 0 := by rw [hXmean, neg_zero]
  have hXmom_neg : HasGammaMomentGrowthWith μ σ (fun ω => -X ω) M := by
    intro p hp
    simpa using hXmom (p := p) hp
  have hupper :
      μ.real (upperTailEvent X a) ≤ B := by
    simpa [B] using
      measureReal_upperTailEvent_le_exp_of_gammaMomentGrowth_small_of_integral_eq_zero
        (μ := μ) (X := X) (σ := σ) (M := M) (l := l) (a := a)
        hXm hσ hM hl hl_small hXmean hXmom
  have hupper_neg :
      μ.real (upperTailEvent (fun ω => -X ω) a) ≤ B := by
    simpa [B] using
      measureReal_upperTailEvent_le_exp_of_gammaMomentGrowth_small_of_integral_eq_zero
        (μ := μ) (X := fun ω => -X ω) (σ := σ) (M := M) (l := l) (a := a)
        hXm.neg hσ hM hl hl_small hXmean_neg hXmom_neg
  calc
    μ.real (absTailEvent X a)
      ≤ μ.real (upperTailEvent X a ∪ upperTailEvent (fun ω => -X ω) a) := by
          exact measureReal_mono hsubset
    _ ≤ μ.real (upperTailEvent X a) + μ.real (upperTailEvent (fun ω => -X ω) a) := by
          exact measureReal_union_le _ _
    _ ≤ B + B := by
          gcongr
    _ = 2 * Real.exp (-l * a + 2 * (Real.exp 1 * M * l) ^ (2 : ℕ)) := by
          simp [B, two_mul]


end

end IndependentSums

end Homogenization
