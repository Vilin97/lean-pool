/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module



public import Mathlib.Probability.Moments.Variance
public import LeanPool.CarlsonFunctions.Dirichlet.Real

public import LeanPool.CarlsonFunctions.Pochhammer.Gamma
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure.Basic
import all LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure.Basic

/-! # Moments, means, variances, and covariances of the real Dirichlet distribution -/

open Real MeasureTheory MeasureTheory.Measure
open scoped ENNReal

@[expose] public noncomputable section DirichletDistribution

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]


/-- The integral of a power product (generalized monomial) against the Dirichlet measure. -/
theorem integral_dirichletMeasure_power_product {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (m : ι → ℝ) (hm : b + m ∈ mvRealBetaDomain) :
    ∫ u, (∏ i, u i ^ m i) ∂(dirichletMeasure b) =
      (Gamma (∑ i, b i) / Gamma (∑ i, (b i + m i))) *
        ∏ i, (Gamma (b i + m i) / Gamma (b i)) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      let : IsEmpty ι := h
      simp [dirichletMeasure, stdSimplexMeasure_empty]
  | inr h =>
      let : Nonempty ι := h
      rw [integral_dirichletMeasure hb]
      have hae := ae_zero_lt_of_mem_stdSimplex (ι := ι)
      have hmem := self_mem_ae_restrict
        (μ := stdSimplexMeasure) (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
      have hint :
          (∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
            (∏ i, u i ^ m i) * dirichletPdfReal b u ∂stdSimplexMeasure) =
          (1 / mvRealBeta b) *
            ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, ∏ i, u i ^ ((b + m) i - 1)
              ∂stdSimplexMeasure := by
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hmem, hae] with u hu hpos
        have hui : u ∈ stdSimplexInterior := ⟨hu, hpos⟩
        rw [dirichletPdfReal, Set.indicator_of_mem hui]
        rw [show (∏ i, u i ^ m i) * ((1 / mvRealBeta b) * ∏ i, u i ^ (b i - 1)) =
          (1 / mvRealBeta b) * ((∏ i, u i ^ m i) * ∏ i, u i ^ (b i - 1)) by ring]
        rw [← Finset.prod_mul_distrib]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        calc
          u i ^ m i * u i ^ (b i - 1) = u i ^ (m i + (b i - 1)) :=
            (rpow_add (hpos i) (m i) (b i - 1)).symm
          _ = u i ^ ((b + m) i - 1) := by
            congr 1
            simp only [Pi.add_apply]
            ring
      rw [hint, ← mvRealBeta_eq_integral hm]
      unfold mvRealBeta
      simp only [Pi.add_apply]
      have hb_sum : Gamma (∑ i, b i) ≠ 0 :=
        ne_of_gt (Gamma_pos_of_pos (Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty))
      have hm_sum : Gamma (∑ i, (b i + m i)) ≠ 0 :=
        ne_of_gt (Gamma_pos_of_pos
          (Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty))
      have hb_each : ∀ i, Gamma (b i) ≠ 0 := fun i =>
        ne_of_gt (Gamma_pos_of_pos (hb i))
      rw [Finset.prod_div_distrib]
      field_simp

/-- The integral of a monomial against the Dirichlet measure. -/
/- The `[Nonempty ι]` hypothesis is essential. For an empty index type the left side is
zero, while the empty products and the degree-zero rising factorial make the right side one. -/
theorem integral_dirichletMeasure_monomial [Nonempty ι]
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain)
    (m : ι → ℕ) :
    ∫ u, (∏ i, u i ^ m i) ∂(dirichletMeasure b) =
      (∏ i, (ascPochhammer ℝ (m i)).eval (b i)) /
        (ascPochhammer ℝ (∑ i, m i)).eval (∑ i, b i) := by
  let mr : ι → ℝ := fun i => m i
  have hm : b + mr ∈ mvRealBetaDomain := by
    intro i
    exact add_pos_of_pos_of_nonneg (hb i) (Nat.cast_nonneg _)
  have hpow := integral_dirichletMeasure_power_product hb mr hm
  have hfun : (fun u : ι → ℝ => ∏ i, u i ^ mr i) = fun u => ∏ i, u i ^ m i := by
    funext u
    simp [mr, rpow_natCast]
  rw [hfun] at hpow
  rw [hpow]
  have hsum_pos : 0 < ∑ i, b i :=
    Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hsum : (∑ i, (b i + mr i)) = (∑ i, b i) + (∑ i, m i) := by
    simp [mr, Finset.sum_add_distrib]
  rw [hsum]
  have hnum : Gamma ((∑ i, b i) + (∑ i, m i)) / Gamma (∑ i, b i) =
      (ascPochhammer ℝ (∑ i, m i)).eval (∑ i, b i) :=
    gamma_add_nat_div_gamma_eq_ascPochhammer _ hsum_pos _
  have hprod : ∏ i, (Gamma (b i + mr i) / Gamma (b i)) =
      ∏ i, (ascPochhammer ℝ (m i)).eval (b i) := by
    apply Finset.prod_congr rfl
    intro i _
    simpa [mr] using gamma_add_nat_div_gamma_eq_ascPochhammer (b i) (hb i) (m i)
  rw [hprod]
  have hG : Gamma (∑ i, b i) ≠ 0 := ne_of_gt (Gamma_pos_of_pos hsum_pos)
  have hGN : Gamma ((∑ i, b i) + (∑ i, m i)) ≠ 0 := by
    apply ne_of_gt (Gamma_pos_of_pos ?_)
    have hm_nonneg : (0 : ℝ) ≤ ∑ i, m i := by positivity
    linarith
  have hP : (ascPochhammer ℝ (∑ i, m i)).eval (∑ i, b i) ≠ 0 := by
    rw [← hnum]
    exact div_ne_zero hGN hG
  have hratio : Gamma (∑ i, b i) / Gamma ((∑ i, b i) + (∑ i, m i)) =
      ((ascPochhammer ℝ (∑ i, m i)).eval (∑ i, b i))⁻¹ := by
    rw [← hnum]
    field_simp
  rw [hratio, div_eq_mul_inv, mul_comm]

open scoped Classical in
/-- The mean of a single `u i`; a specialization of monomial integration. -/
theorem integral_dirichletMeasure_coordinate
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (i : ι) :
    ∫ u, (u i) ∂(dirichletMeasure b) = (b i) / (∑ j, b j) := by
  let : Nonempty ι := ⟨i⟩
  let m : ι → ℝ := fun j => if j = i then 1 else 0
  have hm : b + m ∈ mvRealBetaDomain := by
    intro j
    dsimp [m]
    split_ifs
    · exact add_pos_of_pos_of_nonneg (hb j) zero_le_one
    · simpa using hb j
  have hpow := integral_dirichletMeasure_power_product hb m hm
  have hsum_pos : 0 < ∑ j, b j :=
    Finset.sum_pos (fun j _ => hb j) Finset.univ_nonempty
  have hgamma_sum : Gamma (∑ j, b j) ≠ 0 := ne_of_gt (Gamma_pos_of_pos hsum_pos)
  have hprod : (fun u : ι → ℝ => ∏ j, u j ^ m j) = fun u => u i := by
    funext u
    simp [m]
  rw [hprod] at hpow
  have hsum_m : ∑ j, (b j + m j) = (∑ j, b j) + 1 := by
    simp [m, Finset.sum_add_distrib]
  have hprod_m : ∏ j, (Gamma (b j + m j) / Gamma (b j)) = b i := by
    calc
      ∏ j, (Gamma (b j + m j) / Gamma (b j)) =
          ∏ j, if j = i then b i else 1 := by
            apply Finset.prod_congr rfl
            intro j _
            by_cases hji : j = i
            · subst j
              simp [m, Gamma_add_one, (hb i).ne',
                ne_of_gt (Gamma_pos_of_pos (hb i))]
            · simp [m, hji, ne_of_gt (Gamma_pos_of_pos (hb j))]
      _ = b i := by simp
  rw [hpow, hsum_m, hprod_m, Gamma_add_one hsum_pos.ne']
  field_simp

open scoped Classical in
/-- The second raw moment of one coordinate under a Dirichlet measure. -/
theorem integral_dirichletMeasure_coordinate_sq
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (i : ι) :
    ∫ u, (u i) ^ 2 ∂(dirichletMeasure b) =
      b i * (b i + 1) / ((∑ j, b j) * (∑ j, b j + 1)) := by
  let : Nonempty ι := ⟨i⟩
  let m : ι → ℕ := fun j => if j = i then 2 else 0
  have h := integral_dirichletMeasure_monomial hb m
  have hprod : (fun u : ι → ℝ => ∏ j, u j ^ m j) = fun u => u i ^ 2 := by
    funext u
    simp [m]
  rw [hprod] at h
  rw [h]
  have hnum : ∏ j, (ascPochhammer ℝ (m j)).eval (b j) = b i * (b i + 1) := by
    calc
      _ = ∏ j, if j = i then b i * (b i + 1) else 1 := by
        apply Finset.prod_congr rfl
        intro j _
        by_cases hji : j = i
        · subst j
          simp [m, ascPochhammer_succ_eval]
        · simp [m, hji]
      _ = _ := by simp
  have hsum : ∑ j, m j = 2 := by simp [m]
  rw [hnum, hsum]
  simp [ascPochhammer_succ_eval]

open scoped Classical in
/-- The mixed raw moment of two distinct coordinates under a Dirichlet measure. -/
theorem integral_dirichletMeasure_two_coordinates
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) {i j : ι} (hij : i ≠ j) :
    ∫ u, u i * u j ∂(dirichletMeasure b) =
      b i * b j / ((∑ k, b k) * (∑ k, b k + 1)) := by
  let : Nonempty ι := ⟨i⟩
  let m : ι → ℕ := fun k => if k = i then 1 else if k = j then 1 else 0
  have h := integral_dirichletMeasure_monomial hb m
  have hprod : (fun u : ι → ℝ => ∏ k, u k ^ m k) = fun u => u i * u j := by
    funext u
    simp only [m, pow_ite, pow_one, pow_zero]
    rw [show (∏ k, if k = i then u k else if k = j then u k else 1) =
        ∏ k, (if k = i then u i else 1) * (if k = j then u j else 1) by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp [hki, hkj, hij, hij.symm]]
    rw [Finset.prod_mul_distrib]
    simp
  rw [hprod] at h
  rw [h]
  have hnum : ∏ k, (ascPochhammer ℝ (m k)).eval (b k) = b i * b j := by
    calc
      _ = ∏ k, if k = i then b i else if k = j then b j else 1 := by
        apply Finset.prod_congr rfl
        intro k _
        by_cases hki : k = i
        · subst k
          simp [m]
        · by_cases hkj : k = j
          · subst k
            simp [m, hki]
          · simp [m, hki, hkj]
      _ = ∏ k, (if k = i then b i else 1) * (if k = j then b j else 1) := by
        apply Finset.prod_congr rfl
        intro k _
        by_cases hki : k = i <;> by_cases hkj : k = j <;>
          simp [hki, hkj, hij, hij.symm]
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hsum : ∑ k, m k = 2 := by
    simp only [m]
    rw [show (∑ k, if k = i then 1 else if k = j then 1 else 0) =
        (∑ k, if k = i then 1 else 0) + ∑ k, (if k = j then 1 else 0) by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp [hki, hkj, hij, hij.symm]]
    simp
  rw [hnum, hsum]
  simp [ascPochhammer_succ_eval]

/-- The variance of the coordinate `u i`. -/
theorem variance_dirichletMeasure_coordinate
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (i : ι) :
    ∫ u, (u i - b i / ∑ j, b j) ^ 2 ∂(dirichletMeasure b) =
      (b i) * (∑ j, b j - b i) / ((∑ j, b j) ^ 2 * (∑ j, b j + 1)) := by
  let : Nonempty ι := ⟨i⟩
  let : IsProbabilityMeasure (dirichletMeasure b) := isProbabilityMeasure_dirichletMeasure hb
  have hmean := integral_dirichletMeasure_coordinate hb i
  have hsquare := integral_dirichletMeasure_coordinate_sq hb i
  calc
    _ = variance (fun u : ι → ℝ => u i) (dirichletMeasure b) := by
      rw [variance_eq_integral (measurable_pi_apply i).aemeasurable, hmean]
    _ = (∫ u, u i ^ 2 ∂dirichletMeasure b) -
        (∫ u, u i ∂dirichletMeasure b) ^ 2 :=
      variance_eq_sub (memLp_dirichletMeasure_coordinate hb i 2)
    _ = _ := by
      rw [hsquare, hmean]
      have hS : 0 < ∑ k, b k :=
        Finset.sum_pos (fun k _ => hb k) Finset.univ_nonempty
      field_simp
      ring

/-- The covariance of distinct coordinates `u i` and `u j`. -/
theorem covariance_dirichletMeasure_coordinate
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) {i j : ι} (hij : i ≠ j) :
    ∫ u, (u i - b i / ∑ k, b k) * (u j - b j / ∑ k, b k)
      ∂(dirichletMeasure b) =
      -(b i) * (b j) / ((∑ k, b k) ^ 2 * (∑ k, b k + 1)) := by
  let : Nonempty ι := ⟨i⟩
  let : IsProbabilityMeasure (dirichletMeasure b) := isProbabilityMeasure_dirichletMeasure hb
  have hmeani := integral_dirichletMeasure_coordinate hb i
  have hmeanj := integral_dirichletMeasure_coordinate hb j
  have hcross := integral_dirichletMeasure_two_coordinates hb hij
  calc
    _ = covariance (fun u : ι → ℝ => u i) (fun u => u j) (dirichletMeasure b) := by
      simp only [covariance, hmeani, hmeanj]
    _ = (∫ u, u i * u j ∂dirichletMeasure b) -
        (∫ u, u i ∂dirichletMeasure b) * (∫ u, u j ∂dirichletMeasure b) :=
      covariance_eq_sub (memLp_dirichletMeasure_coordinate hb i 2)
        (memLp_dirichletMeasure_coordinate hb j 2)
    _ = _ := by
      rw [hcross, hmeani, hmeanj]
      have hS : 0 < ∑ k, b k :=
        Finset.sum_pos (fun k _ => hb k) Finset.univ_nonempty
      field_simp
      ring

end ProbabilityTheory

end DirichletDistribution
