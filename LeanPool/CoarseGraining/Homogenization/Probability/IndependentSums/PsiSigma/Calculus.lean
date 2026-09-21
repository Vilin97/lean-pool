/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.PsiSigma.Endpoint

/-! # Calculus -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- Subgaussian upper tails at scale `σ` imply log-normal upper tails for
`exp(X) - 1`, with the explicit witness `exp(σ) - 1`. This is the forward
bridge from the Chapter 4 log-normal remark in the `t ≥ 1` weak-tail
convention used by the project. -/
theorem isBigOWith_psiSigma_exp_sub_one_of_isBigOWith_gammaTwo
    {X : Ω → ℝ} {σ : ℝ}
    (hσ : 1 ≤ σ)
    (hX : IsBigOWith μ (gammaSigma 2) X σ) :
    IsBigOWith μ (psiSigma σ) (fun ω => Real.exp (X ω) - 1) (Real.exp σ - 1) := by
  rw [isBigOWith_psiSigma_iff]
  rw [isBigOWith_gammaSigma_iff] at hX
  intro t ht
  have hσ_pos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  let A : ℝ := Real.exp σ - 1
  let u : ℝ := Real.log (1 + A * t) / σ
  have hA_ge_sigma : σ ≤ A := by
    dsimp [A]
    nlinarith [Real.add_one_le_exp σ]
  have hA_pos : 0 < A := lt_of_lt_of_le hσ_pos hA_ge_sigma
  have hu_eq : σ * u = Real.log (1 + A * t) := by
    dsimp [u]
    field_simp [hσ_pos.ne']
  have hu_one : 1 ≤ u := by
    refine (le_div_iff₀ hσ_pos).2 ?_
    have hA_mul : A ≤ A * t := by
      simpa using mul_le_mul_of_nonneg_left ht hA_pos.le
    have harg_ge : Real.exp σ ≤ 1 + A * t := by
      calc
        Real.exp σ = 1 + A := by
          dsimp [A]
          ring
        _ ≤ 1 + A * t := by
          linarith
    have hlog_ge : σ ≤ Real.log (1 + A * t) := by
      calc
        σ = Real.log (Real.exp σ) := by rw [Real.log_exp]
        _ ≤ Real.log (1 + A * t) := by
            exact Real.log_le_log (Real.exp_pos σ) harg_ge
    simpa [one_mul] using hlog_ge
  have harg_pos : 0 < 1 + A * t := by positivity
  have hset :
      upperTailEvent (fun ω => Real.exp (X ω) - 1) (A * t) =
        upperTailEvent X (σ * u) := by
    ext ω
    rw [hu_eq]
    constructor
    · intro hω
      change A * t < Real.exp (X ω) - 1 at hω
      change Real.log (1 + A * t) < X ω
      have hlt : 1 + A * t < Real.exp (X ω) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          add_lt_add_right hω 1
      exact (Real.log_lt_iff_lt_exp harg_pos).2 hlt
    · intro hω
      change Real.log (1 + A * t) < X ω at hω
      change A * t < Real.exp (X ω) - 1
      have hlt : 1 + A * t < Real.exp (X ω) := by
        exact (Real.log_lt_iff_lt_exp harg_pos).1 hω
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        sub_lt_sub_right hlt 1
  have harg_small_pos : 0 < 1 + σ * t := by positivity
  have harg_small_one : 1 ≤ 1 + σ * t := by
    have hσt_nonneg : 0 ≤ σ * t := mul_nonneg (le_trans zero_le_one hσ) (le_trans zero_le_one ht)
    linarith
  have harg_big_one : 1 ≤ 1 + A * t := by
    have hAt_nonneg : 0 ≤ A * t := mul_nonneg hA_pos.le (le_trans zero_le_one ht)
    linarith
  have harg_le : 1 + σ * t ≤ 1 + A * t := by
    have hmul : σ * t ≤ A * t := by
      exact mul_le_mul_of_nonneg_right hA_ge_sigma (le_trans zero_le_one ht)
    linarith
  have hlog_le : Real.log (1 + σ * t) ≤ Real.log (1 + A * t) := by
    exact Real.log_le_log harg_small_pos harg_le
  have hlog_small_nonneg : 0 ≤ Real.log (1 + σ * t) := Real.log_nonneg harg_small_one
  have hlog_big_nonneg : 0 ≤ Real.log (1 + A * t) := Real.log_nonneg harg_big_one
  have hlog_sq_le :
      (Real.log (1 + σ * t)) ^ (2 : ℕ) ≤ (Real.log (1 + A * t)) ^ (2 : ℕ) := by
    nlinarith
  have hu_sq :
      u ^ (2 : ℕ) = (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + A * t)) ^ (2 : ℕ) := by
    calc
      u ^ (2 : ℕ) = (Real.log (1 + A * t) / σ) ^ (2 : ℕ) := by rfl
      _ = (Real.log (1 + A * t)) ^ (2 : ℕ) / σ ^ (2 : ℕ) := by rw [div_pow]
      _ = (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + A * t)) ^ (2 : ℕ) := by
            rw [div_eq_mul_inv, mul_comm]
  have htarget_le :
      (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ) ≤ u ^ (2 : ℕ) := by
    rw [hu_sq]
    exact mul_le_mul_of_nonneg_left hlog_sq_le (inv_nonneg.mpr (sq_nonneg σ))
  have hX_u :
      μ.real (upperTailEvent X (σ * u)) ≤ Real.exp (-(u ^ (2 : ℕ))) := by
    simpa [Real.rpow_natCast] using hX hu_one
  have hbound :
      μ.real (upperTailEvent (fun ω => Real.exp (X ω) - 1) (A * t)) ≤
        Real.exp (-((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ))) := by
    calc
      μ.real (upperTailEvent (fun ω => Real.exp (X ω) - 1) (A * t))
        = μ.real (upperTailEvent X (σ * u)) := by rw [hset]
      _ ≤ Real.exp (-(u ^ (2 : ℕ))) := hX_u
      _ ≤ Real.exp (-((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ))) := by
          exact (Real.exp_le_exp).2 (neg_le_neg htarget_le)
  simpa [A] using hbound

/-- Log-normal upper tails for `exp(X) - 1` at scale `σ` imply the
subgaussian upper-tail relation for `X` at the same scale. This is the exact
reverse implication from the Chapter 4 log-normal remark. -/
theorem isBigOWith_gammaTwo_of_isBigOWith_psiSigma_exp_sub_one
    {X : Ω → ℝ} {σ : ℝ}
    (hσ : 1 ≤ σ)
    (hX : IsBigOWith μ (psiSigma σ) (fun ω => Real.exp (X ω) - 1) σ) :
    IsBigOWith μ (gammaSigma 2) X σ := by
  rw [isBigOWith_gammaSigma_iff]
  rw [isBigOWith_psiSigma_iff] at hX
  intro t ht
  have hσ_pos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  let u : ℝ := (Real.exp (σ * t) - 1) / σ
  have hu_eq : σ * u = Real.exp (σ * t) - 1 := by
    dsimp [u]
    field_simp [hσ_pos.ne']
  have hu_one : 1 ≤ u := by
    refine (le_div_iff₀ hσ_pos).2 ?_
    have hσ_le : σ ≤ σ * t := by
      nlinarith
    have hst_le : σ * t ≤ Real.exp (σ * t) - 1 := by
      nlinarith [Real.add_one_le_exp (σ * t)]
    simpa [one_mul] using hσ_le.trans hst_le
  have hset :
      upperTailEvent X (σ * t) =
        upperTailEvent (fun ω => Real.exp (X ω) - 1) (σ * u) := by
    ext ω
    rw [hu_eq]
    constructor
    · intro hω
      change σ * t < X ω at hω
      change Real.exp (σ * t) - 1 < Real.exp (X ω) - 1
      have hlt : Real.exp (σ * t) < Real.exp (X ω) := by
        exact (Real.exp_lt_exp).2 hω
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        sub_lt_sub_right hlt 1
    · intro hω
      change Real.exp (σ * t) - 1 < Real.exp (X ω) - 1 at hω
      change σ * t < X ω
      have hlt : Real.exp (σ * t) < Real.exp (X ω) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          add_lt_add_right hω 1
      exact (Real.exp_lt_exp).1 hlt
  have hlog_u : Real.log (1 + σ * u) = σ * t := by
    rw [hu_eq]
    have htmp : 1 + (Real.exp (σ * t) - 1) = Real.exp (σ * t) := by ring
    rw [htmp, Real.log_exp]
  have hexponent :
      (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * u)) ^ (2 : ℕ) = t ^ (2 : ℕ) := by
    rw [hlog_u]
    calc
      (σ ^ (2 : ℕ))⁻¹ * (σ * t) ^ (2 : ℕ)
          = (σ ^ (2 : ℕ))⁻¹ * (σ ^ (2 : ℕ) * t ^ (2 : ℕ)) := by
              rw [mul_pow]
      _ = t ^ (2 : ℕ) := by
            field_simp [pow_two, hσ_pos.ne']
  have hbound :
      μ.real (upperTailEvent X (σ * t)) ≤ Real.exp (-(t ^ (2 : ℕ))) := by
    calc
    μ.real (upperTailEvent X (σ * t))
      = μ.real (upperTailEvent (fun ω => Real.exp (X ω) - 1) (σ * u)) := by
          rw [hset]
    _ ≤ Real.exp (-((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * u)) ^ (2 : ℕ))) := hX hu_one
    _ = Real.exp (-(t ^ (2 : ℕ))) := by rw [hexponent]
  simpa [Real.rpow_natCast] using hbound

/-- Constant-scale finite-family log-normal triangle inequality. -/
theorem isBigO_finset_sum_of_isBigO_psiSigma_const
    (s : Finset ι) {X : ι → Ω → ℝ} {A σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 1 ≤ σ)
    (hs : s.Nonempty)
    (hA : 0 < A)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) A)
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ (psiSigma σ) (fun ω => Finset.sum s (fun i => X i ω))
      (psiSigmaTriangleConst σ * ((s.card : ℝ) * A)) := by
  simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    isBigO_finset_sum_of_isBigO_psiSigma
      (μ := μ) (s := s) (X := X) (a := fun _ => A) (σ := σ)
      hσ hs (fun _ _ => hA) hX hXm

/-- Constant-scale average log-normal triangle inequality. -/
theorem isBigO_finsetAverage_of_isBigO_psiSigma_const
    (s : Finset ι) {X : ι → Ω → ℝ} {A σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 1 ≤ σ)
    (hs : s.Nonempty)
    (hA : 0 < A)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) A)
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ (psiSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω))
      (psiSigmaTriangleConst σ * A) := by
  have hcard_ne : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast hs.card_ne_zero
  simpa [Finset.sum_const, nsmul_eq_mul, hcard_ne, mul_assoc, mul_left_comm, mul_comm] using
    isBigO_finsetAverage_of_isBigO_psiSigma
      (μ := μ) (s := s) (X := X) (a := fun _ => A) (σ := σ)
      hσ hs (fun _ _ => hA) hX hXm

/-- Unit-scale finite-family log-normal triangle inequality. -/
theorem isBigO_finset_sum_of_isBigO_psiSigma_unit
    (s : Finset ι) {X : ι → Ω → ℝ} {σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 1 ≤ σ)
    (hs : s.Nonempty)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) 1)
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ (psiSigma σ) (fun ω => Finset.sum s (fun i => X i ω))
      (psiSigmaTriangleConst σ * (s.card : ℝ)) := by
  simpa using
    isBigO_finset_sum_of_isBigO_psiSigma_const
      (μ := μ) (s := s) (X := X) (A := 1) (σ := σ)
      hσ hs zero_lt_one hX hXm

/-- Unit-scale average log-normal triangle inequality. -/
theorem isBigO_finsetAverage_of_isBigO_psiSigma_unit
    (s : Finset ι) {X : ι → Ω → ℝ} {σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 1 ≤ σ)
    (hs : s.Nonempty)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) 1)
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ (psiSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω))
      (psiSigmaTriangleConst σ) := by
  simpa using
    isBigO_finsetAverage_of_isBigO_psiSigma_const
      (μ := μ) (s := s) (X := X) (A := 1) (σ := σ)
      hσ hs zero_lt_one hX hXm


end

end IndependentSums

end Homogenization
