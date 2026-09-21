/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.GammaSigmaExpRegime.OneVariable

/-! # Finite Sums -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- Finite independent sums inherit exponential mgf bounds when each summand
has one. -/
theorem mgf_finset_sum_le_exp_of_iIndepFun
    {ι : Type*} {X : ι → Ω → ℝ} {v : ι → ℝ} {s : Finset ι} {l : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hmgf : ∀ i ∈ s, mgf (X i) μ l ≤ Real.exp (v i)) :
    mgf (fun ω => ∑ i ∈ s, X i ω) μ l ≤ Real.exp (∑ i ∈ s, v i) := by
  calc
    mgf (fun ω => ∑ i ∈ s, X i ω) μ l = ∏ i ∈ s, mgf (X i) μ l := by
      have hsumfun : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
        funext ω
        simp [Finset.sum_apply]
      rw [hsumfun]
      exact h_indep.mgf_sum (t := l) h_meas s
    _ ≤ ∏ i ∈ s, Real.exp (v i) := by
      refine Finset.prod_le_prod ?_ hmgf
      intro i hi
      exact mgf_nonneg
    _ = Real.exp (∑ i ∈ s, v i) := by
      rw [← Real.exp_sum]

/-- Finite independent sums inherit the large-`λ` exponential mgf bound in the
note-facing `O_{Γ_σ}` language when `σ > 1`. -/
theorem mgf_finset_sum_le_exp_card_mul_of_iIndepFun_of_isBigO_gammaSigma_of_one_lt
    [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} {σ K l : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hσ : 1 < σ) (hK : 0 < K) (hl : 0 ≤ l)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K) :
    mgf (fun ω => ∑ i ∈ s, X i ω) μ l ≤
      Real.exp ((s.card : ℝ) *
        (Real.log 2 +
          gammaSigmaLargeMgfConst σ * (K * l) ^ gammaExpConjExponent σ)) := by
  let v : ι → ℝ := fun _ =>
    Real.log 2 + gammaSigmaLargeMgfConst σ * (K * l) ^ gammaExpConjExponent σ
  have hmain :=
    mgf_finset_sum_le_exp_of_iIndepFun (μ := μ) (X := X) (v := v) (s := s) (l := l)
      h_indep h_meas ?_
  · have hsum : ∑ i ∈ s, v i =
        (s.card : ℝ) *
          (Real.log 2 +
            gammaSigmaLargeMgfConst σ * (K * l) ^ gammaExpConjExponent σ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    calc
      mgf (fun ω => ∑ i ∈ s, X i ω) μ l ≤ Real.exp (∑ i ∈ s, v i) := hmain
      _ = Real.exp ((s.card : ℝ) *
            (Real.log 2 +
              gammaSigmaLargeMgfConst σ * (K * l) ^ gammaExpConjExponent σ)) := by
            rw [hsum]
  · intro i hi
    have hlarge :=
      mgf_le_two_mul_exp_of_isBigO_gammaSigma_of_one_lt
        (μ := μ) (X := X i) (σ := σ) (K := K) (l := l)
        (h_meas i).aemeasurable hσ hK hl (hX i hi)
    calc
      mgf (X i) μ l ≤
          2 * Real.exp
            (gammaSigmaLargeMgfConst σ * (K * l) ^ gammaExpConjExponent σ) := hlarge
      _ = Real.exp
            (Real.log 2 +
              gammaSigmaLargeMgfConst σ * (K * l) ^ gammaExpConjExponent σ) := by
            calc
              2 * Real.exp
                  (gammaSigmaLargeMgfConst σ * (K * l) ^ gammaExpConjExponent σ)
                = Real.exp (Real.log 2) *
                    Real.exp
                      (gammaSigmaLargeMgfConst σ * (K * l) ^ gammaExpConjExponent σ) := by
                        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
              _ = Real.exp
                    (Real.log 2 +
                      gammaSigmaLargeMgfConst σ * (K * l) ^ gammaExpConjExponent σ) := by
                        rw [Real.exp_add]

/-- Large-`λ` Chernoff bound for finite sums of independent
`O_{Γ_σ}` variables when `σ > 1`. -/
theorem measureReal_upperTailEvent_finset_sum_le_exp_card_mul_of_iIndepFun_of_isBigO_gammaSigma_of_one_lt
    [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} {σ K l a : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hσ : 1 < σ) (hK : 0 < K) (hl : 0 ≤ l)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a) ≤
      Real.exp
        (-l * a + (s.card : ℝ) *
          (Real.log 2 +
            gammaSigmaLargeMgfConst σ * (K * l) ^ gammaExpConjExponent σ)) := by
  have hsumfun : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
    funext ω
    simp [Finset.sum_apply]
  have h_int : ∀ i ∈ s, Integrable (fun ω => Real.exp (l * X i ω)) μ := by
    intro i hi
    exact integrable_exp_mul_of_isBigO_gammaSigma_of_one_lt
      (μ := μ) (X := X i) (σ := σ) (K := K) (l := l)
      (h_meas i).aemeasurable hσ hK hl (hX i hi)
  have hsum_int : Integrable (fun ω => Real.exp (l * (∑ i ∈ s, X i ω))) μ := by
    simpa [hsumfun] using h_indep.integrable_exp_mul_sum (t := l) h_meas h_int
  have hsubset : upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a ⊆ {ω | a ≤ ∑ i ∈ s, X i ω} := by
    intro ω hω
    simpa [upperTailEvent] using le_of_lt hω
  refine (measureReal_mono (s₂ := {ω | a ≤ ∑ i ∈ s, X i ω}) hsubset).trans ?_
  calc
    μ.real {ω | a ≤ ∑ i ∈ s, X i ω}
      ≤ Real.exp (-l * a) * mgf (fun ω => ∑ i ∈ s, X i ω) μ l := by
          exact measure_ge_le_exp_mul_mgf
            (μ := μ) (X := fun ω => ∑ i ∈ s, X i ω) (ε := a) (t := l) hl hsum_int
    _ ≤ Real.exp (-l * a) *
          Real.exp ((s.card : ℝ) *
            (Real.log 2 +
              gammaSigmaLargeMgfConst σ * (K * l) ^ gammaExpConjExponent σ)) := by
            gcongr
            exact mgf_finset_sum_le_exp_card_mul_of_iIndepFun_of_isBigO_gammaSigma_of_one_lt
              (μ := μ) (X := X) (s := s) (σ := σ) (K := K) (l := l)
              h_indep h_meas hσ hK hl hX
    _ = Real.exp
          (-l * a + (s.card : ℝ) *
            (Real.log 2 +
              gammaSigmaLargeMgfConst σ * (K * l) ^ gammaExpConjExponent σ)) := by
            rw [← Real.exp_add]

/-- Small-`λ` exponential mgf bound for finite independent sums of centered
`Γ_σ` variables. -/
theorem mgf_finset_sum_le_exp_of_iIndepFun_of_gammaMomentGrowth_small_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {M : ι → ℝ} {s : Finset ι} {σ l : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hσ : 1 ≤ σ) (hl : 0 ≤ l)
    (hM : ∀ i ∈ s, 0 ≤ M i)
    (hl_small : ∀ i ∈ s, l ≤ (2 * Real.exp 1 * M i)⁻¹)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hXmom : ∀ i ∈ s, HasGammaMomentGrowthWith μ σ (X i) (M i)) :
    mgf (fun ω => ∑ i ∈ s, X i ω) μ l ≤
      Real.exp (∑ i ∈ s, 2 * (Real.exp 1 * M i * l) ^ (2 : ℕ)) := by
  refine mgf_finset_sum_le_exp_of_iIndepFun (μ := μ) (X := X) (v := fun i => 2 * (Real.exp 1 * M i * l) ^ (2 : ℕ))
    h_indep h_meas ?_
  intro i hi
  exact mgf_le_exp_two_mul_sq_of_gammaMomentGrowth_small_of_integral_eq_zero
    (μ := μ) (X := X i) (σ := σ) (M := M i) (l := l)
    (h_meas i).aemeasurable hσ (hM i hi) hl (hl_small i hi) (hXmean i hi) (hXmom i hi)

/-- Chernoff upper-tail estimate for finite independent sums of centered
`Γ_σ` variables in the small-`λ` regime. -/
theorem measureReal_upperTailEvent_finset_sum_le_exp_of_iIndepFun_of_gammaMomentGrowth_small_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {M : ι → ℝ} {s : Finset ι} {σ l a : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hσ : 1 ≤ σ) (hl : 0 ≤ l)
    (hM : ∀ i ∈ s, 0 ≤ M i)
    (hl_small : ∀ i ∈ s, l ≤ (2 * Real.exp 1 * M i)⁻¹)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hXmom : ∀ i ∈ s, HasGammaMomentGrowthWith μ σ (X i) (M i)) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a) ≤
      Real.exp (-l * a + ∑ i ∈ s, 2 * (Real.exp 1 * M i * l) ^ (2 : ℕ)) := by
  have hsumfun : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
    funext ω
    simp [Finset.sum_apply]
  have h_int :
      ∀ i ∈ s, Integrable (fun ω => Real.exp (l * X i ω)) μ := by
    intro i hi
    exact integrable_exp_mul_of_gammaMomentGrowth_small
      (μ := μ) (X := X i) (σ := σ) (M := M i) (l := l)
      (h_meas i).aemeasurable hσ (hM i hi) hl (hl_small i hi) (hXmom i hi)
  have hsum_int : Integrable (fun ω => Real.exp (l * (∑ i ∈ s, X i ω))) μ := by
    simpa [hsumfun] using h_indep.integrable_exp_mul_sum (t := l) h_meas h_int
  have hsubset : upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a ⊆ {ω | a ≤ ∑ i ∈ s, X i ω} := by
    intro ω hω
    simpa [upperTailEvent] using le_of_lt hω
  refine (measureReal_mono (s₂ := {ω | a ≤ ∑ i ∈ s, X i ω}) hsubset).trans ?_
  calc
    μ.real {ω | a ≤ ∑ i ∈ s, X i ω}
      ≤ Real.exp (-l * a) * mgf (fun ω => ∑ i ∈ s, X i ω) μ l := by
          exact measure_ge_le_exp_mul_mgf
            (μ := μ) (X := fun ω => ∑ i ∈ s, X i ω) (ε := a) (t := l) hl hsum_int
    _ ≤ Real.exp (-l * a) * Real.exp (∑ i ∈ s, 2 * (Real.exp 1 * M i * l) ^ (2 : ℕ)) := by
          gcongr
          exact mgf_finset_sum_le_exp_of_iIndepFun_of_gammaMomentGrowth_small_of_integral_eq_zero
            (μ := μ) (X := X) (M := M) (s := s) (σ := σ) (l := l)
            h_indep h_meas hσ hl hM hl_small hXmean hXmom
    _ = Real.exp (-l * a + ∑ i ∈ s, 2 * (Real.exp 1 * M i * l) ^ (2 : ℕ)) := by
          rw [← Real.exp_add]

/-- Uniform-witness version of the finite-sum small-`λ` exponential mgf
estimate. -/
theorem mgf_finset_sum_le_exp_card_mul_of_iIndepFun_of_gammaMomentGrowth_small_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} {σ M l : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hXmom : ∀ i ∈ s, HasGammaMomentGrowthWith μ σ (X i) M) :
    mgf (fun ω => ∑ i ∈ s, X i ω) μ l ≤
      Real.exp (2 * (s.card : ℝ) * (Real.exp 1 * M * l) ^ (2 : ℕ)) := by
  have hmain :=
    mgf_finset_sum_le_exp_of_iIndepFun_of_gammaMomentGrowth_small_of_integral_eq_zero
      (μ := μ) (X := X) (M := fun _ : ι => M) (s := s) (σ := σ) (l := l)
      h_indep h_meas hσ hl
      (fun _ _ => hM)
      (fun _ _ => hl_small)
      hXmean
      hXmom
  have hsum :
      (∑ i ∈ s, 2 * (Real.exp 1 * M * l) ^ (2 : ℕ)) =
        2 * (s.card : ℝ) * (Real.exp 1 * M * l) ^ (2 : ℕ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  calc
    mgf (fun ω => ∑ i ∈ s, X i ω) μ l
      ≤ Real.exp (∑ i ∈ s, 2 * (Real.exp 1 * M * l) ^ (2 : ℕ)) := hmain
    _ = Real.exp (2 * (s.card : ℝ) * (Real.exp 1 * M * l) ^ (2 : ℕ)) := by
          rw [hsum]

/-- Uniform-witness version of the finite-sum small-`λ` Chernoff estimate. -/
theorem measureReal_upperTailEvent_finset_sum_le_exp_card_mul_of_iIndepFun_of_gammaMomentGrowth_small_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} {σ M l a : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hσ : 1 ≤ σ) (hM : 0 ≤ M) (hl : 0 ≤ l)
    (hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hXmom : ∀ i ∈ s, HasGammaMomentGrowthWith μ σ (X i) M) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a) ≤
      Real.exp (-l * a + 2 * (s.card : ℝ) * (Real.exp 1 * M * l) ^ (2 : ℕ)) := by
  have hmain :=
    measureReal_upperTailEvent_finset_sum_le_exp_of_iIndepFun_of_gammaMomentGrowth_small_of_integral_eq_zero
      (μ := μ) (X := X) (M := fun _ : ι => M) (s := s) (σ := σ) (l := l) (a := a)
      h_indep h_meas hσ hl
      (fun _ _ => hM)
      (fun _ _ => hl_small)
      hXmean
      hXmom
  have hsum :
      -l * a + (∑ i ∈ s, 2 * (Real.exp 1 * M * l) ^ (2 : ℕ)) =
        -l * a + 2 * (s.card : ℝ) * (Real.exp 1 * M * l) ^ (2 : ℕ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  calc
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a)
      ≤ Real.exp (-l * a + ∑ i ∈ s, 2 * (Real.exp 1 * M * l) ^ (2 : ℕ)) := hmain
    _ = Real.exp (-l * a + 2 * (s.card : ℝ) * (Real.exp 1 * M * l) ^ (2 : ℕ)) := by
          rw [hsum]

/-- Explicit witness for the direct exponential-regime concentration theorem in
the range `1 < σ ≤ 2`. -/
noncomputable def gammaSigmaExpRegimeConst (σ : ℝ) : ℝ :=
  max (8 * Real.exp 1 * gammaMomentConst σ) (2 + gammaSigmaLargeMgfConst σ)

lemma gammaExpLargeLambdaConst_pos {σ : ℝ} (hσ : 1 < σ) :
    0 < gammaExpLargeLambdaConst σ := by
  dsimp [gammaExpLargeLambdaConst]
  have hden : 0 < 4 * Real.exp 1 * gammaMomentConst 1 := by
    have hfour_exp : 0 < 4 * Real.exp 1 := by positivity
    exact mul_pos hfour_exp (gammaMomentConst_pos zero_lt_one)
  exact gammaExpYoungScaleConst_pos hσ (inv_pos.mpr hden)

lemma gammaSigmaLargeMgfConst_pos {σ : ℝ} (hσ : 1 < σ) :
    0 < gammaSigmaLargeMgfConst σ := by
  have hσ_pos : 0 < σ := by linarith
  dsimp [gammaSigmaLargeMgfConst]
  exact mul_pos
    (gammaExpLargeLambdaConst_pos hσ)
    (Real.rpow_pos_of_pos
      (mul_pos (Real.exp_pos 1) (gammaMomentConst_pos hσ_pos)) _)

/-- One-sided direct concentration in the exponential regime `1 < σ ≤ 2`. -/
theorem isBigOWith_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_one_lt
    [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigOWith μ (gammaSigma σ) (fun ω => ∑ i ∈ s, X i ω)
      (gammaSigmaExpRegimeConst σ * Real.sqrt (s.card : ℝ) * K) := by
  let R : ℝ := s.card
  let A : ℝ := gammaSigmaExpRegimeConst σ
  let M : ℝ := gammaMomentConst σ * K
  let B : ℝ := Real.exp 1 * M
  let C : ℝ := gammaSigmaLargeMgfConst σ
  have hσ_pos : 0 < σ := by linarith
  have hσ_sub_nonneg : 0 ≤ σ - 1 := by linarith
  have htwo_sub_nonneg : 0 ≤ 2 - σ := by linarith
  have hR_pos : 0 < R := by
    dsimp [R]
    exact_mod_cast hs.card_pos
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have hsqrtR_pos : 0 < Real.sqrt R := Real.sqrt_pos.2 hR_pos
  have hsqrtR_nonneg : 0 ≤ Real.sqrt R := hsqrtR_pos.le
  have hsqrtR_sq : (Real.sqrt R) ^ (2 : ℕ) = R := by
    simpa [pow_two] using Real.sq_sqrt hR_nonneg
  have hsqrtR_one_le : 1 ≤ Real.sqrt R := by
    have hcard_one : (1 : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hs.card_pos)
    refine (Real.one_le_sqrt).2 ?_
    simpa [R] using hcard_one
  have hM_pos : 0 < M := by
    dsimp [M]
    exact mul_pos (gammaMomentConst_pos hσ_pos) hK
  have hB_pos : 0 < B := by
    dsimp [B]
    exact mul_pos (Real.exp_pos 1) hM_pos
  have hC_pos : 0 < C := gammaSigmaLargeMgfConst_pos hσ
  have hXmom : ∀ i ∈ s, HasGammaMomentGrowthWith μ σ (X i) M := by
    intro i hi
    simpa [M, mul_assoc, mul_left_comm, mul_comm] using
      (hasGammaMomentGrowthWith_of_isBigO_gammaSigma
        (μ := μ) (X := X i) (K := K) (σ := σ)
        hσ_pos hK (h_meas i).aemeasurable (hX i hi))
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht
  by_cases hsmall : t ≤ 2 * Real.sqrt R
  · let l : ℝ := t / (4 * B * Real.sqrt R)
    have hl_nonneg : 0 ≤ l := by
      dsimp [l]
      positivity
    have hl_small : l ≤ (2 * Real.exp 1 * M)⁻¹ := by
      calc
        l = t / (4 * B * Real.sqrt R) := rfl
        _ ≤ (2 * Real.sqrt R) / (4 * B * Real.sqrt R) := by
              gcongr
        _ = (2 * Real.exp 1 * M)⁻¹ := by
              dsimp [B]
              field_simp [hM_pos.ne', hsqrtR_pos.ne']
              norm_num
    have htail :=
      measureReal_upperTailEvent_finset_sum_le_exp_card_mul_of_iIndepFun_of_gammaMomentGrowth_small_of_integral_eq_zero
        (μ := μ) (X := X) (s := s) (σ := σ) (M := M) (l := l)
        (a := A * Real.sqrt R * K * t)
        h_indep h_meas hσ.le hM_pos.le hl_nonneg hl_small hXmean hXmom
    refine htail.trans ?_
    apply (Real.exp_le_exp).2
    have hA_small : 8 * Real.exp 1 * gammaMomentConst σ ≤ A := by
      dsimp [A, gammaSigmaExpRegimeConst]
      exact le_max_left _ _
    have hA_ratio : 2 ≤ A / (4 * Real.exp 1 * gammaMomentConst σ) := by
      have hden_pos : 0 < 4 * Real.exp 1 * gammaMomentConst σ := by
        have hfour_exp : 0 < 4 * Real.exp 1 := by positivity
        exact mul_pos hfour_exp (gammaMomentConst_pos hσ_pos)
      refine (le_div_iff₀ hden_pos).2 ?_
      have hA_small' : 2 * (4 * Real.exp 1 * gammaMomentConst σ) ≤ A := by
        calc
          2 * (4 * Real.exp 1 * gammaMomentConst σ)
              = 8 * Real.exp 1 * gammaMomentConst σ := by ring
          _ ≤ A := hA_small
      exact hA_small'
    have hpow_sigma_le_two : t ^ σ ≤ t ^ (2 : ℕ) := by
      have htmp : t ^ σ ≤ t ^ (2 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le ht hσ₂
      simpa [Real.rpow_natCast] using htmp
    calc
      -l * (A * Real.sqrt R * K * t) +
          2 * R * (Real.exp 1 * M * l) ^ (2 : ℕ)
        = -(A / (4 * Real.exp 1 * gammaMomentConst σ)) * t ^ (2 : ℕ) +
            t ^ (2 : ℕ) / 8 := by
              dsimp [l, A, B, M, R]
              field_simp [hK.ne', (gammaMomentConst_pos hσ_pos).ne',
                hsqrtR_pos.ne', Real.exp_ne_zero, pow_two]
              rw [hsqrtR_sq]
              ring
      _ ≤ -(2 : ℝ) * t ^ (2 : ℕ) + t ^ (2 : ℕ) / 8 := by
            have ht_sq_nonneg : 0 ≤ t ^ (2 : ℕ) := by positivity
            have hmul :
                (2 : ℝ) * t ^ (2 : ℕ) ≤
                  (A / (4 * Real.exp 1 * gammaMomentConst σ)) * t ^ (2 : ℕ) :=
              mul_le_mul_of_nonneg_right hA_ratio ht_sq_nonneg
            have hneg :
                -(A / (4 * Real.exp 1 * gammaMomentConst σ)) * t ^ (2 : ℕ) ≤
                  -(2 : ℝ) * t ^ (2 : ℕ) := by
              calc
                -(A / (4 * Real.exp 1 * gammaMomentConst σ)) * t ^ (2 : ℕ)
                    = -((A / (4 * Real.exp 1 * gammaMomentConst σ)) *
                        t ^ (2 : ℕ)) := by ring
                _ ≤ -((2 : ℝ) * t ^ (2 : ℕ)) := neg_le_neg hmul
                _ = -(2 : ℝ) * t ^ (2 : ℕ) := by ring
            calc
              -(A / (4 * Real.exp 1 * gammaMomentConst σ)) * t ^ (2 : ℕ) +
                  t ^ (2 : ℕ) / 8
                  = t ^ (2 : ℕ) / 8 +
                    -(A / (4 * Real.exp 1 * gammaMomentConst σ)) * t ^ (2 : ℕ) := by
                    ring
              _ ≤ t ^ (2 : ℕ) / 8 + -(2 : ℝ) * t ^ (2 : ℕ) :=
                    add_le_add_right hneg (t ^ (2 : ℕ) / 8)
              _ = -(2 : ℝ) * t ^ (2 : ℕ) + t ^ (2 : ℕ) / 8 := by ring
      _ ≤ -(t ^ (2 : ℕ)) := by
            have ht_sq_nonneg : 0 ≤ t ^ (2 : ℕ) := by positivity
            calc
              -(2 : ℝ) * t ^ (2 : ℕ) + t ^ (2 : ℕ) / 8
                  = -(t ^ (2 : ℕ)) - ((7 : ℝ) / 8) * t ^ (2 : ℕ) := by ring
              _ ≤ -(t ^ (2 : ℕ)) :=
                  sub_le_self _ (mul_nonneg (by norm_num) ht_sq_nonneg)
      _ ≤ -(t ^ σ) := by
            exact neg_le_neg hpow_sigma_le_two
  · let l : ℝ := (t / Real.sqrt R) ^ (σ - 1) / K
    let S : ℝ := R * (t / Real.sqrt R) ^ σ
    have hl_nonneg : 0 ≤ l := by
      dsimp [l]
      positivity
    have htail :=
      measureReal_upperTailEvent_finset_sum_le_exp_card_mul_of_iIndepFun_of_isBigO_gammaSigma_of_one_lt
        (μ := μ) (X := X) (s := s) (σ := σ) (K := K) (l := l)
        (a := A * Real.sqrt R * K * t)
        h_indep h_meas hσ hK hl_nonneg hX
    refine htail.trans ?_
    apply (Real.exp_le_exp).2
    have hbase_nonneg : 0 ≤ t / Real.sqrt R := by positivity
    have hbase_gt_two : 2 < t / Real.sqrt R := by
      exact (lt_div_iff₀ hsqrtR_pos).2 (lt_of_not_ge hsmall)
    have hbase_one : 1 ≤ t / Real.sqrt R := by
      linarith
    have hA_large : 2 + C ≤ A := by
      dsimp [A, C, gammaSigmaExpRegimeConst]
      exact le_max_right _ _
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      positivity
    have hS_ge_log : R * Real.log 2 ≤ S := by
      have hlog_le_one : Real.log 2 ≤ 1 := by
        refine (Real.log_le_iff_le_exp (by norm_num : 0 < (2 : ℝ))).2 ?_
        have htwo_exp_one : (2 : ℝ) < Real.exp 1 := by
          exact lt_trans (by norm_num) Real.exp_one_gt_d9
        simpa using htwo_exp_one.le
      have hone_le : 1 ≤ (t / Real.sqrt R) ^ σ := by
        exact Real.one_le_rpow hbase_one hσ_pos.le
      have hlog_le : Real.log 2 ≤ (t / Real.sqrt R) ^ σ := by
        exact le_trans hlog_le_one hone_le
      have hmul := mul_le_mul_of_nonneg_left hlog_le hR_nonneg
      simpa [S] using hmul
    have hS_ge_tpow : t ^ σ ≤ S := by
      have hsqrt_pow_le : (Real.sqrt R) ^ σ ≤ R := by
        calc
          (Real.sqrt R) ^ σ ≤ (Real.sqrt R) ^ (2 : ℝ) := by
                exact Real.rpow_le_rpow_of_exponent_le hsqrtR_one_le hσ₂
          _ = R := by
                simpa [Real.rpow_natCast] using hsqrtR_sq
      calc
        t ^ σ = (Real.sqrt R * (t / Real.sqrt R)) ^ σ := by
                  congr 1
                  field_simp [hsqrtR_pos.ne']
        _ = (Real.sqrt R) ^ σ * (t / Real.sqrt R) ^ σ := by
                  rw [Real.mul_rpow hsqrtR_nonneg hbase_nonneg]
        _ ≤ R * (t / Real.sqrt R) ^ σ := by
                  gcongr
        _ = S := by
                  rfl
    have hpow_q :
        (K * l) ^ gammaExpConjExponent σ = (t / Real.sqrt R) ^ σ := by
      calc
        (K * l) ^ gammaExpConjExponent σ
          = ((t / Real.sqrt R) ^ (σ - 1)) ^ gammaExpConjExponent σ := by
                dsimp [l]
                congr 1
                field_simp [hK.ne']
        _ = (t / Real.sqrt R) ^ ((σ - 1) * gammaExpConjExponent σ) := by
                rw [← Real.rpow_mul hbase_nonneg]
        _ = (t / Real.sqrt R) ^ σ := by
                dsimp [gammaExpConjExponent]
                congr 2
                field_simp [sub_ne_zero.mpr hσ.ne']
    have hla : l * (A * Real.sqrt R * K * t) = A * S := by
      calc
        l * (A * Real.sqrt R * K * t)
          = A * (((t / Real.sqrt R) ^ (σ - 1)) * (Real.sqrt R * t)) := by
                dsimp [l]
                field_simp [hK.ne']
        _ = A * (R * (t / Real.sqrt R) ^ σ) := by
                congr 1
                calc
                  (t / Real.sqrt R) ^ (σ - 1) * (Real.sqrt R * t)
                    = (t / Real.sqrt R) ^ (σ - 1) * (R * (t / Real.sqrt R)) := by
                          have hRt : R * (t / Real.sqrt R) = Real.sqrt R * t := by
                            field_simp [hsqrtR_pos.ne']
                            rw [hsqrtR_sq]
                          rw [hRt]
                  _ = R * ((t / Real.sqrt R) ^ (σ - 1) * (t / Real.sqrt R)) := by ring
                  _ = R * (t / Real.sqrt R) ^ σ := by
                        have hpow_base :
                            (t / Real.sqrt R) ^ (σ - 1) * (t / Real.sqrt R) =
                              (t / Real.sqrt R) ^ σ := by
                          calc
                            (t / Real.sqrt R) ^ (σ - 1) * (t / Real.sqrt R)
                              = (t / Real.sqrt R) ^ (σ - 1) * (t / Real.sqrt R) ^ (1 : ℝ) := by
                                    rw [Real.rpow_one]
                            _ = (t / Real.sqrt R) ^ σ := by
                                    rw [← Real.rpow_add' hbase_nonneg]
                                    · ring_nf
                                    · linarith
                        rw [hpow_base]
        _ = A * S := by
                rfl
    calc
      -l * (A * Real.sqrt R * K * t) +
          R * (Real.log 2 + C * (K * l) ^ gammaExpConjExponent σ)
        = -(l * (A * Real.sqrt R * K * t)) +
            R * (Real.log 2 + C * (K * l) ^ gammaExpConjExponent σ) := by
              ring
      _ = -(A * S) +
            R * (Real.log 2 + C * (K * l) ^ gammaExpConjExponent σ) := by
              rw [hla]
      _ = -(A - C) * S + R * Real.log 2 := by
              rw [hpow_q]
              dsimp [S]
              ring
      _ ≤ -(2 : ℝ) * S + R * Real.log 2 := by
            have htwo_le : (2 : ℝ) ≤ A - C := by
              rwa [le_sub_iff_add_le]
            have hmul : (2 : ℝ) * S ≤ (A - C) * S :=
              mul_le_mul_of_nonneg_right htwo_le hS_nonneg
            have hneg : -(A - C) * S ≤ -(2 : ℝ) * S := by
              calc
                -(A - C) * S = -((A - C) * S) := by ring
                _ ≤ -((2 : ℝ) * S) := neg_le_neg hmul
                _ = -(2 : ℝ) * S := by ring
            calc
              -(A - C) * S + R * Real.log 2 = R * Real.log 2 + -(A - C) * S := by
                ring
              _ ≤ R * Real.log 2 + -(2 : ℝ) * S :=
                add_le_add_right hneg (R * Real.log 2)
              _ = -(2 : ℝ) * S + R * Real.log 2 := by ring
      _ ≤ -S := by
            calc
              -(2 : ℝ) * S + R * Real.log 2 ≤ S + -(2 : ℝ) * S := by
                rw [add_comm (-(2 : ℝ) * S)]
                exact add_le_add_left hS_ge_log (-(2 : ℝ) * S)
              _ = -S := by ring
      _ ≤ -(t ^ σ) := by
            exact neg_le_neg hS_ge_tpow

/-- Symmetric direct concentration in the exponential regime `1 < σ ≤ 2`. -/
theorem isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_one_lt
    [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigO μ (gammaSigma σ) (fun ω => ∑ i ∈ s, X i ω)
      (2 * gammaSigmaExpRegimeConst σ * Real.sqrt (s.card : ℝ) * K) := by
  let A : ℝ := gammaSigmaExpRegimeConst σ * Real.sqrt (s.card : ℝ) * K
  rw [isBigO_gammaSigma_iff]
  intro t ht
  have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht
  have htwo_t : 1 ≤ 2 * t := by
    have ht_le_two_t : t ≤ 2 * t := by
      simpa using
        mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) ht_nonneg
    exact ht.trans ht_le_two_t
  have hsum :
      absTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (2 * t)) ⊆
        upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (2 * t)) ∪
          upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (A * (2 * t)) := by
    intro ω hω
    rw [Set.mem_union, mem_upperTailEvent, mem_upperTailEvent]
    exact lt_abs.mp (by
      simpa [A, absTailEvent, upperTailEvent, mul_assoc, mul_left_comm, mul_comm] using hω)
  have hupper :
      μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (2 * t))) ≤
        Real.exp (-((2 * t) ^ σ)) := by
    have hone :=
      isBigOWith_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_one_lt
        (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
        h_indep h_meas hs hσ hσ₂ hK hX hXmean
    simpa [A] using
      (isBigOWith_gammaSigma_iff (μ := μ)
        (X := fun ω => ∑ i ∈ s, X i ω)
        (A := A) (σ := σ)).1 hone htwo_t
  let Xneg : ι → Ω → ℝ := fun i ω => -X i ω
  have h_indep_neg : iIndepFun Xneg μ := by
    simpa [Xneg, Function.comp] using!
      h_indep.comp (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
  have h_meas_neg : ∀ i, Measurable (Xneg i) := by
    intro i
    simpa [Xneg] using h_meas i
  have hX_neg : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (Xneg i) K := by
    intro i hi
    simpa [Xneg] using (hX i hi).neg
  have hXmean_neg : ∀ i ∈ s, ∫ ω, Xneg i ω ∂μ = 0 := by
    intro i hi
    calc
      ∫ ω, Xneg i ω ∂μ = -∫ ω, X i ω ∂μ := by
          simpa [Xneg] using integral_neg (X i)
      _ = 0 := by rw [hXmean i hi, neg_zero]
  have hupper_neg :
      μ.real (upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (A * (2 * t))) ≤
        Real.exp (-((2 * t) ^ σ)) := by
    have hone :=
      isBigOWith_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_one_lt
        (μ := μ) (X := Xneg) (s := s) (σ := σ) (K := K)
        h_indep_neg h_meas_neg hs hσ hσ₂ hK hX_neg hXmean_neg
    simpa [Xneg, Finset.sum_apply, A] using
      (isBigOWith_gammaSigma_iff (μ := μ)
        (X := fun ω => ∑ i ∈ s, Xneg i ω)
        (A := A) (σ := σ)).1 hone htwo_t
  calc
    μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω)
      ((2 * gammaSigmaExpRegimeConst σ * Real.sqrt (s.card : ℝ) * K) * t))
      = μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (2 * t))) := by
          congr 1
          simp [A, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ μ.real
          (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (2 * t)) ∪
            upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (A * (2 * t))) := by
            exact measureReal_mono hsum
    _ ≤ μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (2 * t))) +
          μ.real (upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (A * (2 * t))) := by
            exact measureReal_union_le _ _
    _ ≤ Real.exp (-((2 * t) ^ σ)) + Real.exp (-((2 * t) ^ σ)) := by
          exact add_le_add hupper hupper_neg
    _ ≤ Real.exp (-(t ^ σ)) := by
          have htwo_sigma_ge_two : (2 : ℝ) ≤ (2 : ℝ) ^ σ := by
            have htmp : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ σ := by
              exact Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ)) hσ.le
            simpa [Real.rpow_one] using htmp
          have htpow_one : 1 ≤ t ^ σ := by
            have hσ_nonneg : 0 ≤ σ := by linarith
            exact Real.one_le_rpow ht hσ_nonneg
          have hextra_one : 1 ≤ ((2 : ℝ) ^ σ - 1) * t ^ σ := by
            have hfactor_one : 1 ≤ (2 : ℝ) ^ σ - 1 := by
              rw [le_sub_iff_add_le]
              norm_num
              exact htwo_sigma_ge_two
            have hfactor_nonneg : 0 ≤ (2 : ℝ) ^ σ - 1 :=
              zero_le_one.trans hfactor_one
            calc
              (1 : ℝ) = 1 * 1 := by ring
              _ ≤ ((2 : ℝ) ^ σ - 1) * t ^ σ :=
                  mul_le_mul hfactor_one htpow_one zero_le_one hfactor_nonneg
          have htwo_le_exp : (2 : ℝ) ≤ Real.exp (((2 : ℝ) ^ σ - 1) * t ^ σ) := by
            have htwo_exp_one : (2 : ℝ) < Real.exp 1 := by
              exact lt_trans (by norm_num) Real.exp_one_gt_d9
            have hexp_mono : Real.exp 1 ≤ Real.exp (((2 : ℝ) ^ σ - 1) * t ^ σ) := by
              exact (Real.exp_le_exp).2 hextra_one
            exact le_trans htwo_exp_one.le hexp_mono
          have hpow2t : (2 * t) ^ σ = (2 : ℝ) ^ σ * t ^ σ := by
            rw [Real.mul_rpow (by norm_num) ht_nonneg]
          calc
            Real.exp (-((2 * t) ^ σ)) + Real.exp (-((2 * t) ^ σ))
              = 2 * Real.exp (-((2 * t) ^ σ)) := by ring
            _ ≤ Real.exp (((2 : ℝ) ^ σ - 1) * t ^ σ) * Real.exp (-((2 * t) ^ σ)) := by
                  exact mul_le_mul_of_nonneg_right htwo_le_exp (by positivity)
            _ = Real.exp (-(t ^ σ)) := by
                  rw [hpow2t, ← Real.exp_add]
                  congr 1
                  ring

/-- Averaging preserves the direct exponential-regime concentration scale in
the range `1 < σ ≤ 2`. -/
theorem isBigO_gammaSigma_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_one_lt
    [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigO μ (gammaSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω)
      (2 * gammaSigmaExpRegimeConst σ * (Real.sqrt (s.card : ℝ) / (s.card : ℝ)) * K) := by
  have hsum :=
    isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_one_lt
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
      h_indep h_meas hs hσ hσ₂ hK hX hXmean
  have hcard_inv_nonneg : 0 ≤ ((s.card : ℝ)⁻¹) := by positivity
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    IsBigO.const_mul (μ := μ) (Ψ := gammaSigma σ)
      (X := fun ω => ∑ i ∈ s, X i ω)
      (A := 2 * gammaSigmaExpRegimeConst σ * Real.sqrt (s.card : ℝ) * K)
      (c := (s.card : ℝ)⁻¹) hcard_inv_nonneg hsum

/-- Explicit `Γ₁` witness extracted from the small-`λ` exponential-regime
argument. -/
noncomputable def gammaOneExpRegimeConst : ℝ :=
  4 * Real.exp 1 * gammaMomentConst 1

lemma gammaOneExpRegimeConst_pos : 0 < gammaOneExpRegimeConst := by
  dsimp [gammaOneExpRegimeConst]
  exact mul_pos (by positivity) (gammaMomentConst_pos zero_lt_one)

/-- Centered independent `O_{Γ₁}` summands satisfy the one-sided `Γ₁`
concentration estimate with the expected `sqrt(card)` scaling. -/
theorem isBigOWith_gammaOne_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} {K : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma 1) (X i) K)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigOWith μ (gammaSigma 1) (fun ω => ∑ i ∈ s, X i ω)
      (gammaOneExpRegimeConst * Real.sqrt (s.card : ℝ) * K) := by
  let R : ℝ := s.card
  let M : ℝ := gammaMomentConst 1 * K
  let B : ℝ := Real.exp 1 * M
  have hR_pos : 0 < R := by
    dsimp [R]
    exact_mod_cast hs.card_pos
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have hsqrtR_pos : 0 < Real.sqrt R := Real.sqrt_pos.2 hR_pos
  have hsqrtR_nonneg : 0 ≤ Real.sqrt R := hsqrtR_pos.le
  have hsqrtR_sq : (Real.sqrt R) ^ (2 : ℕ) = R := by
    simpa [pow_two] using Real.sq_sqrt hR_nonneg
  have hsqrtR_one_le : 1 ≤ Real.sqrt R := by
    have hcard_one : (1 : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hs.card_pos)
    refine (Real.one_le_sqrt).2 ?_
    simpa [R] using hcard_one
  have hM_pos : 0 < M := by
    dsimp [M]
    exact mul_pos (gammaMomentConst_pos zero_lt_one) hK
  have hM_nonneg : 0 ≤ M := hM_pos.le
  have hB_pos : 0 < B := by
    dsimp [B]
    exact mul_pos (Real.exp_pos 1) hM_pos
  have hXmom : ∀ i ∈ s, HasGammaMomentGrowthWith μ 1 (X i) M := by
    intro i hi
    simpa [M, mul_assoc, mul_left_comm, mul_comm] using
      (hasGammaMomentGrowthWith_of_isBigO_gammaSigma
        (μ := μ) (X := X i) (K := K) (σ := 1)
        zero_lt_one hK (h_meas i).aemeasurable (hX i hi))
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht
  let l : ℝ := min ((2 * B)⁻¹) (t / (B * Real.sqrt R))
  have hl_nonneg : 0 ≤ l := by
    dsimp [l]
    positivity
  have htail :=
    measureReal_upperTailEvent_finset_sum_le_exp_card_mul_of_iIndepFun_of_gammaMomentGrowth_small_of_integral_eq_zero
      (μ := μ) (X := X) (s := s) (σ := 1) (M := M) (l := l)
      (a := gammaOneExpRegimeConst * Real.sqrt R * K * t)
      h_indep h_meas le_rfl hM_nonneg hl_nonneg
      (by
        dsimp [l, B]
        simp [M, mul_assoc, mul_left_comm, mul_comm])
      hXmean hXmom
  refine htail.trans ?_
  apply (Real.exp_le_exp).2
  have hB_ne : B ≠ 0 := hB_pos.ne'
  have hsqrtR_ne : Real.sqrt R ≠ 0 := hsqrtR_pos.ne'
  have hA_eq :
      gammaOneExpRegimeConst * Real.sqrt R * K = 4 * B * Real.sqrt R := by
    dsimp [gammaOneExpRegimeConst, B, M]
    ring
  by_cases hcase : (2 * B)⁻¹ ≤ t / (B * Real.sqrt R)
  · have hl_eq : l = (2 * B)⁻¹ := by
      dsimp [l]
      rw [min_eq_left hcase]
    have hbranch : Real.sqrt R / 2 ≤ t := by
      have hden_nonneg : 0 ≤ B * Real.sqrt R :=
        (mul_pos hB_pos hsqrtR_pos).le
      calc
        Real.sqrt R / 2 = (2 * B)⁻¹ * (B * Real.sqrt R) := by
          field_simp [hB_ne]
        _ ≤ (t / (B * Real.sqrt R)) * (B * Real.sqrt R) :=
          mul_le_mul_of_nonneg_right hcase hden_nonneg
        _ = t := by
          field_simp [hB_ne, hsqrtR_ne]
    have hRm : R / 2 ≤ Real.sqrt R * t := by
      have htmp := mul_le_mul_of_nonneg_left hbranch hsqrtR_nonneg
      have hR_half : R / 2 = (Real.sqrt R) ^ (2 : ℕ) / 2 := by
        rw [hsqrtR_sq]
      calc
        R / 2 = (Real.sqrt R) ^ (2 : ℕ) / 2 := hR_half
        _ = Real.sqrt R * (Real.sqrt R / 2) := by ring
        _ ≤ Real.sqrt R * t := htmp
    calc
      -l * (gammaOneExpRegimeConst * Real.sqrt R * K * t) +
          2 * R * (Real.exp 1 * M * l) ^ (2 : ℕ)
        = -(2 * Real.sqrt R * t) + R / 2 := by
            rw [hl_eq, hA_eq]
            field_simp [hB_ne, pow_two]
            ring
      _ ≤ -(Real.sqrt R * t) := by
            calc
              -(2 * Real.sqrt R * t) + R / 2
                  ≤ -(2 * Real.sqrt R * t) + Real.sqrt R * t :=
                    add_le_add_right hRm (-(2 * Real.sqrt R * t))
              _ = -(Real.sqrt R * t) := by ring
      _ ≤ -t := by
            have hle : t ≤ Real.sqrt R * t := by
              simpa using mul_le_mul_of_nonneg_right hsqrtR_one_le ht_nonneg
            exact neg_le_neg hle
      _ = -(t ^ (1 : ℝ)) := by simp [Real.rpow_one]
  · have hl_eq : l = t / (B * Real.sqrt R) := by
      dsimp [l]
      rw [min_eq_right (le_of_not_ge hcase)]
    calc
      -l * (gammaOneExpRegimeConst * Real.sqrt R * K * t) +
          2 * R * (Real.exp 1 * M * l) ^ (2 : ℕ)
        = -2 * t ^ (2 : ℕ) := by
            rw [hl_eq, hA_eq]
            field_simp [hB_ne, hsqrtR_ne, pow_two]
            rw [hsqrtR_sq]
            ring
      _ ≤ -t := by
            have ht_sq_nonneg : 0 ≤ t ^ (2 : ℕ) := by positivity
            have ht_le_sq : t ≤ t ^ (2 : ℕ) := by
              have hmul := mul_le_mul_of_nonneg_right ht ht_nonneg
              simpa [pow_two] using hmul
            calc
              -2 * t ^ (2 : ℕ) ≤ -(t ^ (2 : ℕ)) := by
                calc
                  -2 * t ^ (2 : ℕ)
                      = -(t ^ (2 : ℕ)) - t ^ (2 : ℕ) := by ring
                  _ ≤ -(t ^ (2 : ℕ)) := sub_le_self _ ht_sq_nonneg
              _ ≤ -t := neg_le_neg ht_le_sq
      _ = -(t ^ (1 : ℝ)) := by simp [Real.rpow_one]

/-- Centered independent `O_{Γ₁}` summands satisfy the symmetric `Γ₁`
concentration estimate with the expected `sqrt(card)` scaling. -/
theorem isBigO_gammaOne_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} {K : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma 1) (X i) K)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigO μ (gammaSigma 1) (fun ω => ∑ i ∈ s, X i ω)
      (2 * gammaOneExpRegimeConst * Real.sqrt (s.card : ℝ) * K) := by
  let A : ℝ := gammaOneExpRegimeConst * Real.sqrt (s.card : ℝ) * K
  rw [isBigO_gammaSigma_iff]
  intro t ht
  have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht
  have htwo_t : 1 ≤ 2 * t := by
    have ht_le_two_t : t ≤ 2 * t := by
      simpa using
        mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) ht_nonneg
    exact ht.trans ht_le_two_t
  have hsum :
      absTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (2 * t)) ⊆
        upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (2 * t)) ∪
          upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (A * (2 * t)) := by
    intro ω hω
    rw [Set.mem_union, mem_upperTailEvent, mem_upperTailEvent]
    exact lt_abs.mp (by simpa [A, absTailEvent, upperTailEvent, mul_assoc, mul_left_comm, mul_comm] using hω)
  have hupper :
      μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (2 * t))) ≤
        Real.exp (-((2 * t) ^ (1 : ℝ))) := by
    have hone :=
      isBigOWith_gammaOne_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
        (μ := μ) (X := X) (s := s) (K := K)
        h_indep h_meas hs hK hX hXmean
    simpa [Real.rpow_one] using (isBigOWith_gammaSigma_iff (μ := μ)
      (X := fun ω => ∑ i ∈ s, X i ω) (A := A) (σ := 1)).1 hone htwo_t
  let Xneg : ι → Ω → ℝ := fun i ω => -X i ω
  have h_indep_neg : iIndepFun Xneg μ := by
    simpa [Xneg, Function.comp] using!
      h_indep.comp (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
  have h_meas_neg : ∀ i, Measurable (Xneg i) := by
    intro i
    simpa [Xneg] using h_meas i
  have hX_neg : ∀ i ∈ s, IsBigO μ (gammaSigma 1) (Xneg i) K := by
    intro i hi
    simpa [Xneg] using (hX i hi).neg
  have hXmean_neg : ∀ i ∈ s, ∫ ω, Xneg i ω ∂μ = 0 := by
    intro i hi
    calc
      ∫ ω, Xneg i ω ∂μ = -∫ ω, X i ω ∂μ := by
          simpa [Xneg] using integral_neg (X i)
      _ = 0 := by rw [hXmean i hi, neg_zero]
  have hupper_neg :
      μ.real (upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (A * (2 * t))) ≤
        Real.exp (-((2 * t) ^ (1 : ℝ))) := by
    have hone :=
      isBigOWith_gammaOne_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
        (μ := μ) (X := Xneg) (s := s) (K := K)
        h_indep_neg h_meas_neg hs hK hX_neg hXmean_neg
    simpa [Xneg, Finset.sum_apply] using
      (isBigOWith_gammaSigma_iff (μ := μ)
        (X := fun ω => ∑ i ∈ s, Xneg i ω) (A := A) (σ := 1)).1 hone htwo_t
  calc
    μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω)
      ((2 * gammaOneExpRegimeConst * Real.sqrt (s.card : ℝ) * K) * t))
      = μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (2 * t))) := by
          congr 1
          simp [A, mul_assoc, mul_left_comm, mul_comm]
    _
      ≤ μ.real
          (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (2 * t)) ∪
            upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (A * (2 * t))) := by
            exact measureReal_mono hsum
    _ ≤ μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (2 * t))) +
          μ.real (upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (A * (2 * t))) := by
            exact measureReal_union_le _ _
    _ ≤ Real.exp (-((2 * t) ^ (1 : ℝ))) + Real.exp (-((2 * t) ^ (1 : ℝ))) := by
          exact add_le_add hupper hupper_neg
    _ ≤ Real.exp (-(t ^ (1 : ℝ))) := by
          have haux : 2 * Real.exp (-((2 * t) ^ (1 : ℝ))) ≤ Real.exp (-(t ^ (1 : ℝ))) := by
            have htwo_exp : (2 : ℝ) ≤ Real.exp t := by
              have htwo_exp_one : (2 : ℝ) < Real.exp 1 := by
                exact lt_trans (by norm_num) Real.exp_one_gt_d9
              have hexp_mono : Real.exp 1 ≤ Real.exp t := by
                exact (Real.exp_le_exp).2 ht
              exact le_trans htwo_exp_one.le hexp_mono
            calc
              2 * Real.exp (-((2 * t) ^ (1 : ℝ)))
                  = 2 * Real.exp (-(2 * t)) := by rw [Real.rpow_one]
              _ ≤ Real.exp t * Real.exp (-(2 * t)) := by
                    exact mul_le_mul_of_nonneg_right htwo_exp (by positivity)
              _ = Real.exp (-(t ^ (1 : ℝ))) := by
                    rw [← Real.exp_add]
                    have hExp :
                        t + -(2 * t) = -(t ^ (1 : ℝ)) := by
                      rw [Real.rpow_one]
                      ring
                    rw [hExp]
          simpa [two_mul] using haux

/-- Averaging preserves the `Γ₁` concentration scale of centered independent
`O_{Γ₁}` summands. -/
theorem isBigO_gammaOne_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} {K : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma 1) (X i) K)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigO μ (gammaSigma 1)
      (fun ω => ((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω)
      (2 * gammaOneExpRegimeConst * (Real.sqrt (s.card : ℝ) / (s.card : ℝ)) * K) := by
  have hsum :=
    isBigO_gammaOne_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
      (μ := μ) (X := X) (s := s) (K := K)
      h_indep h_meas hs hK hX hXmean
  have hcard_inv_nonneg : 0 ≤ ((s.card : ℝ)⁻¹) := by positivity
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    IsBigO.const_mul (μ := μ) (Ψ := gammaSigma 1)
      (X := fun ω => ∑ i ∈ s, X i ω)
      (A := 2 * gammaOneExpRegimeConst * Real.sqrt (s.card : ℝ) * K)
      (c := (s.card : ℝ)⁻¹) hcard_inv_nonneg hsum

/-- Unified endpoint constant for the Chapter 4 direct exponential-regime
concentration theorem on the range `σ ∈ [1, 2]`. -/
noncomputable def gammaSigmaExpRegimeEndpointConst (σ : ℝ) : ℝ :=
  if σ = 1 then 2 * gammaOneExpRegimeConst else 2 * gammaSigmaExpRegimeConst σ

/-- Note-facing direct concentration theorem in the exponential regime
`σ ∈ [1, 2]`. -/
theorem isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_expRegime
    [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigO μ (gammaSigma σ) (fun ω => ∑ i ∈ s, X i ω)
      (gammaSigmaExpRegimeEndpointConst σ * Real.sqrt (s.card : ℝ) * K) := by
  by_cases hσ_eq : σ = 1
  · subst hσ_eq
    simpa [gammaSigmaExpRegimeEndpointConst] using
      isBigO_gammaOne_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
        (μ := μ) (X := X) (s := s) (K := K)
        h_indep h_meas hs hK hX hXmean
  · have hσ_gt : 1 < σ := by
      exact lt_of_le_of_ne hσ₁ (fun h => hσ_eq h.symm)
    simpa [gammaSigmaExpRegimeEndpointConst, hσ_eq] using
      isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_one_lt
        (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
        h_indep h_meas hs hσ_gt hσ₂ hK hX hXmean

/-- Averaged version of the direct exponential-regime concentration theorem on
the range `σ ∈ [1, 2]`. -/
theorem isBigO_gammaSigma_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero_expRegime
    [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K)
    (hXmean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigO μ (gammaSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω)
      (gammaSigmaExpRegimeEndpointConst σ * (Real.sqrt (s.card : ℝ) / (s.card : ℝ)) * K) := by
  by_cases hσ_eq : σ = 1
  · subst hσ_eq
    simpa [gammaSigmaExpRegimeEndpointConst] using
      isBigO_gammaOne_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero
        (μ := μ) (X := X) (s := s) (K := K)
        h_indep h_meas hs hK hX hXmean
  · have hσ_gt : 1 < σ := by
      exact lt_of_le_of_ne hσ₁ (fun h => hσ_eq h.symm)
    simpa [gammaSigmaExpRegimeEndpointConst, hσ_eq] using
      isBigO_gammaSigma_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_one_lt
        (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
        h_indep h_meas hs hσ_gt hσ₂ hK hX hXmean

end

end IndependentSums

end Homogenization
