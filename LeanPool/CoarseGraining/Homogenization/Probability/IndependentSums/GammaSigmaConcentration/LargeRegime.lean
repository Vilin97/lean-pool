/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.GammaSigmaConcentration.SmallRegime

/-! # Large Regime -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- Large-regime one-sided heavy-tail concentration for centered independent
unit-scale `O_{Γ_σ}` summands. -/
theorem measureReal_upperTailEvent_finset_sum_le_exp_neg_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one_unit_largeRegime
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ t : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) 1)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (ht : 1 ≤ t)
    (hlarge : (s.card : ℝ) ^ (σ / (2 * (2 - σ))) ≤ t) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω)
      (gammaSigmaHeavyTailConst σ * Real.sqrt (s.card : ℝ) * t)) ≤
      Real.exp (-(t ^ σ)) := by
  let R : ℝ := s.card
  let D : ℝ := gammaSigmaHeavyTailRoundedConst σ
  let B : ℝ := gammaSigmaHeavyTailConst σ
  let q : ℝ := σ / (1 - σ)
  let S : ℝ := R ^ (σ / 2) * t ^ σ
  have hR_pos : 0 < R := by
    dsimp [R]
    exact_mod_cast hs.card_pos
  have hR_one : 1 ≤ R := by
    dsimp [R]
    exact_mod_cast (Nat.succ_le_of_lt hs.card_pos)
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have hsqrtR_pos : 0 < Real.sqrt R := Real.sqrt_pos.2 hR_pos
  have hsqrtR_nonneg : 0 ≤ Real.sqrt R := hsqrtR_pos.le
  have hD_pos : 0 < D := by
    simpa [D] using gammaSigmaHeavyTailRoundedConst_pos (σ := σ) hσ₀
  have hsqrtD_pos : 0 < Real.sqrt D := Real.sqrt_pos.2 hD_pos
  have hsqrtD_two : 2 ≤ Real.sqrt D := by
    simpa [D] using two_le_sqrt_gammaSigmaHeavyTailRoundedConst (σ := σ) hσ₀
  have hXmom : ∀ i ∈ s, HasGammaMomentGrowthWith μ σ (X i) (gammaMomentConst σ) := by
    intro i hi
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (hasGammaMomentGrowthWith_of_isBigO_gammaSigma
        (μ := μ) (X := X i) (K := 1) (σ := σ)
        hσ₀ zero_lt_one (h_meas i).aemeasurable (hX i hi))
  have h_int : ∀ i ∈ s, Integrable (X i) μ := by
    intro i hi
    have hXone :=
      gammaMomentGrowth_natCast_bound
        (μ := μ) (X := X i) (σ := σ) (M := gammaMomentConst σ) (n := 1)
        (by norm_num) (hXmom i hi)
    have hX_abs_int : Integrable (fun ω => |X i ω|) μ := by
      simpa using hXone.1
    have hX_norm_int : Integrable (fun ω => ‖X i ω‖) μ := by
      simpa [Real.norm_eq_abs] using hX_abs_int
    exact (integrable_norm_iff ((h_meas i).aemeasurable.aestronglyMeasurable)).1 hX_norm_int
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    positivity
  have hS_tpow : t ^ σ ≤ S := by
    have hRpow_one : 1 ≤ R ^ (σ / 2) := by
      exact Real.one_le_rpow hR_one (by positivity : 0 ≤ σ / 2)
    calc
      t ^ σ ≤ R ^ (σ / 2) * t ^ σ := by
            calc
              t ^ σ = 1 * t ^ σ := by ring
              _ ≤ R ^ (σ / 2) * t ^ σ :=
                mul_le_mul_of_nonneg_right hRpow_one
                  (Real.rpow_nonneg ht_nonneg σ)
      _ = S := by rfl
  let l : ℝ := R ^ ((σ - 1) / 2) * t ^ (σ - 1) / (4 * Real.sqrt D)
  let L : ℝ := (2 * Real.sqrt D) ^ (1 / (1 - σ)) * Real.sqrt R * t
  have hl_nonneg : 0 ≤ l := by
    dsimp [l]
    positivity
  have hRpow_le_one : R ^ ((σ - 1) / 2) ≤ 1 := by
    have hExp_nonpos : (σ - 1) / 2 ≤ 0 := by linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos hR_one hExp_nonpos
  have htpow_le_one : t ^ (σ - 1) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
  have hl_half : l ≤ 1 / 2 := by
    dsimp [l]
    have hle :
        R ^ ((σ - 1) / 2) * t ^ (σ - 1) / (4 * Real.sqrt D) ≤
          1 / (4 * Real.sqrt D) := by
      have hprod :
          R ^ ((σ - 1) / 2) * t ^ (σ - 1) ≤ 1 := by
        have hnonneg : 0 ≤ t ^ (σ - 1) := Real.rpow_nonneg ht_nonneg _
        calc
          R ^ ((σ - 1) / 2) * t ^ (σ - 1) ≤ 1 * t ^ (σ - 1) := by
                gcongr
          _ ≤ 1 := by simpa using htpow_le_one
      have hden_pos : 0 < 4 * Real.sqrt D := by positivity
      exact div_le_div_of_nonneg_right hprod hden_pos.le
    calc
      l = R ^ ((σ - 1) / 2) * t ^ (σ - 1) / (4 * Real.sqrt D) := rfl
      _ ≤ 1 / (4 * Real.sqrt D) := hle
      _ ≤ 1 / 2 := by
            have hden : (8 : ℝ) ≤ 4 * Real.sqrt D := by
              have hden' :=
                mul_le_mul_of_nonneg_left hsqrtD_two
                  (by norm_num : 0 ≤ (4 : ℝ))
              norm_num at hden'
              exact hden'
            have hinv : 1 / (4 * Real.sqrt D) ≤ 1 / (8 : ℝ) := by
              exact one_div_le_one_div_of_le (by positivity : 0 < (8 : ℝ)) hden
            exact hinv.trans (by norm_num : (1 / (8 : ℝ)) ≤ 1 / 2)
  have hl_one : l ≤ 1 := by linarith
  have hL_one : 1 ≤ L := by
    have hconst_one : 1 ≤ (2 * Real.sqrt D) ^ (1 / (1 - σ)) := by
      have hbase_one : 1 ≤ 2 * Real.sqrt D := by
        calc
          (1 : ℝ) ≤ Real.sqrt D := le_trans (by norm_num) hsqrtD_two
          _ ≤ 2 * Real.sqrt D := by
            exact le_mul_of_one_le_left hsqrtD_pos.le (by norm_num : (1 : ℝ) ≤ 2)
      have hexp_nonneg : 0 ≤ 1 / (1 - σ) := by
        have hone_sub_pos : 0 < 1 - σ := sub_pos.mpr hσ₁
        positivity
      exact Real.one_le_rpow hbase_one hexp_nonneg
    have hsqrtR_one : 1 ≤ Real.sqrt R := by
      refine (Real.one_le_sqrt).2 ?_
      exact hR_one
    dsimp [L]
    calc
      1 ≤ (2 * Real.sqrt D) ^ (1 / (1 - σ)) := hconst_one
      _ ≤ (2 * Real.sqrt D) ^ (1 / (1 - σ)) * Real.sqrt R := by
            calc
              (2 * Real.sqrt D) ^ (1 / (1 - σ))
                  =
                (2 * Real.sqrt D) ^ (1 / (1 - σ)) * 1 := by ring
              _ ≤ (2 * Real.sqrt D) ^ (1 / (1 - σ)) * Real.sqrt R :=
                mul_le_mul_of_nonneg_left hsqrtR_one
                  (Real.rpow_nonneg (by positivity : 0 ≤ 2 * Real.sqrt D) _)
      _ ≤ (2 * Real.sqrt D) ^ (1 / (1 - σ)) * Real.sqrt R * t := by
            calc
              (2 * Real.sqrt D) ^ (1 / (1 - σ)) * Real.sqrt R
                  = ((2 * Real.sqrt D) ^ (1 / (1 - σ)) * Real.sqrt R) * 1 := by ring
              _ ≤ ((2 * Real.sqrt D) ^ (1 / (1 - σ)) * Real.sqrt R) * t := by
                    gcongr
              _ = (2 * Real.sqrt D) ^ (1 / (1 - σ)) * Real.sqrt R * t := by ring
  have hlL_eq : (1 / 2) * L ^ (σ - 1) = l := by
    have hconst_pow :
        ((2 * Real.sqrt D) ^ (1 / (1 - σ))) ^ (σ - 1) = (2 * Real.sqrt D) ^ (-1 : ℝ) := by
      rw [← Real.rpow_mul (show 0 ≤ 2 * Real.sqrt D by positivity)]
      congr 2
      field_simp [sub_ne_zero.mpr hσ₁.ne.symm]
      ring
    have hsqrtR_pow :
        (Real.sqrt R) ^ (σ - 1) = R ^ ((σ - 1) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR_nonneg]
      congr 1
      ring
    calc
      (1 / 2) * L ^ (σ - 1)
        = (1 / 2) *
            (((2 * Real.sqrt D) ^ (1 / (1 - σ)) * (Real.sqrt R * t))) ^ (σ - 1) := by
              simp [L, mul_assoc]
      _ = (1 / 2) *
            ((2 * Real.sqrt D) ^ (1 / (1 - σ))) ^ (σ - 1) *
              (Real.sqrt R * t) ^ (σ - 1) := by
              rw [Real.mul_rpow (by positivity) (by positivity)]
              ring
      _ = (1 / 2) * (2 * Real.sqrt D) ^ (-1 : ℝ) * (Real.sqrt R * t) ^ (σ - 1) := by
              rw [hconst_pow]
      _ = (1 / 2) * (1 / (2 * Real.sqrt D)) *
            ((Real.sqrt R) ^ (σ - 1) * t ^ (σ - 1)) := by
              rw [Real.rpow_neg_one, inv_eq_one_div, Real.mul_rpow hsqrtR_nonneg ht_nonneg]
      _ = l := by
              rw [hsqrtR_pow]
              dsimp [l]
              ring_nf
  have hlL : l ≤ (1 / 2) * L ^ (σ - 1) := by
    rw [hlL_eq]
  have htail :=
    measureReal_upperTailEvent_finset_sum_le_exp_card_mul_add_card_mul_exp_neg_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one
      (μ := μ) (X := X) (s := s) (σ := σ)
      (a := B * Real.sqrt R * t) (l := l) (L := L)
      h_indep h_meas h_int h_mean hσ₀ hσ₁ hX hl_nonneg hl_one hL_one hlL
  have hmgf :
      Real.exp (-l * (B * Real.sqrt R * t) + R * (l ^ (2 : ℕ) * D))
        ≤ Real.exp (-2 * t ^ σ) := by
    apply (Real.exp_le_exp).2
    have hRpow : R ^ ((σ - 1) / 2) * Real.sqrt R = R ^ (σ / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hR_pos]
      congr 1
      ring
    have htpow : t ^ (σ - 1) * t = t ^ σ := by
      calc
        t ^ (σ - 1) * t = t ^ (σ - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = t ^ σ := by
              rw [← Real.rpow_add ht_pos]
              congr 1
              ring
    have hla : l * (B * Real.sqrt R * t) = 4 * S := by
      calc
        l * (B * Real.sqrt R * t)
          = (R ^ ((σ - 1) / 2) * t ^ (σ - 1) / (4 * Real.sqrt D)) *
              (16 * Real.sqrt D * Real.sqrt R * t) := by
                dsimp [l, B, gammaSigmaHeavyTailConst]
        _ = 4 * (R ^ ((σ - 1) / 2) * Real.sqrt R) * (t ^ (σ - 1) * t) := by
              field_simp [hsqrtD_pos.ne']
              ring
        _ = 4 * S := by
              rw [hRpow, htpow]
              ring
    have hquad : R * (l ^ (2 : ℕ) * D) = (1 / 16 : ℝ) * (R ^ σ * t ^ (2 * σ - 2)) := by
      have hRpow_sq :
          (R ^ ((σ - 1) / 2)) ^ (2 : ℕ) = R ^ (σ - 1) := by
        rw [show (2 : ℝ) = (2 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul hR_nonneg]
        congr 1
        ring
      have htpow_sq :
          (t ^ (σ - 1)) ^ (2 : ℕ) = t ^ (2 * σ - 2) := by
        rw [show (2 : ℝ) = (2 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul ht_nonneg]
        congr 1
        ring
      have hR_sigma : R * R ^ (σ - 1) = R ^ σ := by
        calc
          R * R ^ (σ - 1) = R ^ (1 : ℝ) * R ^ (σ - 1) := by rw [Real.rpow_one]
          _ = R ^ σ := by
                rw [← Real.rpow_add hR_pos]
                congr 1
                ring
      dsimp [l]
      field_simp [hsqrtD_pos.ne', pow_two]
      rw [Real.sq_sqrt hD_pos.le, hRpow_sq, htpow_sq]
      rw [hR_sigma]
      ring_nf
    have hscale :
        -l * (B * Real.sqrt R * t) + R * (l ^ (2 : ℕ) * D)
          ≤ -4 * S + (1 / 16 : ℝ) * S := by
      calc
        -l * (B * Real.sqrt R * t) + R * (l ^ (2 : ℕ) * D)
          = -(l * (B * Real.sqrt R * t)) + R * (l ^ (2 : ℕ) * D) := by ring
        _ = -(4 : ℝ) * S + (1 / 16 : ℝ) * (R ^ σ * t ^ (2 * σ - 2)) := by
              rw [hla, hquad]
              ring
        _ ≤ -(4 : ℝ) * S + (1 / 16 : ℝ) * S := by
              have hcorr :
                  R ^ σ * t ^ (2 * σ - 2) ≤ S := by
                simpa [S] using
                  largeRegime_correction_le_gammaSigmaScale (σ := σ) (R := R) (t := t)
                    hσ₀ hσ₁ hR_pos ht_pos (by simpa [R] using hlarge)
              have hscaled :
                  (1 / 16 : ℝ) * (R ^ σ * t ^ (2 * σ - 2)) ≤
                    (1 / 16 : ℝ) * S := by
                exact mul_le_mul_of_nonneg_left hcorr (by norm_num)
              linarith
    calc
      -l * (B * Real.sqrt R * t) + R * (l ^ (2 : ℕ) * D)
        ≤ -4 * S + (1 / 16 : ℝ) * S := hscale
      _ = (-(63 / 16 : ℝ)) * S := by ring
      _ ≤ -(2 : ℝ) * S :=
            mul_le_mul_of_nonneg_right
              (by norm_num : (-(63 / 16 : ℝ)) ≤ -2) hS_nonneg
      _ ≤ -(2 : ℝ) * t ^ σ := by
            have hscaled :
                (2 : ℝ) * t ^ σ ≤ (2 : ℝ) * S := by
              exact mul_le_mul_of_nonneg_left hS_tpow (by positivity)
            have hneg := neg_le_neg hscaled
            simpa [two_mul] using hneg
  have hx_card :
      R ^ (σ / (2 - σ)) ≤ S := by
    simpa [S] using
      largeRegime_cardPow_le_gammaSigmaScale (σ := σ) (R := R) (t := t)
        hσ₀ hσ₁ hR_pos ht_pos (by simpa [R] using hlarge)
  have hLpow :
      L ^ σ = gammaSigmaHeavyTailUnionConst σ * S := by
    have hq_eq : (1 / (1 - σ)) * σ = q := by
      dsimp [q]
      field_simp [sub_ne_zero.mpr hσ₁.ne.symm]
    have hsqrtR_sigma : (Real.sqrt R) ^ σ = R ^ (σ / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR_nonneg]
      congr 1
      ring
    calc
      L ^ σ
        = (((2 * Real.sqrt D) ^ (1 / (1 - σ)) * Real.sqrt R * t) ^ σ) := by
            simp [L]
      _ = (((2 * Real.sqrt D) ^ (1 / (1 - σ)) * Real.sqrt R) ^ σ) * t ^ σ := by
            rw [Real.mul_rpow (by positivity) ht_nonneg]
      _ = ((2 * Real.sqrt D) ^ (1 / (1 - σ))) ^ σ * (Real.sqrt R) ^ σ * t ^ σ := by
            rw [Real.mul_rpow (by positivity) hsqrtR_nonneg]
      _ = (2 * Real.sqrt D) ^ q * (R ^ (σ / 2) * t ^ σ) := by
            rw [← Real.rpow_mul (show 0 ≤ 2 * Real.sqrt D by positivity)]
            rw [hsqrtR_sigma]
            rw [hq_eq]
            simp [mul_assoc, mul_comm]
      _ = gammaSigmaHeavyTailUnionConst σ * S := by
            rfl
  have hunion :
      R * Real.exp (-(L ^ σ)) ≤ Real.exp (-2 * t ^ σ) := by
    rw [hLpow]
    calc
      R * Real.exp (-(gammaSigmaHeavyTailUnionConst σ * S))
        ≤ Real.exp (-2 * S) := by
            exact card_mul_exp_neg_gammaSigmaHeavyTailUnionConst_mul_le_exp_neg_two_mul
              (σ := σ) (R := R) (x := S) hσ₀ hσ₁ hR_one hS_nonneg hx_card
      _ ≤ Real.exp (-2 * t ^ σ) := by
            have hscaled :
                (2 : ℝ) * t ^ σ ≤ (2 : ℝ) * S :=
              mul_le_mul_of_nonneg_left hS_tpow (by norm_num)
            have hneg := neg_le_neg hscaled
            exact (Real.exp_le_exp).2 (by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hneg)
  have htail' :
      μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω)
        (gammaSigmaHeavyTailConst σ * Real.sqrt (s.card : ℝ) * t)) ≤
        Real.exp (-l * (B * Real.sqrt R * t) + R * (l ^ (2 : ℕ) * D)) +
          R * Real.exp (-(L ^ σ)) := by
    simpa [B, R] using htail
  calc
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω)
      (gammaSigmaHeavyTailConst σ * Real.sqrt (s.card : ℝ) * t))
      ≤ Real.exp (-l * (B * Real.sqrt R * t) + R * (l ^ (2 : ℕ) * D)) +
          R * Real.exp (-(L ^ σ)) := htail'
    _ ≤ Real.exp (-2 * t ^ σ) + Real.exp (-2 * t ^ σ) := by
          exact add_le_add hmgf hunion
    _ = 2 * Real.exp (-2 * t ^ σ) := by ring
    _ ≤ Real.exp (-(t ^ σ)) := by
          exact two_mul_exp_neg_two_mul_le_exp_neg
            (x := t ^ σ) (Real.one_le_rpow ht hσ₀.le)

/-- One-sided heavy-tail concentration for centered independent unit-scale
`O_{Γ_σ}` summands on the range `0 < σ < 1`. -/
theorem isBigOWith_gammaSigma_finset_sum_unit_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) 1)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigOWith μ (gammaSigma σ) (fun ω => ∑ i ∈ s, X i ω)
      (gammaSigmaHeavyTailConst σ * Real.sqrt (s.card : ℝ)) := by
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  by_cases hsmall : t ≤ (s.card : ℝ) ^ (σ / (2 * (2 - σ)))
  · simpa [mul_assoc, mul_left_comm, mul_comm] using
      measureReal_upperTailEvent_finset_sum_le_exp_neg_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one_unit_smallRegime
        (μ := μ) (X := X) (s := s) (σ := σ) (t := t)
        h_indep h_meas hs hσ₀ hσ₁ hX h_mean ht hsmall
  · have hlarge : (s.card : ℝ) ^ (σ / (2 * (2 - σ))) ≤ t := le_of_not_ge hsmall
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      measureReal_upperTailEvent_finset_sum_le_exp_neg_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one_unit_largeRegime
        (μ := μ) (X := X) (s := s) (σ := σ) (t := t)
        h_indep h_meas hs hσ₀ hσ₁ hX h_mean ht hlarge

/-- One-sided heavy-tail concentration for centered independent `O_{Γ_σ}`
summands on the range `0 < σ < 1`. -/
theorem isBigOWith_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigOWith μ (gammaSigma σ) (fun ω => ∑ i ∈ s, X i ω)
      (gammaSigmaHeavyTailConst σ * Real.sqrt (s.card : ℝ) * K) := by
  let Y : ι → Ω → ℝ := fun i ω => K⁻¹ * X i ω
  have h_indep_Y : iIndepFun Y μ := by
    simpa [Y, Function.comp] using!
      h_indep.comp (fun _ => fun x : ℝ => K⁻¹ * x)
        (fun _ => measurable_const.mul measurable_id)
  have h_meas_Y : ∀ i, Measurable (Y i) := by
    intro i
    simpa [Y, mul_comm] using (h_meas i).const_mul K⁻¹
  have hX_Y : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (Y i) 1 := by
    intro i hi
    have hscaled :=
      IsBigO.const_mul (μ := μ) (Ψ := gammaSigma σ) (X := X i) (A := K) (c := K⁻¹)
        (inv_nonneg.mpr hK.le) (hX i hi)
    have hscale : K⁻¹ * K = (1 : ℝ) := by
      field_simp [hK.ne']
    simpa [Y, hscale] using hscaled
  have h_mean_Y : ∀ i ∈ s, ∫ ω, Y i ω ∂μ = 0 := by
    intro i hi
    calc
      ∫ ω, Y i ω ∂μ = K⁻¹ * ∫ ω, X i ω ∂μ := by
          simpa [Y] using integral_const_mul K⁻¹ (X i)
      _ = 0 := by rw [h_mean i hi]; ring
  have hsum_Y :=
    isBigOWith_gammaSigma_finset_sum_unit_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one
      (μ := μ) (X := Y) (s := s) (σ := σ)
      h_indep_Y h_meas_Y hs hσ₀ hσ₁ hX_Y h_mean_Y
  have hsum_X :=
    IsBigOWith.const_mul (μ := μ) (Ψ := gammaSigma σ)
      (X := fun ω => ∑ i ∈ s, Y i ω)
      (A := gammaSigmaHeavyTailConst σ * Real.sqrt (s.card : ℝ))
      (c := K) hK.le hsum_Y
  have hk : K * K⁻¹ = (1 : ℝ) := by
    field_simp [hK.ne']
  have hsum_eq :
      (fun ω => K * ∑ i ∈ s, Y i ω) = fun ω => ∑ i ∈ s, X i ω := by
    funext ω
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    dsimp [Y]
    rw [← mul_assoc, hk, one_mul]
  simpa [hsum_eq, mul_assoc, mul_left_comm, mul_comm] using hsum_X

/-- Symmetric heavy-tail concentration for centered independent `O_{Γ_σ}`
summands on the range `0 < σ < 1`. -/
theorem isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigO μ (gammaSigma σ) (fun ω => ∑ i ∈ s, X i ω)
      (gammaSigmaHeavyTailEndpointConst σ * Real.sqrt (s.card : ℝ) * K) := by
  let C : ℝ := (2 : ℝ) ^ (1 / σ)
  let A : ℝ := gammaSigmaHeavyTailConst σ * Real.sqrt (s.card : ℝ) * K
  rw [isBigO_gammaSigma_iff]
  intro t ht
  have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hC_one : 1 ≤ C := by
    dsimp [C]
    exact Real.one_le_rpow (by norm_num : 1 ≤ (2 : ℝ)) (by positivity : 0 ≤ 1 / σ)
  have hCt : 1 ≤ C * t := by
    simpa using
      mul_le_mul hC_one ht (by norm_num : 0 ≤ (1 : ℝ)) hC_nonneg
  have hC_pow : C ^ σ = 2 := by
    dsimp [C]
    rw [one_div, Real.rpow_inv_rpow (show 0 ≤ (2 : ℝ) by norm_num) hσ₀.ne']
  have hCt_pow : (C * t) ^ σ = 2 * t ^ σ := by
    calc
      (C * t) ^ σ = C ^ σ * t ^ σ := by
            rw [Real.mul_rpow hC_nonneg ht_nonneg]
      _ = 2 * t ^ σ := by
            rw [hC_pow]
  have hfinal : 2 * Real.exp (-(2 * t ^ σ)) ≤ Real.exp (-(t ^ σ)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc, neg_mul] using
      (two_mul_exp_neg_two_mul_le_exp_neg (x := t ^ σ) (Real.one_le_rpow ht hσ₀.le))
  have hsum :
      absTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (C * t)) ⊆
        upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (C * t)) ∪
          upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (A * (C * t)) := by
    intro ω hω
    rw [Set.mem_union, mem_upperTailEvent, mem_upperTailEvent]
    exact lt_abs.mp (by
      simpa [A, absTailEvent, upperTailEvent, mul_assoc, mul_left_comm, mul_comm] using hω)
  have hupper :
      μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (C * t))) ≤
        Real.exp (-((C * t) ^ σ)) := by
    have hone :=
      isBigOWith_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one
        (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
        h_indep h_meas hs hσ₀ hσ₁ hK hX h_mean
    simpa [A] using
      (isBigOWith_gammaSigma_iff (μ := μ)
        (X := fun ω => ∑ i ∈ s, X i ω)
        (A := A) (σ := σ)).1 hone hCt
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
  have h_mean_neg : ∀ i ∈ s, ∫ ω, Xneg i ω ∂μ = 0 := by
    intro i hi
    calc
      ∫ ω, Xneg i ω ∂μ = -∫ ω, X i ω ∂μ := by
          simpa [Xneg] using integral_neg (X i)
      _ = 0 := by rw [h_mean i hi, neg_zero]
  have hupper_neg :
      μ.real (upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (A * (C * t))) ≤
        Real.exp (-((C * t) ^ σ)) := by
    have hone :=
      isBigOWith_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one
        (μ := μ) (X := Xneg) (s := s) (σ := σ) (K := K)
        h_indep_neg h_meas_neg hs hσ₀ hσ₁ hK hX_neg h_mean_neg
    simpa [Xneg, Finset.sum_apply, A] using
      (isBigOWith_gammaSigma_iff (μ := μ)
        (X := fun ω => ∑ i ∈ s, Xneg i ω)
        (A := A) (σ := σ)).1 hone hCt
  calc
    μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω)
      ((gammaSigmaHeavyTailEndpointConst σ * Real.sqrt (s.card : ℝ) * K) * t))
      = μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (C * t))) := by
          congr 1
          simp [A, C, gammaSigmaHeavyTailEndpointConst, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ μ.real
          (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (C * t)) ∪
            upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (A * (C * t))) := by
            exact measureReal_mono hsum
    _ ≤ μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (A * (C * t))) +
          μ.real (upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (A * (C * t))) := by
            exact measureReal_union_le _ _
    _ ≤ Real.exp (-((C * t) ^ σ)) + Real.exp (-((C * t) ^ σ)) := by
          exact add_le_add hupper hupper_neg
    _ = 2 * Real.exp (-(2 * t ^ σ)) := by
          rw [hCt_pow]
          ring
    _ ≤ Real.exp (-(t ^ σ)) := by
          exact hfinal

/-- Averaging preserves the heavy-tail `Γ_σ` concentration scale in the range
`0 < σ < 1`. -/
theorem isBigO_gammaSigma_finsetAverage_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigO μ (gammaSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω)
      (gammaSigmaHeavyTailEndpointConst σ * (Real.sqrt (s.card : ℝ) / (s.card : ℝ)) * K) := by
  have hsum :=
    isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
      h_indep h_meas hs hσ₀ hσ₁ hK hX h_mean
  have hcard_inv_nonneg : 0 ≤ ((s.card : ℝ)⁻¹) := by positivity
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    IsBigO.const_mul (μ := μ) (Ψ := gammaSigma σ)
      (X := fun ω => ∑ i ∈ s, X i ω)
      (A := gammaSigmaHeavyTailEndpointConst σ * Real.sqrt (s.card : ℝ) * K)
      (c := (s.card : ℝ)⁻¹) hcard_inv_nonneg hsum


end

end IndependentSums

end Homogenization
