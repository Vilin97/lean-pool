/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.GammaSigmaConcentration.Preliminaries

/-! # Small Regime -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- Specialized rounded heavy-tail concentration estimate for `Γ_σ` on the
range `σ ∈ (0, 1)`. This is the concrete `Γ_σ` wrapper around the generic
rounded truncation-Chernoff theorem from `PsiConcentration.lean`. -/
theorem measureReal_upperTailEvent_finset_sum_le_exp_card_mul_add_card_mul_exp_neg_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ a l L : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) 1)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hL : 1 ≤ L)
    (hlL : l ≤ (1 / 2) * L ^ (σ - 1)) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a) ≤
      Real.exp (-l * a + (s.card : ℝ) * (l ^ (2 : ℕ) * gammaSigmaHeavyTailRoundedConst σ)) +
        (s.card : ℝ) * Real.exp (-(L ^ σ)) := by
  have hmain :=
    measureReal_upperTailEvent_finset_sum_le_exp_card_mul_add_card_mul_invPsi_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_log_constraint_rounded
      (μ := μ) (Ψ := gammaSigma σ) (X := X) (s := s) (a := a) (l := l) (L := L)
      (CΨ := gammaSigmaTailIntegralConst σ) (M := gammaSigmaLogControlConst σ)
      h_indep h_meas h_int h_mean
      (admissiblePsi_gammaSigma hσ₀.le)
      (gammaSigmaTailIntegralConst_nonneg hσ₀)
      (lintegral_Ioi_one_gammaSigma_le_gammaSigmaTailIntegralConst hσ₀)
      hX hl hl1 hL (one_le_gammaSigmaLogControlConst σ) ?_
  · simpa [gammaSigmaHeavyTailRoundedConst, gammaSigmaTailIntegralConst,
      gammaSigmaLogControlConst, gammaSigma, ← Real.exp_neg] using hmain
  · intro i hi t ht
    exact gammaSigma_log_constraint (σ := σ) (l := l) (L := L) (t := t)
      hσ₀ hσ₁ hlL ht

/-- The rounded heavy-tail scale is uniformly at least `4`, so its square root
is at least `2`. -/
lemma four_le_gammaSigmaHeavyTailRoundedConst {σ : ℝ} (hσ : 0 < σ) :
    4 ≤ gammaSigmaHeavyTailRoundedConst σ := by
  dsimp [gammaSigmaHeavyTailRoundedConst]
  linarith [gammaSigmaTailIntegralConst_nonneg (σ := σ) hσ,
    one_le_gammaSigmaLogControlConst σ]

lemma two_le_sqrt_gammaSigmaHeavyTailRoundedConst {σ : ℝ} (hσ : 0 < σ) :
    2 ≤ Real.sqrt (gammaSigmaHeavyTailRoundedConst σ) := by
  have hfour :
      (4 : ℝ) ≤ gammaSigmaHeavyTailRoundedConst σ :=
    four_le_gammaSigmaHeavyTailRoundedConst (σ := σ) hσ
  have hsqrt :
      Real.sqrt 4 ≤ Real.sqrt (gammaSigmaHeavyTailRoundedConst σ) :=
    Real.sqrt_le_sqrt hfour
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simpa [hsqrt4] using hsqrt

lemma gammaSigmaHeavyTailConst_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < gammaSigmaHeavyTailConst σ := by
  dsimp [gammaSigmaHeavyTailConst]
  exact mul_pos (by positivity) (Real.sqrt_pos.2 (gammaSigmaHeavyTailRoundedConst_pos hσ))

lemma heavyTail_rpow_choice_eq {σ l : ℝ}
    (hσ₁ : σ < 1) (hl : 0 < l) :
    let L : ℝ := (2 * l) ^ (-(1 / (1 - σ)))
    (1 / 2) * L ^ (σ - 1) = l := by
  let L : ℝ := (2 * l) ^ (-(1 / (1 - σ)))
  have hbase_nonneg : 0 ≤ 2 * l := by positivity
  have hone_sub_ne : 1 - σ ≠ 0 := sub_ne_zero.mpr hσ₁.ne.symm
  calc
    (1 / 2) * L ^ (σ - 1)
      = (1 / 2) * ((2 * l) ^ (-(1 / (1 - σ)))) ^ (σ - 1) := by
          rfl
    _ = (1 / 2) * (2 * l) ^ ((-(1 / (1 - σ))) * (σ - 1)) := by
          rw [← Real.rpow_mul hbase_nonneg]
    _ = (1 / 2) * (2 * l) ^ (1 : ℝ) := by
          congr 2
          field_simp [hone_sub_ne]
          ring
    _ = l := by
          rw [Real.rpow_one]
          ring

lemma one_le_heavyTail_rpow_choice {σ l : ℝ}
    (hσ₁ : σ < 1) (hl : 0 < l) (hl_half : l ≤ 1 / 2) :
    1 ≤ (2 * l) ^ (-(1 / (1 - σ))) := by
  have hbase_le_one : 2 * l ≤ 1 := by
    calc
      2 * l ≤ 2 * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hl_half (by norm_num)
      _ = 1 := by norm_num
  have hexp_nonpos : -(1 / (1 - σ)) ≤ 0 := by
    have hone_sub_pos : 0 < 1 - σ := sub_pos.mpr hσ₁
    have hnonneg : 0 ≤ 1 / (1 - σ) := by positivity
    exact neg_nonpos.mpr hnonneg
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    (by positivity : 0 < 2 * l) hbase_le_one hexp_nonpos

lemma card_mul_exp_neg_gammaSigmaHeavyTailUnionConst_mul_le_exp_neg_two_mul
    {σ R x : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hR_one : 1 ≤ R) (hx_nonneg : 0 ≤ x)
    (hcardPow : R ^ (σ / (2 - σ)) ≤ x) :
    R * Real.exp (-(gammaSigmaHeavyTailUnionConst σ * x)) ≤
      Real.exp (-2 * x) := by
  let β : ℝ := σ / (2 - σ)
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR_one
  have hβ_pos : 0 < β := by
    dsimp [β]
    have htwo_sub_pos : 0 < 2 - σ := by linarith
    exact div_pos hσ₀ htwo_sub_pos
  have hlog_le_pow_div : Real.log R ≤ R ^ β / β := by
    simpa [β] using Real.log_le_rpow_div (show 0 ≤ R by linarith) hβ_pos
  have hpow_div_le : R ^ β / β ≤ x / β := by
    exact div_le_div_of_nonneg_right hcardPow hβ_pos.le
  have hx_scaled : x / β ≤ (2 / σ) * x := by
    have hcoef :
        (2 - σ) / σ ≤ 2 / σ := by
      have hσ_ne : σ ≠ 0 := hσ₀.ne'
      field_simp [hσ_ne]
      linarith
    have hrewrite : x / β = ((2 - σ) / σ) * x := by
      have htwo_sub_ne : 2 - σ ≠ 0 := by linarith
      dsimp [β]
      field_simp [hσ₀.ne', htwo_sub_ne]
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_right hcoef hx_nonneg
  have hlog_le_scaled : Real.log R ≤ (2 / σ) * x := by
    exact hlog_le_pow_div.trans (hpow_div_le.trans hx_scaled)
  have hR_le_exp : R ≤ Real.exp ((2 / σ) * x) := by
    calc
      R = Real.exp (Real.log R) := by rw [Real.exp_log hR_pos]
      _ ≤ Real.exp ((2 / σ) * x) := by
            exact (Real.exp_le_exp).2 hlog_le_scaled
  have hU :
      2 + 2 / σ ≤ gammaSigmaHeavyTailUnionConst σ :=
    two_add_two_div_le_gammaSigmaHeavyTailUnionConst (σ := σ) hσ₀ hσ₁
  calc
    R * Real.exp (-(gammaSigmaHeavyTailUnionConst σ * x))
      ≤ Real.exp ((2 / σ) * x) *
          Real.exp (-(gammaSigmaHeavyTailUnionConst σ * x)) := by
            exact mul_le_mul_of_nonneg_right hR_le_exp (by positivity)
    _ = Real.exp (((2 / σ) - gammaSigmaHeavyTailUnionConst σ) * x) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ ≤ Real.exp (-2 * x) := by
          apply (Real.exp_le_exp).2
          have hcoef : (2 / σ) - gammaSigmaHeavyTailUnionConst σ ≤ -2 := by
            linarith
          exact mul_le_mul_of_nonneg_right hcoef hx_nonneg

lemma two_mul_exp_neg_two_mul_le_exp_neg {x : ℝ} (hx : 1 ≤ x) :
    2 * Real.exp (-2 * x) ≤ Real.exp (-x) := by
  have htwo_exp_one : (2 : ℝ) < Real.exp 1 := by
    exact lt_trans (by norm_num) Real.exp_one_gt_d9
  have htwo_le_exp : (2 : ℝ) ≤ Real.exp x := by
    have hexp_mono : Real.exp 1 ≤ Real.exp x := by
      exact (Real.exp_le_exp).2 hx
    exact le_trans htwo_exp_one.le hexp_mono
  calc
    2 * Real.exp (-2 * x) ≤ Real.exp x * Real.exp (-2 * x) := by
          exact mul_le_mul_of_nonneg_right htwo_le_exp (by positivity)
    _ = Real.exp (-x) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- The small-regime heavy-tail choice gives the desired quadratic mgf decay. -/
lemma smallRegime_heavyTail_mgf_le {σ R t : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hR_pos : 0 < R) (ht : 1 ≤ t) :
    let D : ℝ := gammaSigmaHeavyTailRoundedConst σ
    let B : ℝ := gammaSigmaHeavyTailConst σ
    let l : ℝ := t / (4 * Real.sqrt D * Real.sqrt R)
    Real.exp (-l * (B * Real.sqrt R * t) + R * (l ^ (2 : ℕ) * D))
      ≤ Real.exp (-2 * t ^ σ) := by
  let D : ℝ := gammaSigmaHeavyTailRoundedConst σ
  let B : ℝ := gammaSigmaHeavyTailConst σ
  let l : ℝ := t / (4 * Real.sqrt D * Real.sqrt R)
  have hD_pos : 0 < D := by
    simpa [D] using gammaSigmaHeavyTailRoundedConst_pos (σ := σ) hσ₀
  have hsqrtD_pos : 0 < Real.sqrt D := Real.sqrt_pos.2 hD_pos
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have hsqrtR_pos : 0 < Real.sqrt R := Real.sqrt_pos.2 hR_pos
  have hsqrtR_sq : (Real.sqrt R) ^ (2 : ℕ) = R := by
    simpa [pow_two] using Real.sq_sqrt hR_nonneg
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have htpow_sigma_le_two : t ^ σ ≤ t ^ (2 : ℝ) := by
    have hσ_two : σ ≤ 2 := by linarith
    exact Real.rpow_le_rpow_of_exponent_le ht hσ_two
  apply (Real.exp_le_exp).2
  have hB_eq : B = 16 * Real.sqrt D := by
    dsimp [B, D, gammaSigmaHeavyTailConst]
  have hla : l * (B * Real.sqrt R * t) = 4 * t ^ (2 : ℕ) := by
    rw [hB_eq]
    dsimp [l]
    field_simp [hsqrtR_pos.ne', hsqrtD_pos.ne', pow_two]
    ring_nf
  have hquad : R * (l ^ (2 : ℕ) * D) = t ^ (2 : ℕ) / 16 := by
    dsimp [l]
    field_simp [hsqrtR_pos.ne', hsqrtD_pos.ne', pow_two]
    rw [hsqrtR_sq, Real.sq_sqrt hD_pos.le]
    ring_nf
  have hexpr :
      -l * (B * Real.sqrt R * t) + R * (l ^ (2 : ℕ) * D) =
        -(4 * t ^ (2 : ℕ)) + t ^ (2 : ℕ) / 16 := by
    calc
      -l * (B * Real.sqrt R * t) + R * (l ^ (2 : ℕ) * D)
          = -(l * (B * Real.sqrt R * t)) + R * (l ^ (2 : ℕ) * D) := by ring
      _ = -(4 * t ^ (2 : ℕ)) + t ^ (2 : ℕ) / 16 := by rw [hla, hquad]
  calc
    -l * (B * Real.sqrt R * t) + R * (l ^ (2 : ℕ) * D)
      = -(4 * t ^ (2 : ℕ)) + t ^ (2 : ℕ) / 16 := hexpr
    _ ≤ -(2 : ℝ) * t ^ (2 : ℕ) := by
          have ht_sq_nonneg : 0 ≤ t ^ (2 : ℕ) := by positivity
          calc
            -(4 * t ^ (2 : ℕ)) + t ^ (2 : ℕ) / 16
                = -(2 : ℝ) * t ^ (2 : ℕ) - ((31 : ℝ) / 16) * t ^ (2 : ℕ) := by
                  ring
            _ ≤ -(2 : ℝ) * t ^ (2 : ℕ) :=
                sub_le_self _ (mul_nonneg (by norm_num) ht_sq_nonneg)
    _ ≤ -(2 : ℝ) * t ^ σ := by
          have hscaled :
              (2 : ℝ) * t ^ σ ≤ (2 : ℝ) * t ^ (2 : ℝ) := by
            exact mul_le_mul_of_nonneg_left htpow_sigma_le_two (by positivity)
          have hneg := neg_le_neg hscaled
          simpa [two_mul, Real.rpow_natCast] using hneg

/-- The small-regime heavy-tail cutoff gives the desired tail decay for the
union term. -/
lemma smallRegime_heavyTail_union_le {σ R t : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hR_pos : 0 < R) (hR_one : 1 ≤ R) (ht : 1 ≤ t)
    (hsmall : t ≤ R ^ (σ / (2 * (2 - σ)))) :
    let D : ℝ := gammaSigmaHeavyTailRoundedConst σ
    let L : ℝ := ((2 * Real.sqrt D) * (Real.sqrt R / t)) ^ (1 / (1 - σ))
    R * Real.exp (-(L ^ σ)) ≤ Real.exp (-2 * t ^ σ) := by
  let D : ℝ := gammaSigmaHeavyTailRoundedConst σ
  let q : ℝ := σ / (1 - σ)
  let L : ℝ := ((2 * Real.sqrt D) * (Real.sqrt R / t)) ^ (1 / (1 - σ))
  have hD_pos : 0 < D := by
    simpa [D] using gammaSigmaHeavyTailRoundedConst_pos (σ := σ) hσ₀
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have hsqrtR_pos : 0 < Real.sqrt R := Real.sqrt_pos.2 hR_pos
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have htpow_sigma_le_two : t ^ σ ≤ t ^ (2 : ℝ) := by
    have hσ_two : σ ≤ 2 := by linarith
    exact Real.rpow_le_rpow_of_exponent_le ht hσ_two
  let x : ℝ := (Real.sqrt R / t) ^ q
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, q]
    positivity
  have hx_card :
      R ^ (σ / (2 - σ)) ≤ x := by
    simpa [x, q] using
      smallRegime_cardPow_le_gammaSigmaTailPower (σ := σ) (R := R) (t := t)
        hσ₀ hσ₁ hR_pos ht_pos hsmall
  have hx_tpow : t ^ σ ≤ x := by
    have hx_sq :
        t ^ (2 : ℝ) ≤ x := by
      simpa [x, q] using
        smallRegime_sq_le_gammaSigmaTailPower (σ := σ) (R := R) (t := t)
          hσ₀ hσ₁ hR_pos ht_pos hsmall
    exact le_trans htpow_sigma_le_two hx_sq
  have hLpow :
      L ^ σ = gammaSigmaHeavyTailUnionConst σ * x := by
    have hq_eq : (1 / (1 - σ)) * σ = q := by
      dsimp [q]
      field_simp [sub_ne_zero.mpr hσ₁.ne.symm]
    calc
      L ^ σ
        = ((((2 * Real.sqrt D) * (Real.sqrt R / t)) ^ (1 / (1 - σ))) ^ σ) := by
            rfl
      _ = (((2 * Real.sqrt D) * (Real.sqrt R / t)) ^ ((1 / (1 - σ)) * σ)) := by
            rw [← Real.rpow_mul (show 0 ≤ (2 * Real.sqrt D) * (Real.sqrt R / t) by positivity)]
      _ = (((2 * Real.sqrt D) * (Real.sqrt R / t)) ^ q) := by rw [hq_eq]
      _ = (2 * Real.sqrt D) ^ q * (Real.sqrt R / t) ^ q := by
            rw [Real.mul_rpow (by positivity) (by positivity)]
      _ = gammaSigmaHeavyTailUnionConst σ * x := by
            dsimp [D, x, gammaSigmaHeavyTailUnionConst]
  have hrewrite :
      R * Real.exp (-(L ^ σ)) =
        R * Real.exp (-(gammaSigmaHeavyTailUnionConst σ * x)) := by
    simpa using congrArg (fun y => R * Real.exp (-y)) hLpow
  calc
    R * Real.exp (-(L ^ σ))
      = R * Real.exp (-(gammaSigmaHeavyTailUnionConst σ * x)) := hrewrite
    _
      ≤ Real.exp (-2 * x) := by
          exact card_mul_exp_neg_gammaSigmaHeavyTailUnionConst_mul_le_exp_neg_two_mul
            (σ := σ) (R := R) (x := x) hσ₀ hσ₁ hR_one hx_nonneg hx_card
    _ ≤ Real.exp (-2 * t ^ σ) := by
          apply (Real.exp_le_exp).2
          have hscaled : (2 : ℝ) * t ^ σ ≤ (2 : ℝ) * x :=
            mul_le_mul_of_nonneg_left hx_tpow (by norm_num)
          simpa [mul_comm, mul_left_comm, mul_assoc] using neg_le_neg hscaled

/-- Small-regime one-sided heavy-tail concentration for centered independent
unit-scale `O_{Γ_σ}` summands. -/
theorem measureReal_upperTailEvent_finset_sum_le_exp_neg_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_lt_one_unit_smallRegime
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ t : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hs : s.Nonempty)
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) 1)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (ht : 1 ≤ t)
    (hsmall : t ≤ (s.card : ℝ) ^ (σ / (2 * (2 - σ)))) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω)
      (gammaSigmaHeavyTailConst σ * Real.sqrt (s.card : ℝ) * t)) ≤
      Real.exp (-(t ^ σ)) := by
  let R : ℝ := s.card
  let D : ℝ := gammaSigmaHeavyTailRoundedConst σ
  let B : ℝ := gammaSigmaHeavyTailConst σ
  let q : ℝ := σ / (1 - σ)
  have hR_pos : 0 < R := by
    dsimp [R]
    exact_mod_cast hs.card_pos
  have hR_one : 1 ≤ R := by
    dsimp [R]
    exact_mod_cast (Nat.succ_le_of_lt hs.card_pos)
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have hsqrtR_pos : 0 < Real.sqrt R := Real.sqrt_pos.2 hR_pos
  have hsqrtR_nonneg : 0 ≤ Real.sqrt R := hsqrtR_pos.le
  have hsqrtR_sq : (Real.sqrt R) ^ (2 : ℕ) = R := by
    simpa [pow_two] using Real.sq_sqrt hR_nonneg
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
  have htpow_sigma_le_two : t ^ σ ≤ t ^ (2 : ℝ) := by
    have hσ_two : σ ≤ 2 := by linarith
    exact Real.rpow_le_rpow_of_exponent_le ht hσ_two
  let l : ℝ := t / (4 * Real.sqrt D * Real.sqrt R)
  let L : ℝ := ((2 * Real.sqrt D) * (Real.sqrt R / t)) ^ (1 / (1 - σ))
  let x : ℝ := (Real.sqrt R / t) ^ q
  have hl_nonneg : 0 ≤ l := by
    dsimp [l]
    positivity
  have hγ_le_half : σ / (2 * (2 - σ)) ≤ (1 / 2 : ℝ) := by
    have hden_pos : 0 < 2 * (2 - σ) := by
      exact mul_pos (by norm_num) (by linarith)
    refine (div_le_iff₀ hden_pos).2 ?_
    linarith
  have ht_le_sqrtR : t ≤ Real.sqrt R := by
    calc
      t ≤ R ^ (σ / (2 * (2 - σ))) := by simpa [R] using hsmall
      _ ≤ R ^ (1 / 2 : ℝ) := by
            exact Real.rpow_le_rpow_of_exponent_le hR_one hγ_le_half
      _ = Real.sqrt R := by rw [Real.sqrt_eq_rpow]
  have hl_half : l ≤ 1 / 2 := by
    dsimp [l]
    have hbound :
        t / (4 * Real.sqrt D * Real.sqrt R) ≤
          Real.sqrt R / (4 * Real.sqrt D * Real.sqrt R) := by
      gcongr
    have hcancel :
        Real.sqrt R / (4 * Real.sqrt D * Real.sqrt R) =
          1 / (4 * Real.sqrt D) := by
      field_simp [hsqrtR_pos.ne']
    calc
      l = t / (4 * Real.sqrt D * Real.sqrt R) := rfl
      _ ≤ Real.sqrt R / (4 * Real.sqrt D * Real.sqrt R) := hbound
      _ = 1 / (4 * Real.sqrt D) := hcancel
      _ ≤ 1 / 2 := by
            have hden : (8 : ℝ) ≤ 4 * Real.sqrt D := by
              calc
                (8 : ℝ) = 4 * 2 := by norm_num
                _ ≤ 4 * Real.sqrt D :=
                    mul_le_mul_of_nonneg_left hsqrtD_two (by norm_num)
            have hinv : 1 / (4 * Real.sqrt D) ≤ 1 / (8 : ℝ) := by
              exact one_div_le_one_div_of_le (by positivity : 0 < (8 : ℝ)) hden
            exact hinv.trans (by norm_num)
  have hl_one : l ≤ 1 := by linarith
  have hL_one : 1 ≤ L := by
    have hratio_one : 1 ≤ Real.sqrt R / t := by
      have htmp : t / t ≤ Real.sqrt R / t := by
        exact div_le_div_of_nonneg_right ht_le_sqrtR ht_nonneg
      simpa [ht_pos.ne'] using htmp
    have hbase_one : 1 ≤ (2 * Real.sqrt D) * (Real.sqrt R / t) := by
      have hleft : (1 : ℝ) ≤ 2 * Real.sqrt D := by
        calc
          (1 : ℝ) ≤ 4 := by norm_num
          _ = 2 * 2 := by norm_num
          _ ≤ 2 * Real.sqrt D := mul_le_mul_of_nonneg_left hsqrtD_two (by norm_num)
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (2 * Real.sqrt D) * (Real.sqrt R / t) :=
            mul_le_mul hleft hratio_one zero_le_one (le_trans zero_le_one hleft)
    have hexp_nonneg : 0 ≤ 1 / (1 - σ) := by
      have hone_sub_pos : 0 < 1 - σ := sub_pos.mpr hσ₁
      positivity
    dsimp [L]
    exact Real.one_le_rpow hbase_one hexp_nonneg
  have hlL_eq : (1 / 2) * L ^ (σ - 1) = l := by
    calc
      (1 / 2) * L ^ (σ - 1)
        = (1 / 2) * ((((2 * Real.sqrt D) * (Real.sqrt R / t)) ^ (1 / (1 - σ))) ^ (σ - 1)) := by
            rfl
      _ = (1 / 2) * (((2 * Real.sqrt D) * (Real.sqrt R / t)) ^ ((1 / (1 - σ)) * (σ - 1))) := by
            rw [← Real.rpow_mul (show 0 ≤ (2 * Real.sqrt D) * (Real.sqrt R / t) by positivity)]
      _ = (1 / 2) * (((2 * Real.sqrt D) * (Real.sqrt R / t)) ^ (-1 : ℝ)) := by
            congr 2
            field_simp [sub_ne_zero.mpr hσ₁.ne.symm]
            ring
      _ = (1 / 2) * (t / (2 * Real.sqrt D * Real.sqrt R)) := by
            rw [Real.rpow_neg_one]
            field_simp [ht_pos.ne', hsqrtD_pos.ne', hsqrtR_pos.ne']
      _ = l := by
            dsimp [l]
            ring
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
    simpa [D, B, l] using
      smallRegime_heavyTail_mgf_le (σ := σ) (R := R) (t := t) hσ₀ hσ₁ hR_pos ht
  have hunion :
      R * Real.exp (-(L ^ σ)) ≤ Real.exp (-2 * t ^ σ) := by
    simpa [D, q, L] using
      smallRegime_heavyTail_union_le (σ := σ) (R := R) (t := t)
        hσ₀ hσ₁ hR_pos hR_one ht (by simpa [R] using hsmall)
  calc
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω)
      (gammaSigmaHeavyTailConst σ * Real.sqrt (s.card : ℝ) * t))
      = μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (B * Real.sqrt R * t)) := by
          simp [B, R]
    _ ≤ Real.exp (-l * (B * Real.sqrt R * t) + R * (l ^ (2 : ℕ) * D)) +
          R * Real.exp (-(L ^ σ)) := htail
    _ ≤ Real.exp (-2 * t ^ σ) + Real.exp (-2 * t ^ σ) := by
          exact add_le_add hmgf hunion
    _ = 2 * Real.exp (-2 * t ^ σ) := by ring
    _ ≤ Real.exp (-(t ^ σ)) := by
          exact two_mul_exp_neg_two_mul_le_exp_neg
            (x := t ^ σ) (Real.one_le_rpow ht hσ₀.le)
end

end IndependentSums

end Homogenization
