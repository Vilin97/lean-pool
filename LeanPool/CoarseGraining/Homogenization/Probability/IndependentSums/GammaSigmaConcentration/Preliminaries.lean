/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.GammaSigmaExpRegime
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.PsiConcentration

/-! # Preliminaries -/

@[expose] public section

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- Explicit upper bound for the Chapter 4 tail integral
`∫_1^∞ t e^{-t^σ} dt`. We use the full `(0, ∞)` Gamma-integral value because
it is simpler to package and still sufficient for the generic heavy-tail
backend. -/
noncomputable def gammaSigmaTailIntegralConst (σ : ℝ) : ℝ :=
  (1 / σ) * Real.Gamma (2 / σ)

/-- Explicit logarithmic-control constant for the `Γ_σ` specialization. -/
noncomputable def gammaSigmaLogControlConst (σ : ℝ) : ℝ :=
  Real.exp (32 / σ ^ (2 : ℕ))

/-- Rounded scalar constant appearing in the specialized `Γ_σ` heavy-tail mgf
bound after feeding `gammaSigmaTailIntegralConst` and
`gammaSigmaLogControlConst` into the generic rounded backend. -/
noncomputable def gammaSigmaHeavyTailRoundedConst (σ : ℝ) : ℝ :=
  3 + gammaSigmaLogControlConst σ + gammaSigmaTailIntegralConst σ

/-- Auxiliary union-term constant for the corrected small-`σ` Chapter 4
concentration split. -/
noncomputable def gammaSigmaHeavyTailUnionConst (σ : ℝ) : ℝ :=
  (2 * Real.sqrt (gammaSigmaHeavyTailRoundedConst σ)) ^ (σ / (1 - σ))

/-- Explicit one-sided `sqrt(card)` scale for the heavy-tail `Γ_σ`
concentration theorem on the range `σ ∈ (0, 1)`. -/
noncomputable def gammaSigmaHeavyTailConst (σ : ℝ) : ℝ :=
  16 * Real.sqrt (gammaSigmaHeavyTailRoundedConst σ)

/-- Symmetric `sqrt(card)` scale for the heavy-tail `Γ_σ` concentration theorem
on the range `σ ∈ (0, 1)`. The factor `2^(1/σ)` absorbs the two-sided tail
union. -/
noncomputable def gammaSigmaHeavyTailEndpointConst (σ : ℝ) : ℝ :=
  (2 : ℝ) ^ (1 / σ) * gammaSigmaHeavyTailConst σ

lemma gammaSigmaTailIntegralConst_nonneg {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ gammaSigmaTailIntegralConst σ := by
  dsimp [gammaSigmaTailIntegralConst]
  exact mul_nonneg (by positivity) (Real.Gamma_nonneg_of_nonneg (by positivity))

lemma gammaSigmaHeavyTailRoundedConst_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < gammaSigmaHeavyTailRoundedConst σ := by
  have hlog_one : 1 ≤ gammaSigmaLogControlConst σ := by
    have hnonneg : 0 ≤ 32 / σ ^ (2 : ℕ) := by
      exact div_nonneg (by positivity) (pow_two_nonneg σ)
    simpa [gammaSigmaLogControlConst] using Real.one_le_exp hnonneg
  dsimp [gammaSigmaHeavyTailRoundedConst]
  nlinarith [gammaSigmaTailIntegralConst_nonneg hσ, hlog_one]

lemma one_le_gammaSigmaLogControlConst (σ : ℝ) :
    1 ≤ gammaSigmaLogControlConst σ := by
  have hnonneg : 0 ≤ 32 / σ ^ (2 : ℕ) := by
    exact div_nonneg (by positivity) (pow_two_nonneg σ)
  simpa [gammaSigmaLogControlConst] using Real.one_le_exp hnonneg

lemma two_add_two_div_le_gammaSigmaHeavyTailUnionConst
    {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
    2 + 2 / σ ≤ gammaSigmaHeavyTailUnionConst σ := by
  let D : ℝ := gammaSigmaHeavyTailRoundedConst σ
  let q : ℝ := σ / (1 - σ)
  have hD_pos : 0 < D := by
    simpa [D] using gammaSigmaHeavyTailRoundedConst_pos (σ := σ) hσ₀
  have hD_ge_log : gammaSigmaLogControlConst σ ≤ D := by
    dsimp [D, gammaSigmaHeavyTailRoundedConst]
    nlinarith [gammaSigmaTailIntegralConst_nonneg (σ := σ) hσ₀,
      one_le_gammaSigmaLogControlConst σ]
  have hσ_ne : σ ≠ 0 := hσ₀.ne'
  have hone_sub_ne : 1 - σ ≠ 0 := sub_ne_zero.mpr hσ₁.ne.symm
  have hq_pos : 0 < q := by
    dsimp [q]
    have hone_sub_pos : 0 < 1 - σ := sub_pos.mpr hσ₁
    exact div_pos hσ₀ hone_sub_pos
  have hsqrt_lower : Real.exp (16 / σ ^ (2 : ℕ)) ≤ Real.sqrt D := by
    calc
      Real.exp (16 / σ ^ (2 : ℕ))
          = Real.sqrt (gammaSigmaLogControlConst σ) := by
              rw [gammaSigmaLogControlConst, Real.sqrt_eq_rpow]
              rw [show (16 / σ ^ (2 : ℕ)) = (32 / σ ^ (2 : ℕ)) * (1 / 2 : ℝ) by
                    field_simp [hσ_ne]
                    ring]
              rw [Real.exp_mul]
      _ ≤ Real.sqrt D := Real.sqrt_le_sqrt hD_ge_log
  have hbase_lower : Real.exp (16 / σ ^ (2 : ℕ)) ≤ 2 * Real.sqrt D := by
    calc
      Real.exp (16 / σ ^ (2 : ℕ)) ≤ Real.sqrt D := hsqrt_lower
      _ ≤ 2 * Real.sqrt D := by nlinarith [Real.sqrt_nonneg D]
  have hunion_lower :
      Real.exp (16 / (σ * (1 - σ))) ≤ gammaSigmaHeavyTailUnionConst σ := by
    calc
      Real.exp (16 / (σ * (1 - σ)))
          = (Real.exp (16 / σ ^ (2 : ℕ))) ^ q := by
              dsimp [q]
              rw [← Real.exp_mul]
              congr 1
              field_simp [hσ_ne, hone_sub_ne]
      _ ≤ (2 * Real.sqrt D) ^ q := by
            exact Real.rpow_le_rpow (by positivity) hbase_lower hq_pos.le
      _ = gammaSigmaHeavyTailUnionConst σ := by
            rfl
  have hone_inv : 1 ≤ 1 / σ := by
    simpa [one_div] using (one_le_inv₀ hσ₀).2 hσ₁.le
  have htwo_le_exp : (2 : ℝ) ≤ Real.exp (1 / σ) := by
    have htwo_exp_one : (2 : ℝ) < Real.exp 1 := by
      exact lt_trans (by norm_num) Real.exp_one_gt_d9
    exact le_trans htwo_exp_one.le ((Real.exp_le_exp).2 hone_inv)
  have hone_add_le_exp : 1 + 1 / σ ≤ Real.exp (1 / σ) := by
    simpa [add_comm] using Real.add_one_le_exp (1 / σ)
  have htwo_add_le_exp : 2 + 2 / σ ≤ Real.exp (2 / σ) := by
    calc
      2 + 2 / σ = 2 * (1 + 1 / σ) := by ring
      _ ≤ Real.exp (1 / σ) * Real.exp (1 / σ) := by
            gcongr
      _ = Real.exp (2 / σ) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have hexp_mono :
      Real.exp (2 / σ) ≤ Real.exp (16 / (σ * (1 - σ))) := by
    have hone_sub_pos : 0 < 1 - σ := sub_pos.mpr hσ₁
    have hone_sub_inv : 1 ≤ (1 - σ)⁻¹ := by
      have hone_sub_le_one : 1 - σ ≤ 1 := by linarith
      exact (one_le_inv₀ hone_sub_pos).2 hone_sub_le_one
    have hineq :
        2 / σ ≤ 16 / (σ * (1 - σ)) := by
      have htwo_sixteen : (2 : ℝ) ≤ 16 := by norm_num
      calc
        2 / σ = 2 * (1 / σ) := by ring
        _ ≤ 16 * (1 / σ) := by
              exact mul_le_mul_of_nonneg_right htwo_sixteen (by positivity)
        _ = (16 * (1 / σ)) * 1 := by ring
        _ ≤ (16 * (1 / σ)) * (1 - σ)⁻¹ := by
              gcongr
        _ = 16 / (σ * (1 - σ)) := by
              field_simp [hσ_ne, hone_sub_ne]
    exact (Real.exp_le_exp).2 hineq
  exact htwo_add_le_exp.trans (le_trans hexp_mono hunion_lower)

/-- The concrete logarithmic control from the Chapter 4 notes, with an explicit
choice of constant that is convenient in Lean. -/
theorem four_mul_log_le_half_rpow_add_log_gammaSigmaLogControlConst
    {σ t : ℝ} (hσ : 0 < σ) (ht : 1 ≤ t) :
    4 * Real.log t ≤ (1 / 2) * t ^ σ + Real.log (gammaSigmaLogControlConst σ) := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hσ_half : 0 < σ / 2 := by positivity
  have hlog :
      Real.log t ≤ t ^ (σ / 2) / (σ / 2) := by
    exact Real.log_le_rpow_div ht0 hσ_half
  have hlog' : 4 * Real.log t ≤ (8 / σ) * t ^ (σ / 2) := by
    have hσ_ne : σ ≠ 0 := hσ.ne'
    have hlog'' : Real.log t ≤ (2 / σ) * t ^ (σ / 2) := by
      have hrewrite : t ^ (σ / 2) / (σ / 2) = (2 / σ) * t ^ (σ / 2) := by
        field_simp [hσ_ne]
      rw [hrewrite] at hlog
      exact hlog
    have hscaled := mul_le_mul_of_nonneg_left hlog'' (by positivity : 0 ≤ (4 : ℝ))
    ring_nf at hscaled ⊢
    exact hscaled
  have hpow : (t ^ (σ / 2)) ^ (2 : ℕ) = t ^ σ := by
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul ht0]
    ring_nf
  have hquad : (8 / σ) * t ^ (σ / 2) ≤ (1 / 2) * t ^ σ + 32 / σ ^ (2 : ℕ) := by
    have hσ_ne : σ ≠ 0 := hσ.ne'
    let u : ℝ := t ^ (σ / 2)
    have hsquare : 0 ≤ (σ * u - 8) ^ (2 : ℕ) := by
      dsimp [u]
      positivity
    have hu_sq : u ^ (2 : ℕ) = t ^ σ := by
      dsimp [u]
      exact hpow
    have hquad' : 16 * σ * u ≤ σ ^ (2 : ℕ) * t ^ σ + 64 := by
      have htmp := hsquare
      rw [pow_two] at htmp
      ring_nf at htmp
      rw [hu_sq] at htmp
      nlinarith
    calc
      (8 / σ) * t ^ (σ / 2)
          = (16 * σ * u) / (2 * σ ^ (2 : ℕ)) := by
              dsimp [u]
              field_simp [hσ_ne]
              ring
      _ ≤ (σ ^ (2 : ℕ) * t ^ σ + 64) / (2 * σ ^ (2 : ℕ)) := by
            exact div_le_div_of_nonneg_right hquad' (by positivity)
      _ = (1 / 2) * t ^ σ + 32 / σ ^ (2 : ℕ) := by
            field_simp [hσ_ne]
            ring
  have hmain :
      4 * Real.log t ≤ (1 / 2) * t ^ σ + 32 / σ ^ (2 : ℕ) := by
    exact hlog'.trans hquad
  simpa [gammaSigmaLogControlConst] using hmain

/-- The `Γ_σ` tail integral on `(1, ∞)` is controlled by the explicit Gamma
constant `gammaSigmaTailIntegralConst σ`. -/
theorem lintegral_Ioi_one_gammaSigma_le_gammaSigmaTailIntegralConst
    {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / gammaSigma σ t) ∂volume ≤
      ENNReal.ofReal (gammaSigmaTailIntegralConst σ) := by
  have hmono :
      ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / gammaSigma σ t) ∂volume ≤
        ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t / gammaSigma σ t) ∂volume := by
    refine lintegral_mono_set ?_
    intro t ht
    simpa using (lt_trans zero_lt_one ht)
  have hInt :
      IntegrableOn (fun t : ℝ => t * Real.exp (-(t ^ σ))) (Set.Ioi 0) volume := by
    convert
      (integrableOn_rpow_mul_exp_neg_rpow_of_pos (σ := σ) (p := 2) hσ (by norm_num : 0 < (2 : ℝ)))
        using 1
    ext t
    rw [show (2 : ℝ) - 1 = (1 : ℝ) by norm_num, Real.rpow_one]
  have hNonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi 0)] fun t : ℝ => t * Real.exp (-(t ^ σ)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro t ht
    exact mul_nonneg (le_of_lt ht) (by positivity)
  have hLin :
      ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t * Real.exp (-(t ^ σ))) ∂volume =
        ENNReal.ofReal (gammaSigmaTailIntegralConst σ) := by
    have hEq :
        ENNReal.ofReal (∫ t in Set.Ioi 0, t * Real.exp (-(t ^ σ)) ∂volume) =
          ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t * Real.exp (-(t ^ σ))) ∂volume := by
      simpa [IntegrableOn] using
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (μ := volume.restrict (Set.Ioi (0 : ℝ))) hInt hNonneg)
    have hIntEq :
        ∫ t in Set.Ioi 0, t * Real.exp (-(t ^ σ)) ∂volume =
          gammaSigmaTailIntegralConst σ := by
      have harg : (1 + 1) / σ = 2 / σ := by
        ring
      simpa [gammaSigmaTailIntegralConst, harg] using
        (integral_rpow_mul_exp_neg_rpow hσ (by norm_num : -1 < (1 : ℝ)))
    rw [← hEq]
    rw [hIntEq]
  calc
    ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / gammaSigma σ t) ∂volume
      ≤ ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t / gammaSigma σ t) ∂volume := hmono
    _ = ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t * Real.exp (-(t ^ σ))) ∂volume := by
          congr with t
          simp [gammaSigma, div_eq_mul_inv, ← Real.exp_neg]
    _ = ENNReal.ofReal (gammaSigmaTailIntegralConst σ) := hLin

/-- If `λ ≤ (1/2) L^(σ - 1)` and `1 ≤ t ≤ L`, then the deterministic part of
the `Γ_σ` logarithmic kernel constraint holds. -/
theorem gammaSigma_log_constraint
    {σ l L t : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hlL : l ≤ (1 / 2) * L ^ (σ - 1))
    (ht : t ∈ Set.Icc 1 L) :
    l * t ≤ Real.log (gammaSigma σ t) - 4 * Real.log t +
      Real.log (gammaSigmaLogControlConst σ) := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht.1
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one (le_trans ht.1 ht.2)
  have hanti := Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (show σ - 1 ≤ 0 by linarith)
  have hpow_mono : L ^ (σ - 1) ≤ t ^ (σ - 1) := by
    exact hanti (show t ∈ Set.Ioi (0 : ℝ) by exact ht_pos)
      (show L ∈ Set.Ioi (0 : ℝ) by exact hL_pos) ht.2
  have hlt : l * t ≤ (1 / 2) * t ^ σ := by
    calc
      l * t ≤ ((1 / 2) * L ^ (σ - 1)) * t := by
            gcongr
      _ ≤ ((1 / 2) * t ^ (σ - 1)) * t := by
            have hscaled : (1 / 2 : ℝ) * L ^ (σ - 1) ≤ (1 / 2 : ℝ) * t ^ (σ - 1) := by
              exact mul_le_mul_of_nonneg_left hpow_mono (by positivity)
            exact mul_le_mul_of_nonneg_right hscaled ht0
      _ = (1 / 2) * t ^ σ := by
            rw [show ((1 / 2 : ℝ) * t ^ (σ - 1)) * t = (1 / 2 : ℝ) * (t ^ (σ - 1) * t) by ring]
            congr 1
            calc
              t ^ (σ - 1) * t = t ^ (σ - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
              _ = t ^ σ := by
                    rw [← Real.rpow_add ht_pos]
                    congr 1
                    ring
  have hlog :=
    four_mul_log_le_half_rpow_add_log_gammaSigmaLogControlConst (σ := σ) (t := t) hσ₀ ht.1
  have hmain : l * t ≤ t ^ σ - 4 * Real.log t + Real.log (gammaSigmaLogControlConst σ) := by
    nlinarith
  simpa [gammaSigma] using hmain

lemma smallRegime_sq_le_gammaSigmaTailPower
    {σ R t : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hR_pos : 0 < R) (ht_pos : 0 < t)
    (hsmall : t ≤ R ^ (σ / (2 * (2 - σ)))) :
    t ^ (2 : ℝ) ≤ (Real.sqrt R / t) ^ (σ / (1 - σ)) := by
  let q : ℝ := σ / (1 - σ)
  let γ : ℝ := σ / (2 * (2 - σ))
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have htwo_sub_ne : 2 - σ ≠ 0 := by linarith
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    have hone_sub_pos : 0 < 1 - σ := sub_pos.mpr hσ₁
    exact div_nonneg hσ₀.le hone_sub_pos.le
  have hgamma_q_two : γ * (q + 2) = q / 2 := by
    have hone_sub_ne : 1 - σ ≠ 0 := sub_ne_zero.mpr hσ₁.ne.symm
    dsimp [γ, q]
    field_simp [hone_sub_ne, htwo_sub_ne]
    nlinarith
  have hq_two :
      t ^ (q + 2) ≤ R ^ (q / 2) := by
    calc
      t ^ (q + 2) ≤ (R ^ γ) ^ (q + 2) := by
            exact Real.rpow_le_rpow ht_nonneg hsmall (by positivity)
      _ = R ^ (γ * (q + 2)) := by
            rw [← Real.rpow_mul hR_nonneg]
      _ = R ^ (q / 2) := by rw [hgamma_q_two]
  have htq_pos : 0 < t ^ q := Real.rpow_pos_of_pos ht_pos q
  have hpow_add : t ^ (2 : ℝ) * t ^ q = t ^ (q + 2) := by
    rw [← Real.rpow_add ht_pos]
    congr 1
    ring
  have hdiv_eq :
      (Real.sqrt R / t) ^ q = R ^ (q / 2) / t ^ q := by
    calc
      (Real.sqrt R / t) ^ q = (Real.sqrt R) ^ q / t ^ q := by
            rw [Real.div_rpow (Real.sqrt_nonneg _) ht_nonneg]
      _ = R ^ (q / 2) / t ^ q := by
            congr 1
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR_nonneg]
            congr 1
            ring_nf
  rw [hdiv_eq]
  have hmul : t ^ (2 : ℝ) * t ^ q ≤ R ^ (q / 2) := by
    rw [hpow_add]
    exact hq_two
  exact (le_div_iff₀ htq_pos).2 hmul

lemma smallRegime_cardPow_le_gammaSigmaTailPower
    {σ R t : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hR_pos : 0 < R) (ht_pos : 0 < t)
    (hsmall : t ≤ R ^ (σ / (2 * (2 - σ)))) :
    R ^ (σ / (2 - σ)) ≤ (Real.sqrt R / t) ^ (σ / (1 - σ)) := by
  let q : ℝ := σ / (1 - σ)
  let β : ℝ := σ / (2 - σ)
  let γ : ℝ := σ / (2 * (2 - σ))
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have htwo_sub_ne : 2 - σ ≠ 0 := by linarith
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    have hone_sub_pos : 0 < 1 - σ := sub_pos.mpr hσ₁
    exact div_nonneg hσ₀.le hone_sub_pos.le
  have hgamma_q : γ * q = q / 2 - β := by
    have hone_sub_ne : 1 - σ ≠ 0 := sub_ne_zero.mpr hσ₁.ne.symm
    dsimp [γ, q, β]
    field_simp [hone_sub_ne, htwo_sub_ne]
    nlinarith
  have htq_le :
      t ^ q ≤ R ^ (q / 2 - β) := by
    calc
      t ^ q ≤ (R ^ γ) ^ q := by
            exact Real.rpow_le_rpow ht_nonneg hsmall hq_nonneg
      _ = R ^ (γ * q) := by
            rw [← Real.rpow_mul hR_nonneg]
      _ = R ^ (q / 2 - β) := by rw [hgamma_q]
  have hβ_nonneg : 0 ≤ R ^ β := Real.rpow_nonneg hR_nonneg β
  have htq_pos : 0 < t ^ q := Real.rpow_pos_of_pos ht_pos q
  have hmul :
      R ^ β * t ^ q ≤ R ^ (q / 2) := by
    calc
      R ^ β * t ^ q ≤ R ^ β * R ^ (q / 2 - β) := by
            gcongr
      _ = R ^ (q / 2) := by
            rw [← Real.rpow_add hR_pos]
            congr 1
            ring
  have hdiv_eq :
      (Real.sqrt R / t) ^ q = R ^ (q / 2) / t ^ q := by
    calc
      (Real.sqrt R / t) ^ q = (Real.sqrt R) ^ q / t ^ q := by
            rw [Real.div_rpow (Real.sqrt_nonneg _) ht_nonneg]
      _ = R ^ (q / 2) / t ^ q := by
            congr 1
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR_nonneg]
            congr 1
            ring_nf
  rw [hdiv_eq]
  exact (le_div_iff₀ htq_pos).2 hmul

lemma largeRegime_cardPow_le_gammaSigmaScale
    {σ R t : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hR_pos : 0 < R) (ht_pos : 0 < t)
    (hlarge : R ^ (σ / (2 * (2 - σ))) ≤ t) :
    R ^ (σ / (2 - σ)) ≤ R ^ (σ / 2) * t ^ σ := by
  let γ : ℝ := σ / (2 * (2 - σ))
  let β : ℝ := σ / (2 - σ)
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have hσ_nonneg : 0 ≤ σ := hσ₀.le
  have htwo_sub_ne : 2 - σ ≠ 0 := by linarith
  have hgamma_sigma : σ / 2 + γ * σ = β := by
    dsimp [γ, β]
    field_simp [htwo_sub_ne]
    ring
  have hpow :
      R ^ (γ * σ) ≤ t ^ σ := by
    have hpow' : (R ^ γ) ^ σ ≤ t ^ σ := by
      exact Real.rpow_le_rpow (Real.rpow_nonneg hR_nonneg _) hlarge hσ_nonneg
    simpa [Real.rpow_mul hR_nonneg] using hpow'
  calc
    R ^ β = R ^ (σ / 2 + γ * σ) := by rw [hgamma_sigma]
    _ = R ^ (σ / 2) * R ^ (γ * σ) := by
          rw [Real.rpow_add hR_pos]
    _ ≤ R ^ (σ / 2) * t ^ σ := by
          gcongr

lemma largeRegime_correction_le_gammaSigmaScale
    {σ R t : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hR_pos : 0 < R) (ht_pos : 0 < t)
    (hlarge : R ^ (σ / (2 * (2 - σ))) ≤ t) :
    R ^ σ * t ^ (2 * σ - 2) ≤ R ^ (σ / 2) * t ^ σ := by
  let γ : ℝ := σ / (2 * (2 - σ))
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have htwo_sub_pos : 0 < 2 - σ := by linarith
  have htwo_sub_ne : 2 - σ ≠ 0 := by linarith
  have hR_half_le : R ^ (σ / 2) ≤ t ^ (2 - σ) := by
    calc
      R ^ (σ / 2) = (R ^ γ) ^ (2 - σ) := by
            dsimp [γ]
            rw [← Real.rpow_mul hR_nonneg]
            congr 1
            field_simp [htwo_sub_ne]
      _ ≤ t ^ (2 - σ) := by
            simpa [γ] using
              Real.rpow_le_rpow (Real.rpow_nonneg hR_nonneg _) hlarge htwo_sub_pos.le
  have hRσ : R ^ σ = R ^ (σ / 2) * R ^ (σ / 2) := by
    rw [← Real.rpow_add hR_pos]
    congr 1
    ring
  calc
    R ^ σ * t ^ (2 * σ - 2)
      = R ^ (σ / 2) * (R ^ (σ / 2) * t ^ (2 * σ - 2)) := by
          rw [hRσ]
          ring
    _ ≤ R ^ (σ / 2) * (t ^ (2 - σ) * t ^ (2 * σ - 2)) := by
          gcongr
    _ = R ^ (σ / 2) * t ^ σ := by
          congr 1
          rw [← Real.rpow_add ht_pos]
          congr 1
          ring


end

end IndependentSums

end Homogenization
