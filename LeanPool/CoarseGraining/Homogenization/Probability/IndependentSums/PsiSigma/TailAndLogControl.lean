/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.Triangle
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.PsiConcentration

/-! # Tail And Log Control -/

@[expose] public section

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

private lemma measurable_psiSigma_tail_integrand (σ : ℝ) :
    Measurable fun t : ℝ => t / psiSigma σ t := by
  unfold psiSigma
  measurability

private lemma psiSigma_pow_three_le_of_exp_three_mul_sq_le {σ t : ℝ}
    (hσ : 1 ≤ σ) (ht : Real.exp (3 * σ ^ (2 : ℕ)) ≤ t) :
    t ^ (3 : ℝ) ≤ psiSigma σ t := by
  have hσ_pos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  have hσsq_pos : 0 < σ ^ (2 : ℕ) := sq_pos_of_pos hσ_pos
  have hT_pos : 0 < Real.exp (3 * σ ^ (2 : ℕ)) := Real.exp_pos _
  have ht_pos : 0 < t := lt_of_lt_of_le hT_pos ht
  have hlogT :
      Real.log (Real.exp (3 * σ ^ (2 : ℕ))) ≤ Real.log t :=
    Real.log_le_log hT_pos ht
  have hlog_t_ge : 3 * σ ^ (2 : ℕ) ≤ Real.log t := by
    simpa [Real.log_exp] using hlogT
  have hlog_t_nonneg : 0 ≤ Real.log t := by
    exact le_trans (by positivity : 0 ≤ 3 * σ ^ (2 : ℕ)) hlog_t_ge
  have harg_le : t ≤ 1 + σ * t := by
    have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
    have hσt_ge_t : t ≤ σ * t := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hσ ht_nonneg
    linarith
  have harg_pos : 0 < 1 + σ * t := by
    linarith
  have hlog_le :
      Real.log t ≤ Real.log (1 + σ * t) :=
    Real.log_le_log ht_pos harg_le
  have hlog_arg_nonneg : 0 ≤ Real.log (1 + σ * t) := by
    exact le_trans hlog_t_nonneg hlog_le
  have hsq_le :
      (Real.log t) ^ (2 : ℕ) ≤ (Real.log (1 + σ * t)) ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ hlog_t_nonneg hlog_le 2
  have hmain :
      3 * Real.log t ≤
        (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ) := by
    have hfirst :
        3 * Real.log t ≤ (σ ^ (2 : ℕ))⁻¹ * (Real.log t) ^ (2 : ℕ) := by
      rw [le_inv_mul_iff₀ hσsq_pos]
      calc
        σ ^ (2 : ℕ) * (3 * Real.log t)
            = (3 * σ ^ (2 : ℕ)) * Real.log t := by ring
        _ ≤ Real.log t * Real.log t :=
            mul_le_mul_of_nonneg_right hlog_t_ge hlog_t_nonneg
        _ = (Real.log t) ^ (2 : ℕ) := by ring
    exact hfirst.trans (mul_le_mul_of_nonneg_left hsq_le (inv_nonneg.mpr (sq_nonneg σ)))
  have hexp : Real.exp (3 * Real.log t) ≤ psiSigma σ t := by
    simpa [psiSigma] using Real.exp_le_exp.2 hmain
  have hpoweq : Real.exp (3 * Real.log t) = t ^ (3 : ℝ) := by
    rw [mul_comm 3 (Real.log t), Real.exp_mul, Real.exp_log ht_pos]
  rwa [hpoweq] at hexp

private lemma psiSigma_tail_integrand_le_rpow_neg_two_of_exp_three_mul_sq_le
    {σ t : ℝ} (hσ : 1 ≤ σ) (ht : Real.exp (3 * σ ^ (2 : ℕ)) ≤ t) :
    t / psiSigma σ t ≤ t ^ (-2 : ℝ) := by
  have hT_pos : 0 < Real.exp (3 * σ ^ (2 : ℕ)) := Real.exp_pos _
  have ht_pos : 0 < t := lt_of_lt_of_le hT_pos ht
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  have hψ_lower : t ^ (3 : ℝ) ≤ psiSigma σ t :=
    psiSigma_pow_three_le_of_exp_three_mul_sq_le hσ ht
  have ht3_pos : 0 < t ^ (3 : ℝ) := Real.rpow_pos_of_pos ht_pos _
  calc
    t / psiSigma σ t ≤ t / t ^ (3 : ℝ) := by
      exact div_le_div_of_nonneg_left ht_nonneg ht3_pos hψ_lower
    _ = t ^ (-2 : ℝ) := by
      calc
        t / t ^ (3 : ℝ) = t ^ (1 : ℝ) / t ^ (3 : ℝ) := by
          rw [Real.rpow_one]
        _ = t ^ ((1 : ℝ) - 3) := by
          rw [Real.rpow_sub ht_pos (1 : ℝ) 3]
        _ = t ^ (-2 : ℝ) := by
          norm_num

/-- The log-normal tail-integral kernel is integrable on `(1, ∞)` for
`σ ≥ 1`. The proof is intentionally non-sharp: after the cutoff
`exp(3 σ^2)`, `Ψ_σ(t)` dominates `t^3`, so the kernel is bounded by `t⁻²`. -/
theorem integrableOn_Ioi_one_psiSigma_tail_integrand {σ : ℝ} (hσ : 1 ≤ σ) :
    IntegrableOn (fun t : ℝ => t / psiSigma σ t) (Set.Ioi 1) volume := by
  let T : ℝ := Real.exp (3 * σ ^ (2 : ℕ))
  have hT_pos : 0 < T := by
    positivity
  have hT : 1 ≤ T := by
    have hexp : 0 ≤ 3 * σ ^ (2 : ℕ) := by
      positivity
    simpa [T] using Real.one_le_exp hexp
  have hmeas_Ioc :
      AEStronglyMeasurable (fun t : ℝ => t / psiSigma σ t)
        (volume.restrict (Set.Ioc 1 T)) :=
    (measurable_psiSigma_tail_integrand σ).aestronglyMeasurable
  have hmeas_IoiT :
      AEStronglyMeasurable (fun t : ℝ => t / psiSigma σ t)
        (volume.restrict (Set.Ioi T)) :=
    (measurable_psiSigma_tail_integrand σ).aestronglyMeasurable
  have hcompact_id : IntegrableOn (fun t : ℝ => t) (Set.Ioc 1 T) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact intervalIntegral.intervalIntegrable_id
  have hcompact :
      IntegrableOn (fun t : ℝ => t / psiSigma σ t) (Set.Ioc 1 T) volume := by
    change Integrable (fun t : ℝ => t / psiSigma σ t) (volume.restrict (Set.Ioc 1 T))
    change Integrable (fun t : ℝ => t) (volume.restrict (Set.Ioc 1 T)) at hcompact_id
    refine hcompact_id.mono hmeas_Ioc ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have ht_nonneg : 0 ≤ t := le_trans zero_le_one (le_of_lt ht.1)
    have hψ_one : 1 ≤ psiSigma σ t := one_le_psiSigma
    have hψ_pos : 0 < psiSigma σ t := lt_of_lt_of_le zero_lt_one hψ_one
    have hdiv_nonneg : 0 ≤ t / psiSigma σ t := div_nonneg ht_nonneg hψ_pos.le
    have hdiv_le : t / psiSigma σ t ≤ t := by
      calc
        t / psiSigma σ t ≤ t / 1 := by
          exact div_le_div_of_nonneg_left ht_nonneg zero_lt_one hψ_one
        _ = t := by
          rw [div_one]
    simpa [Real.norm_eq_abs, abs_of_nonneg hdiv_nonneg, abs_of_nonneg ht_nonneg]
      using hdiv_le
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi T) volume :=
    integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hT_pos
  have htail :
      IntegrableOn (fun t : ℝ => t / psiSigma σ t) (Set.Ioi T) volume := by
    change Integrable (fun t : ℝ => t / psiSigma σ t) (volume.restrict (Set.Ioi T))
    change Integrable (fun t : ℝ => t ^ (-2 : ℝ)) (volume.restrict (Set.Ioi T)) at hpow
    refine hpow.mono hmeas_IoiT ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_ge : T ≤ t := le_of_lt ht
    have ht_pos : 0 < t := lt_of_lt_of_le hT_pos ht_ge
    have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
    have hle :=
      psiSigma_tail_integrand_le_rpow_neg_two_of_exp_three_mul_sq_le (σ := σ) hσ ht_ge
    have hdiv_nonneg : 0 ≤ t / psiSigma σ t :=
      div_nonneg ht_nonneg (Real.exp_pos _).le
    have hrpow_nonneg : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hdiv_nonneg, abs_of_nonneg hrpow_nonneg,
      abs_of_nonneg ht_nonneg, abs_of_nonneg (Real.exp_pos _).le] using hle
  have hsplit : Set.Ioi (1 : ℝ) = Set.Ioc (1 : ℝ) T ∪ Set.Ioi T := by
    exact (Set.Ioc_union_Ioi_eq_Ioi (a := (1 : ℝ)) (b := T) hT).symm
  rw [hsplit, integrableOn_union]
  exact ⟨hcompact, htail⟩

/-- A non-sharp finite constant for the `Ψ_σ` analytic tail-integral input. -/
noncomputable def psiSigmaTailIntegralConst (σ : ℝ) : ℝ :=
  (∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / psiSigma σ t) ∂volume).toReal

lemma psiSigmaTailIntegralConst_nonneg (σ : ℝ) :
    0 ≤ psiSigmaTailIntegralConst σ :=
  ENNReal.toReal_nonneg

/-- Note-facing discharge of the analytic `Ψ_σ` tail-integral hypothesis. -/
theorem lintegral_Ioi_one_psiSigma_le_psiSigmaTailIntegralConst {σ : ℝ}
    (hσ : 1 ≤ σ) :
    ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / psiSigma σ t) ∂volume ≤
      ENNReal.ofReal (psiSigmaTailIntegralConst σ) := by
  let f : ℝ → ℝ := fun t => t / psiSigma σ t
  have hmeas :
      AEStronglyMeasurable f (volume.restrict (Set.Ioi 1)) :=
    (measurable_psiSigma_tail_integrand σ).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi 1)] f := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro t ht
    exact div_nonneg (le_trans zero_le_one (le_of_lt ht)) (Real.exp_pos _).le
  have hfinite :
      (∫⁻ t, ENNReal.ofReal (f t) ∂(volume.restrict (Set.Ioi 1))) ≠ ⊤ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).2
      (integrableOn_Ioi_one_psiSigma_tail_integrand hσ)
  rw [psiSigmaTailIntegralConst]
  change (∫⁻ t, ENNReal.ofReal (f t) ∂(volume.restrict (Set.Ioi 1))) ≤
    ENNReal.ofReal
      ((∫⁻ t, ENNReal.ofReal (f t) ∂(volume.restrict (Set.Ioi 1))).toReal)
  rw [ENNReal.ofReal_toReal hfinite]

/-- A simple non-sharp logarithmic-control constant for the raw `Ψ_σ`
truncation-Chernoff theorem on the interval `[1, L]`. It is intentionally
allowed to depend on the Chernoff parameter `l` and cutoff `L`; later endpoint
optimization can replace this with a sharper `σ`-dependent package. -/
noncomputable def psiSigmaLogControlConst (l L : ℝ) : ℝ :=
  Real.exp (l * L + 4 * Real.log L)

lemma one_le_psiSigmaLogControlConst {l L : ℝ} (hl : 0 ≤ l) (hL : 1 ≤ L) :
    1 ≤ psiSigmaLogControlConst l L := by
  have hL_nonneg : 0 ≤ L := le_trans zero_le_one hL
  have hlogL_nonneg : 0 ≤ Real.log L := Real.log_nonneg hL
  have hexp_nonneg : 0 ≤ l * L + 4 * Real.log L := by
    exact add_nonneg (mul_nonneg hl hL_nonneg)
      (mul_nonneg (by norm_num) hlogL_nonneg)
  simpa [psiSigmaLogControlConst] using Real.one_le_exp hexp_nonneg

/-- A sharper reusable logarithmic-control constant for the optimized
`Ψ_σ` endpoint. If the optimizer can prove
`l t ≤ (1/2) log Ψ_σ(t) + C`, this constant absorbs the remaining polynomial
factor `t^4` in the raw Chernoff theorem. -/
noncomputable def psiSigmaPolynomialLogControlConst (σ C : ℝ) : ℝ :=
  Real.exp (C + 8 * σ ^ (2 : ℕ))

noncomputable def psiSigmaLogExponent (σ t : ℝ) : ℝ :=
  (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ)

noncomputable def psiSigmaIndependentSumRawConst (σ : ℝ) : ℝ :=
  3 + psiSigmaPolynomialLogControlConst σ (Real.exp 2) + psiSigmaTailIntegralConst σ

noncomputable def psiSigmaIndependentSumConst (σ : ℝ) : ℝ :=
  128 * Real.exp (σ ^ (2 : ℕ) / 2) *
    Real.sqrt (psiSigmaIndependentSumRawConst σ)

noncomputable def psiSigmaIndependentSumCutoff (σ R t : ℝ) : ℝ :=
  ((1 + σ * t) * Real.exp (σ * Real.sqrt (Real.log (4 * R))) - 1) / σ

noncomputable def psiSigmaIndependentSumLambda (σ R t : ℝ) : ℝ :=
  4 * (psiSigmaLogExponent σ t + Real.log 2) /
    (psiSigmaIndependentSumConst σ * Real.sqrt R * t)

lemma one_le_psiSigmaPolynomialLogControlConst {σ C : ℝ} (hC : 0 ≤ C) :
    1 ≤ psiSigmaPolynomialLogControlConst σ C := by
  have hexp_nonneg : 0 ≤ C + 8 * σ ^ (2 : ℕ) := by
    exact add_nonneg hC (mul_nonneg (by norm_num) (sq_nonneg σ))
  simpa [psiSigmaPolynomialLogControlConst] using Real.one_le_exp hexp_nonneg

lemma one_le_psiSigmaIndependentSumRawConst (σ : ℝ) :
    1 ≤ psiSigmaIndependentSumRawConst σ := by
  have hpoly : 1 ≤ psiSigmaPolynomialLogControlConst σ (Real.exp 2) :=
    one_le_psiSigmaPolynomialLogControlConst (Real.exp_pos 2).le
  have htail : 0 ≤ psiSigmaTailIntegralConst σ :=
    psiSigmaTailIntegralConst_nonneg σ
  dsimp [psiSigmaIndependentSumRawConst]
  linarith

lemma psiSigmaIndependentSumRawConst_pos (σ : ℝ) :
    0 < psiSigmaIndependentSumRawConst σ :=
  lt_of_lt_of_le zero_lt_one (one_le_psiSigmaIndependentSumRawConst σ)

lemma psiSigmaIndependentSumConst_pos (σ : ℝ) :
    0 < psiSigmaIndependentSumConst σ := by
  have hraw : 0 < Real.sqrt (psiSigmaIndependentSumRawConst σ) :=
    Real.sqrt_pos.2 (psiSigmaIndependentSumRawConst_pos σ)
  dsimp [psiSigmaIndependentSumConst]
  positivity

lemma one_add_mul_psiSigmaIndependentSumCutoff {σ R t : ℝ}
    (hσ : σ ≠ 0) :
    1 + σ * psiSigmaIndependentSumCutoff σ R t =
      (1 + σ * t) * Real.exp (σ * Real.sqrt (Real.log (4 * R))) := by
  dsimp [psiSigmaIndependentSumCutoff]
  field_simp [hσ]
  ring

lemma one_le_psiSigmaIndependentSumCutoff {σ R t : ℝ}
    (hσ : 1 ≤ σ) (hR : 1 ≤ R) (ht : 1 ≤ t) :
    1 ≤ psiSigmaIndependentSumCutoff σ R t := by
  have hσ_pos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  have hR_nonneg : 0 ≤ R := le_trans zero_le_one hR
  have hlog_nonneg : 0 ≤ Real.log (4 * R) := by
    have hfourR : 1 ≤ 4 * R := by
      calc
        (1 : ℝ) ≤ 4 := by norm_num
        _ = 4 * 1 := by ring
        _ ≤ 4 * R := mul_le_mul_of_nonneg_left hR (by norm_num)
    exact Real.log_nonneg hfourR
  have hexp_one : 1 ≤ Real.exp (σ * Real.sqrt (Real.log (4 * R))) := by
    exact Real.one_le_exp (mul_nonneg hσ_pos.le (Real.sqrt_nonneg _))
  have harg :
      1 + σ * t ≤
        (1 + σ * t) * Real.exp (σ * Real.sqrt (Real.log (4 * R))) := by
    have harg_nonneg : 0 ≤ 1 + σ * t := by positivity
    simpa [mul_one] using mul_le_mul_of_nonneg_left hexp_one harg_nonneg
  have hcut :=
    one_add_mul_psiSigmaIndependentSumCutoff (σ := σ) (R := R) (t := t) hσ_pos.ne'
  rw [← hcut] at harg
  have hmul : σ * t ≤ σ * psiSigmaIndependentSumCutoff σ R t := by linarith
  exact ht.trans (le_of_mul_le_mul_left hmul hσ_pos)

lemma psiSigmaIndependentSumCutoff_union_log {σ R t : ℝ}
    (hσ : 1 ≤ σ) (hR : 1 ≤ R) (ht : 1 ≤ t) :
    Real.log (2 * R) +
        ((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ) +
          Real.log 2) ≤
      (σ ^ (2 : ℕ))⁻¹ *
        (Real.log (1 + σ * psiSigmaIndependentSumCutoff σ R t)) ^ (2 : ℕ) := by
  have hσ_pos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  have hσsq_pos : 0 < σ ^ (2 : ℕ) := by positivity
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hfourR_pos : 0 < 4 * R := by positivity
  have htwoR_pos : 0 < 2 * R := by positivity
  let A : ℝ := Real.log (4 * R)
  let a : ℝ := Real.log (1 + σ * t)
  have hA_nonneg : 0 ≤ A := by
    have hfourR : 1 ≤ 4 * R := by
      calc
        (1 : ℝ) ≤ 4 := by norm_num
        _ = 4 * 1 := by ring
        _ ≤ 4 * R := mul_le_mul_of_nonneg_left hR (by norm_num)
    exact Real.log_nonneg hfourR
  have ha_nonneg : 0 ≤ a := by
    have harg : 1 ≤ 1 + σ * t :=
      le_add_of_nonneg_right (mul_nonneg hσ_pos.le (le_trans zero_le_one ht))
    exact Real.log_nonneg harg
  have hcut :
      1 + σ * psiSigmaIndependentSumCutoff σ R t =
        (1 + σ * t) * Real.exp (σ * Real.sqrt A) := by
    simpa [A] using
      one_add_mul_psiSigmaIndependentSumCutoff (σ := σ) (R := R) (t := t) hσ_pos.ne'
  have hlog_cut :
      Real.log (1 + σ * psiSigmaIndependentSumCutoff σ R t) =
        a + σ * Real.sqrt A := by
    rw [hcut]
    have harg_pos : 0 < 1 + σ * t := by positivity
    rw [Real.log_mul harg_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlog_four :
      Real.log (2 * R) + Real.log 2 = A := by
    calc
      Real.log (2 * R) + Real.log 2 = Real.log ((2 * R) * 2) := by
        rw [Real.log_mul htwoR_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
      _ = A := by
        congr 1
        ring
  have hquad :
      (σ ^ (2 : ℕ))⁻¹ * a ^ (2 : ℕ) + A ≤
        (σ ^ (2 : ℕ))⁻¹ * (a + σ * Real.sqrt A) ^ (2 : ℕ) := by
    have hsqrt_sq : (Real.sqrt A) ^ (2 : ℕ) = A := by
      rw [Real.sq_sqrt hA_nonneg]
    field_simp [hσsq_pos.ne']
    conv_lhs => rw [← hsqrt_sq]
    ring_nf
    have hcross : 0 ≤ a * (σ * Real.sqrt A) :=
      mul_nonneg ha_nonneg (mul_nonneg hσ_pos.le (Real.sqrt_nonneg A))
    linarith
  rw [hlog_cut]
  calc
    Real.log (2 * R) + ((σ ^ (2 : ℕ))⁻¹ * a ^ (2 : ℕ) + Real.log 2)
        = (σ ^ (2 : ℕ))⁻¹ * a ^ (2 : ℕ) + A := by
          rw [← hlog_four]
          ring
    _ ≤ (σ ^ (2 : ℕ))⁻¹ * (a + σ * Real.sqrt A) ^ (2 : ℕ) := hquad

lemma exp_mul_sqrt_log_four_mul_le {σ R : ℝ}
    (hσ : 1 ≤ σ) (hR : 1 ≤ R) :
    Real.exp (σ * Real.sqrt (Real.log (4 * R))) ≤
      2 * Real.exp (σ ^ (2 : ℕ) / 2) * Real.sqrt R := by
  have hσ_nonneg : 0 ≤ σ := le_trans zero_le_one hσ
  have hR_nonneg : 0 ≤ R := le_trans zero_le_one hR
  have hfourR_pos : 0 < 4 * R := by positivity
  let A : ℝ := Real.log (4 * R)
  have hA_nonneg : 0 ≤ A := by
    have hfourR : 1 ≤ 4 * R := by
      calc
        (1 : ℝ) ≤ 4 := by norm_num
        _ = 4 * 1 := by ring
        _ ≤ 4 * R := mul_le_mul_of_nonneg_left hR (by norm_num)
    exact Real.log_nonneg hfourR
  have hyoung : σ * Real.sqrt A ≤ σ ^ (2 : ℕ) / 2 + A / 2 := by
    have hsqrt_sq : (Real.sqrt A) ^ (2 : ℕ) = A := by
      rw [Real.sq_sqrt hA_nonneg]
    have hdiff : 0 ≤ σ ^ (2 : ℕ) / 2 + A / 2 - σ * Real.sqrt A := by
      calc
        0 ≤ (σ - Real.sqrt A) ^ (2 : ℕ) / 2 :=
          div_nonneg (sq_nonneg _) (by norm_num)
        _ = σ ^ (2 : ℕ) / 2 + (Real.sqrt A) ^ (2 : ℕ) / 2 -
              σ * Real.sqrt A := by
          ring
        _ = σ ^ (2 : ℕ) / 2 + A / 2 - σ * Real.sqrt A := by
          rw [hsqrt_sq]
    exact sub_nonneg.mp hdiff
  have hexp :=
    Real.exp_le_exp.2 hyoung
  have hhalf :
      Real.exp (A / 2) = Real.sqrt (4 * R) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hfourR_pos]
    congr 1
    ring
  have hsqrt_four : Real.sqrt (4 * R) = 2 * Real.sqrt R := by
    have hleft_nonneg : 0 ≤ 4 * R := by positivity
    have hright_nonneg : 0 ≤ 2 * Real.sqrt R := by positivity
    rw [Real.sqrt_eq_iff_eq_sq hleft_nonneg hright_nonneg]
    rw [mul_pow, Real.sq_sqrt hR_nonneg]
    norm_num
  calc
    Real.exp (σ * Real.sqrt (Real.log (4 * R)))
        = Real.exp (σ * Real.sqrt A) := by simp [A]
    _ ≤ Real.exp (σ ^ (2 : ℕ) / 2 + A / 2) := hexp
    _ = Real.exp (σ ^ (2 : ℕ) / 2) * Real.exp (A / 2) := by
          rw [Real.exp_add]
    _ = 2 * Real.exp (σ ^ (2 : ℕ) / 2) * Real.sqrt R := by
          rw [hhalf, hsqrt_four]
          ring

lemma psiSigmaIndependentSumCutoff_le_four_mul_exp_mul_sqrt_mul {σ R t : ℝ}
    (hσ : 1 ≤ σ) (hR : 1 ≤ R) (ht : 1 ≤ t) :
    psiSigmaIndependentSumCutoff σ R t ≤
      4 * Real.exp (σ ^ (2 : ℕ) / 2) * Real.sqrt R * t := by
  have hσ_pos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht
  have harg_bound : 1 + σ * t ≤ 2 * σ * t := by
    have hone_le_σt : (1 : ℝ) ≤ σ * t := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ σ * t := mul_le_mul hσ ht zero_le_one hσ_pos.le
    linarith
  have hexp_bound :=
    exp_mul_sqrt_log_four_mul_le (σ := σ) (R := R) hσ hR
  calc
    psiSigmaIndependentSumCutoff σ R t
        ≤ ((1 + σ * t) *
            Real.exp (σ * Real.sqrt (Real.log (4 * R)))) / σ := by
          dsimp [psiSigmaIndependentSumCutoff]
          rw [div_le_div_iff₀ hσ_pos hσ_pos]
          linarith
    _ ≤ (2 * σ * t *
            (2 * Real.exp (σ ^ (2 : ℕ) / 2) * Real.sqrt R)) / σ := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul harg_bound hexp_bound (by positivity) (by positivity))
            hσ_pos.le
    _ = 4 * Real.exp (σ ^ (2 : ℕ) / 2) * Real.sqrt R * t := by
          field_simp [hσ_pos.ne']
          ring

lemma eight_mul_psiSigmaIndependentSumCutoff_le_const_mul_sqrt_mul {σ R t : ℝ}
    (hσ : 1 ≤ σ) (hR : 1 ≤ R) (ht : 1 ≤ t) :
    8 * psiSigmaIndependentSumCutoff σ R t ≤
      psiSigmaIndependentSumConst σ * Real.sqrt R * t := by
  have hcut :=
    psiSigmaIndependentSumCutoff_le_four_mul_exp_mul_sqrt_mul
      (σ := σ) (R := R) (t := t) hσ hR ht
  have hraw_sqrt : 1 ≤ Real.sqrt (psiSigmaIndependentSumRawConst σ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (one_le_psiSigmaIndependentSumRawConst σ)
  have hnonneg : 0 ≤ Real.exp (σ ^ (2 : ℕ) / 2) * Real.sqrt R * t := by
    positivity
  calc
    8 * psiSigmaIndependentSumCutoff σ R t
        ≤ 8 * (4 * Real.exp (σ ^ (2 : ℕ) / 2) * Real.sqrt R * t) := by
          exact mul_le_mul_of_nonneg_left hcut (by norm_num)
    _ ≤ psiSigmaIndependentSumConst σ * Real.sqrt R * t := by
          dsimp [psiSigmaIndependentSumConst]
          have hfactor :
              (32 : ℝ) ≤ 128 * Real.sqrt (psiSigmaIndependentSumRawConst σ) := by
            calc
              (32 : ℝ) ≤ 128 * 1 := by norm_num
              _ ≤ 128 * Real.sqrt (psiSigmaIndependentSumRawConst σ) :=
                mul_le_mul_of_nonneg_left hraw_sqrt (by norm_num)
          have hmul := mul_le_mul_of_nonneg_right hfactor hnonneg
          calc
            8 * (4 * Real.exp (σ ^ (2 : ℕ) / 2) * Real.sqrt R * t)
                = 32 * (Real.exp (σ ^ (2 : ℕ) / 2) * Real.sqrt R * t) := by
                  ring
            _ ≤ (128 * Real.sqrt (psiSigmaIndependentSumRawConst σ)) *
                  (Real.exp (σ ^ (2 : ℕ) / 2) * Real.sqrt R * t) := hmul
            _ = 128 * Real.exp (σ ^ (2 : ℕ) / 2) *
                  Real.sqrt (psiSigmaIndependentSumRawConst σ) * Real.sqrt R * t := by
                  ring

lemma four_mul_log_le_half_log_psiSigma_add_const {σ t : ℝ}
    (hσ : 1 ≤ σ) (ht : 1 ≤ t) :
    4 * Real.log t ≤
      (1 / 2 : ℝ) * Real.log (psiSigma σ t) + 8 * σ ^ (2 : ℕ) := by
  have hσ_pos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  have hσsq_pos : 0 < σ ^ (2 : ℕ) := sq_pos_of_pos hσ_pos
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have harg_le : t ≤ 1 + σ * t := by
    have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht
    have hσt_ge_t : t ≤ σ * t := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hσ ht_nonneg
    linarith
  have hlog_le : Real.log t ≤ Real.log (1 + σ * t) :=
    Real.log_le_log ht_pos harg_le
  have hlogt_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlogarg_nonneg : 0 ≤ Real.log (1 + σ * t) := by
    exact le_trans hlogt_nonneg hlog_le
  have hsq_le :
      (Real.log t) ^ (2 : ℕ) ≤ (Real.log (1 + σ * t)) ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ hlogt_nonneg hlog_le 2
  have hquad :
      4 * Real.log t ≤
        (Real.log t) ^ (2 : ℕ) / (2 * σ ^ (2 : ℕ)) + 8 * σ ^ (2 : ℕ) := by
    let s : ℝ := σ ^ (2 : ℕ)
    have hs_pos : 0 < s := by
      simpa [s] using hσsq_pos
    have hsq_nonneg : 0 ≤ (Real.log t - 4 * s) ^ (2 : ℕ) := sq_nonneg _
    have hsq_expand :
        (Real.log t - 4 * s) ^ (2 : ℕ) =
          (Real.log t) ^ (2 : ℕ) - 8 * s * Real.log t + 16 * s ^ (2 : ℕ) := by
      ring
    have hquad : 8 * s * Real.log t ≤ (Real.log t) ^ (2 : ℕ) + 16 * s ^ (2 : ℕ) := by
      rw [hsq_expand] at hsq_nonneg
      linarith
    have hrewrite :
        (Real.log t) ^ (2 : ℕ) / (2 * s) + 8 * s =
          ((Real.log t) ^ (2 : ℕ) + 16 * s ^ (2 : ℕ)) / (2 * s) := by
      field_simp [hs_pos.ne']
      ring
    change 4 * Real.log t ≤ (Real.log t) ^ (2 : ℕ) / (2 * s) + 8 * s
    rw [hrewrite]
    rw [le_div_iff₀ (show 0 < 2 * s by positivity)]
    linarith
  have hhalf_le :
      (Real.log t) ^ (2 : ℕ) / (2 * σ ^ (2 : ℕ)) ≤
        (Real.log (1 + σ * t)) ^ (2 : ℕ) / (2 * σ ^ (2 : ℕ)) := by
    exact div_le_div_of_nonneg_right hsq_le (by positivity : 0 ≤ 2 * σ ^ (2 : ℕ))
  have hmain :
      4 * Real.log t ≤
        (Real.log (1 + σ * t)) ^ (2 : ℕ) / (2 * σ ^ (2 : ℕ)) +
          8 * σ ^ (2 : ℕ) := by
    calc
      4 * Real.log t ≤
          (Real.log t) ^ (2 : ℕ) / (2 * σ ^ (2 : ℕ)) + 8 * σ ^ (2 : ℕ) := hquad
      _ = 8 * σ ^ (2 : ℕ) + (Real.log t) ^ (2 : ℕ) / (2 * σ ^ (2 : ℕ)) := by
            ring
      _ ≤ 8 * σ ^ (2 : ℕ) +
            (Real.log (1 + σ * t)) ^ (2 : ℕ) / (2 * σ ^ (2 : ℕ)) :=
            add_le_add_right hhalf_le (8 * σ ^ (2 : ℕ))
      _ = (Real.log (1 + σ * t)) ^ (2 : ℕ) / (2 * σ ^ (2 : ℕ)) +
            8 * σ ^ (2 : ℕ) := by ring
  have hrewrite :
      (1 / 2 : ℝ) * Real.log (psiSigma σ t) =
        (Real.log (1 + σ * t)) ^ (2 : ℕ) / (2 * σ ^ (2 : ℕ)) := by
    rw [psiSigma, Real.log_exp]
    field_simp [hσsq_pos.ne']
  rwa [hrewrite]

lemma log_sq_le_four_mul_self_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ (2 : ℕ) ≤ 4 * x := by
  have hx_nonneg : 0 ≤ x := le_trans zero_le_one hx
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog_le : Real.log x ≤ 2 * Real.sqrt x := by
    have h := Real.log_le_rpow_div hx_nonneg (by norm_num : (0 : ℝ) < 1 / 2)
    simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_assoc, mul_comm] using h
  have hsq := mul_le_mul hlog_le hlog_le hlog_nonneg (by positivity : 0 ≤ 2 * Real.sqrt x)
  calc
    (Real.log x) ^ (2 : ℕ) ≤ (2 * Real.sqrt x) ^ (2 : ℕ) := by
      simpa [pow_two] using hsq
    _ = 4 * x := by
      rw [mul_pow, Real.sq_sqrt hx_nonneg]
      ring

lemma psiSigma_log_exponent_le_eight_mul_self {σ t : ℝ}
    (hσ : 1 ≤ σ) (ht : 1 ≤ t) :
    (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ) ≤ 8 * t := by
  have hσ_pos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  have hσsq_pos : 0 < σ ^ (2 : ℕ) := by positivity
  have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht
  have harg_one : 1 ≤ 1 + σ * t :=
    le_add_of_nonneg_right (mul_nonneg hσ_pos.le ht_nonneg)
  have hlogsq :
      (Real.log (1 + σ * t)) ^ (2 : ℕ) ≤ 4 * (1 + σ * t) :=
    log_sq_le_four_mul_self_of_one_le harg_one
  have hσ_le_sq : σ ≤ σ ^ (2 : ℕ) := by
    calc
      σ = σ * 1 := by ring
      _ ≤ σ * σ := mul_le_mul_of_nonneg_left hσ hσ_pos.le
      _ = σ ^ (2 : ℕ) := by ring
  have harg_bound : 4 * (1 + σ * t) ≤ 8 * (σ ^ (2 : ℕ) * t) := by
    have hone_le_σt : (1 : ℝ) ≤ σ * t := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ σ * t := mul_le_mul hσ ht zero_le_one hσ_pos.le
    have harg_le : 1 + σ * t ≤ 2 * (σ * t) := by linarith
    have hσt_le : σ * t ≤ σ ^ (2 : ℕ) * t :=
      mul_le_mul_of_nonneg_right hσ_le_sq ht_nonneg
    calc
      4 * (1 + σ * t) ≤ 4 * (2 * (σ * t)) :=
        mul_le_mul_of_nonneg_left harg_le (by norm_num)
      _ = 8 * (σ * t) := by ring
      _ ≤ 8 * (σ ^ (2 : ℕ) * t) :=
        mul_le_mul_of_nonneg_left hσt_le (by norm_num)
  calc
    (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ)
        ≤ (σ ^ (2 : ℕ))⁻¹ * (8 * (σ ^ (2 : ℕ) * t)) := by
          exact mul_le_mul_of_nonneg_left (hlogsq.trans harg_bound)
            (inv_nonneg.mpr (sq_nonneg σ))
    _ = 8 * t := by
          field_simp [hσsq_pos.ne']

lemma psiSigma_log_exponent_add_log_two_le_nine_mul_self {σ t : ℝ}
    (hσ : 1 ≤ σ) (ht : 1 ≤ t) :
    (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ) + Real.log 2 ≤
      9 * t := by
  have hq := psiSigma_log_exponent_le_eight_mul_self (σ := σ) (t := t) hσ ht
  have hlog_two : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  calc
    (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ) + Real.log 2
        ≤ 8 * t + 1 := add_le_add hq hlog_two
    _ ≤ 8 * t + t := by
          calc
            8 * t + 1 = 1 + 8 * t := by ring
            _ ≤ t + 8 * t := add_le_add_left ht (8 * t)
            _ = 8 * t + t := by ring
    _ = 9 * t := by ring

lemma psiSigmaIndependentSumLambda_nonneg {σ R t : ℝ}
    (_hσ : 1 ≤ σ) (hR : 1 ≤ R) (ht : 1 ≤ t) :
    0 ≤ psiSigmaIndependentSumLambda σ R t := by
  have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht
  have hR_nonneg : 0 ≤ R := le_trans zero_le_one hR
  have hq_nonneg : 0 ≤ psiSigmaLogExponent σ t := by
    dsimp [psiSigmaLogExponent]
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg σ)) (sq_nonneg _)
  have hlog_two_nonneg : 0 ≤ Real.log 2 :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hnum_nonneg : 0 ≤ 4 * (psiSigmaLogExponent σ t + Real.log 2) := by
    exact mul_nonneg (by norm_num) (add_nonneg hq_nonneg hlog_two_nonneg)
  have hden_nonneg :
      0 ≤ psiSigmaIndependentSumConst σ * Real.sqrt R * t := by
    exact mul_nonneg
      (mul_nonneg (psiSigmaIndependentSumConst_pos σ).le (Real.sqrt_nonneg R))
      ht_nonneg
  dsimp [psiSigmaIndependentSumLambda]
  exact div_nonneg hnum_nonneg hden_nonneg

lemma psiSigmaIndependentSumLambda_le_one {σ R t : ℝ}
    (hσ : 1 ≤ σ) (hR : 1 ≤ R) (ht : 1 ≤ t) :
    psiSigmaIndependentSumLambda σ R t ≤ 1 := by
  let Q : ℝ := psiSigmaLogExponent σ t + Real.log 2
  let B : ℝ := psiSigmaIndependentSumConst σ * Real.sqrt R
  have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hQ_le : Q ≤ 9 * t := by
    dsimp [Q, psiSigmaLogExponent]
    exact psiSigma_log_exponent_add_log_two_le_nine_mul_self (σ := σ) (t := t) hσ ht
  have hExp_one : 1 ≤ Real.exp (σ ^ (2 : ℕ) / 2) := by
    exact Real.one_le_exp (by positivity)
  have hraw_one : 1 ≤ Real.sqrt (psiSigmaIndependentSumRawConst σ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (one_le_psiSigmaIndependentSumRawConst σ)
  have hsqrtR_one : 1 ≤ Real.sqrt R := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hR
  have hprod1 :
      1 ≤ Real.exp (σ ^ (2 : ℕ) / 2) *
          Real.sqrt (psiSigmaIndependentSumRawConst σ) := by
    simpa using
      mul_le_mul hExp_one hraw_one (by norm_num : (0 : ℝ) ≤ 1)
        (le_trans zero_le_one hExp_one)
  have hprod2 :
      1 ≤ Real.exp (σ ^ (2 : ℕ) / 2) *
          Real.sqrt (psiSigmaIndependentSumRawConst σ) * Real.sqrt R := by
    simpa [mul_assoc] using
      mul_le_mul hprod1 hsqrtR_one (by norm_num : (0 : ℝ) ≤ 1)
        (le_trans zero_le_one hprod1)
  have hB_ge : 36 ≤ B := by
    have h128_le : 128 ≤ B := by
      dsimp [B, psiSigmaIndependentSumConst]
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hprod2 (by norm_num : (0 : ℝ) ≤ 128)
    exact (by norm_num : (36 : ℝ) ≤ 128).trans h128_le
  have hB_pos : 0 < B := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 36) hB_ge
  have hnum_le : 4 * Q ≤ B * t := by
    have h4Q : 4 * Q ≤ 36 * t := by
      calc
        4 * Q ≤ 4 * (9 * t) := mul_le_mul_of_nonneg_left hQ_le (by norm_num)
        _ = 36 * t := by ring
    have h36 : 36 * t ≤ B * t := mul_le_mul_of_nonneg_right hB_ge ht_nonneg
    exact h4Q.trans h36
  dsimp [psiSigmaIndependentSumLambda, Q, B]
  rw [div_le_iff₀ (mul_pos hB_pos ht_pos)]
  simpa [Q, B, mul_assoc] using hnum_le

lemma psiSigmaIndependentSumLambda_le_half_cutoff_logExponent_div {σ R t : ℝ}
    (hσ : 1 ≤ σ) (hR : 1 ≤ R) (ht : 1 ≤ t) :
    psiSigmaIndependentSumLambda σ R t ≤
      (1 / 2 : ℝ) *
        (psiSigmaLogExponent σ (psiSigmaIndependentSumCutoff σ R t) /
          psiSigmaIndependentSumCutoff σ R t) := by
  let Q : ℝ := psiSigmaLogExponent σ t + Real.log 2
  let B : ℝ := psiSigmaIndependentSumConst σ * Real.sqrt R
  let L : ℝ := psiSigmaIndependentSumCutoff σ R t
  let qL : ℝ := psiSigmaLogExponent σ L
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hL_one : 1 ≤ L := by
    simpa [L] using
      one_le_psiSigmaIndependentSumCutoff (σ := σ) (R := R) (t := t) hσ hR ht
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_one
  have hB_pos : 0 < B := by
    dsimp [B]
    exact mul_pos (psiSigmaIndependentSumConst_pos σ)
      (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hR))
  have h8 : 8 * L ≤ B * t := by
    simpa [B, L] using
      eight_mul_psiSigmaIndependentSumCutoff_le_const_mul_sqrt_mul
        (σ := σ) (R := R) (t := t) hσ hR ht
  have hcoef : 4 / (B * t) ≤ 1 / (2 * L) := by
    rw [div_le_div_iff₀ (mul_pos hB_pos ht_pos) (mul_pos (by norm_num) hL_pos)]
    calc
      4 * (2 * L) = 8 * L := by ring
      _ ≤ B * t := h8
      _ = 1 * (B * t) := by ring
  have hQ_nonneg : 0 ≤ Q := by
    have hq_nonneg : 0 ≤ psiSigmaLogExponent σ t := by
      dsimp [psiSigmaLogExponent]
      positivity
    have hlog_two_nonneg : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    dsimp [Q]
    exact add_nonneg hq_nonneg hlog_two_nonneg
  have hQ_le_qL : Q ≤ qL := by
    have hunion :=
      psiSigmaIndependentSumCutoff_union_log (σ := σ) (R := R) (t := t) hσ hR ht
    have hlog_nonneg : 0 ≤ Real.log (2 * R) := by
      have htwoR : 1 ≤ 2 * R := by
        calc
          (1 : ℝ) ≤ 2 := by norm_num
          _ = 2 * 1 := by ring
          _ ≤ 2 * R := mul_le_mul_of_nonneg_left hR (by norm_num)
      exact Real.log_nonneg htwoR
    calc
      Q ≤ Real.log (2 * R) + Q := by
        exact (le_add_of_nonneg_left hlog_nonneg : Q ≤ Real.log (2 * R) + Q)
      _ ≤ qL := by
        simpa [Q, qL, psiSigmaLogExponent, add_assoc, add_comm, add_left_comm] using hunion
  calc
    psiSigmaIndependentSumLambda σ R t
        = Q * (4 / (B * t)) := by
          dsimp [psiSigmaIndependentSumLambda, Q, B, psiSigmaLogExponent]
          ring
    _ ≤ Q * (1 / (2 * L)) := by
          exact mul_le_mul_of_nonneg_left hcoef hQ_nonneg
    _ ≤ qL * (1 / (2 * L)) := by
          exact mul_le_mul_of_nonneg_right hQ_le_qL (by positivity)
    _ = (1 / 2 : ℝ) * (qL / L) := by
          field_simp [hL_pos.ne']

lemma psiSigmaIndependentSumLambda_mgf_log {σ R t : ℝ}
    (hσ : 1 ≤ σ) (hR : 1 ≤ R) (ht : 1 ≤ t) :
    Real.log 2 + (psiSigmaLogExponent σ t + Real.log 2) +
        R * (psiSigmaIndependentSumLambda σ R t ^ (2 : ℕ) *
          psiSigmaIndependentSumRawConst σ) ≤
      psiSigmaIndependentSumLambda σ R t *
        ((psiSigmaIndependentSumConst σ * Real.sqrt R) * t) := by
  let Q : ℝ := psiSigmaLogExponent σ t + Real.log 2
  let D : ℝ := psiSigmaIndependentSumRawConst σ
  let B : ℝ := psiSigmaIndependentSumConst σ * Real.sqrt R
  let l : ℝ := psiSigmaIndependentSumLambda σ R t
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hR_nonneg : 0 ≤ R := le_trans zero_le_one hR
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hD_pos : 0 < D := by
    dsimp [D]
    exact psiSigmaIndependentSumRawConst_pos σ
  have hD_nonneg : 0 ≤ D := hD_pos.le
  have hB_pos : 0 < B := by
    dsimp [B]
    exact mul_pos (psiSigmaIndependentSumConst_pos σ)
      (Real.sqrt_pos.2 hR_pos)
  have hC_pos : 0 < psiSigmaIndependentSumConst σ :=
    psiSigmaIndependentSumConst_pos σ
  have hQ_nonneg : 0 ≤ Q := by
    have hq_nonneg : 0 ≤ psiSigmaLogExponent σ t := by
      dsimp [psiSigmaLogExponent]
      positivity
    have hlog_two_nonneg : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    dsimp [Q]
    exact add_nonneg hq_nonneg hlog_two_nonneg
  have hQ_le : Q ≤ 9 * t := by
    dsimp [Q, psiSigmaLogExponent]
    exact psiSigma_log_exponent_add_log_two_le_nine_mul_self (σ := σ) (t := t) hσ ht
  have hlog_two_le_Q : Real.log 2 ≤ Q := by
    have hq_nonneg : 0 ≤ psiSigmaLogExponent σ t := by
      dsimp [psiSigmaLogExponent]
      positivity
    dsimp [Q]
    exact (le_add_of_nonneg_left hq_nonneg :
      Real.log 2 ≤ psiSigmaLogExponent σ t + Real.log 2)
  have hlBt : l * (B * t) = 4 * Q := by
    dsimp [l, B, Q, psiSigmaIndependentSumLambda]
    field_simp [hB_pos.ne', hC_pos.ne', ht_pos.ne']
  have hvar_le_Q : R * (l ^ (2 : ℕ) * D) ≤ Q := by
    have hQ_le_big : Q ≤ 1024 * t ^ (2 : ℕ) := by
      have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht
      have ht_le_sq : t ≤ t ^ (2 : ℕ) := by
        calc
          t = t * 1 := by ring
          _ ≤ t * t := mul_le_mul_of_nonneg_left ht ht_nonneg
          _ = t ^ (2 : ℕ) := by ring
      calc
        Q ≤ 9 * t := hQ_le
        _ ≤ 1024 * t := mul_le_mul_of_nonneg_right (by norm_num : (9 : ℝ) ≤ 1024) ht_nonneg
        _ ≤ 1024 * t ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left ht_le_sq (by norm_num)
    have hvar_eq :
        R * (l ^ (2 : ℕ) * D) =
          (Q ^ (2 : ℕ)) /
            (1024 * (Real.exp (σ ^ (2 : ℕ) / 2)) ^ (2 : ℕ) * t ^ (2 : ℕ)) := by
      subst D
      dsimp [l, B, Q, psiSigmaIndependentSumLambda, psiSigmaIndependentSumConst]
      field_simp [hR_pos.ne', (psiSigmaIndependentSumRawConst_pos σ).ne',
        hC_pos.ne', ht_pos.ne',
        (Real.exp_pos (σ ^ (2 : ℕ) / 2)).ne']
      rw [Real.sq_sqrt hR_nonneg,
        Real.sq_sqrt (psiSigmaIndependentSumRawConst_pos σ).le]
      ring_nf
    rw [hvar_eq]
    have hden_ge : 1024 * (Real.exp (σ ^ (2 : ℕ) / 2)) ^ (2 : ℕ) * t ^ (2 : ℕ) ≥
        Q := by
      have hexp_sq_one : 1 ≤ (Real.exp (σ ^ (2 : ℕ) / 2)) ^ (2 : ℕ) := by
        have hone : 1 ≤ Real.exp (σ ^ (2 : ℕ) / 2) := Real.one_le_exp (by positivity)
        exact one_le_pow₀ hone
      have hbase_nonneg : 0 ≤ 1024 * t ^ (2 : ℕ) := by positivity
      have hbase_le :
          1024 * t ^ (2 : ℕ) ≤
            1024 * (Real.exp (σ ^ (2 : ℕ) / 2)) ^ (2 : ℕ) * t ^ (2 : ℕ) := by
        calc
          1024 * t ^ (2 : ℕ) = 1 * (1024 * t ^ (2 : ℕ)) := by ring
          _ ≤ (Real.exp (σ ^ (2 : ℕ) / 2)) ^ (2 : ℕ) *
              (1024 * t ^ (2 : ℕ)) :=
                mul_le_mul_of_nonneg_right hexp_sq_one hbase_nonneg
          _ = 1024 * (Real.exp (σ ^ (2 : ℕ) / 2)) ^ (2 : ℕ) *
              t ^ (2 : ℕ) := by ring
      exact hQ_le_big.trans hbase_le
    have hden_pos :
        0 < 1024 * (Real.exp (σ ^ (2 : ℕ) / 2)) ^ (2 : ℕ) * t ^ (2 : ℕ) := by
      positivity
    rw [div_le_iff₀ hden_pos]
    calc
      Q ^ (2 : ℕ) = Q * Q := by ring
      _ ≤ Q *
          (1024 * (Real.exp (σ ^ (2 : ℕ) / 2)) ^ (2 : ℕ) * t ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hden_ge hQ_nonneg
  rw [hlBt]
  calc
    Real.log 2 + Q + R * (l ^ (2 : ℕ) * D) ≤ Q + Q + Q := by
      exact add_le_add (add_le_add hlog_two_le_Q le_rfl) hvar_le_Q
    _ = 3 * Q := by ring
    _ ≤ 4 * Q :=
      mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 4) hQ_nonneg

/-- Turn a local linear-control estimate into the generic logarithmic
constraint needed by the raw `Ψ_σ` Chernoff theorem. -/
lemma psiSigma_log_constraint_of_linear_control {σ l L C u : ℝ}
    (hσ : 1 ≤ σ) (hu : u ∈ Set.Icc 1 L)
    (hlinear : ∀ ⦃v : ℝ⦄, v ∈ Set.Icc 1 L →
      l * v ≤ (1 / 2 : ℝ) * Real.log (psiSigma σ v) + C) :
    l * u ≤
      Real.log (psiSigma σ u) - 4 * Real.log u +
        Real.log (psiSigmaPolynomialLogControlConst σ C) := by
  have hlin := hlinear hu
  have hpoly := four_mul_log_le_half_log_psiSigma_add_const (σ := σ) (t := u) hσ hu.1
  rw [psiSigmaPolynomialLogControlConst, Real.log_exp]
  linarith

lemma psiSigma_linear_control_of_mul_le_const {σ l L C u : ℝ}
    (hl : 0 ≤ l) (hC : l * L ≤ C) (hu : u ∈ Set.Icc 1 L) :
    l * u ≤ (1 / 2 : ℝ) * Real.log (psiSigma σ u) + C := by
  have hlog_nonneg : 0 ≤ Real.log (psiSigma σ u) :=
    Real.log_nonneg one_le_psiSigma
  have hlu : l * u ≤ l * L := mul_le_mul_of_nonneg_left hu.2 hl
  linarith


end

end IndependentSums

end Homogenization
