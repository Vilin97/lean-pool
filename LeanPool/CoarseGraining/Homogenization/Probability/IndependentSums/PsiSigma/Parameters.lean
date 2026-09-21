/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.PsiSigma.TailAndLogControl

/-! # Parameters -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- A fixed-constant local-control lemma for the optimized log-normal
parameter choice. The condition is the note-facing admissibility scale
`l ≲ log Ψ_σ(L) / L`; the proof avoids differentiating
`log(1 + σ t)^2 / t` by using Mathlib's monotonicity of
`log x / sqrt x` on `[exp 2, ∞)`, and handles the small range with the
additive constant `exp 2`. -/
lemma psiSigma_linear_control_of_le_half_log_sq_div {σ l L u : ℝ}
    (hσ : 1 ≤ σ) (hl_one : l ≤ 1) (hL : 1 ≤ L)
    (hl : l ≤
      (1 / 2 : ℝ) *
        (((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * L)) ^ (2 : ℕ)) / L))
    (hu : u ∈ Set.Icc 1 L) :
    l * u ≤ (1 / 2 : ℝ) * Real.log (psiSigma σ u) + Real.exp 2 := by
  have hσ_pos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  have hσsq_pos : 0 < σ ^ (2 : ℕ) := by positivity
  have hu_nonneg : 0 ≤ u := le_trans zero_le_one hu.1
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu.1
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let x : ℝ := 1 + σ * u
  let y : ℝ := 1 + σ * L
  have hx_pos : 0 < x := by positivity
  have hy_pos : 0 < y := by positivity
  have hx_one : 1 ≤ x := by
    dsimp [x]
    exact le_add_of_nonneg_right (mul_nonneg hσ_pos.le hu_nonneg)
  have hy_one : 1 ≤ y := by
    dsimp [y]
    exact le_add_of_nonneg_right
      (mul_nonneg hσ_pos.le (le_trans zero_le_one hL))
  have hxy : x ≤ y := by
    dsimp [x, y]
    have hmul : σ * u ≤ σ * L := mul_le_mul_of_nonneg_left hu.2 hσ_pos.le
    linarith
  have hlogψ :
      (1 / 2 : ℝ) * Real.log (psiSigma σ u) =
        (1 / 2 : ℝ) * ((σ ^ (2 : ℕ))⁻¹ * (Real.log x) ^ (2 : ℕ)) := by
    simp [psiSigma, x]
  by_cases hlarge : Real.exp 2 ≤ x
  · have hy_large : Real.exp 2 ≤ y := hlarge.trans hxy
    have hanti : Real.log y / Real.sqrt y ≤ Real.log x / Real.sqrt x :=
      Real.log_div_sqrt_antitoneOn hlarge hy_large hxy
    have hleft_nonneg : 0 ≤ Real.log y / Real.sqrt y :=
      div_nonneg (Real.log_nonneg hy_one) (Real.sqrt_nonneg y)
    have hsq_mono :
        (Real.log y / Real.sqrt y) ^ (2 : ℕ) ≤
          (Real.log x / Real.sqrt x) ^ (2 : ℕ) := by
      simpa using (pow_le_pow_left₀ hleft_nonneg hanti 2)
    have hratio :
        (Real.log y) ^ (2 : ℕ) / y ≤ (Real.log x) ^ (2 : ℕ) / x := by
      calc
        (Real.log y) ^ (2 : ℕ) / y = (Real.log y / Real.sqrt y) ^ (2 : ℕ) := by
          rw [show (Real.log y / Real.sqrt y) ^ (2 : ℕ) =
            (Real.log y) ^ (2 : ℕ) / (Real.sqrt y) ^ (2 : ℕ) by ring]
          rw [Real.sq_sqrt hy_pos.le]
        _ ≤ (Real.log x / Real.sqrt x) ^ (2 : ℕ) := hsq_mono
        _ = (Real.log x) ^ (2 : ℕ) / x := by
          rw [show (Real.log x / Real.sqrt x) ^ (2 : ℕ) =
            (Real.log x) ^ (2 : ℕ) / (Real.sqrt x) ^ (2 : ℕ) by ring]
          rw [Real.sq_sqrt hx_pos.le]
    have hylxu : y / L ≤ x / u := by
      rw [div_le_div_iff₀ hL_pos hu_pos]
      dsimp [x, y]
      ring_nf
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hu.2 (σ * L * u)
    have hcoef : (y / L) * (u / x) ≤ 1 := by
      calc
        (y / L) * (u / x) ≤ (x / u) * (u / x) := by
          exact mul_le_mul_of_nonneg_right hylxu (by positivity)
        _ = 1 := by
          field_simp [hu_pos.ne', hx_pos.ne']
    have hscale :
        ((Real.log y) ^ (2 : ℕ) / L) * u ≤ (Real.log x) ^ (2 : ℕ) := by
      calc
        ((Real.log y) ^ (2 : ℕ) / L) * u
            = (y / L) * (u * ((Real.log y) ^ (2 : ℕ) / y)) := by
                field_simp [hy_pos.ne']
        _ ≤ (y / L) * (u * ((Real.log x) ^ (2 : ℕ) / x)) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hratio hu_nonneg) (by positivity)
        _ = ((y / L) * (u / x)) * (Real.log x) ^ (2 : ℕ) := by
                field_simp [hx_pos.ne']
        _ ≤ 1 * (Real.log x) ^ (2 : ℕ) := by
                exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg (Real.log x))
        _ = (Real.log x) ^ (2 : ℕ) := by ring
    have hscale_div :
        (((σ ^ (2 : ℕ))⁻¹ * (Real.log y) ^ (2 : ℕ)) / L) * u ≤
          (σ ^ (2 : ℕ))⁻¹ * (Real.log x) ^ (2 : ℕ) := by
      have hmul := mul_le_mul_of_nonneg_left hscale (inv_nonneg.mpr (sq_nonneg σ))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hl_u :
        l * u ≤
          ((1 / 2 : ℝ) *
            (((σ ^ (2 : ℕ))⁻¹ * (Real.log y) ^ (2 : ℕ)) / L)) * u := by
      dsimp [y] at hl ⊢
      exact mul_le_mul_of_nonneg_right hl hu_nonneg
    rw [hlogψ]
    calc
      l * u ≤
          ((1 / 2 : ℝ) *
            (((σ ^ (2 : ℕ))⁻¹ * (Real.log y) ^ (2 : ℕ)) / L)) * u :=
        hl_u
      _ ≤
          (1 / 2 : ℝ) * ((σ ^ (2 : ℕ))⁻¹ * (Real.log x) ^ (2 : ℕ)) := by
        calc
          ((1 / 2 : ℝ) *
              (((σ ^ (2 : ℕ))⁻¹ * (Real.log y) ^ (2 : ℕ)) / L)) * u =
              (1 / 2 : ℝ) *
                ((((σ ^ (2 : ℕ))⁻¹ * (Real.log y) ^ (2 : ℕ)) / L) * u) := by
            ring
          _ ≤ (1 / 2 : ℝ) *
              ((σ ^ (2 : ℕ))⁻¹ * (Real.log x) ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hscale_div (by norm_num : 0 ≤ (1 / 2 : ℝ))
      _ ≤
          (1 / 2 : ℝ) * ((σ ^ (2 : ℕ))⁻¹ * (Real.log x) ^ (2 : ℕ)) +
            Real.exp 2 :=
        le_add_of_nonneg_right (Real.exp_pos 2).le
  · have hx_le_exp : x ≤ Real.exp 2 := le_of_not_ge hlarge
    have hu_le_exp : u ≤ Real.exp 2 := by
      dsimp [x] at hx_le_exp
      have hσu_ge_u : u ≤ σ * u := by
        simpa [one_mul] using mul_le_mul_of_nonneg_right hσ hu_nonneg
      exact (hσu_ge_u.trans (le_add_of_nonneg_left zero_le_one)).trans hx_le_exp
    have hlu : l * u ≤ u := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hl_one hu_nonneg
    have hlog_nonneg : 0 ≤ Real.log (psiSigma σ u) :=
      Real.log_nonneg one_le_psiSigma
    calc
      l * u ≤ u := hlu
      _ ≤ Real.exp 2 := hu_le_exp
      _ ≤ (1 / 2 : ℝ) * Real.log (psiSigma σ u) + Real.exp 2 :=
        le_add_of_nonneg_left
          (mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) hlog_nonneg)

lemma psiSigmaIndependentSumLambda_linear_control {σ R t u : ℝ}
    (hσ : 1 ≤ σ) (hR : 1 ≤ R) (ht : 1 ≤ t)
    (hu : u ∈ Set.Icc 1 (psiSigmaIndependentSumCutoff σ R t)) :
    psiSigmaIndependentSumLambda σ R t * u ≤
      (1 / 2 : ℝ) * Real.log (psiSigma σ u) + Real.exp 2 := by
  exact
    psiSigma_linear_control_of_le_half_log_sq_div
      (σ := σ) (l := psiSigmaIndependentSumLambda σ R t)
      (L := psiSigmaIndependentSumCutoff σ R t) (u := u)
      hσ
      (psiSigmaIndependentSumLambda_le_one (σ := σ) (R := R) (t := t) hσ hR ht)
      (one_le_psiSigmaIndependentSumCutoff (σ := σ) (R := R) (t := t) hσ hR ht)
      (psiSigmaIndependentSumLambda_le_half_cutoff_logExponent_div
        (σ := σ) (R := R) (t := t) hσ hR ht)
      hu

lemma psiSigma_independentSum_parameter_choice {σ R t : ℝ}
    (hσ : 1 ≤ σ) (hR : 1 ≤ R) (ht : 1 ≤ t) :
    ∃ l L C : ℝ,
      0 ≤ l ∧ l ≤ 1 ∧ 1 ≤ L ∧ 0 ≤ C ∧
        (∀ ⦃u : ℝ⦄, u ∈ Set.Icc 1 L →
          l * u ≤ (1 / 2 : ℝ) * Real.log (psiSigma σ u) + C) ∧
        Real.log 2 +
            ((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ) +
              Real.log 2) +
              R * (l ^ (2 : ℕ) *
                (3 + psiSigmaPolynomialLogControlConst σ C + psiSigmaTailIntegralConst σ)) ≤
          l * ((psiSigmaIndependentSumConst σ * Real.sqrt R) * t) ∧
        Real.log (2 * R) +
            ((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ) +
              Real.log 2) ≤
          (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * L)) ^ (2 : ℕ) := by
  refine ⟨psiSigmaIndependentSumLambda σ R t, psiSigmaIndependentSumCutoff σ R t,
    Real.exp 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact psiSigmaIndependentSumLambda_nonneg (σ := σ) (R := R) (t := t) hσ hR ht
  · exact psiSigmaIndependentSumLambda_le_one (σ := σ) (R := R) (t := t) hσ hR ht
  · exact one_le_psiSigmaIndependentSumCutoff (σ := σ) (R := R) (t := t) hσ hR ht
  · exact (Real.exp_pos 2).le
  · intro u hu
    exact psiSigmaIndependentSumLambda_linear_control
      (σ := σ) (R := R) (t := t) (u := u) hσ hR ht hu
  · simpa [psiSigmaLogExponent, psiSigmaIndependentSumRawConst] using
      psiSigmaIndependentSumLambda_mgf_log (σ := σ) (R := R) (t := t) hσ hR ht
  · simpa [psiSigmaLogExponent] using
      psiSigmaIndependentSumCutoff_union_log (σ := σ) (R := R) (t := t) hσ hR ht

lemma psiSigma_log_constraint_of_mul_le_const {σ l L C u : ℝ}
    (hσ : 1 ≤ σ) (hl : 0 ≤ l) (hC : l * L ≤ C) (hu : u ∈ Set.Icc 1 L) :
    l * u ≤
      Real.log (psiSigma σ u) - 4 * Real.log u +
        Real.log (psiSigmaPolynomialLogControlConst σ C) := by
  refine psiSigma_log_constraint_of_linear_control (σ := σ) (l := l) (L := L) (C := C)
    hσ hu ?_
  intro v hv
  exact psiSigma_linear_control_of_mul_le_const (σ := σ) (l := l) (L := L) (C := C)
    hl hC hv

lemma two_mul_card_mul_inv_psiSigma_le_exp_neg_of_log_le {σ R L t : ℝ}
    (hR_pos : 0 < R)
    (hlog :
      Real.log (2 * R) +
        (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ) ≤
          (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * L)) ^ (2 : ℕ)) :
    2 * (R * (psiSigma σ L)⁻¹) ≤
      Real.exp (-((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ))) := by
  let qt : ℝ := (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ)
  let qL : ℝ := (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * L)) ^ (2 : ℕ)
  have htwoR_pos : 0 < 2 * R := by
    positivity
  have hexp_rewrite :
      2 * (R * (psiSigma σ L)⁻¹) = Real.exp (Real.log (2 * R) - qL) := by
    calc
      2 * (R * (psiSigma σ L)⁻¹) = (2 * R) * Real.exp (-qL) := by
        change 2 * (R * (Real.exp qL)⁻¹) = (2 * R) * Real.exp (-qL)
        rw [← Real.exp_neg]
        ring
      _ = Real.exp (Real.log (2 * R)) * Real.exp (-qL) := by
        rw [Real.exp_log htwoR_pos]
      _ = Real.exp (Real.log (2 * R) - qL) := by
        rw [← Real.exp_add]
        ring_nf
  rw [hexp_rewrite]
  exact Real.exp_le_exp.2 (by dsimp [qt, qL] at hlog ⊢; linarith)

lemma two_mul_card_mul_inv_psiSigma_le_exp_neg_of_log_add_le {σ R L q : ℝ}
    (hR_pos : 0 < R)
    (hlog :
      Real.log (2 * R) + q ≤
          (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * L)) ^ (2 : ℕ)) :
    2 * (R * (psiSigma σ L)⁻¹) ≤ Real.exp (-q) := by
  let qL : ℝ := (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * L)) ^ (2 : ℕ)
  have htwoR_pos : 0 < 2 * R := by
    positivity
  have hexp_rewrite :
      2 * (R * (psiSigma σ L)⁻¹) = Real.exp (Real.log (2 * R) - qL) := by
    calc
      2 * (R * (psiSigma σ L)⁻¹) = (2 * R) * Real.exp (-qL) := by
        change 2 * (R * (Real.exp qL)⁻¹) = (2 * R) * Real.exp (-qL)
        rw [← Real.exp_neg]
        ring
      _ = Real.exp (Real.log (2 * R)) * Real.exp (-qL) := by
        rw [Real.exp_log htwoR_pos]
      _ = Real.exp (Real.log (2 * R) - qL) := by
        rw [← Real.exp_add]
        ring_nf
  rw [hexp_rewrite]
  exact Real.exp_le_exp.2 (by dsimp [qL] at hlog ⊢; linarith)

lemma two_mul_exp_neg_add_le_exp_neg_of_log_two_add_le {x y q : ℝ}
    (h : Real.log 2 + q + y ≤ x) :
    2 * Real.exp (-x + y) ≤ Real.exp (-q) := by
  have htwo_pos : 0 < (2 : ℝ) := by
    norm_num
  have hrewrite : 2 * Real.exp (-x + y) = Real.exp (Real.log 2 - x + y) := by
    calc
      2 * Real.exp (-x + y) = Real.exp (Real.log 2) * Real.exp (-x + y) := by
        rw [Real.exp_log htwo_pos]
      _ = Real.exp (Real.log 2 + (-x + y)) := by
        rw [← Real.exp_add]
      _ = Real.exp (Real.log 2 - x + y) := by
        ring_nf
  rw [hrewrite]
  exact Real.exp_le_exp.2 (by linarith)

lemma psiSigma_raw_bound_le_exp_neg_of_mgf_and_union_log {σ R l B t D L : ℝ}
    (hR_pos : 0 < R)
    (hmgf :
      Real.log 2 +
        ((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ) + Real.log 2) +
          R * (l ^ (2 : ℕ) * D) ≤ l * (B * t))
    (hunion :
      Real.log (2 * R) +
        ((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ) + Real.log 2) ≤
          (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * L)) ^ (2 : ℕ)) :
    2 * Real.exp (-l * (B * t) + R * (l ^ (2 : ℕ) * D)) +
        2 * (R * (psiSigma σ L)⁻¹) ≤
      Real.exp (-((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ))) := by
  let q : ℝ := (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ)
  have hmgf_bound :
      2 * Real.exp (-l * (B * t) + R * (l ^ (2 : ℕ) * D)) ≤
        Real.exp (-(q + Real.log 2)) := by
    simpa [neg_mul] using
      two_mul_exp_neg_add_le_exp_neg_of_log_two_add_le
        (x := l * (B * t)) (y := R * (l ^ (2 : ℕ) * D)) (q := q + Real.log 2)
        (by simpa [q, add_assoc] using hmgf)
  have hunion_bound :
      2 * (R * (psiSigma σ L)⁻¹) ≤ Real.exp (-(q + Real.log 2)) :=
    two_mul_card_mul_inv_psiSigma_le_exp_neg_of_log_add_le
      (σ := σ) (R := R) (L := L) (q := q + Real.log 2)
      hR_pos (by simpa [q, add_assoc] using hunion)
  have hhalf :
      Real.exp (-(q + Real.log 2)) + Real.exp (-(q + Real.log 2)) =
        Real.exp (-q) := by
    have htwo_pos : 0 < (2 : ℝ) := by
      norm_num
    rw [neg_add, Real.exp_add]
    have hlog_two : Real.exp (-Real.log 2) = (2 : ℝ)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log htwo_pos]
    rw [hlog_two]
    ring
  calc
    2 * Real.exp (-l * (B * t) + R * (l ^ (2 : ℕ) * D)) +
        2 * (R * (psiSigma σ L)⁻¹)
        ≤ Real.exp (-(q + Real.log 2)) + Real.exp (-(q + Real.log 2)) := by
          exact add_le_add hmgf_bound hunion_bound
    _ = Real.exp (-q) := hhalf


end

end IndependentSums

end Homogenization
