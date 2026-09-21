/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.PsiSigma.Parameters

/-! # Endpoint -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- The simple logarithmic-control constant satisfies the generic raw
truncation-Chernoff log constraint for `Ψ_σ` on `[1, L]`. -/
lemma psiSigma_log_constraint_of_le {σ l L t : ℝ}
    (hl : 0 ≤ l) (ht : t ∈ Set.Icc 1 L) :
    l * t ≤
      Real.log (psiSigma σ t) - 4 * Real.log t +
        Real.log (psiSigmaLogControlConst l L) := by
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hlogψ_nonneg : 0 ≤ Real.log (psiSigma σ t) :=
    Real.log_nonneg one_le_psiSigma
  have hltL : l * t ≤ l * L := mul_le_mul_of_nonneg_left ht.2 hl
  have hlogt_le_logL : Real.log t ≤ Real.log L :=
    Real.log_le_log ht_pos ht.2
  have hfourdiff : 0 ≤ 4 * Real.log L - 4 * Real.log t := by
    nlinarith
  rw [psiSigmaLogControlConst, Real.log_exp]
  nlinarith

/-- Raw truncation-Chernoff concentration for independent centered
`O_{Ψ_σ}(1)` summands, with the analytic `Ψ_σ` tail-integral and logarithmic
constraint hypotheses left explicit.

This is the specialization point for the log-normal independent-sum endpoint.
The remaining endpoint proof will choose `l`, `L`, `M`, and `CΨ` as functions
of `σ`, the family size, and the tail parameter, then optimize this raw bound
to obtain the clean `sqrt(card)` weak-`Ψ_σ` scale. -/
theorem measureReal_upperTailEvent_finset_sum_le_exp_card_mul_add_card_mul_invPsi_psiSigma_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_log_constraint_rounded
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ a l L CΨ M : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hσ : 1 ≤ σ)
    (hCΨ_nonneg : 0 ≤ CΨ)
    (hCΨ :
      ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / psiSigma σ t) ∂volume ≤
        ENNReal.ofReal CΨ)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) 1)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hconstraint : ∀ i ∈ s, ∀ ⦃t : ℝ⦄, t ∈ Set.Icc 1 L →
      l * t ≤ Real.log (psiSigma σ t) - 4 * Real.log t + Real.log M) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a) ≤
      Real.exp (-l * a + (s.card : ℝ) * (l ^ (2 : ℕ) * (3 + M + CΨ))) +
        (s.card : ℝ) * (psiSigma σ L)⁻¹ := by
  exact
    measureReal_upperTailEvent_finset_sum_le_exp_card_mul_add_card_mul_invPsi_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_log_constraint_rounded
      (μ := μ) (Ψ := psiSigma σ) (X := X) (s := s) (a := a) (l := l) (L := L)
      (CΨ := CΨ) (M := M)
      h_indep h_meas h_int h_mean
      (admissiblePsi_psiSigma (le_trans zero_le_one hσ))
      hCΨ_nonneg hCΨ hX hl hl1 hL hM hconstraint

/-- Scaled raw truncation-Chernoff concentration for independent centered
`O_{Ψ_σ}(K)` summands. The conclusion is written at threshold `K * a`, so the
right-hand side is exactly the unit-scale raw bound. -/
theorem measureReal_upperTailEvent_finset_sum_le_exp_card_mul_add_card_mul_invPsi_psiSigma_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_log_constraint_rounded
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K a l L CΨ M : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hCΨ_nonneg : 0 ≤ CΨ)
    (hCΨ :
      ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / psiSigma σ t) ∂volume ≤
        ENNReal.ofReal CΨ)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) K)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hconstraint : ∀ i ∈ s, ∀ ⦃t : ℝ⦄, t ∈ Set.Icc 1 L →
      l * t ≤ Real.log (psiSigma σ t) - 4 * Real.log t + Real.log M) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (K * a)) ≤
      Real.exp (-l * a + (s.card : ℝ) * (l ^ (2 : ℕ) * (3 + M + CΨ))) +
        (s.card : ℝ) * (psiSigma σ L)⁻¹ := by
  let Y : ι → Ω → ℝ := fun i ω => K⁻¹ * X i ω
  have h_indep_Y : iIndepFun Y μ := by
    simpa [Y, Function.comp] using!
      h_indep.comp (fun _ => fun x : ℝ => K⁻¹ * x)
        (fun _ => measurable_const.mul measurable_id)
  have h_meas_Y : ∀ i, Measurable (Y i) := by
    intro i
    simpa [Y, mul_comm] using (h_meas i).const_mul K⁻¹
  have h_int_Y : ∀ i ∈ s, Integrable (Y i) μ := by
    intro i hi
    simpa [Y] using (h_int i hi).const_mul K⁻¹
  have h_mean_Y : ∀ i ∈ s, ∫ ω, Y i ω ∂μ = 0 := by
    intro i hi
    calc
      ∫ ω, Y i ω ∂μ = K⁻¹ * ∫ ω, X i ω ∂μ := by
          simpa [Y] using integral_const_mul K⁻¹ (X i)
      _ = 0 := by rw [h_mean i hi]; ring
  have hX_Y : ∀ i ∈ s, IsBigO μ (psiSigma σ) (Y i) 1 := by
    intro i hi
    have hscaled :=
      IsBigO.const_mul (μ := μ) (Ψ := psiSigma σ) (X := X i) (A := K) (c := K⁻¹)
        (inv_nonneg.mpr hK.le) (hX i hi)
    have hscale : K⁻¹ * K = (1 : ℝ) := by
      field_simp [hK.ne']
    simpa [Y, hscale] using hscaled
  have htail_Y :=
    measureReal_upperTailEvent_finset_sum_le_exp_card_mul_add_card_mul_invPsi_psiSigma_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_log_constraint_rounded
      (μ := μ) (X := Y) (s := s) (σ := σ) (a := a) (l := l) (L := L)
      (CΨ := CΨ) (M := M)
      h_indep_Y h_meas_Y h_int_Y h_mean_Y hσ hCΨ_nonneg hCΨ hX_Y hl hl1 hL hM
      hconstraint
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
  have hset :
      upperTailEvent (fun ω => ∑ i ∈ s, Y i ω) a =
        upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (K * a) := by
    ext ω
    constructor
    · intro hω
      change a < ∑ i ∈ s, Y i ω at hω
      have hmul : K * a < K * ∑ i ∈ s, Y i ω :=
        mul_lt_mul_of_pos_left hω hK
      have hpoint :
          K * ∑ i ∈ s, Y i ω = ∑ i ∈ s, X i ω :=
        congrFun hsum_eq ω
      simpa [upperTailEvent, hpoint] using hmul
    · intro hω
      change K * a < ∑ i ∈ s, X i ω at hω
      have hmul : K * a < K * ∑ i ∈ s, Y i ω := by
        have hpoint :
            K * ∑ i ∈ s, Y i ω = ∑ i ∈ s, X i ω :=
          congrFun hsum_eq ω
        simpa [hpoint] using hω
      exact lt_of_mul_lt_mul_left hmul hK.le
  simpa [hset] using htail_Y

/-- Symmetric raw truncation-Chernoff concentration for independent centered
`O_{Ψ_σ}(K)` summands. This is just the scaled upper-tail estimate applied to
`X` and `-X`, before the final log-normal absorption step. -/
theorem measureReal_absTailEvent_finset_sum_le_two_mul_exp_add_two_mul_card_mul_invPsi_psiSigma_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_log_constraint_rounded
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K a l L CΨ M : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hCΨ_nonneg : 0 ≤ CΨ)
    (hCΨ :
      ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / psiSigma σ t) ∂volume ≤
        ENNReal.ofReal CΨ)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) K)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hconstraint : ∀ i ∈ s, ∀ ⦃t : ℝ⦄, t ∈ Set.Icc 1 L →
      l * t ≤ Real.log (psiSigma σ t) - 4 * Real.log t + Real.log M) :
    μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) (K * a)) ≤
      2 * Real.exp (-l * a + (s.card : ℝ) * (l ^ (2 : ℕ) * (3 + M + CΨ))) +
        2 * ((s.card : ℝ) * (psiSigma σ L)⁻¹) := by
  let B : ℝ := Real.exp (-l * a + (s.card : ℝ) * (l ^ (2 : ℕ) * (3 + M + CΨ)))
  let U : ℝ := (s.card : ℝ) * (psiSigma σ L)⁻¹
  have hsum :
      absTailEvent (fun ω => ∑ i ∈ s, X i ω) (K * a) ⊆
        upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (K * a) ∪
          upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (K * a) := by
    intro ω hω
    rw [Set.mem_union, mem_upperTailEvent, mem_upperTailEvent]
    exact lt_abs.mp (by
      simpa [absTailEvent, upperTailEvent] using hω)
  have hupper :
      μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (K * a)) ≤ B + U := by
    simpa [B, U] using
      measureReal_upperTailEvent_finset_sum_le_exp_card_mul_add_card_mul_invPsi_psiSigma_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_log_constraint_rounded
        (μ := μ) (X := X) (s := s) (σ := σ) (K := K) (a := a) (l := l)
        (L := L) (CΨ := CΨ) (M := M)
        h_indep h_meas h_int h_mean hσ hK hCΨ_nonneg hCΨ hX
        hl hl1 hL hM hconstraint
  let Xneg : ι → Ω → ℝ := fun i ω => -X i ω
  have h_indep_neg : iIndepFun Xneg μ := by
    simpa [Xneg, Function.comp] using!
      h_indep.comp (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
  have h_meas_neg : ∀ i, Measurable (Xneg i) := by
    intro i
    simpa [Xneg] using h_meas i
  have h_int_neg : ∀ i ∈ s, Integrable (Xneg i) μ := by
    intro i hi
    dsimp [Xneg]
    exact (h_int i hi).neg
  have h_mean_neg : ∀ i ∈ s, ∫ ω, Xneg i ω ∂μ = 0 := by
    intro i hi
    calc
      ∫ ω, Xneg i ω ∂μ = -∫ ω, X i ω ∂μ := by
          simpa [Xneg] using integral_neg (X i)
      _ = 0 := by rw [h_mean i hi, neg_zero]
  have hX_neg : ∀ i ∈ s, IsBigO μ (psiSigma σ) (Xneg i) K := by
    intro i hi
    simpa [Xneg] using (hX i hi).neg
  have hupper_neg :
      μ.real (upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (K * a)) ≤ B + U := by
    have hraw :=
      measureReal_upperTailEvent_finset_sum_le_exp_card_mul_add_card_mul_invPsi_psiSigma_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_log_constraint_rounded
        (μ := μ) (X := Xneg) (s := s) (σ := σ) (K := K) (a := a) (l := l)
        (L := L) (CΨ := CΨ) (M := M)
        h_indep_neg h_meas_neg h_int_neg h_mean_neg hσ hK hCΨ_nonneg hCΨ hX_neg
        hl hl1 hL hM hconstraint
    simpa [Xneg, B, U, Finset.sum_neg_distrib] using hraw
  calc
    μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) (K * a))
        ≤ μ.real
          (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (K * a) ∪
            upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (K * a)) := by
          exact measureReal_mono hsum
    _ ≤ μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) (K * a)) +
          μ.real (upperTailEvent (fun ω => -∑ i ∈ s, X i ω) (K * a)) := by
          exact measureReal_union_le _ _
    _ ≤ (B + U) + (B + U) := by
          exact add_le_add hupper hupper_neg
    _ = 2 * B + 2 * U := by ring
    _ = 2 * Real.exp (-l * a + (s.card : ℝ) * (l ^ (2 : ℕ) * (3 + M + CΨ))) +
          2 * ((s.card : ℝ) * (psiSigma σ L)⁻¹) := by
          simp [B, U]

/-- Symmetric raw `Ψ_σ` concentration with the scalar tail-integral input
discharged, but with an arbitrary logarithmic-control constant `M`. This is
the preferred backend for the final optimized log-normal endpoint: the
deterministic optimizer can choose `M` sharply instead of using the simple
fallback `exp(l L + 4 log L)`. -/
theorem measureReal_absTailEvent_finset_sum_le_two_mul_exp_add_two_mul_card_mul_invPsi_psiSigma_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_log_constraint_tail_const_rounded
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K a l L M : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) K)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hconstraint : ∀ i ∈ s, ∀ ⦃t : ℝ⦄, t ∈ Set.Icc 1 L →
      l * t ≤ Real.log (psiSigma σ t) - 4 * Real.log t + Real.log M) :
    μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) (K * a)) ≤
      2 * Real.exp
        (-l * a +
          (s.card : ℝ) *
            (l ^ (2 : ℕ) * (3 + M + psiSigmaTailIntegralConst σ))) +
        2 * ((s.card : ℝ) * (psiSigma σ L)⁻¹) := by
  exact
    measureReal_absTailEvent_finset_sum_le_two_mul_exp_add_two_mul_card_mul_invPsi_psiSigma_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_log_constraint_rounded
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K) (a := a) (l := l) (L := L)
      (CΨ := psiSigmaTailIntegralConst σ) (M := M)
      h_indep h_meas h_int h_mean hσ hK
      (psiSigmaTailIntegralConst_nonneg σ)
      (lintegral_Ioi_one_psiSigma_le_psiSigmaTailIntegralConst hσ)
      hX hl hl1 hL hM hconstraint

/-- Symmetric raw `Ψ_σ` concentration with the simple log-control constant
already plugged into the generic log-constraint slot. The only analytic input
still explicit is the tail-integral bound for `t / Ψ_σ(t)`. -/
theorem measureReal_absTailEvent_finset_sum_le_two_mul_exp_add_two_mul_card_mul_invPsi_psiSigma_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_simple_log_control_rounded
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K a l L CΨ : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hCΨ_nonneg : 0 ≤ CΨ)
    (hCΨ :
      ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / psiSigma σ t) ∂volume ≤
        ENNReal.ofReal CΨ)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) K)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hL : 1 ≤ L) :
    μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) (K * a)) ≤
      2 * Real.exp
        (-l * a +
          (s.card : ℝ) * (l ^ (2 : ℕ) * (3 + psiSigmaLogControlConst l L + CΨ))) +
        2 * ((s.card : ℝ) * (psiSigma σ L)⁻¹) := by
  exact
    measureReal_absTailEvent_finset_sum_le_two_mul_exp_add_two_mul_card_mul_invPsi_psiSigma_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_log_constraint_rounded
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K) (a := a) (l := l) (L := L)
      (CΨ := CΨ) (M := psiSigmaLogControlConst l L)
      h_indep h_meas h_int h_mean hσ hK hCΨ_nonneg hCΨ hX hl hl1 hL
      (one_le_psiSigmaLogControlConst hl hL)
      (fun i hi t ht => psiSigma_log_constraint_of_le (σ := σ) (l := l) (L := L) hl ht)

/-- Symmetric raw `Ψ_σ` concentration with both scalar analytic inputs
discharged by the packaged log-control and tail-integral constants. -/
theorem measureReal_absTailEvent_finset_sum_le_two_mul_exp_add_two_mul_card_mul_invPsi_psiSigma_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_simple_log_control_tail_const_rounded
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K a l L : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) K)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hL : 1 ≤ L) :
    μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) (K * a)) ≤
      2 * Real.exp
        (-l * a +
          (s.card : ℝ) *
            (l ^ (2 : ℕ) *
              (3 + psiSigmaLogControlConst l L + psiSigmaTailIntegralConst σ))) +
        2 * ((s.card : ℝ) * (psiSigma σ L)⁻¹) := by
  exact
    measureReal_absTailEvent_finset_sum_le_two_mul_exp_add_two_mul_card_mul_invPsi_psiSigma_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_simple_log_control_rounded
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K) (a := a) (l := l) (L := L)
      (CΨ := psiSigmaTailIntegralConst σ)
      h_indep h_meas h_int h_mean hσ hK
      (psiSigmaTailIntegralConst_nonneg σ)
      (lintegral_Ioi_one_psiSigma_le_psiSigmaTailIntegralConst hσ)
      hX hl hl1 hL

/-- Scalar independent-sum `Ψ_σ` endpoint reduced to the remaining
deterministic choice of truncation/Chernoff parameters. This isolates the
probability part of the log-normal endpoint: after this theorem, the only
missing input is the optimization/absorption inequality for the raw bound. -/
theorem isBigO_psiSigma_finset_sum_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_simple_log_control_tail_const_absorption
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K B : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) K)
    (h_absorb : ∀ ⦃t : ℝ⦄, 1 ≤ t →
      ∃ l L : ℝ,
        0 ≤ l ∧ l ≤ 1 ∧ 1 ≤ L ∧
          2 * Real.exp
            (-l * (B * t) +
              (s.card : ℝ) *
                (l ^ (2 : ℕ) *
                  (3 + psiSigmaLogControlConst l L + psiSigmaTailIntegralConst σ))) +
            2 * ((s.card : ℝ) * (psiSigma σ L)⁻¹) ≤
              Real.exp
                (-((σ ^ (2 : ℕ))⁻¹ *
                  (Real.log (1 + σ * t)) ^ (2 : ℕ)))) :
    IsBigO μ (psiSigma σ) (fun ω => ∑ i ∈ s, X i ω) (B * K) := by
  rw [isBigO_psiSigma_iff]
  intro t ht
  rcases h_absorb ht with ⟨l, L, hl, hl1, hL, hbound⟩
  have hraw :=
    measureReal_absTailEvent_finset_sum_le_two_mul_exp_add_two_mul_card_mul_invPsi_psiSigma_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_simple_log_control_tail_const_rounded
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K) (a := B * t) (l := l) (L := L)
      h_indep h_meas h_int h_mean hσ hK hX hl hl1 hL
  calc
    μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) ((B * K) * t))
        = μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) (K * (B * t))) := by
          ring_nf
    _ ≤
        2 * Real.exp
          (-l * (B * t) +
            (s.card : ℝ) *
              (l ^ (2 : ℕ) *
                (3 + psiSigmaLogControlConst l L + psiSigmaTailIntegralConst σ))) +
          2 * ((s.card : ℝ) * (psiSigma σ L)⁻¹) := hraw
    _ ≤ Real.exp
        (-((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ))) := hbound

/-- Scalar independent-sum `Ψ_σ` endpoint reduced to deterministic
optimization with an arbitrary logarithmic-control constant. This is the
general note-facing staging theorem for the final log-normal scalar endpoint:
the probability and analytic tail-integral parts are fully discharged, while
the remaining hypothesis is exactly the deterministic parameter choice
`(l, L, M)` and absorption of the raw bound. -/
theorem isBigO_psiSigma_finset_sum_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_log_constraint_tail_const_absorption
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K B : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) K)
    (h_absorb : ∀ ⦃t : ℝ⦄, 1 ≤ t →
      ∃ l L M : ℝ,
        0 ≤ l ∧ l ≤ 1 ∧ 1 ≤ L ∧ 1 ≤ M ∧
          (∀ i ∈ s, ∀ ⦃u : ℝ⦄, u ∈ Set.Icc 1 L →
            l * u ≤ Real.log (psiSigma σ u) - 4 * Real.log u + Real.log M) ∧
          2 * Real.exp
            (-l * (B * t) +
              (s.card : ℝ) *
                (l ^ (2 : ℕ) * (3 + M + psiSigmaTailIntegralConst σ))) +
            2 * ((s.card : ℝ) * (psiSigma σ L)⁻¹) ≤
              Real.exp
                (-((σ ^ (2 : ℕ))⁻¹ *
                  (Real.log (1 + σ * t)) ^ (2 : ℕ)))) :
    IsBigO μ (psiSigma σ) (fun ω => ∑ i ∈ s, X i ω) (B * K) := by
  rw [isBigO_psiSigma_iff]
  intro t ht
  rcases h_absorb ht with
    ⟨l, L, M, hl, hl1, hL, hM, hconstraint, hbound⟩
  have hraw :=
    measureReal_absTailEvent_finset_sum_le_two_mul_exp_add_two_mul_card_mul_invPsi_psiSigma_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_log_constraint_tail_const_rounded
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K) (a := B * t) (l := l) (L := L)
      (M := M)
      h_indep h_meas h_int h_mean hσ hK hX hl hl1 hL hM hconstraint
  calc
    μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) ((B * K) * t))
        = μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) (K * (B * t))) := by
          ring_nf
    _ ≤
        2 * Real.exp
          (-l * (B * t) +
            (s.card : ℝ) *
              (l ^ (2 : ℕ) * (3 + M + psiSigmaTailIntegralConst σ))) +
          2 * ((s.card : ℝ) * (psiSigma σ L)⁻¹) := hraw
    _ ≤ Real.exp
        (-((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ))) := hbound

/-- Scalar independent-sum `Ψ_σ` endpoint reduced to a linear-control
parameter choice. The helper
`four_mul_log_le_half_log_psiSigma_add_const` absorbs the polynomial factor in
the raw theorem, so the deterministic optimizer only needs to find
`l, L, C` such that `l u ≤ (1/2) log Ψ_σ(u) + C` on `[1,L]` and the resulting
raw bound is absorbed by the target `Ψ_σ` tail. -/
theorem isBigO_psiSigma_finset_sum_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_linear_control_tail_const_absorption
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K B : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) K)
    (h_absorb : ∀ ⦃t : ℝ⦄, 1 ≤ t →
      ∃ l L C : ℝ,
        0 ≤ l ∧ l ≤ 1 ∧ 1 ≤ L ∧ 0 ≤ C ∧
          (∀ ⦃u : ℝ⦄, u ∈ Set.Icc 1 L →
            l * u ≤ (1 / 2 : ℝ) * Real.log (psiSigma σ u) + C) ∧
          2 * Real.exp
            (-l * (B * t) +
              (s.card : ℝ) *
                (l ^ (2 : ℕ) *
                  (3 + psiSigmaPolynomialLogControlConst σ C +
                    psiSigmaTailIntegralConst σ))) +
            2 * ((s.card : ℝ) * (psiSigma σ L)⁻¹) ≤
              Real.exp
                (-((σ ^ (2 : ℕ))⁻¹ *
                  (Real.log (1 + σ * t)) ^ (2 : ℕ)))) :
    IsBigO μ (psiSigma σ) (fun ω => ∑ i ∈ s, X i ω) (B * K) := by
  refine
    isBigO_psiSigma_finset_sum_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_log_constraint_tail_const_absorption
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K) (B := B)
      h_indep h_meas h_int h_mean hσ hK hX ?_
  intro t ht
  rcases h_absorb ht with ⟨l, L, C, hl, hl1, hL, hC, hlinear, hbound⟩
  refine ⟨l, L, psiSigmaPolynomialLogControlConst σ C, hl, hl1, hL,
    one_le_psiSigmaPolynomialLogControlConst hC, ?_, ?_⟩
  · intro i hi u hu
    exact psiSigma_log_constraint_of_linear_control (σ := σ) (l := l) (L := L) (C := C)
      hσ hu hlinear
  · exact hbound

/-- Scalar independent-sum `Ψ_σ` endpoint reduced to three deterministic
logarithmic inequalities: local linear control, mgf-term absorption, and
union-term absorption. This is the preferred staging point for the final
parameter-choice proof. -/
theorem isBigO_psiSigma_finset_sum_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_linear_control_tail_const_mgf_union_log
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K B : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hs : s.Nonempty)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) K)
    (h_absorb : ∀ ⦃t : ℝ⦄, 1 ≤ t →
      ∃ l L C : ℝ,
        0 ≤ l ∧ l ≤ 1 ∧ 1 ≤ L ∧ 0 ≤ C ∧
          (∀ ⦃u : ℝ⦄, u ∈ Set.Icc 1 L →
            l * u ≤ (1 / 2 : ℝ) * Real.log (psiSigma σ u) + C) ∧
          Real.log 2 +
              ((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ) +
                Real.log 2) +
                (s.card : ℝ) *
                  (l ^ (2 : ℕ) *
                    (3 + psiSigmaPolynomialLogControlConst σ C +
                      psiSigmaTailIntegralConst σ)) ≤
            l * (B * t) ∧
          Real.log (2 * (s.card : ℝ)) +
              ((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ) +
                Real.log 2) ≤
            (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * L)) ^ (2 : ℕ)) :
    IsBigO μ (psiSigma σ) (fun ω => ∑ i ∈ s, X i ω) (B * K) := by
  refine
    isBigO_psiSigma_finset_sum_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_linear_control_tail_const_absorption
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K) (B := B)
      h_indep h_meas h_int h_mean hσ hK hX ?_
  intro t ht
  rcases h_absorb ht with ⟨l, L, C, hl, hl1, hL, hC, hlinear, hmgf, hunion⟩
  refine ⟨l, L, C, hl, hl1, hL, hC, hlinear, ?_⟩
  have hR_pos : 0 < (s.card : ℝ) := by
    exact_mod_cast hs.card_pos
  exact
    psiSigma_raw_bound_le_exp_neg_of_mgf_and_union_log
      (σ := σ) (R := (s.card : ℝ)) (l := l) (B := B) (t := t)
      (D := 3 + psiSigmaPolynomialLogControlConst σ C + psiSigmaTailIntegralConst σ)
      (L := L) hR_pos hmgf hunion

/-- Note-facing scalar independent-sum endpoint for the log-normal class
`Ψ_σ`: centered independent summands with common `O_{Ψ_σ}` scale `K`
concentrate at the square-root cardinality scale. -/
theorem isBigO_psiSigma_finset_sum_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hs : s.Nonempty)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) K) :
    IsBigO μ (psiSigma σ) (fun ω => ∑ i ∈ s, X i ω)
      (psiSigmaIndependentSumConst σ * Real.sqrt (s.card : ℝ) * K) := by
  refine
    isBigO_psiSigma_finset_sum_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero_of_linear_control_tail_const_mgf_union_log
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
      (B := psiSigmaIndependentSumConst σ * Real.sqrt (s.card : ℝ))
      h_indep h_meas h_int h_mean hs hσ hK hX ?_
  intro t ht
  have hR : 1 ≤ (s.card : ℝ) := by
    exact_mod_cast hs.card_pos
  simpa [psiSigmaLogExponent, psiSigmaIndependentSumRawConst] using
    psiSigma_independentSum_parameter_choice
      (σ := σ) (R := (s.card : ℝ)) (t := t) hσ hR ht

/-- Average version of the log-normal centered independent-sum endpoint. -/
theorem isBigO_psiSigma_finsetAverage_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hs : s.Nonempty)
    (hσ : 1 ≤ σ) (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) K) :
    IsBigO μ (psiSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * ∑ i ∈ s, X i ω)
      (psiSigmaIndependentSumConst σ *
        (Real.sqrt (s.card : ℝ) / (s.card : ℝ)) * K) := by
  have hsum :=
    isBigO_psiSigma_finset_sum_of_iIndepFun_of_isBigO_scale_of_integral_eq_zero
      (μ := μ) (X := X) (s := s) (σ := σ) (K := K)
      h_indep h_meas h_int h_mean hs hσ hK hX
  have hcard_inv_nonneg : 0 ≤ ((s.card : ℝ)⁻¹) := by positivity
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    IsBigO.const_mul (μ := μ) (Ψ := psiSigma σ)
      (X := fun ω => ∑ i ∈ s, X i ω)
      (A := psiSigmaIndependentSumConst σ * Real.sqrt (s.card : ℝ) * K)
      (c := (s.card : ℝ)⁻¹) hcard_inv_nonneg hsum


end

end IndependentSums

end Homogenization
