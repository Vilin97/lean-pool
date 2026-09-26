/-
Copyright (c) 2026 Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka
-/

module

public import LeanPool.NemytskiiLebesgue.Nemytskii

/-!
# Nemytskii operators: Vitali

Adapted from `madvorak/nemytskii-lebesgue` (Apache-2.0).
-/

public section

namespace NemytskiiLebesgue

open scoped NemytskiiLebesgue

open MeasureTheory _root_.Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology

theorem integralLpNorm_nemytskii_rpow_le_of_growth
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F}
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q ≠ ⊤)
    {a : Ω → ℝ} (haq : AEMeasurable a μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    (u : Ω → D) :
    integralLpNorm (fun ω : Ω => f ω (u ω)) q μ ^ q.toReal ≤
      (2 : ℝ≥0∞) ^ (q.toReal - 1) * integralLpNorm a q μ ^ q.toReal +
      (2 : ℝ≥0∞) ^ (q.toReal - 1) * ↱C ^ q.toReal * integralLpNorm u p μ ^ p.toReal := by
  have integral_bound :
      ∫⁻ ω : Ω, (‖f ω (u ω)‖₊ : ℝ≥0∞) ^ q.toReal ∂μ ≤
      2 ^ (q.toReal - 1) * (∫⁻ ω : Ω, (‖a ω‖₊ : ℝ≥0∞) ^ q.toReal ∂μ) +
        2 ^ (q.toReal - 1) * ↱C ^ q.toReal * (∫⁻ ω : Ω, (‖u ω‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) := by
    have integral_bound :
      ∀ᵐ ω : Ω ∂μ,
        (‖f ω (u ω)‖₊ : ℝ≥0∞) ^ q.toReal ≤
        2 ^ (q.toReal - 1) * (‖a ω‖₊ : ℝ≥0∞) ^ q.toReal +
          2 ^ (q.toReal - 1) * ↱C ^ q.toReal * (‖u ω‖₊ : ℝ≥0∞) ^ p.toReal := by
      have integral_bound :
        ∀ᵐ ω : Ω ∂μ,
          (‖f ω (u ω)‖₊ : ℝ≥0∞) ^ q.toReal ≤
          (2 : ℝ≥0∞) ^ (q.toReal - 1) *
            ((‖a ω‖₊ : ℝ≥0∞) ^ q.toReal + ↱C ^ q.toReal * (‖u ω‖₊ : ℝ≥0∞) ^ p.toReal) := by
        have integral_bound :
          ∀ᵐ ω : Ω ∂μ,
            (‖f ω (u ω)‖₊ : ℝ≥0∞) ^ q.toReal ≤
            (2 : ℝ≥0∞) ^ (q.toReal - 1) *
              ((‖a ω‖₊ : ℝ≥0∞) ^ q.toReal +
                (↱C * (‖u ω‖₊ : ℝ≥0∞) ^ (p / q).toReal) ^ q.toReal) := by
          have integral_bound :
            ∀ᵐ ω : Ω ∂μ,
              (‖f ω (u ω)‖₊ : ℝ≥0∞) ≤
              (‖a ω‖₊ : ℝ≥0∞) + ↱C * (‖u ω‖₊ : ℝ≥0∞) ^ (p / q).toReal := by
            filter_upwards [hfaCpq] with ω hω
            convert ENNReal.ofReal_le_ofReal (hω (u ω)) using 1
            · norm_num [ENNReal.ofReal]
            · rw [ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _)
                _)), ENNReal.ofReal_mul hC]
              rw [←ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity)]
              norm_num [←ENNReal.ofReal_coe_nnreal]
          filter_upwards [integral_bound] with ω hω
          apply le_trans (ENNReal.rpow_le_rpow hω ENNReal.toReal_nonneg)
          have h12 :=
            ENNReal.rpow_arith_mean_le_arith_mean_rpow { 0, 1 } ↓(1 / 2)
              (if · = 0 then (‖a ω‖₊ : ℝ≥0∞) else (↱C * ‖u ω‖₊ ^ (p / q).toReal))
          norm_num at h12
          convert! mul_le_mul_right (h12
            (by rw [ENNReal.mul_inv_cancel] <;> norm_num)
            (show 1 ≤ q.toReal by
              rw [←ENNReal.toReal_one]
              exact ENNReal.toReal_mono hq h1q
            )) (2 ^ q.toReal)
              using 1 <;> ring_nf
          · rw [←ENNReal.mul_rpow_of_nonneg] <;> norm_num
            ring_nf
            simp [mul_assoc, ENNReal.inv_mul_cancel]
          · rw [ENNReal.rpow_add] <;> norm_num
            rw [ENNReal.rpow_neg_one]
            ring_nf
        filter_upwards [integral_bound] with ω hω
        convert hω using 2
        rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, ←ENNReal.rpow_mul]
        norm_num [hp, hq]
        rw [div_mul_cancel₀ _ (ne_of_gt (ENNReal.toReal_pos (ne_zero_of_ge_one h1q) hq))]
      simpa only [mul_add, mul_assoc] using integral_bound
    apply le_trans (lintegral_mono_ae integral_bound)
    rw [lintegral_add_left']
    · rw [lintegral_const_mul', lintegral_const_mul'] <;> norm_num
      have h1q : 1 ≤ q.toReal := ENNReal.toReal_mono hq h1q
      apply ENNReal.mul_ne_top <;> exact (ENNReal.rpow_ne_top_of_nonneg (by linarith [h1q]) (by
        simp))
    · apply AEMeasurable.const_mul (haq.nnnorm.coe_nnreal_ennreal.pow_const _)
  convert integral_bound using 1
  · rw [integralLpNorm_eq_lintegral_rpow_enorm_toReal]
    · rewrite [←ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt (ENNReal.toReal_pos
      (ne_zero_of_ge_one h1q) hq)), ENNReal.rpow_one]
      rfl
    · aesop
    · exact hq
  · rw [integralLpNorm_eq_lintegral_rpow_enorm_toReal (ne_zero_of_ge_one h1p) hp,
        integralLpNorm_eq_lintegral_rpow_enorm_toReal (ne_zero_of_ge_one h1q) hq]
    · rw [←ENNReal.rpow_mul, ←ENNReal.rpow_mul]
      norm_num [
        show q.toReal ≠ 0 from ne_of_gt (ENNReal.toReal_pos (ne_zero_of_ge_one h1q) hq),
        show p.toReal ≠ 0 from ne_of_gt (ENNReal.toReal_pos (ne_zero_of_ge_one h1p) hp)]
      rfl

theorem integralLpNorm_nemytskii_rpow_le_of_growth_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k}
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    (u : Ω → ℝ^m) :
    integralLpNorm (fun ω : Ω => f ω (u ω)) q μ ^ q.toReal ≤
      (2 : ℝ≥0∞) ^ (q.toReal - 1) * integralLpNorm a q μ ^ q.toReal +
      (2 : ℝ≥0∞) ^ (q.toReal - 1) * ↱C ^ q.toReal * integralLpNorm u p μ ^ p.toReal :=
  integralLpNorm_nemytskii_rpow_le_of_growth h1p hp.ne_top h1q hq.ne_top haq.aemeasurable hC hfaCpq
    u

theorem IsCaratheodory.seqContinuous_nemytskii_of_aestronglyMeas_of_growth
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {D F : Type*} [NormedAddCommGroup D] [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q ≠ ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {uₙ : ℕ → Ω → D} (huₙ : ∀ n : ℕ, AEStronglyMeasurable (uₙ n) μ)
    {u : Ω → D} (hup : MemLp u p μ)
    (huuₙ : TendstoInMeasure μ uₙ atTop u)
    (hpuₙ : UnifIntegrable uₙ p μ) :
    (fun n : ℕ => fun ω : Ω => f ω (uₙ n ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (u ω)) q μ := by
  have hs :
    ∀ s : ℕ → ℕ, StrictMono s → ∃ s' : ℕ → ℕ,
      StrictMono s' ∧
      (fun n : ℕ => fun ω : Ω => f ω (uₙ (s (s' n)) ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (u
        ω)) q μ := by
    intro s hs
    obtain ⟨s', s'_mono, s'_ae⟩ :
      ∃ s' : ℕ → ℕ,
        StrictMono s' ∧
        ∀ᵐ ω : Ω ∂μ, Tendsto (fun n : ℕ => uₙ (s (s' n)) ω) atTop (𝓝 (u ω)) := by
      have := (huuₙ.comp hs.tendsto_atTop).exists_seq_tendsto_ae
      simp_all
    refine ⟨s', s'_mono, ?_⟩
    apply hf.nemytskii_seqContinuous_of_aestronglyMeas_of_growth h1p hp h1q hq haq hC hfaCpq ↓(huₙ
      _) hup
    have : TendstoInMeasure μ (fun n : ℕ => uₙ (s (s' n))) atTop u :=
      huuₙ.comp (hs.tendsto_atTop.comp s'_mono.tendsto_atTop)
    have : UnifIntegrable (fun n : ℕ => uₙ (s (s' n))) p μ :=
      hpuₙ.comp (fun n => s (s' n))
    unfold Function.NemytskiiConvergesTo
    grind +suggestions
  contrapose! hs
  unfold Function.NemytskiiConvergesTo at *
  rw [ENNReal.tendsto_atTop_zero] at hs
  simp_all only [ne_eq,
      ENNReal.toReal_div,
      gt_iff_lt,
      ge_iff_le,
      not_forall,
      not_exists,
      not_le,
      ENNReal.tendsto_nhds_zero,
      eventually_atTop]
  obtain ⟨x, hx₀, hx⟩ := hs
  choose g hgx hgq using hx
  exact ⟨
    (g <| Nat.recOn · 0 ↓(g · + 1)),
    strictMono_nat_of_lt_succ ↓(lt_of_lt_of_le (Nat.lt_succ_self _) (hgx _)),
    ↓↓⟨x, hx₀, (⟨·, le_rfl, hgq _⟩)⟩⟩

theorem IsCaratheodory.seqContinuous_nemytskii_of_aestronglyMeas_of_growth_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {uₙ : ℕ → Ω → ℝ^m} (huₙ : ∀ n : ℕ, AEMeasurable (uₙ n) μ)
    {u : Ω → ℝ^m} (hup : MemLp u p μ)
    (huuₙ : TendstoInMeasure μ uₙ atTop u)
    (hpuₙ : UnifIntegrable uₙ p μ) :
    (fun n : ℕ => fun ω : Ω => f ω (uₙ n ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (u ω)) q μ :=
  hf.seqContinuous_nemytskii_of_aestronglyMeas_of_growth h1p hp.ne_top h1q hq.ne_top haq hC hfaCpq
    (huₙ ·|>.aestronglyMeasurable) hup huuₙ hpuₙ

lemma integral_inner_ge_of_ae_inner_ge_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : ℕ}
    {g u : Ω → ℝ^k} (hgu : Integrable (fun ω : Ω => ⟪g ω, u ω⟫) μ)
    {b : Ω → ℝ} (hb : Integrable b μ)
    {p : ℝ} (hup : Integrable (‖u ·‖ ^ p) μ)
    {C : ℝ} (hguCupb : ∀ᵐ ω ∂μ, ⟪g ω, u ω⟫ ≥ C * ‖u ω‖ ^ p - b ω) :
    ∫ ω : Ω, ⟪g ω, u ω⟫ ∂μ ≥ C * ∫ ω : Ω, ‖u ω‖ ^ p ∂μ - ∫ ω : Ω, |b ω| ∂μ := by
  have integral_mono : ∫ ω : Ω, ⟪g ω, u ω⟫ ∂μ ≥ ∫ ω : Ω, (C * ‖u ω‖ ^ p - b ω) ∂μ := by
    apply_rules [integral_mono_ae]
    exact Integrable.sub (Integrable.const_mul hup C) hb
  rw [integral_sub (Integrable.const_mul hup _) hb, integral_const_mul] at integral_mono
  exact le_trans (sub_le_sub_left (le_of_abs_le (norm_integral_le_integral_norm b)) _) integral_mono

theorem IsCaratheodory.integral_nemytskii_inner_ge_of_ae_all_inner_ge_of_growth
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : ℕ}
    {f : Ω → ℝ^k → ℝ^k} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^k, ‖f ω ξ‖ ≤ |a ω| + C₁ * ‖ξ‖ ^ (p / q))
    {b : Ω → ℝ} (hb1 : Integrable b μ)
    {C₂ : ℝ} (hfCpb : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^k, ⟪f ω ξ, ξ⟫ ≥ C₂ * ‖ξ‖ ^ p - b ω)
    {u : Ω → ℝ^k} (hup : MemLp u ↱p μ) :
    MemLp (fun ω : Ω => f ω (u ω)) ↱q μ ∧
    Integrable (fun ω : Ω => ⟪f ω (u ω), u ω⟫) μ ∧
    ∫ ω : Ω, ⟪f ω (u ω), u ω⟫ ∂μ ≥ C₂ * ∫ ω : Ω, ‖u ω‖ ^ p ∂μ - ∫ ω : Ω, |b ω| ∂μ :=
  have hp : 1 < p :=
    Real.HolderTriple.lt hpq
  have hwd : MemLp (fun ω : Ω => f ω (u ω)) ↱q μ :=
    hf.memLp_nemytskii_of_growth_of_holderConjugate hpq haq hC₁ hfaCpq hup
  have hinteg : Integrable (fun ω : Ω => ⟪f ω (u ω), u ω⟫) μ :=
    Real.HolderConjugate.integrable_memLp_inner_memLp hpq hwd hup
  have hnorm_integ : Integrable (‖u ·‖ ^ p) μ :=
    integrable_norm_rpow_of_memLp hp hup
  have hae : ∀ᵐ ω ∂μ, ⟪f ω (u ω), u ω⟫ ≥ C₂ * ‖u ω‖ ^ p - b ω := by
    filter_upwards [hfCpb] with ω hω
    exact hω (u ω)
  ⟨hwd, hinteg, integral_inner_ge_of_ae_inner_ge_of_integrable hinteg hb1 hnorm_integ hae⟩

theorem IsCaratheodory.memLp_nemytskii_ofReal_of_growth_of_holderConjugate_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : ℕ}
    {f : Ω → ℝ^k → ℝ^k} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^k, ‖f ω ξ‖ ≤ |a ω| + C₁ * ‖ξ‖ ^ (p / q))
    {u : Ω → ℝ^k} (hup : MemLp u ↱p μ) :
    MemLp (fun ω : Ω => f ω (u ω)) ↱q μ :=
  hf.memLp_nemytskii_of_growth_of_holderConjugate hpq haq hC₁ hfaCpq hup

theorem IsCaratheodory.integrable_inner_difference
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : Ω → E → E} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : E, ‖f ω ξ‖ ≤ |a ω| + C₁ * ‖ξ‖ ^ (p / q))
    {u : Ω → E} (hup : MemLp u ↱p μ)
    {v : Ω → E} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫) μ :=
  Real.HolderConjugate.integrable_memLp_inner_memLp hpq
    (MemLp.sub
      (hf.memLp_nemytskii_of_growth_of_holderConjugate hpq haq hC₁ hfaCpq hup)
      (hf.memLp_nemytskii_of_growth_of_holderConjugate hpq haq hC₁ hfaCpq hvp)
    ) (MemLp.sub hup hvp)

theorem IsCaratheodory.integrable_inner_difference_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : ℕ}
    {f : Ω → ℝ^k → ℝ^k} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^k, ‖f ω ξ‖ ≤ |a ω| + C₁ * ‖ξ‖ ^ (p / q))
    {u : Ω → ℝ^k} (hup : MemLp u ↱p μ)
    {v : Ω → ℝ^k} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫) μ :=
  hf.integrable_inner_difference hpq haq hC₁ hfaCpq hup hvp

theorem IsCaratheodory.coercive_integral_difference
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : Ω → E → E} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : E, ‖f ω ξ‖ ≤ |a ω| + C₁ * ‖ξ‖ ^ (p / q))
    {C₂ : ℝ} (hC₂ : 0 < C₂)
    (hfCp : ∀ᵐ ω ∂μ, ∀ ξ η : E, ⟪f ω ξ - f ω η, ξ - η⟫ ≥ C₂ * ‖ξ - η‖ ^ p)
    {u : Ω → E} (hup : MemLp u ↱p μ)
    {v : Ω → E} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫) μ ∧
    ∫ ω : Ω, ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫ ∂μ ≥ C₂ * ∫ ω : Ω, ‖u ω - v ω‖ ^ p ∂μ := by
  constructor
  · exact hf.integrable_inner_difference hpq haq hC₁ hfaCpq hup hvp
  · rw [←integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall ↓(mul_nonneg hC₂.le (Real.rpow_nonneg (norm_nonneg _) _))
    · apply_rules [IsCaratheodory.integrable_inner_difference]
    · filter_upwards [hfCp] with ω hω
      apply hω

theorem IsCaratheodory.coercive_integral_difference_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : ℕ}
    {f : Ω → ℝ^k → ℝ^k} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^k, ‖f ω ξ‖ ≤ |a ω| + C₁ * ‖ξ‖ ^ (p / q))
    {C₂ : ℝ} (hC₂ : 0 < C₂)
    (hfCp : ∀ᵐ ω ∂μ, ∀ ξ η : ℝ^k, ⟪f ω ξ - f ω η, ξ - η⟫ ≥ C₂ * ‖ξ - η‖ ^ p)
    {u : Ω → ℝ^k} (hup : MemLp u ↱p μ)
    {v : Ω → ℝ^k} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫) μ ∧
    ∫ ω : Ω, ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫ ∂μ ≥ C₂ * ∫ ω : Ω, ‖u ω - v ω‖ ^ p ∂μ :=
  hf.coercive_integral_difference hpq haq hC₁ hfaCpq hC₂ hfCp hup hvp

theorem ae_eq_of_ae_nemytskii_eq_nemytskii_of_ae_all_sub_inner_sub_ge
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : Ω → E → E} {p : ℝ} {C₂ : ℝ} (hC₂ : 0 < C₂)
    (hfCp : ∀ᵐ ω ∂μ, ∀ ξ η : E, ⟪f ω ξ - f ω η, ξ - η⟫ ≥ C₂ * ‖ξ - η‖ ^ p)
    {u v : Ω → E} (huv : (fun ω : Ω => f ω (u ω)) =ᵐ[μ] (fun ω : Ω => f ω (v ω))) :
    u =ᵐ[μ] v := by
  have norm_zero : ∀ᵐ ω ∂μ, ‖u ω - v ω‖ ^ p ≤ 0 := by
    filter_upwards [hfCp, huv] with ω hω₁ hω₂
    contrapose! hω₁
    exact ⟨u ω, v ω, by simpa [hω₂] using mul_pos hC₂ hω₁⟩
  filter_upwards [norm_zero] with ω hω
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  contrapose! hω
  positivity

theorem ae_eq_of_ae_nemytskii_eq_nemytskii_of_ae_all_sub_inner_sub_ge_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : ℕ}
    {f : Ω → ℝ^k → ℝ^k} {p : ℝ} {C₂ : ℝ} (hC₂ : 0 < C₂)
    (hfCp : ∀ᵐ ω ∂μ, ∀ ξ η : ℝ^k, ⟪f ω ξ - f ω η, ξ - η⟫ ≥ C₂ * ‖ξ - η‖ ^ p)
    {u v : Ω → ℝ^k} (huv : (fun ω : Ω => f ω (u ω)) =ᵐ[μ] (fun ω : Ω => f ω (v ω))) :
    u =ᵐ[μ] v :=
  ae_eq_of_ae_nemytskii_eq_nemytskii_of_ae_all_sub_inner_sub_ge hC₂ hfCp huv

end NemytskiiLebesgue
