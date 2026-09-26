/-
Copyright (c) 2026 Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import LeanPool.NemytskiiLebesgue.Continuity

/-!
# Nemytskii operators: Frechet

Adapted from `madvorak/nemytskii-lebesgue` (Apache-2.0).
-/

public section

namespace NemytskiiLebesgue

open scoped NemytskiiLebesgue

open MeasureTheory _root_.Filter
open scoped ENNReal Topology

lemma frechet_remainder_le_of_all_in_set_icc_zero_one_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {g' : E → E →L[ℝ] F} (hgg' : ∀ ξ : E, HasFDerivAt g (g' ξ) ξ)
    {x e : E} {M : ℝ} (hxeM : ∀ t : ℝ, t ∈ Set.Icc 0 1 → ‖g' (x + t • e) - g' x‖ ≤ M) :
    ‖g (x + e) - g x - g' x e‖ ≤ M * ‖e‖ := by
  have remainder : ∀ ξ ∈ segment ℝ x (x + e), ‖g' ξ - g' x‖ ≤ M := by
    simp_all only [Set.mem_Icc,
        and_imp,
        segment_eq_image,
        smul_add,
        Set.mem_image,
        forall_exists_index]
    rintro _ t ht₁ ht₂ rfl
    convert hxeM t ht₁ ht₂ using 1
    simp [←add_assoc, ←add_smul]
  convert (Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (show ∀ ξ ∈ segment ℝ x (x + e), HasFDerivWithinAt (fun ξ : E => g ξ - g' x ξ)
        (g' ξ - g' x) (segment ℝ x (x + e)) ξ from
        fun ξ : E => ↓(HasFDerivAt.hasFDerivWithinAt
          (HasFDerivAt.sub (hgg' ξ) (ContinuousLinearMap.hasFDerivAt _))))
      remainder (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)
    ) using 1 <;> simp [sub_sub_sub_comm]

lemma ae_norm_frechet_ratio_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)}
    (hff' : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {l : ℕ → Ω → ℝ^m} (hl : ∀ᵐ ω : Ω ∂μ, Tendsto (l · ω) atTop (𝓝 0))
    (u : Ω → ℝ^m) :
    ∀ᵐ ω : Ω ∂μ, Tendsto
      (fun n : ℕ => ‖f ω (u ω + l n ω) - f ω (u ω) - f' ω (u ω) (l n ω)‖ / ‖l n ω‖)
      atTop
      (𝓝 0) := by
  filter_upwards [hff', hl] with ω hω hω'
  have hffu := hω (u ω)
  rw [hasFDerivAt_iff_tendsto] at hffu
  convert hffu.comp (show Tendsto (fun n : ℕ => u ω + l n ω) atTop (𝓝 (u ω)) by
    simpa using hω'.const_add (u ω)) using 2
  simp [div_eq_inv_mul]

private lemma ae_norm_frechet_remainder_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)}
    (hf' : ∀ᵐ ω : Ω ∂μ, Continuous (f' ω))
    (hff' : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {C : ℝ} (hC : 0 < C)
    {α : ℝ} (hα : 0 ≤ α)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b)
    (hf'bCα : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ α)
    (u l : Ω → ℝ^m) :
    ∀ᵐ ω : Ω ∂μ,
      ‖f ω (u ω + l ω) - f ω (u ω) - f' ω (u ω) (l ω)‖ ≤
      (2 * b ω + C * (‖u ω‖ + ‖l ω‖) ^ α + C * ‖u ω‖ ^ α) * ‖l ω‖ := by
  filter_upwards [hff', hf', h0b, hf'bCα] with ω hω₁ hω₂ hω₃ hω₄
  apply frechet_remainder_le_of_all_in_set_icc_zero_one_norm_le hω₁
  intro t ht
  apply le_trans (norm_sub_le _ _)
  apply le_trans (add_le_add (hω₄ _) (hω₄ _))
  nlinarith [show ‖u ω + t • l ω‖ ^ α ≤ (‖u ω‖ + ‖l ω‖) ^ α from
    Real.rpow_le_rpow (norm_nonneg _) (by
      simpa [norm_smul, abs_of_nonneg ht.left] using
        le_trans (norm_add_le (u ω) (t • l ω)) <| by
          simpa [norm_smul, abs_of_nonneg ht.left] using
            mul_le_mul_of_nonneg_right ht.right (norm_nonneg (l ω)))
      hα]

lemma integralLpNorm_le_eLpNorm_mul_eLpNorm_of_aestronglyMeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ} {p q r : ℝ} (hrpq : Real.HolderTriple r p q)
    {l : Ω → ℝ^m} (hl : AEStronglyMeasurable l μ)
    {ψ : Ω → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {R : Ω → ℝ^k} (hRψl : ∀ᵐ ω : Ω ∂μ, ‖R ω‖ ≤ ψ ω * ‖l ω‖) :
    integralLpNorm R ↱q μ ≤ eLpNorm ψ ↱r μ * eLpNorm l ↱p μ := by
  let := Real.HolderTriple.ennrealOfReal hrpq
  refine (integralLpNorm_le_eLpNorm_of_ae_le (hψ.mul hl.norm) ?_).trans ?_
  · exact hRψl.mono fun ω hω => hω.trans (le_abs_self _)
  · simpa only [Pi.smul_def, smul_eq_mul, eLpNorm_norm l hl] using
      (eLpNorm_smul_le_mul_eLpNorm (p := ↱r) (q := ↱p) (r := ↱q) hψ hl.norm)

lemma eLpNorm_le_eLpNorm_mul_eLpNorm_of_aestronglyMeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ} {p q r : ℝ} (hrpq : Real.HolderTriple r p q)
    {l : Ω → ℝ^m} (hl : AEStronglyMeasurable l μ)
    {ψ : Ω → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {R : Ω → ℝ^k} (hR : AEStronglyMeasurable R μ)
    (hRψl : ∀ᵐ ω : Ω ∂μ, ‖R ω‖ ≤ ψ ω * ‖l ω‖) :
    eLpNorm R ↱q μ ≤ eLpNorm ψ ↱r μ * eLpNorm l ↱p μ := by
  rw [← integralLpNorm_eq_eLpNorm hR]
  exact integralLpNorm_le_eLpNorm_mul_eLpNorm_of_aestronglyMeas hrpq hl hψ hRψl

private lemma memLp_dominating_of_memLp_of_ea_nonneg_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ} (h1p : 1 ≤ p)
    {r : ℝ} (h1r : 1 ≤ r)
    {b : Ω → ℝ} (hbr : MemLp b ↱r μ)
    {m : ℕ} {u : Ω → ℝ^m} (hup : MemLp u ↱p μ)
    {g : Ω → ℝ} (h0g : 0 ≤ᵐ[μ] g) (hgp : MemLp g ↱p μ)
    (C : ℝ) :
    MemLp (fun ω : Ω => 2 * b ω + C * (‖u ω‖ + g ω) ^ (p / r) + C * ‖u ω‖ ^ (p / r)) ↱r μ := by
  refine MemLp.add (MemLp.add (hbr.const_mul 2) ?_) ?_
  · apply MemLp.const_mul
    convert memLp_rpow_div_of_memLp_of_ae_nonneg .. using 1
    any_goals positivity
    · rw [div_div_cancel₀ (ne_zero_of_ge_one h1p)]
    · filter_upwards [h0g] with ω hω
      exact add_nonneg (norm_nonneg _) hω
    · exact hup.norm.add hgp
  · convert (memLp_norm_rpow_div_of_memLp (show 0 < p / r by positivity) hup.norm).const_mul C
    using 1
    · norm_num
    · rw [div_div_cancel₀ (ne_zero_of_ge_one h1p)]

lemma IsCaratheodory.aestronglyMeas_nemytskii
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {u : Ω → ℝ^m} {p : ℝ} (hup : MemLp u ↱p μ) :
    AEStronglyMeasurable (fun ω : Ω => f ω (u ω)) μ :=
  hf.aestronglyMeas_nemytskii_of_aestronglyMeas hup.aestronglyMeasurable

lemma IsCaratheodory.aestronglyMeas_frechet_remainder
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)} (hf' : IsCaratheodory f' μ)
    {p : ℝ} {u : Ω → ℝ^m} (hup : MemLp u ↱p μ)
    {u' : Ω → ℝ^m} (hu' : AEStronglyMeasurable u' μ) :
    AEStronglyMeasurable
      (fun ω : Ω => f ω (u ω + u' ω) - f ω (u ω) - f' ω (u ω) (u' ω))
      μ := by
  have hderiv := hf'.aestronglyMeas_nemytskii_of_aestronglyMeas hup.aestronglyMeasurable
  have happly : AEStronglyMeasurable (fun ω => f' ω (u ω) (u' ω)) μ :=
    (show Continuous (fun z : (ℝ^m →L[ℝ] ℝ^k) × ℝ^m => z.1 z.2) by
      fun_prop).comp_aestronglyMeasurable
      (hderiv.prodMk hu')
  exact ((hf.aestronglyMeas_nemytskii_of_aestronglyMeas
    (hup.aestronglyMeasurable.add hu')).sub
    (hf.aestronglyMeas_nemytskii hup)).sub happly

lemma ae_frechet_ratio_le_of_ae_all_growth_deriv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)}
    (hf' : ∀ᵐ ω : Ω ∂μ, Continuous (f' ω))
    (hff' : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {C : ℝ} (hC : 0 < C)
    {p : ℝ} (h1p : 1 ≤ p)
    {r : ℝ} (h1r : 1 ≤ r)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b)
    (hf'bCpr : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p / r))
    {g : Ω → ℝ} (h0g : 0 ≤ᵐ[μ] g)
    {v : Ω → ℝ^m} (hvg : ∀ᵐ ω : Ω ∂μ, ‖v ω‖ ≤ g ω)
    (u : Ω → ℝ^m) :
    ∀ᵐ ω : Ω ∂μ,
      ‖f ω (u ω + v ω) - f ω (u ω) - f' ω (u ω) (v ω)‖ / ‖v ω‖ ≤
      2 * b ω + C * (‖u ω‖ + g ω) ^ (p / r) + C * ‖u ω‖ ^ (p / r) := by
  have remainder_bound :
    ∀ᵐ ω : Ω ∂μ,
      ‖f ω (u ω + v ω) - f ω (u ω) - f' ω (u ω) (v ω)‖ ≤
      (2 * b ω + C * (‖u ω‖ + ‖v ω‖) ^ (p / r) + C * ‖u ω‖ ^ (p / r)) * ‖v ω‖ := by
    apply_rules [ae_norm_frechet_remainder_le]
    positivity
  filter_upwards [remainder_bound, hvg, h0b, h0g] with ω hω₁ hω₂ hω₃ hω₄
  apply div_le_of_le_mul₀ <;> simp_all only [Pi.zero_apply,
      norm_nonneg]
  · positivity
  · exact hω₁.trans
      (mul_le_mul_of_nonneg_right (add_le_add_three le_rfl
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow
            (add_nonneg (norm_nonneg (u ω)) (norm_nonneg (v ω)))
            ((add_le_add_iff_left ‖u ω‖).← hω₂) (by positivity))
        hC.le)
      le_rfl) (norm_nonneg (v ω)))

lemma convergesTo_of_ae_tendsTo_of_ae_norm_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    {F : ℕ → Ω → E} (hF : ∀ n : ℕ, AEStronglyMeasurable (F n) μ)
    {g : Ω → E} (hg : AEStronglyMeasurable g μ)
    {b : Ω → ℝ} (hbp : MemLp b p μ)
    (hFb : ∀ n : ℕ, ∀ᵐ ω : Ω ∂μ, ‖F n ω‖ ≤ b ω)
    (hgb : ∀ᵐ ω : Ω ∂μ, ‖g ω‖ ≤ b ω)
    (hFg : ∀ᵐ ω : Ω ∂μ, Tendsto (F · ω) atTop (𝓝 (g ω))) :
    F.NemytskiiConvergesTo g p μ := by
  exact convergesTo_of_tendsTo_of_growth_of_aestronglyMeas hp1 hp hF
    ((eLpNorm_mono_ae hg (hgb.mono fun _ h => h.trans (le_abs_self _))).trans_lt hbp)
    hbp hFb hFg

lemma IsCaratheodory.tendsTo_eLpNorm_frechet_ratio_of_ae_tendsTo
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)} (hf' : IsCaratheodory f' μ)
    (hff' : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {p : ℝ} (h1p : 1 ≤ p)
    {r : ℝ} (h1r : 1 ≤ r)
    {C : ℝ} (hC : 0 < C)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b) (hbr : MemLp b ↱r μ)
    (hf'bCpr : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p / r))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ)
    {l : ℕ → Ω → ℝ^m} (hl : ∀ n : ℕ, AEStronglyMeasurable (l n) μ)
    {g : Ω → ℝ} (h0g : 0 ≤ᵐ[μ] g) (hgp : MemLp g ↱p μ)
    (hlg : ∀ᵐ ω : Ω ∂μ, ∀ n : ℕ, ‖l n ω‖ ≤ g ω)
    (hl0 : ∀ᵐ ω : Ω ∂μ, Tendsto (l · ω) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => eLpNorm
        (fun ω : Ω => ‖f ω (u ω + l n ω) - f ω (u ω) - f' ω (u ω) (l n ω)‖ / ‖l n ω‖) ↱r μ)
      atTop
      (𝓝 0) := by
  simpa [Function.NemytskiiConvergesTo, Pi.sub_def, sub_zero] using
    convergesTo_of_ae_tendsTo_of_ae_norm_le
      (b := fun ω : Ω => 2 * b ω + C * (‖u ω‖ + g ω) ^ (p / r) + C * ‖u ω‖ ^ (p / r))
      (ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal h1r)
      ENNReal.ofReal_ne_top
      (fun n : ℕ => by
        have remainder_meas : AEStronglyMeasurable (fun ω : Ω => f ω (u ω + l n ω) - f ω (u ω) -
          (f' ω (u ω)) (l n ω)) μ := by
          apply_rules [aestronglyMeas_frechet_remainder]
        exact remainder_meas.norm.mul ((hl n).norm.aemeasurable.inv.aestronglyMeasurable)
      )
      aestronglyMeasurable_const
      (by apply_rules [memLp_dominating_of_memLp_of_ea_nonneg_of_memLp])
      (fun n : ℕ => by
        filter_upwards [ae_frechet_ratio_le_of_ae_all_growth_deriv hf'.ae_continuous hff' hC h1p
          h1r h0b hf'bCpr h0g (hlg.mono ↓(· n)) u] with _ _
        rwa [Real.norm_of_nonneg (by positivity)]
      )
      (by
        filter_upwards [h0b, h0g] with ω hbω hgω
        simpa using add_nonneg
          (add_nonneg (mul_nonneg zero_le_two hbω) (mul_nonneg hC.le (Real.rpow_nonneg (add_nonneg
            (norm_nonneg _) hgω) _)))
          (mul_nonneg hC.le (Real.rpow_nonneg (norm_nonneg _) _))
      )
      (ae_norm_frechet_ratio_tendsto_zero hff' hl0 _)

lemma Filter.Tendsto.extract_fast_subseq_eLpNorm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {l : ℕ → Ω → E} (hlp : Tendsto (fun n : ℕ => eLpNorm (l n) p μ) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ k : ℕ, eLpNorm (l (s k)) p μ ≤ ↱(1 / 2 ^ k) := by
  convert Filter.Tendsto.exists_fast_subseq hlp
  rw [←one_pow, ←div_pow, ENNReal.ofReal_pow one_half_pos.le]
  norm_num [ENNReal.ofReal_div_of_pos]

private lemma ae_summable_rpow_of_tsum_lintegral_finite
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {l : ℕ → Ω → E} (hl : ∀ n : ℕ, AEStronglyMeasurable (l n) μ)
    {p : ℝ} (hlp : ∑' k : ℕ, ∫⁻ ω : Ω, ↱(‖l k ω‖ ^ p) ∂μ ≠ ⊤) :
    ∀ᵐ ω : Ω ∂μ, Summable (‖l · ω‖ ^ p) := by
  have fubini :
      ∫⁻ ω : Ω, ∑' k : ℕ, ↱(‖l k ω‖ ^ p) ∂μ =
      ∑' k : ℕ, ∫⁻ ω : Ω, ↱(‖l k ω‖ ^ p) ∂μ := by
    rw [lintegral_tsum]
    intro n
    exact ((hl n).norm.aemeasurable.pow_const p).ennreal_ofReal
  have fubin : ∀ᵐ ω : Ω ∂μ, ∑' k : ℕ, ↱(‖l k ω‖ ^ p) < ⊤ := by
    have fubi : ∫⁻ ω : Ω, ∑' k : ℕ, ↱(‖l k ω‖ ^ p) ∂μ < ⊤ :=
      fubini ▸ lt_top_iff_ne_top.← hlp
    refine ae_lt_top' ?_ fubi.ne
    apply AEMeasurable.tsum
    exact (ENNReal.continuous_ofReal.measurable.comp_aemeasurable <| hl · |>.norm
      |>.aemeasurable.pow_const p)
  filter_upwards [fubin] with ω hω
  convert ENNReal.summable_toReal _
  rotate_left
  · exact fun k : ℕ => ↱(‖l k ω‖ ^ p)
  · exact ne_of_lt hω
  · rw [ENNReal.toReal_ofReal (by positivity)]

private lemma ae_all_norm_le_tsum_norm_rpow_inv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {p : ℝ} (h1p : 1 ≤ p)
    {l : ℕ → Ω → E} (hlp : ∀ᵐ ω : Ω ∂μ, Summable (‖l · ω‖ ^ p)) :
    ∀ᵐ ω : Ω ∂μ, ∀ n : ℕ, ‖l n ω‖ ≤ (∑' k : ℕ, ‖l k ω‖ ^ p) ^ (1/p) := by
  filter_upwards [hlp] with ω hω
  intro n
  rw [one_div]
  refine le_trans ?_ (Real.rpow_le_rpow (by positivity) (hω.le_tsum n ↓↓(by positivity)) (by
    positivity))
  rw [←Real.rpow_mul (norm_nonneg (l n ω)), mul_inv_cancel₀ (ne_zero_of_ge_one h1p), Real.rpow_one]

private lemma ae_tendsto_zero_of_ae_summable_rpow
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {p : ℝ} (hp : 0 < p)
    {l : ℕ → Ω → E} (hlp : ∀ᵐ ω : Ω ∂μ, Summable (‖l · ω‖ ^ p)) :
    ∀ᵐ ω : Ω ∂μ, Tendsto (l · ω) atTop (𝓝 0) := by
  have norm_zero : ∀ᵐ ω : Ω ∂μ, Tendsto (‖l · ω‖) atTop (𝓝 0) := by
    filter_upwards [hlp] with ω hω
    convert hω.tendsto_atTop_zero.rpow_const _ using 1
    · ext
      rw [←Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ (ne_of_gt hp), Real.rpow_one]
    · simp [hp.ne']
    · right
      exact inv_nonneg.← hp.le
  filter_upwards [norm_zero] with ω hω using tendsto_zero_iff_norm_tendsto_zero.← hω

private lemma exists_exists_strictMono_and_memLp_and_ae_nonneg_and
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E]
    {p : ℝ} (hp : 1 ≤ p)
    {l : ℕ → Ω → E} (hl : ∀ n : ℕ, AEStronglyMeasurable (l n) μ)
    (hlp : Tendsto (fun n : ℕ => eLpNorm (l n) ↱p μ) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, ∃ g : Ω → ℝ,
      StrictMono s ∧
      MemLp g ↱p μ ∧
      (0 ≤ᵐ[μ] g) ∧
      (∀ᵐ ω : Ω ∂μ, ∀ n : ℕ, ‖l (s n) ω‖ ≤ g ω) ∧
      (∀ᵐ ω : Ω ∂μ, Tendsto (fun n : ℕ => l (s n) ω) atTop (𝓝 0)) := by
  obtain ⟨s, s_mono, s_eLpNorm⟩ : ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ k : ℕ, eLpNorm (l (s k)) ↱p μ ≤ ↱(1
    / 2 ^ k) :=
    Filter.Tendsto.extract_fast_subseq_eLpNorm hlp
  have hlp : ∑' k : ℕ, ∫⁻ ω, ↱(‖l (s k) ω‖ ^ p) ∂μ ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum
      (g := fun k : ℕ => ↱(1 / 2 ^ k) ^ p) fun k => ?_) ?_)
    · convert ENNReal.rpow_le_rpow (s_eLpNorm k) (by positivity) using 1
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
      · simp [ENNReal.toReal_ofReal (zero_le_one.trans hp), ←ENNReal.rpow_mul]
        simp [←ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity), ne_of_gt
          (zero_lt_one.trans_le hp)]
      · positivity
      · exact ENNReal.ofReal_ne_top
      · exact hl (s k)
    · have geo_series : ∑' k : ℕ, ↱(1 / 2 ^ k) ^ p = ∑' k : ℕ, ↱((1 / 2 ^ p) ^ k) := by
        refine tsum_congr ↓?_
        rw [ENNReal.ofReal_rpow_of_pos (by positivity)]
        ring_nf
        rw [←Real.rpow_natCast, ←Real.rpow_mul (by positivity), mul_comm, Real.rpow_mul (by
          positivity), Real.inv_rpow zero_le_two]
        norm_num
      rw [geo_series, ←ENNReal.ofReal_tsum_of_nonneg] <;> norm_num
      · intro
        positivity
      · apply inv_lt_one_of_one_lt₀
        rw [abs_of_nonneg (by positivity)]
        apply Real.one_lt_rpow one_lt_two
        positivity
  refine ⟨s, fun ω : Ω => (∑' k : ℕ, ‖l (s k) ω‖ ^ p) ^ (1 / p), s_mono, ?_, ?_, ?_, ?_⟩
  · have g_in_Lp : ∫⁻ ω, ↱((∑' k : ℕ, ‖l (s k) ω‖ ^ p) ^ (1 / p * p)) ∂μ < ⊤ := by
      have g_in_Lp : ∫⁻ ω, ↱(∑' k : ℕ, ‖l (s k) ω‖ ^ p) ∂μ ≤ ∑' k : ℕ, ∫⁻ ω, ↱(‖l (s k) ω‖ ^ p) ∂μ
        := by
        rw [←lintegral_tsum]
        · refine lintegral_mono fun ω : Ω => ?_
          by_cases summabl : Summable (fun k : ℕ => ‖l (s k) ω‖ ^ p)
          · rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
              summabl]
          · rw [tsum_eq_zero_of_not_summable summabl]
            simp
        · intro k
          apply ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          exact (hl (s k)).norm.aemeasurable.pow_const p
      simpa [ne_zero_of_ge_one hp] using lt_of_le_of_lt g_in_Lp (lt_top_iff_ne_top.← hlp)
    have hmeas : AEStronglyMeasurable
        (fun ω => (∑' k : ℕ, ‖l (s k) ω‖ ^ p) ^ (1 / p)) μ := by
      have : ∀ k : ℕ, AEStronglyMeasurable (fun ω : Ω => ‖l (s k) ω‖ ^ p) μ :=
        fun k : ℕ => (hl (s k)).norm.aemeasurable.pow_const p |>.aestronglyMeasurable
      have g_in_Lp : AEStronglyMeasurable (fun ω : Ω => ∑' k : ℕ, ‖l (s k) ω‖ ^ p) μ :=
        have g_in_Lp₁ : ∀ᵐ ω : Ω ∂μ, Summable (fun k : ℕ => ‖l (s k) ω‖ ^ p) := by
          apply_rules [ae_summable_rpow_of_tsum_lintegral_finite]
          exact ↓(hl _)
        have g_in_Lp₂ :
          ∀ᵐ ω : Ω ∂μ,
            Tendsto
              (fun n : ℕ => ∑ k ∈ Finset.range n, ‖l (s k) ω‖ ^ p)
              atTop
              (𝓝 (∑' k : ℕ, ‖l (s k) ω‖ ^ p)) :=
          g_in_Lp₁.mono ↓(·.hasSum.tendsto_sum_nat)
        have g_in_Lp₃ : ∀ n : ℕ, AEStronglyMeasurable (fun ω : Ω => ∑ k ∈ Finset.range n, ‖l (s k)
          ω‖ ^ p) μ := by
          fun_prop
        aestronglyMeasurable_of_tendsto_ae _ g_in_Lp₃ g_in_Lp₂
      exact g_in_Lp.aemeasurable.pow_const (1/p) |>.aestronglyMeasurable
    apply memLp_iff_measurable_and_finite.mpr
    refine ⟨hmeas, ?_⟩
    · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal _ _ hmeas]
      · apply ENNReal.rpow_lt_top_of_nonneg
        · positivity
        · convert g_in_Lp.ne using 1
          apply lintegral_congr
          intro
          rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (tsum_nonneg ↓(by positivity)) _),
              ENNReal.toReal_ofReal (by positivity),
              ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (tsum_nonneg ↓(by positivity)) _) (by
                positivity),
              ←Real.rpow_mul (tsum_nonneg ↓(by positivity))]
      · positivity
      · exact ENNReal.ofReal_ne_top
  · exact Eventually.of_forall ↓(Real.rpow_nonneg (tsum_nonneg ↓(Real.rpow_nonneg (norm_nonneg _)
    _)) _)
  · exact ae_all_norm_le_tsum_norm_rpow_inv hp (ae_summable_rpow_of_tsum_lintegral_finite (hl <| s
    ·) hlp)
  · apply_rules [ae_tendsto_zero_of_ae_summable_rpow]
    · positivity
    · apply_rules [ae_summable_rpow_of_tsum_lintegral_finite]
      exact ↓(hl _)

theorem IsCaratheodory.eLpNorm_frechet_remainder_le_ofReal_mul_eLpNorm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)} (hf' : IsCaratheodory f' μ)
    (hff' : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {p q r : ℝ} (h1p : 1 ≤ p) (h1r : 1 ≤ r) (hrpq : Real.HolderTriple r p q)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b) (hbr : MemLp b ↱r μ)
    {C : ℝ} (hC : 0 < C)
    (hf'bCpr : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p / r))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ) :
    ∀ ε > 0, ∃ δ > 0, ∀ l : Ω → ℝ^m,
      MemLp l ↱p μ →
        eLpNorm l ↱p μ ≤ ↱δ →
          eLpNorm (fun ω : Ω => f ω (u ω + l ω) - f ω (u ω) - f' ω (u ω) (l ω)) ↱q μ ≤
          ↱ε * eLpNorm l ↱p μ := by
  intro ε hε
  by_contra! contra
  obtain ⟨l, l_mem, l_small, l_bad⟩ :
    ∃ l : ℕ → Ω → ℝ^m,
      (∀ n : ℕ, MemLp (l n) ↱p μ) ∧
      (∀ n : ℕ, eLpNorm (l n) ↱p μ ≤ ↱(1 / (n + 1))) ∧
      (∀ n : ℕ, ↱ε * eLpNorm (l n) ↱p μ < eLpNorm (fun ω : Ω => f ω (u ω + l n ω) - f ω (u ω) - (f'
        ω (u ω)) (l n ω)) ↱q μ) :=
    ⟨fun n : ℕ => Classical.choose      (contra (1 / (n + 1)) (Nat.real_one_div_succ_pos n)),
     fun n : ℕ => Classical.choose_spec (contra (1 / (n + 1)) (Nat.real_one_div_succ_pos n))
       |>.left,
     fun n : ℕ => Classical.choose_spec (contra (1 / (n + 1)) (Nat.real_one_div_succ_pos n))
       |>.right.left,
     fun n : ℕ => Classical.choose_spec (contra (1 / (n + 1)) (Nat.real_one_div_succ_pos n))
       |>.right.right⟩
  obtain ⟨s, g, s_mono, g_mem, h0g, g_dom, g_tendsto⟩ :
    ∃ s : ℕ → ℕ, ∃ g : Ω → ℝ,
      StrictMono s ∧
      MemLp g ↱p μ ∧
      0 ≤ᵐ[μ] g ∧
      (∀ᵐ ω : Ω ∂μ, ∀ n : ℕ, ‖l (s n) ω‖ ≤ g ω) ∧
      (∀ᵐ ω : Ω ∂μ, Tendsto (fun n : ℕ => l (s n) ω) atTop (𝓝 0)) := by
    apply exists_exists_strictMono_and_memLp_and_ae_nonneg_and
    · exact h1p
    · exact fun n : ℕ => (l_mem n).aestronglyMeasurable
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ ↓zero_le l_small
      simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have ratio_tendsto :
    Tendsto
      (fun n : ℕ => eLpNorm (fun ω : Ω => ‖f ω (u ω + l (s n) ω) - f ω (u ω) - (f' ω (u ω)) (l (s
        n) ω)‖ / ‖l (s n) ω‖) ↱r μ)
      atTop
      (𝓝 0) :=
    hf.tendsTo_eLpNorm_frechet_ratio_of_ae_tendsTo hf' hff' h1p h1r hC h0b hbr hf'bCpr hup
      (MemLp.aestronglyMeasurable <| l_mem <| s ·) h0g g_mem g_dom g_tendsto
  have remainder_tendsto :
    ∀ n : ℕ,
      eLpNorm (fun ω : Ω =>  f ω (u ω + l (s n) ω) - f ω (u ω) - (f' ω (u ω)) (l (s n) ω)) ↱q μ ≤
      eLpNorm (fun ω : Ω => ‖f ω (u ω + l (s n) ω) - f ω (u ω) - (f' ω (u ω)) (l (s n) ω)‖ / ‖l (s
        n) ω‖) ↱r μ *
        eLpNorm (l (s n)) ↱p μ := by
    intro n
    have hl := (l_mem (s n)).aestronglyMeasurable
    have hR := hf.aestronglyMeas_frechet_remainder hf' hup hl
    apply eLpNorm_le_eLpNorm_mul_eLpNorm_of_aestronglyMeas hrpq hl
      (hR.norm.mul hl.norm.aemeasurable.inv.aestronglyMeasurable) hR
    filter_upwards with ω
    by_cases h0 : l (s n) ω = 0 <;> simp [h0]
  have contradicti :
    ∀ᶠ n in atTop,
      eLpNorm (fun ω : Ω => f ω (u ω + l (s n) ω) - f ω (u ω) - (f' ω (u ω)) (l (s n) ω)) ↱q μ ≤
      ↱ε * eLpNorm (l (s n)) ↱p μ := by
    filter_upwards [ratio_tendsto.eventually (gt_mem_nhds <| show 0 < ↱ε from ENNReal.ofReal_pos.←
      hε)]
      with n hn
      using le_trans (remainder_tendsto n) (mul_le_mul_left hn.le _)
  exact (fun ⟨n, hn⟩ => not_le_of_gt (l_bad (s n)) hn) contradicti.exists

end NemytskiiLebesgue
