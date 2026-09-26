/-
Copyright (c) 2026 Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka
-/

module

public import Mathlib.MeasureTheory.Function.UnifTight
public import LeanPool.NemytskiiLebesgue.Caratheodory

/-!
# Nemytskii operators: Continuity

Adapted from `madvorak/nemytskii-lebesgue` (Apache-2.0).
-/

public section

namespace NemytskiiLebesgue

open scoped NemytskiiLebesgue

open MeasureTheory _root_.Filter
open scoped NNReal ENNReal Topology

/-- A sequence of functions `f` converges to a function `g` in the L`p` norm with respect to a
  measure `μ`. -/
@[expose] def _root_.Function.NemytskiiConvergesTo
    {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [NormedAddCommGroup D]
    (f : ℕ → Ω → D) (g : Ω → D) (p : ℝ≥0∞) (μ : Measure Ω) :
    Prop :=
  Tendsto (fun n : ℕ => eLpNorm (f n - g) p μ) atTop (𝓝 0)

lemma memLp_nemytskii_of_growth_of_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F}
    {p : ℝ≥0∞} (h0p : 0 < p) (hp : p ≠ ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q ≠ ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {u : Ω → D} (hup : MemLp u p μ)
    (hfu : AEStronglyMeasurable (fun ω : Ω => f ω (u ω)) μ) :
    MemLp (fun ω : Ω => f ω (u ω)) q μ := by
  have hfuaCpq : ∀ᵐ ω : Ω ∂μ, ‖f ω (u ω)‖ ≤ |a ω| + C * ‖u ω‖ ^ (p / q).toReal := by
    filter_upwards [hfaCpq] with ω hω using hω (u ω)
  have integrabl : Integrable (fun ω : Ω => (|a ω| + C * ‖u ω‖ ^ (p / q).toReal) ^ q.toReal) μ := by
    have integrab :
        Integrable (fun ω : Ω => |a ω| ^ q.toReal) μ ∧
        Integrable (fun ω : Ω => (C * ‖u ω‖ ^ (p / q).toReal) ^ q.toReal) μ := by
      constructor
      · have := haq.integrable_norm_rpow
        aesop
      · have integra : Integrable (‖u ·‖ ^ p.toReal) μ := by
          convert hup.integrable_norm_rpow _ using 1 <;> aesop
        convert integra.const_mul (C ^ q.toReal) using 2
        rw [Real.mul_rpow hC (Real.rpow_nonneg (norm_nonneg (u _)) (p / q).toReal),
            ←Real.rpow_mul (norm_nonneg _),
            ENNReal.toReal_div,
            div_mul_cancel₀ _ (ne_of_gt (ENNReal.toReal_pos (ne_zero_of_ge_one h1q) hq))]
    apply ((integrab.left.add integrab.right).const_mul (2 ^ q.toReal)).mono'
    · exact ((haq.aestronglyMeasurable.norm.add
      ((hup.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable.const_mul
      C)).aemeasurable.pow_const _).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_of_nonneg (by positivity)]
      have ineq : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x + y) ^ q.toReal ≤ 2 ^ q.toReal * (x ^ q.toReal + y
        ^ q.toReal) := by
        intro x y hx hy
        have ineq : (x + y) ^ q.toReal ≤ (2 * max x y) ^ q.toReal :=
          Real.rpow_le_rpow (add_nonneg hx hy) (by linarith [le_max_left x y, le_max_right x y])
            ENNReal.toReal_nonneg
        rw [Real.mul_rpow zero_le_two (le_sup_of_le_right hy)] at ineq
        apply ineq.trans
        apply mul_le_mul_of_nonneg_left
        · rw [max_def_lt]
          split_ifs <;> linarith [Real.rpow_nonneg hx q.toReal, Real.rpow_nonneg hy q.toReal]
        · positivity
      exact ineq |a ω| _ (abs_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _))
  have integrble : Integrable (fun ω : Ω => ‖f ω (u ω)‖ ^ q.toReal) μ := by
    refine integrabl.mono' ?_ ?_
    · exact (hfu.norm.aemeasurable.pow_const q.toReal).aestronglyMeasurable
    · filter_upwards [hfuaCpq] with ω hω
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg (f ω (u ω))) q.toReal)]
      exact Real.rpow_le_rpow (norm_nonneg (f ω (u ω))) hω ENNReal.toReal_nonneg
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_zero_of_ge_one h1q) hq hfu]
  · apply ENNReal.rpow_lt_top_of_nonneg
    · positivity
    · convert integrble.right.ne using 1
      simp [Real.enorm_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg]

theorem IsCaratheodory.memLp_nemytskii_of_growth
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q ≠ ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {u : Ω → D} (hup : MemLp u p μ) :
    MemLp (fun ω : Ω => f ω (u ω)) q μ := by
  apply memLp_nemytskii_of_growth_of_aestronglyMeasurable (zero_lt_one.trans_le h1p) hp h1q hq haq
    hC hfaCpq hup
  exact hf.aestronglyMeas_nemytskii_of_aestronglyMeas hup.aestronglyMeasurable

theorem IsCaratheodory.memLp_nemytskii_of_growth_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {u : Ω → ℝ^m} (hup : MemLp u p μ) :
    MemLp (fun ω : Ω => f ω (u ω)) q μ :=
  hf.memLp_nemytskii_of_growth h1p hp.ne_top h1q hq.ne_top haq hC hfaCpq hup

theorem IsCaratheodory.memLp_nemytskii_of_growth_of_holderConjugate
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {f : Ω → D → D} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q))
    {u : Ω → D} (hup : MemLp u ↱p μ) :
    MemLp (fun ω : Ω => f ω (u ω)) ↱q μ := by
  have hp : 1 ≤ p := by
    rw [Real.holderConjugate_iff] at hpq
    exact hpq.left.le
  have hq : 1 ≤ q := by
    rw [Real.holderConjugate_comm, Real.holderConjugate_iff] at hpq
    exact hpq.left.le
  exact
    hf.memLp_nemytskii_of_growth
      (by rwa [ENNReal.one_le_ofReal]) ENNReal.ofReal_ne_top
      (by rwa [ENNReal.one_le_ofReal]) ENNReal.ofReal_ne_top
      haq hC (ofReal_div_ofReal_toReal (zero_le_one.trans hp) (zero_le_one.trans hq) ▸ hfaCpq)
      hup

lemma convergesTo_of_tendsTo_of_growth_of_aestronglyMeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : Type*} [NormedAddCommGroup F]
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {f : ℕ → Ω → F} (f_meas : ∀ n : ℕ, AEStronglyMeasurable (f n) μ)
    {g : Ω → F} (hgp : MemLp g p μ)
    {l : Ω → ℝ} (hlp : MemLp l p μ)
    (hfl : ∀ n : ℕ, ∀ᵐ ω : Ω ∂μ, ‖f n ω‖ ≤ l ω)
    (hfg : ∀ᵐ ω : Ω ∂μ, Tendsto (fun n : ℕ => f n ω) atTop (𝓝 (g ω))) :
    f.NemytskiiConvergesTo g p μ := by
  apply tendsto_Lp_of_tendsto_ae h1p hp f_meas hgp _ _ hfg
  · rw [unifIntegrable_iff]
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ :=
      unifIntegrable_iff.mp (unifIntegrable_const (ι := ℕ) h1p hp hlp) ε hε
    refine ⟨δ, hδ, fun n s hs => ?_⟩
    apply le_trans (eLpNorm_mono_ae (f_meas n).restrict _) (hbound n s hs)
    filter_upwards [ae_restrict_of_ae (hfl n)] with ω hω
    exact hω.trans (le_abs_self _)
  · intro ε hε
    obtain ⟨s, hs, hμs, hbound⟩ :=
      (unifTight_const (ι := ℕ) hp hlp).exists_measurableSet_indicator hε.ne'
    refine ⟨s, hμs.ne, fun n => ?_⟩
    apply le_trans (eLpNorm_mono_ae ((f_meas n).indicator hs.compl) _) (hbound n)
    filter_upwards [hfl n] with ω hω
    by_cases hωs : ω ∈ sᶜ
    · rw [Set.indicator_of_mem hωs, Set.indicator_of_mem hωs]
      exact hω.trans (le_abs_self _)
    · rw [Set.indicator_of_notMem hωs, Set.indicator_of_notMem hωs]
      simp

lemma Filter.Tendsto.exists_fast_subseq
    {f : ℕ → ℝ≥0∞} (hf : Tendsto f atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ n : ℕ, f (s n) ≤ (1 / 2 : ℝ≥0∞) ^ n := by
  have hN : ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, f n ≤ (1 / 2) ^ k :=
    fun k : ℕ => by simpa using hf.eventually (ge_mem_nhds <| ENNReal.pow_pos (by norm_num) _)
  choose N hN using hN
  exact ⟨fun n : ℕ => n.recOn (N 0) fun k : ℕ => fun m : ℕ => (N (k + 1)) ⊔ (m + 1),
    strictMono_nat_of_lt_succ (by simp),
    (hN _ _ <| ·.recOn (by norm_num) (by simp))⟩

lemma ae_summable_norm_of_tsum_eLpNorm_ne_top_of_aestronglyMeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {g : ℕ → Ω → D} (hg : ∀ n : ℕ, AEStronglyMeasurable (g n) μ) (hgp : ∑' n : ℕ, eLpNorm (g n) p μ
      ≠ ⊤) :
    ∀ᵐ ω : Ω ∂μ, Summable (‖g · ω‖) := by
  have minkowski : ∀ N : ℕ, eLpNorm (∑ n ∈ Finset.range N, ‖g n ·‖) p μ ≤ ∑ n ∈ Finset.range N,
    eLpNorm (g n) p μ := by
    have summ : ∀ N : ℕ, eLpNorm (∑ n ∈ Finset.range N, ‖g n ·‖) p μ ≤ ∑ n ∈ Finset.range N,
      eLpNorm (‖g n ·‖) p μ := by
      intro N
      simpa only [Finset.sum_apply, Finset.sum_fn] using
        (eLpNorm_sum_le (f := fun n ω => ‖g n ω‖) (μ := μ) (s := Finset.range N) h1p)
    intro N
    simpa only [eLpNorm_norm _ (hg _)] using summ N
  have finite_integral : ∫⁻ ω : Ω, (∑' n : ℕ, ‖g n ω‖ₑ) ^ p.toReal ∂μ ≤ (∑' n : ℕ, eLpNorm (g n) p
    μ) ^ p.toReal := by
    have integral_le :
      ∀ N : ℕ,
        ∫⁻ ω : Ω, (∑ n ∈ Finset.range N, ‖g n ω‖ₑ) ^ p.toReal ∂μ ≤ (∑ n ∈ Finset.range N, eLpNorm
          (g n) p μ) ^ p.toReal := by
      intro N
      have integral_le_step : eLpNorm (∑ n ∈ Finset.range N, ‖g n ·‖) p μ ≤ ∑ n ∈ Finset.range N,
        eLpNorm (g n) p μ :=
        minkowski N
      have integral_le_step' :
          (∫⁻ ω : Ω, (∑ n ∈ Finset.range N, ‖g n ω‖ₑ) ^ p.toReal ∂μ) ^ (1 / p.toReal) ≤
          ∑ n ∈ Finset.range N, eLpNorm (g n) p μ := by
        convert integral_le_step using 1
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
        · simp [Real.enorm_eq_ofReal (Finset.sum_nonneg ↓↓(norm_nonneg _))]
          simp [ENNReal.ofReal_sum_of_nonneg ↓↓(norm_nonneg _)]
        · exact ne_of_gt (lt_of_lt_of_le zero_lt_one h1p)
        · exact hp
        · fun_prop
      have integral_le_step'' :
          ∫⁻ ω : Ω, (∑ n ∈ Finset.range N, ‖g n ω‖ₑ) ^ p.toReal ∂μ ≤
          (∑ n ∈ Finset.range N, eLpNorm (g n) p μ) ^ p.toReal := by
        convert ENNReal.rpow_le_rpow integral_le_step' _ using 1
        · rw [←ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt (ENNReal.toReal_pos
          (ne_zero_of_ge_one h1p) hp)), ENNReal.rpow_one]
        · positivity
      exact integral_le_step''
    have integral_le' : ∫⁻ ω : Ω, (∑' n : ℕ, ‖g n ω‖ₑ) ^ p.toReal ∂μ ≤ ∫⁻ ω : Ω, (⨆ N : ℕ, (∑ n ∈
      Finset.range N, ‖g n ω‖ₑ) ^ p.toReal) ∂μ := by
      refine lintegral_mono fun ω : Ω => ?_
      by_cases summmable : Summable (‖g · ω‖ₑ)
      · have integral_le : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, ‖g n ω‖ₑ) ^ p.toReal) atTop
          (𝓝 ((∑' n : ℕ, ‖g n ω‖ₑ) ^ p.toReal)) :=
          ENNReal.continuous_rpow_const.continuousAt.tendsto.comp summmable.hasSum.tendsto_sum_nat
        exact le_of_tendsto integral_le (eventually_atTop.← ⟨0, fun N : ℕ => ↓(le_iSup_of_le N
          le_rfl)⟩)
      · rw [tsum_eq_zero_of_not_summable summmable,
          ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos (ne_zero_of_ge_one h1p) hp)]
        exact zero_le
    nontriviality
    refine integral_le'.trans (le_of_tendsto_of_tendsto'
      (f := fun N => ∫⁻ ω, (∑ n ∈ Finset.range N, ‖g n ω‖ₑ) ^ p.toReal ∂μ)
      (g := fun N => (∑ n ∈ Finset.range N, eLpNorm (g n) p μ) ^ p.toReal)
      (lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_) ?_ integral_le)
    · fun_prop
    · exact Eventually.of_forall ↓(fun hle : · ≤ · =>
          ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (Finset.range_mono hle))
            ENNReal.toReal_nonneg)
    · exact Eventually.of_forall ↓(tendsto_atTop_iSup (fun hle : · ≤ · =>
          ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (Finset.range_mono hle))
            ENNReal.toReal_nonneg))
    · apply ENNReal.continuous_rpow_const.continuousAt.tendsto.comp
      exact ENNReal.summable.hasSum.tendsto_sum_nat
  have finite_ae : ∀ᵐ ω : Ω ∂μ, (∑' n : ℕ, ‖g n ω‖ₑ) ^ p.toReal < ⊤ :=
    have finite_integr : ∫⁻ ω : Ω, (∑' n : ℕ, ‖g n ω‖ₑ) ^ p.toReal ∂μ < ⊤ :=
      lt_of_le_of_lt finite_integral (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hgp)
    ae_lt_top' (by measurability) finite_integr.ne
  filter_upwards [finite_ae] with ω hω
  convert! ENNReal.tsum_coe_ne_top_iff_summable.→ (show (∑' n : ℕ, ‖g n ω‖ₑ) ≠ ⊤ from ?_) using 1
  · ext
    simp [←NNReal.summable_coe]
  · contrapose! hω
    rw [hω, ENNReal.top_rpow_of_pos (ENNReal.toReal_pos (ne_zero_of_ge_one h1p) hp)]

private lemma ae_norm_le_add_tsum_dist_of_ae_summable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {g : ℕ → Ω → D} {u : Ω → D}
    (hgu : ∀ᵐ ω : Ω ∂μ, Summable (‖g · ω - u ω‖))
    (n : ℕ) :
    ∀ᵐ ω : Ω ∂μ, ‖g n ω‖ ≤ ‖u ω‖ + ∑' k : ℕ, ‖g k ω - u ω‖ := by
  have ineq : ∀ᵐ ω : Ω ∂μ, ‖g n ω - u ω‖ ≤ ∑' k : ℕ, ‖g k ω - u ω‖ := by
    filter_upwards [hgu] with ω hω using Summable.le_tsum hω n ↓↓(norm_nonneg _)
  filter_upwards [ineq] with ω hω
  simpa using
    le_trans (norm_add_le (u ω) (g n ω - u ω)) <| by
      simpa only [add_le_add_iff_left] using hω

private lemma memLp_norm_add_tsum_dist_of_eastronglyMeas_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {g : ℕ → Ω → D} {u : Ω → D}
    (hg : ∀ n : ℕ, AEStronglyMeasurable (g n) μ)
    (hup : MemLp u p μ)
    (hgp : ∑' n : ℕ, eLpNorm (g n - u) p μ ≠ ⊤) :
    MemLp (fun ω : Ω => ‖u ω‖ + ∑' n : ℕ, ‖g n ω - u ω‖) p μ := by
  have summable : ∀ᵐ ω ∂μ, Summable (‖g · ω - u ω‖) :=
    ae_summable_norm_of_tsum_eLpNorm_ne_top_of_aestronglyMeas h1p hp
      (fun n => (hg n).sub hup.aestronglyMeasurable) hgp
  have sum_meas (N : ℕ) :
      AEStronglyMeasurable (fun ω => ∑ n ∈ Finset.range N, ‖g n ω - u ω‖) μ := by
    exact (Finset.range N).aestronglyMeasurable_fun_sum
      (fun n _ => ((hg n).sub hup.aestronglyMeasurable).norm)
  have tsum_meas : AEStronglyMeasurable (fun ω => ∑' n, ‖g n ω - u ω‖) μ :=
    aestronglyMeasurable_of_tendsto_ae _ sum_meas
      (summable.mono fun _ h => h.hasSum.tendsto_sum_nat)
  have eLpNorm_sum : eLpNorm (fun ω : Ω => ∑' n : ℕ, ‖g n ω - u ω‖) p μ ≤ ∑' n : ℕ, eLpNorm (fun ω
    : Ω => ‖g n ω - u ω‖) p μ := by
    have eLpNorm_summ :
      ∀ N : ℕ,
        eLpNorm (fun ω : Ω => ∑ n ∈ Finset.range N, ‖g n ω - u ω‖) p μ ≤
        ∑ n ∈ Finset.range N, eLpNorm (fun ω : Ω => ‖g n ω - u ω‖) p μ := by
      intro N
      have eLpNorm_summm :
        ∀ f : ℕ → Ω → ℝ, (∀ n : ℕ, AEStronglyMeasurable (f n) μ) →
          eLpNorm (fun ω : Ω => ∑ n ∈ Finset.range N, f n ω) p μ ≤
          ∑ n ∈ Finset.range N, eLpNorm (f n) p μ := by
        intro f hf
        simpa only [Finset.sum_apply, Finset.sum_fn] using
          (eLpNorm_sum_le (f := f) (μ := μ) (s := Finset.range N) h1p)
      exact eLpNorm_summm _ (hg · |>.sub hup.aestronglyMeasurable |>.norm)
    have eLpNorm_suum : Tendsto (fun N : ℕ => eLpNorm (fun ω : Ω => ∑ n ∈ Finset.range N, ‖g n ω -
      u ω‖) p μ) atTop (𝓝 (eLpNorm (fun ω : Ω => ∑' n : ℕ, ‖g n ω - u ω‖) p μ)) := by
      have eLpNorm_suumm : ∀ᵐ ω : Ω ∂μ, Summable (‖g · ω - u ω‖) := by
        exact summable
      have eLpNorm_suummm : Tendsto (fun N : ℕ => ∫⁻ ω : Ω, ↱(‖∑ n ∈ Finset.range N, ‖g n ω - u ω‖‖
        ^ p.toReal) ∂μ) atTop (𝓝 (∫⁻ ω : Ω, ↱(‖∑' n : ℕ, ‖g n ω - u ω‖‖ ^ p.toReal) ∂μ)) := by
        refine lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
        · intro n
          have eLpNorm_sum : ∀ n : ℕ, AEMeasurable (fun ω : Ω => ‖g n ω - u ω‖) μ :=
            (hg · |>.sub hup.aestronglyMeasurable |>.norm.aemeasurable)
          apply ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          measurability
        · filter_upwards [eLpNorm_suumm] with ω hω
          refine fun n : ℕ => fun m : ℕ => fun hnm : n ≤ m => ENNReal.ofReal_le_ofReal ?_;
          exact Real.rpow_le_rpow (norm_nonneg _) (by
              rw [Real.norm_of_nonneg (Finset.sum_nonneg ↓↓(norm_nonneg _)),
                  Real.norm_of_nonneg (Finset.sum_nonneg ↓↓(norm_nonneg _))]
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm) ↓↓↓(norm_nonneg
                _))
            ENNReal.toReal_nonneg
        · filter_upwards [eLpNorm_suumm] with ω hω
          refine ENNReal.tendsto_ofReal (hω.hasSum.tendsto_sum_nat.norm.rpow tendsto_const_nhds ?_)
          right
          exact (ENNReal.toReal_pos (ne_zero_of_ge_one h1p) hp)
      convert ENNReal.continuous_rpow_const.continuousAt.tendsto.comp eLpNorm_suummm using 2
      any_goals exact p.toReal⁻¹
      · norm_num [eLpNorm, sum_meas]
        split_ifs <;> simp_all [eLpNorm']
        simp [←ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) ENNReal.toReal_nonneg,
          Real.enorm_eq_ofReal_abs]
      · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
        · simp only [one_div, Real.norm_eq_abs, Real.enorm_eq_ofReal_abs,
            abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
          congr! 2
          ext ω
          rw [ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg ↓(norm_nonneg _)) ENNReal.toReal_nonneg]
        · exact ne_of_gt (lt_of_lt_of_le zero_lt_one h1p)
        · exact hp
        · exact tsum_meas
    exact
      le_of_tendsto
        eLpNorm_suum
        (eventually_atTop.← ⟨0, ↓↓(le_trans (by solve_by_elim) (Summable.sum_le_tsum _ ↓↓(by
          positivity) ENNReal.summable))⟩)
  apply hup.norm.add
  apply eLpNorm_sum.trans_lt
  have hnorm (n : ℕ) :
      eLpNorm (fun ω => ‖g n ω - u ω‖) p μ = eLpNorm (g n - u) p μ :=
    eLpNorm_norm (g n - u) ((hg n).sub hup.aestronglyMeasurable)
  simp_rw [hnorm]
  exact lt_top_iff_ne_top.mpr hgp

theorem IsCaratheodory.nemytskii_seqContinuous_of_aestronglyMeas_of_growth
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q ≠ ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {uₙ : ℕ → Ω → D} (huₙ : ∀ n : ℕ, AEStronglyMeasurable (uₙ n) μ)
    {u : Ω → D} (hup : MemLp u p μ)
    (huuₙ : uₙ.NemytskiiConvergesTo u p μ) :
    (fun n : ℕ => fun ω : Ω => f ω (uₙ n ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (u ω)) q μ := by
  apply tendsto_of_subseq_tendsto
  intro s hs
  obtain ⟨s', _, hs'⟩ := Filter.Tendsto.exists_fast_subseq (huuₙ.comp hs)
  have tsum_ne_top : ∑' n : ℕ, eLpNorm (uₙ (s (s' n)) - u) p μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hs')
    rw [ENNReal.tsum_geometric]
    simp
  have ae_summable : ∀ᵐ ω : Ω ∂μ, Summable (fun n : ℕ => ‖uₙ (s (s' n)) ω - u ω‖) :=
    ae_summable_norm_of_tsum_eLpNorm_ne_top_of_aestronglyMeas h1p hp
      (fun n : ℕ => (huₙ (s (s' n))).sub hup.aestronglyMeasurable) tsum_ne_top
  have ae_conv_u : ∀ᵐ ω : Ω ∂μ, Tendsto (fun k : ℕ => uₙ (s (s' k)) ω) atTop (𝓝 (u ω)) := by
    filter_upwards [ae_summable] with ω hω using tendsto_iff_norm_sub_tendsto_zero.←
      hω.tendsto_atTop_zero
  have ae_conv_comp : ∀ᵐ ω : Ω ∂μ,
      Tendsto (fun k : ℕ => f ω ((uₙ (s (s' k))) ω)) atTop (𝓝 (f ω (u ω))) := by
    filter_upwards [hf.ae_continuous, ae_conv_u] with ω ω_cont ω_conv
    exact ω_cont.continuousAt.tendsto.comp ω_conv
  have huss' : MemLp (fun ω : Ω => ‖u ω‖ + ∑' n : ℕ, ‖uₙ (s (s' n)) ω - u ω‖) p μ :=
    memLp_norm_add_tsum_dist_of_eastronglyMeas_of_memLp h1p hp (fun n : ℕ => huₙ (s (s' n))) hup
      tsum_ne_top
  have ae_bound_u : ∀ k : ℕ, ∀ᵐ ω : Ω ∂μ,
      ‖uₙ (s (s' k)) ω‖ ≤ ‖u ω‖ + ∑' n : ℕ, ‖uₙ (s (s' n)) ω - u ω‖ :=
    ae_norm_le_add_tsum_dist_of_ae_summable ae_summable
  have ae_bound_comp : ∀ k : ℕ, ∀ᵐ ω : Ω ∂μ,
      ‖f ω (uₙ (s (s' k)) ω)‖ ≤ |a ω| + C * (‖u ω‖ + ∑' n : ℕ, ‖uₙ (s (s' n)) ω - u ω‖) ^ (p /
        q).toReal := by
    intro k
    filter_upwards [hfaCpq, ae_bound_u k] with ω ω_bound _
    calc ‖f ω ((uₙ (s (s' k))) ω)‖ = ‖f ω (uₙ (s (s' k)) ω)‖ := rfl
      _ ≤ |a ω| + C * ‖uₙ (s (s' k)) ω‖ ^ (p / q).toReal := ω_bound _
      _ ≤ |a ω| + C * (‖u ω‖ + ∑' n : ℕ, ‖uₙ (s (s' n)) ω - u ω‖) ^ (p / q).toReal := by gcongr
  have dom_memLp : MemLp (fun ω : Ω => |a ω| + C * (‖u ω‖ + ∑' n : ℕ, ‖uₙ (s (s' n)) ω - u ω‖) ^ (p
    / q).toReal) q μ :=
    have ae_memLp_comp : MemLp (fun ω : Ω => (‖u ω‖ + ∑' n : ℕ, ‖uₙ (s (s' n)) ω - u ω‖) ^ (p /
      q).toReal) q μ := by
      convert huss'.norm_rpow_div (p / q) using 1
      · ext x
        rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (tsum_nonneg ↓(norm_nonneg _)))]
      · rw [ENNReal.div_div_cancel] <;> aesop
    MemLp.add haq.abs (ae_memLp_comp.const_mul C)
  have hfuq : MemLp (fun ω : Ω => f ω (u ω)) q μ :=
    memLp_nemytskii_of_growth_of_aestronglyMeasurable (zero_lt_one.trans_le h1p) hp h1q hq haq hC
      hfaCpq hup
      (hf.aestronglyMeas_nemytskii_of_aestronglyMeas hup.aestronglyMeasurable)
  have comp_meas : ∀ k : ℕ, AEStronglyMeasurable (fun ω => f ω (uₙ (s (s' k)) ω)) μ :=
    fun k => hf.aestronglyMeas_nemytskii_of_aestronglyMeas (huₙ (s (s' k)))
  exact ⟨s', convergesTo_of_tendsTo_of_growth_of_aestronglyMeas h1q hq comp_meas hfuq dom_memLp
    ae_bound_comp ae_conv_comp⟩

theorem IsCaratheodory.nemytskii_seqContinuous_of_memLp_of_growth_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {uₙ : ℕ → Ω → ℝ^m} (huₙ : ∀ n : ℕ, MemLp (uₙ n) p μ)
    {u : Ω → ℝ^m} (hup : MemLp u p μ)
    (huuₙ : uₙ.NemytskiiConvergesTo u p μ) :
    (fun n : ℕ => fun ω : Ω => f ω (uₙ n ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (u ω)) q μ :=
  hf.nemytskii_seqContinuous_of_aestronglyMeas_of_growth h1p hp.ne_top h1q hq.ne_top haq hC hfaCpq
    (huₙ ·|>.aestronglyMeasurable) hup huuₙ

end NemytskiiLebesgue
