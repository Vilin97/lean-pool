/-
Copyright (c) 2026 Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import LeanPool.NemytskiiLebesgue.Continuity

/-!
# Nemytskii operators: ConverseImplication

Adapted from `madvorak/nemytskii-lebesgue` (Apache-2.0).
-/

public section

namespace NemytskiiLebesgue

open scoped NemytskiiLebesgue

open MeasureTheory _root_.Filter TopologicalSpace
open scoped NNReal ENNReal Topology

private noncomputable def denseSeqEucl (m : ℕ) : ℕ → ℝ^m :=
  fun n : ℕ => if n = 0 then 0 else denseSeq ℝ^m (n - 1)

private lemma denseRange_denseSeqEucl (m : ℕ) : DenseRange (denseSeqEucl m) := by
  rw [Metric.denseRange_iff]
  intro x r hr
  obtain ⟨y, hy⟩ := Metric.mem_closure_iff.→ (denseRange_denseSeq ℝ^m x) r hr
  rcases hy.left with ⟨n, rfl⟩
  exact ⟨n + 1, by simpa [denseSeqEucl] using hy.right⟩

private noncomputable def growthSup {m k : ℕ} (f : ℝ → ℝ^m → ℝ^k) (r C : ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ↱(‖f x (denseSeqEucl m n)‖ - C * ‖denseSeqEucl m n‖ ^ r)

private lemma IsCaratheodory.measurable_growthSup
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    (r C : ℝ) :
    Measurable (growthSup f r C) := by
  apply_rules [Measurable.iSup]
  have strongly_measurable : ∀ n : ℕ, StronglyMeasurable (f · (denseSeqEucl m n)) :=
    ↓(hf.isStronglyMeasurable _)
  intro n
  exact (Measurable.sub ((strongly_measurable n).measurable).norm measurable_const).ennreal_ofReal

private lemma IsCaratheodory.growth_of_lintegral_growthSup_rpow_toReal_ne_top
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    {p q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {C : ℝ} (hfpqC : ∫⁻ x : ℝ, (growthSup f (p / q).toReal C x) ^ q.toReal ∂volume ≠ ⊤) :
    ∃ a : ℝ → ℝ, MemLp a q volume ∧
      ∀ᵐ x : ℝ ∂volume, ∀ ξ : ℝ^m,
        ‖f x ξ‖ ≤ |a x| + C * ‖ξ‖ ^ (p / q).toReal := by
  refine ⟨(growthSup f (p / q).toReal C · |>.toReal), memLp_iff_measurable_and_finite.mpr
    ⟨(hf.measurable_growthSup (p / q).toReal C).ennreal_toReal.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_zero_of_ge_one h1q) hq.ne
      (hf.measurable_growthSup _ _).ennreal_toReal.aestronglyMeasurable]
    refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt ?_)
    refine lt_of_le_of_lt (lintegral_mono fun x : ℝ => ?_) (lt_top_iff_ne_top.← hfpqC)
    apply ENNReal.rpow_le_rpow _ ENNReal.toReal_nonneg
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  · have ae_finite : ∀ᵐ x ∂volume, growthSup f (p / q).toReal C x < ⊤ := by
      have ae_finite : ∀ᵐ x ∂volume, growthSup f (p / q).toReal C x ^ q.toReal < ⊤ := by
        apply_rules [ae_lt_top]
        apply Measurable.pow_const (hf.measurable_growthSup ..)
      filter_upwards [ae_finite] with x hx
      rw [lt_top_iff_ne_top]
      exact (hx.ne <| by
        rw [·]
        apply ENNReal.top_rpow_of_pos
        apply ENNReal.toReal_pos
        · positivity
        · aesop)
    have ae_continuous : ∀ᵐ x ∂volume, Continuous (f x) :=
      hf.ae_continuous
    filter_upwards [ae_finite, ae_continuous] with x hx₁ hx₂
    have bound_denseSeqEucl : ∀ n : ℕ, ‖f x (denseSeqEucl m n)‖ ≤ |(growthSup f (p / q).toReal C
      x).toReal| + C * ‖denseSeqEucl m n‖ ^ (p / q).toReal := by
      intro n
      have bound_denseSeqEucl_step : ↱(‖f x (denseSeqEucl m n)‖ - C * ‖denseSeqEucl m n‖ ^ (p /
        q).toReal) ≤ growthSup f (p / q).toReal C x :=
        le_iSup (fun n : ℕ => ↱(‖f x (denseSeqEucl m n)‖ - C * ‖denseSeqEucl m n‖ ^ (p /
          q).toReal)) n
      have bound := (ENNReal.ofReal_le_iff_le_toReal hx₁.ne).mp bound_denseSeqEucl_step
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      linarith
    have S_closed : IsClosed { ξ : ℝ^m | ‖f x ξ‖ ≤ |(growthSup f (p / q).toReal C x).toReal| + C *
      ‖ξ‖ ^ (p / q).toReal } :=
      isClosed_le hx₂.norm (continuous_const.add (continuous_const.mul (continuous_norm.rpow_const
        (by
        intro
        right
        positivity
      ))))
    have S_dense : Dense (Set.range (denseSeqEucl m)) :=
      denseRange_denseSeqEucl m
    exact fun ξ : ℝ^m => S_closed.closure_subset_iff.← (Set.range_subset_iff.← bound_denseSeqEucl)
      (S_dense.closure_eq ▸ Set.mem_univ ξ)

private lemma exists_measurable_subset_lintegral_eq_lt_lintegral
    {l : ℝ → ℝ≥0∞} (hl : Measurable l)
    {B : Set ℝ} (hB : MeasurableSet B)
    {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hlK : ∀ x ∈ B, l x ≤ K)
    {t : ℝ≥0∞} (htl : t < ∫⁻ x in B, l x ∂volume) :
    ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ B ∧ volume A < ⊤ ∧ ∫⁻ x in A, l x ∂volume = t := by
  obtain ⟨S, hS⟩ : ∃ S : ℕ, t < ∫⁻ x in B ∩ Set.Icc (-S : ℝ) S, l x :=
    have hBlx : Tendsto (fun S : ℕ => ∫⁻ x in B ∩ Set.Icc (-S : ℝ) S, l x) atTop (𝓝 (∫⁻ x in B, l
      x)) := by
      convert lintegral_tendsto_of_tendsto_of_monotone
        (f := fun n : ℕ => fun x : ℝ => l x * (if x ∈ Set.Icc (-n : ℝ) n then 1 else 0))
        _ _ _ using 1
      rotate_left
      · exact ↓(Measurable.aemeasurable (Measurable.mul hl (Measurable.ite measurableSet_Icc
        measurable_const measurable_const)))
      · filter_upwards [ae_restrict_mem hB] with x hx
        intro n m hnm
        simp only [Set.mem_Icc, mul_ite, mul_one, mul_zero]
        split_ifs with _ hmxm <;> norm_num
        exfalso
        apply hmxm
        constructor <;> linarith [show (n : ℝ) ≤ m by norm_cast]
      · filter_upwards [ae_restrict_mem hB] with x hx
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_gt_atTop ⌈|x|⌉₊] with n hn
        rw [ite_eq_left]
        · ring
        · constructor <;> linarith [Nat.le_ceil |x|, abs_le.→ (Nat.le_of_ceil_le hn.le)]
      · ext
        rw [←lintegral_indicator] <;> norm_num [Set.indicator, hB]
        rw [←lintegral_indicator] <;> norm_num [Set.indicator, hB]
        grind
    (hBlx.eventually (lt_mem_nhds htl)).exists
  set G : ℝ → ℝ≥0∞ := fun s => ∫⁻ x in B ∩ Set.Icc (-s : ℝ) s, l x
  obtain ⟨s, hs⟩ : ∃ s ∈ Set.Icc (0 : ℝ) S, G s = t := by
    have : ContinuousOn G (Set.Icc (0 : ℝ) S) := by
      have G_cont : ContinuousOn (fun s : ℝ => ∫⁻ x in B ∩ Set.Icc (-s : ℝ) s, l x) (Set.Icc 0 (S :
        ℝ)) := by
        have G_cont_aux : ∀ s ∈ Set.Icc 0 (S : ℝ),
            ∫⁻ x in B ∩ Set.Icc (-s : ℝ) s, l x =
            ∫⁻ x in B ∩ Set.Icc (-S : ℝ) S, l x * (if -s ≤ x ∧ x ≤ s then 1 else 0) := by
          intro s hs
          rw [←lintegral_indicator, ←lintegral_indicator] <;> norm_num [Set.indicator]
          · grind
          · exact hB.inter measurableSet_Icc
          · exact hB.inter measurableSet_Icc
        rw [continuousOn_congr G_cont_aux]
        apply continuousOn_of_forall_continuousAt
        intro s hs
        apply tendsto_lintegral_filter_of_dominated_convergence ↓K
        · exact Eventually.of_forall ↓(Measurable.mul hl (Measurable.ite measurableSet_Icc
          measurable_const measurable_const))
        · filter_upwards with
          exact eventually_of_mem (ae_restrict_mem (hB.inter measurableSet_Icc))
            (fun x hx => (mul_le_of_le_one_right zero_le (by aesop)).trans (hlK x hx.left))
        · simpa using ENNReal.mul_ne_top hK (ne_of_lt (lt_of_le_of_lt (measure_mono
          (Set.inter_subset_right)) (by simp [Real.volume_Icc])))
        · refine measure_mono_null (t := { -s, s }) ?_ ?_
          · intro x hx
            contrapose! hx
            by_cases hsx : -s ≤ x <;> by_cases hxs : x ≤ s <;> simp_all only [ne_eq,
                Set.mem_Icc,
                Nat.cast_nonneg,
                Std.le_refl,
                and_self,
                mul_ite,
                mul_one,
                mul_zero,
                and_imp,
                Set.mem_insert_iff,
                Set.mem_singleton_iff,
                not_or,
                Set.mem_compl_iff,
                Set.mem_ofPred_eq,
                ↓reduceIte,
                not_not,
                not_le,
                true_and,
                and_true] <;> apply
              tendsto_const_nhds.congr'
            · filter_upwards [
                  Ioi_mem_nhds (show s > x from lt_of_le_of_ne hxs hx.right),
                  Ioi_mem_nhds (show s > -x from lt_of_le_of_ne (neg_le.→ hsx) (by
                    cases lt_or_gt_of_ne hx.left <;> linarith)
                )] with n hn hn'
              rw [ite_eq_left]
              exact ⟨(neg_lt_of_neg_lt hn').le, hn.out.le⟩
            · filter_upwards [Iio_mem_nhds hxs] with n hn
              split_ifs <;> norm_num <;> linarith [hn.out]
            · filter_upwards [Iio_mem_nhds (lt_neg_of_lt_neg hsx)] with n hn
              split_ifs <;> norm_num <;> linarith [hn.out]
            · linarith
          · rw [Set.insert_eq, measure_union_null] <;> norm_num
      exact G_cont
    apply_rules [intermediate_value_Icc] <;> norm_num
    simp +zetaDelta only [ne_eq,
        neg_zero,
        Set.Icc_self] at *
    rw [Measure.restrict_eq_zero.← (measure_mono_null Set.inter_subset_right (measure_singleton 0))]
    constructor
    · norm_num
    · exact hS.le
  refine ⟨B ∩ Set.Icc (-s) s, ?_, ?_, ?_, hs.right⟩ <;> norm_num [hB]
  apply lt_of_le_of_lt (measure_mono Set.inter_subset_right)
  simp

private lemma exists_measurable_all_half_argmax_of_all_measurable
    {φ : ℕ → ℝ → ℝ≥0∞} (hφ : ∀ n : ℕ, Measurable (φ n)) :
    ∃ s : ℝ → ℕ, Measurable s ∧
      ∀ x : ℝ, (∃ n : ℕ, (⨆ k : ℕ, φ k x) / 2 < φ n x) → (⨆ k : ℕ, φ k x) / 2 < φ (s x) x := by
  classical
  set S : ℝ → ℝ≥0∞ := fun x : ℝ => ⨆ k : ℕ, φ k x with hS
  set p : ℝ → ℕ → Prop := fun x : ℝ => fun n : ℕ => S x / 2 < φ n x ∨ (∀ m : ℕ, ¬ S x / 2 < φ m x)
    with hp
  have hp : ∀ x : ℝ, ∃ N : ℕ, p x N := by
    intro x
    by_cases hx : ∃ n : ℕ, S x / 2 < φ n x
    · obtain ⟨n, hn⟩ := hx
      use n
      left
      exact hn
    · push Not at hx
      use 0
      right
      intro m
      rw [not_lt]
      exact hx m
  refine ⟨fun x : ℝ => Nat.find (hp x), ?_, ?_⟩
  · have hS : Measurable S := Measurable.iSup hφ
    refine measurable_find hp (fun k : ℕ => ?_)
    have hSk : MeasurableSet { x : ℝ | S x / 2 < φ k x } :=
      measurableSet_lt (hS.div_const 2) (hφ k)
    have hSm : MeasurableSet { x : ℝ | ∀ m : ℕ, ¬ S x / 2 < φ m x } := by
      have hSφ : { x : ℝ | ∀ m : ℕ, ¬ S x / 2 < φ m x } = ⋂ m, { x : ℝ | ¬ S x / 2 < φ m x } := by
        ext
        simp
      rw [hSφ]
      exact MeasurableSet.iInter (fun m : ℕ => (measurableSet_lt (hS.div_const 2) (hφ m)).compl)
    exact hSk.union hSm
  · intro x hx
    rcases Nat.find_spec (hp x) with h | h
    · exact h
    · obtain ⟨n, hn⟩ := hx
      exact absurd hn (h n)

private noncomputable def growthWindowTerm
    {m k : ℕ} (f : ℝ → ℝ^m → ℝ^k)
    (C r : ℝ) (N n : ℕ) (x : ℝ) :
    ℝ≥0∞ :=
  ↱(‖f x (denseSeqEucl m n)‖ - C * ‖denseSeqEucl m n‖ ^ r) * (if ‖f x (denseSeqEucl m n)‖ ≤ (N : ℝ)
    then 1 else 0)

private noncomputable def growthWindowSupr
    {m k : ℕ} (f : ℝ → ℝ^m → ℝ^k)
    (C r : ℝ) (N : ℕ) (x : ℝ) :
    ℝ≥0∞ :=
  ⨆ n : ℕ, growthWindowTerm f C r N n x

private lemma growthWindowTerm_measurable
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    (C r : ℝ) (N n : ℕ) :
    Measurable (growthWindowTerm f C r N n) :=
  have norm_measurable : Measurable (‖f · (denseSeqEucl m n)‖) :=
    have strongly_measurable : StronglyMeasurable (f · (denseSeqEucl m n)) :=
      hf.isStronglyMeasurable _
    strongly_measurable.measurable.norm
  Measurable.mul
    (Measurable.ennreal_ofReal (norm_measurable.sub (measurable_const.mul
      (measurable_const.pow_const _))))
    (Measurable.ite (norm_measurable measurableSet_Iic) measurable_const measurable_const)

private lemma measurable_growthWindowSupr
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    (C r : ℝ) (N : ℕ) :
    Measurable (growthWindowSupr f C r N) :=
  Measurable.iSup (growthWindowTerm_measurable hf C r N)

private lemma growthWindowTerm_le_growthSup
    {m k : ℕ} (f : ℝ → ℝ^m → ℝ^k)
    (C r : ℝ) (N n : ℕ) (x : ℝ) :
    growthWindowTerm f C r N n x ≤ growthSup f r C x :=
  le_trans
    (mul_le_of_le_one_right (by positivity) (by aesop))
    (le_iSup (fun z : ℕ => ↱(‖f x (denseSeqEucl m z)‖ - C * ‖denseSeqEucl m z‖ ^ r)) n)

private lemma growthWindowSupr_le_ofReal
    {m k : ℕ} (f : ℝ → ℝ^m → ℝ^k)
    {C r : ℝ} (hC : 0 ≤ C)
    (N : ℕ) (x : ℝ) :
    growthWindowSupr f C r N x ≤ ↱(N : ℝ) := by
  apply iSup_le
  intro n
  unfold growthWindowTerm
  split_ifs with h
  · rw [mul_one]
    exact ENNReal.ofReal_le_ofReal
      ((sub_le_self _ (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _))).trans h)
  · simp

private lemma iSup_growthWindowSupr
    {m k : ℕ} (f : ℝ → ℝ^m → ℝ^k)
    (C r : ℝ) (x : ℝ) :
    ⨆ N : ℕ, growthWindowSupr f C r N x = growthSup f r C x := by
  unfold growthWindowSupr growthSup
  rw [iSup_comm]
  refine iSup_congr fun n : ℕ => ?_
  apply le_antisymm
  · refine iSup_le fun N : ℕ => ?_
    exact mul_le_of_le_one_right (by positivity) (by aesop)
  · refine le_trans ?_ (le_iSup _ ⌈‖f x (denseSeqEucl m n)‖⌉₊)
    unfold growthWindowTerm
    rw [ite_eq_left (Nat.le_ceil _)]
    norm_num

private lemma exists_growthWindowSupr_lintegral_gt
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    {e : ℝ} (he : 0 ≤ e)
    {C r : ℝ} {c : ℝ≥0∞} {E : Set ℝ} (hcE : c < ∫⁻ x in E, (growthSup f r C x) ^ e ∂volume) :
    ∃ N : ℕ, c < ∫⁻ x in E, (growthWindowSupr f C r N x) ^ e ∂volume := by
  by_contra! contra
  have monoton : Monotone (fun N : ℕ => fun x : ℝ => (growthWindowSupr f C r N x) ^ e) := by
    refine fun N M hNM x => ENNReal.rpow_le_rpow ?_ he
    refine iSup_mono fun n : ℕ => mul_le_mul_right ?_ _
    split_ifs <;> norm_num
    linarith [show (N : ℝ) ≤ M by norm_cast]
  have hfCrNxe : Tendsto (fun N : ℕ => ∫⁻ x in E, (growthWindowSupr f C r N x) ^ e) atTop (𝓝 (∫⁻ x
    in E, (⨆ N : ℕ, (growthWindowSupr f C r N x)) ^ e)) := by
    convert lintegral_tendsto_of_tendsto_of_monotone _ _ _
    · exact fun N : ℕ => ((measurable_growthWindowSupr hf C r N).pow_const e).aemeasurable
    · exact Eventually.of_forall fun x : ℝ => ↓↓(monoton · x)
    · refine Eventually.of_forall fun x : ℝ => ?_
      refine
        (ENNReal.continuous_rpow_const.tendsto _).comp
          (tendsto_atTop_iSup
            (show Monotone fun N : ℕ => growthWindowSupr f C r N x from fun N M hNM => ?_))
      refine iSup_mono fun n : ℕ => ?_
      apply mul_le_mul_right
      split_ifs <;> norm_num
      linarith [show (N : ℝ) ≤ M by norm_cast]
  exact hcE.not_ge <| by
    simpa only [iSup_growthWindowSupr] using
      le_of_tendsto_of_tendsto' hfCrNxe tendsto_const_nhds contra

private lemma IsCaratheodory.measurable_comp_denseSeqEucl_measurable
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    {s : ℝ → ℕ} (hs : Measurable s) :
    Measurable (fun x : ℝ => f x (denseSeqEucl m (s x))) := by
  have hpair : Measurable (fun p : ℝ × ℕ => f p.fst (denseSeqEucl m p.snd)) :=
    measurable_from_prod_countable_left (fun n : ℕ => (hf.isStronglyMeasurable (denseSeqEucl m
      n)).measurable)
  exact hpair.comp (measurable_id.prodMk hs)

private lemma norm_nemytskii_denseSeqEucl_le_of_growthWindowTerm_pos
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k}
    {C r x : ℝ} {N n : ℕ} (hf0 : 0 < growthWindowTerm f C r N n x) :
    ‖f x (denseSeqEucl m n)‖ ≤ (N : ℝ) := by
  unfold growthWindowTerm at *
  aesop

private lemma growthWindowTerm_pos_input_bound
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k}
    {C r x : ℝ} {N n : ℕ} (hf0 : 0 < growthWindowTerm f C r N n x) :
    C * ‖denseSeqEucl m n‖ ^ r < ‖f x (denseSeqEucl m n)‖ := by
  unfold growthWindowTerm at hf0
  split_ifs at hf0 <;> simp_all [ENNReal.ofReal_pos]

private lemma growthWindowTerm_le_enorm
    {m k : ℕ} (f : ℝ → ℝ^m → ℝ^k)
    {C : ℝ} (hC : 0 ≤ C)
    (r : ℝ) (N n : ℕ) (x : ℝ) :
    growthWindowTerm f C r N n x ≤ ‖f x (denseSeqEucl m n)‖ₑ := by
  unfold growthWindowTerm
  split_ifs
  · rw [mul_one, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      (sub_le_self _ (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _)))
  · simp

private lemma pow_transfer_enorm_norm
    {d : ℕ} {ξ : ℝ^d}
    {e : ℕ} {y : ℝ^e}
    {C : ℝ} (hC : 0 < C)
    {P Q r : ℝ} (hQ : 0 < Q) (hr : 0 ≤ r) (hPQr : P = Q * r)
    (hCy : C * ‖ξ‖ ^ r < ‖y‖) :
    ‖ξ‖ₑ ^ P ≤ ↱(C ^ (-Q)) * ‖y‖ₑ ^ Q := by
  simpa only [←ofReal_norm] using
    hPQr ▸ pow_transfer_ennreal_ofReal (norm_nonneg ξ) (norm_nonneg y) hC hQ hr hCy

private lemma IsCaratheodory.exists_bad_subset_measurableSet
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    {p q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {C : ℝ} (h1C : 1 ≤ C)
    {E : Set ℝ} (hE : MeasurableSet E)
    (h2q : (2 : ℝ≥0∞) ^ q.toReal < ∫⁻ x in E, (growthSup f (p / q).toReal C x) ^ q.toReal ∂volume) :
    ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ E ∧ volume A < ⊤ ∧
      ∃ u : ℝ → ℝ^m,
        Measurable u ∧
        (∀ x : ℝ, x ∉ A → u x = 0) ∧
        1 ≤ ∫⁻ x in A, ‖f x (u x)‖ₑ ^ q.toReal ∂volume ∧
        ∫⁻ x in A, ‖f x (u x)‖ₑ ^ q.toReal ∂volume ≤ 2 ∧
        ∫⁻ x in A, ‖u x‖ₑ ^ p.toReal ∂volume ≤ 2 * ↱(C ^ (-q.toReal)) := by
  set r := (p / q).toReal
  set Q := q.toReal
  set P := p.toReal
  have h0Q : 0 ≤ Q := by positivity
  have h0C : 0 ≤ C := by positivity
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 ^ Q < ∫⁻ x in E, (growthWindowSupr f C r N x) ^ Q ∂volume :=
    exists_growthWindowSupr_lintegral_gt hf h0Q h2q
  obtain ⟨s, s_meas, hs⟩ : ∃ s : ℝ → ℕ, Measurable s ∧
      (∀ x : ℝ, 0 < growthWindowSupr f C r N x → growthWindowSupr f C r N x / 2 < growthWindowTerm
        f C r N (s x) x) := by
    obtain ⟨s, s_meas, hs⟩ : ∃ s : ℝ → ℕ, Measurable s ∧
        (∀ x : ℝ, (∃ n : ℕ, growthWindowSupr f C r N x / 2 < growthWindowTerm f C r N n x) →
          growthWindowSupr f C r N x / 2 < growthWindowTerm f C r N (s x) x) :=
      exists_measurable_all_half_argmax_of_all_measurable (growthWindowTerm_measurable hf C r N)
    refine ⟨s, s_meas, fun x hx => hs x ?_⟩
    have := ENNReal.half_lt_self hx.ne' (show growthWindowSupr f C r N x ≠ ⊤ from ?_)
    · rwa [←lt_iSup_iff]
    · exact ne_of_lt (lt_of_le_of_lt (growthWindowSupr_le_ofReal f h0C N x) ENNReal.ofReal_lt_top)
  set E' := E ∩ { x : ℝ | 0 < growthWindowSupr f C r N x } with E'_def
  have hE'_meas : MeasurableSet E' :=
    hE.inter (measurableSet_lt measurable_const (measurable_growthWindowSupr hf C r N))
  set u₀ : ℝ → ℝ^m := fun x : ℝ => denseSeqEucl m (s x) with u₀_def
  have hu₀_meas : Measurable u₀ :=
    Measurable.comp (show Measurable (denseSeqEucl m) from Measurable.of_discrete) s_meas
  have f_u₀_meas : Measurable (fun x : ℝ => f x (u₀ x)) :=
    hf.measurable_comp_denseSeqEucl_measurable s_meas
  have meas_out : Measurable (fun x : ℝ => ‖f x (u₀ x)‖ₑ ^ Q) := f_u₀_meas.enorm.pow_const _
  have hu₀_bound : ∀ x ∈ E', ‖f x (u₀ x)‖ₑ ^ Q ≤ (↱N) ^ Q := by
    intro x hx
    have hfN : ‖f x (u₀ x)‖ ≤ N :=
      norm_nemytskii_denseSeqEucl_le_of_growthWindowTerm_pos (lt_of_le_of_lt (by positivity) (hs x
        hx.right))
    gcongr
    convert hfN using 1
    norm_num [←ENNReal.toReal_le_toReal]
  have hu₀_input_bound : ∀ x ∈ E',
      ‖u₀ x‖ₑ ^ P ≤ ↱(C ^ (-Q)) * ‖f x (u₀ x)‖ₑ ^ Q := by
    intro x hx
    have h0 : 0 < growthWindowTerm f C r N (s x) x :=
      lt_of_le_of_lt (ENNReal.half_pos (ne_of_gt hx.right)).le (hs x hx.right)
    have hCu₀ : C * ‖u₀ x‖ ^ r < ‖f x (u₀ x)‖ := growthWindowTerm_pos_input_bound h0
    refine le_of_eq_of_le rfl (pow_transfer_enorm_norm (lt_of_le_of_ne h0C (ne_zero_of_ge_one
      h1C).symm)
      (show 0 < Q from ENNReal.toReal_pos (ne_zero_of_ge_one h1q) hq.ne_top)
      (show 0 ≤ r from ENNReal.toReal_nonneg) (show P = Q * r from ?_) hCu₀)
    rw [←ENNReal.toReal_mul, mul_comm, ENNReal.div_mul_cancel (ne_zero_of_ge_one h1q) hq.ne_top]
  have lower_bound : 1 < ∫⁻ x in E', ‖f x (u₀ x)‖ₑ ^ Q ∂volume := by
    have h1 : ∫⁻ x in E', (growthWindowSupr f C r N x / 2) ^ Q ∂volume > 1 := by
      have h2 :
          ∫⁻ x in E', (growthWindowSupr f C r N x / 2) ^ Q ∂volume =
          (∫⁻ x in E, (growthWindowSupr f C r N x) ^ Q ∂volume) / 2 ^ Q := by
        have hEE' :
            ∫⁻ x in E', (growthWindowSupr f C r N x / 2) ^ Q ∂volume =
            ∫⁻ x in E,  (growthWindowSupr f C r N x / 2) ^ Q ∂volume := by
          rw [←lintegral_indicator, ←lintegral_indicator] <;>
            norm_num [Set.indicator, hE, hE'_meas]
          congr with x
          by_cases hx : x ∈ E <;> by_cases hx' : 0 < growthWindowSupr f C r N x <;> simp only [hx,
              ↓reduceIte,
              ite_eq_left_iff,
              ite_eq_right_iff,
              ENNReal.rpow_eq_zero_iff,
              ENNReal.div_eq_zero_iff,
              ENNReal.ofNat_ne_top,
              or_false]
          · exact (False.elim <| · ⟨hx, hx'⟩)
          · simp_all only [ENNReal.div_eq_inv_mul, Set.mem_inter_iff, Set.mem_ofPred_eq,
              ENNReal.ofReal_natCast, and_imp, not_lt, nonpos_iff_eq_zero, lt_self_iff_false,
              and_false, not_false_eq_true, mul_zero, forall_const]
            rw [ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos (ne_zero_of_ge_one h1q) hq.ne_top)]
          · exact (False.elim <| hx ·.left)
          · aesop
        rw [hEE', ENNReal.div_eq_inv_mul, ←lintegral_const_mul]
        · congr
          ext
          rw [ENNReal.div_eq_inv_mul, ENNReal.mul_rpow_of_nonneg _ _ h0Q]
          rw [ENNReal.inv_rpow]
        · exact Measurable.pow_const (measurable_growthWindowSupr hf C r N) _
      rw [h2, gt_iff_lt, ENNReal.lt_div_iff_mul_lt] <;> norm_num [hN]
    refine h1.trans_le (setLIntegral_mono' hE'_meas ?_)
    intro x hx
    have hsx := hs x hx.right
    exact (ENNReal.rpow_le_rpow hsx.le h0Q).trans (ENNReal.rpow_le_rpow (growthWindowTerm_le_enorm
      f h0C r N (s x) x) h0Q)
  obtain ⟨A, A_meas, A_subset, A_vol, A_integr⟩ :
      ∃ A : Set ℝ,
        MeasurableSet A ∧
        A ⊆ E' ∧
        volume A < ⊤ ∧
        ∫⁻ x in A, ‖f x (u₀ x)‖ₑ ^ Q ∂volume = 1 :=
    exists_measurable_subset_lintegral_eq_lt_lintegral
      meas_out
      hE'_meas
      (ENNReal.rpow_ne_top_of_nonneg h0Q ENNReal.ofReal_ne_top)
      hu₀_bound
      lower_bound
  have hAfQ :
      ∫⁻ x in A, ‖f x (Set.indicator A u₀ x)‖ₑ ^ Q ∂volume =
      ∫⁻ x in A, ‖f x (u₀ x)‖ₑ ^ Q ∂volume :=
    setLIntegral_congr_fun A_meas ↓(by rw [Set.indicator_of_mem ·])
  refine ⟨A, A_meas, A_subset.trans Set.inter_subset_left, A_vol,
      Set.indicator A u₀, hu₀_meas.indicator A_meas,
      ↓(Set.indicator_of_notMem · u₀), ?_, ?_, ?_⟩
  · rw [hAfQ, A_integr]
  · rw [hAfQ, A_integr]
    exact one_le_two
  · rw [setLIntegral_congr_fun A_meas ↓(by rw [Set.indicator_of_mem ·])]
    calc ∫⁻ x in A, ‖u₀ x‖ₑ ^ P ∂volume
        ≤ ∫⁻ x in A, ↱(C ^ (-Q)) * ‖f x (u₀ x)‖ₑ ^ Q ∂volume :=
            setLIntegral_mono (meas_out.const_mul _) (hu₀_input_bound · <| A_subset ·)
      _ = ↱(C ^ (-Q)) * ∫⁻ x in A, ‖f x (u₀ x)‖ₑ ^ Q ∂volume :=
            lintegral_const_mul _ meas_out
      _ = ↱(C ^ (-Q)) * 1 := by rw [A_integr]
      _ ≤ 2 * ↱(C ^ (-Q)) := by
            rw [mul_one]
            exact le_mul_of_one_le_left zero_le one_le_two

private lemma exists_memLp_and_not_memLp_nemytskii_of_pairwise_disjoint_measurableSet
    {m k : ℕ}
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {f : ℝ → ℝ^m → ℝ^k}
    {A : ℕ → Set ℝ} (hA : Pairwise (Function.onFun Disjoint A)) (A_meas : ∀ j : ℕ, MeasurableSet (A
      j))
    {u : ℕ → ℝ → ℝ^m} (u_meas : ∀ j : ℕ, Measurable (u j))
    (h1 : ∀ j : ℕ, 1 ≤ ∫⁻ x in A j, ‖f x (u j x)‖ₑ ^ q.toReal ∂volume)
    (h2 : ∀ j : ℕ, ∫⁻ x in A j, ‖u j x‖ₑ ^ p.toReal ∂volume ≤ (2 : ℝ≥0∞)⁻¹ ^ j) :
    ∃ U : ℝ → ℝ^m, MemLp U p volume ∧ ¬ MemLp (fun x : ℝ => f x (U x)) q volume := by
  refine ⟨fun x : ℝ => ∑' j : ℕ, (A j).indicator (u j) x, ?_, ?_⟩
  · have hmeas : AEStronglyMeasurable (fun x => ∑' j, (A j).indicator (u j) x) volume := by
      apply Measurable.aestronglyMeasurable
      refine measurable_of_tendsto_metrizable
        (f := fun n x => ∑ j ∈ Finset.range n, (A j).indicator (u j) x) ?_ ?_
      · exact ↓(Finset.measurable_sum _ fun i : ℕ => ↓(Measurable.indicator (u_meas i) (A_meas i)))
      · rw [tendsto_pi_nhds]
        intro x
        refine (Summable.hasSum ?_).tendsto_sum_nat
        by_cases hx : ∃ j, x ∈ A j
        · obtain ⟨j, hj⟩ := hx
          refine ⟨_, hasSum_single j ?_⟩
          intro k hk
          apply Set.indicator_of_notMem
          intro hk'
          apply hk
          exfalso
          exact (hA hk).le_bot ⟨hk', hj⟩
        · exact ⟨_, hasSum_single 0 (by aesop)⟩
    apply memLp_iff_measurable_and_finite.mpr
    refine ⟨hmeas, ?_⟩
    · have integral :
          ∫⁻ x, ‖∑' j : ℕ, Set.indicator (A j) (u j) x‖ₑ ^ p.toReal ∂volume =
          ∑' j : ℕ, ∫⁻ x in A j, ‖u j x‖ₑ ^ p.toReal ∂volume := by
        have integral :
            ∫⁻ x, ‖∑' j : ℕ, Set.indicator (A j) (u j) x‖ₑ ^ p.toReal ∂volume =
            ∫⁻ x in ⋃ j, A j, ‖∑' j : ℕ, Set.indicator (A j) (u j) x‖ₑ ^ p.toReal ∂volume := by
          rw [lintegral_congr_ae, lintegral_indicator]
          · exact MeasurableSet.iUnion A_meas
          · filter_upwards with x
            by_cases hx : x ∈ ⋃ j, A j <;>
              simp_all only [Set.mem_iUnion, Set.indicator_of_mem, not_exists,
                not_false_eq_true, Set.indicator_of_notMem, tsum_zero, enorm_zero,
                exists_const, ENNReal.rpow_eq_zero_iff, true_and, ENNReal.zero_ne_top,
                false_and, or_false]
            exact ENNReal.toReal_pos (ne_zero_of_ge_one h1p) hp.ne
        rw [integral, lintegral_iUnion]
        · refine tsum_congr fun j : ℕ => setLIntegral_congr_fun (A_meas j) ?_
          intro x hx
          simp only
          rw [tsum_eq_single j]
          · aesop
          · exact fun i hi => Set.indicator_of_notMem (hi <| False.elim <| (hA hi).le_bot ⟨·, hx⟩) _
        · exact A_meas
        · exact hA
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal _ _ hmeas]
      · refine ENNReal.rpow_lt_top_of_nonneg ?_ ?_ <;> norm_num
        exact integral.symm ▸ ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum h2) (by simp
          [ENNReal.tsum_geometric]))
      · exact ne_zero_of_ge_one h1p
      · exact ne_of_lt hp
  · intro hfAq
    have output :
        ∫⁻ x, ‖f x (∑' j : ℕ, (A j).indicator (u j) x)‖ₑ ^ q.toReal ∂volume ≥
        ∑' j : ℕ, ∫⁻ x in A j, ‖f x (u j x)‖ₑ ^ q.toReal ∂volume := by
      have output :
          ∫⁻ x in ⋃ j, A j, ‖f x (∑' j : ℕ, (A j).indicator (u j) x)‖ₑ ^ q.toReal ∂volume ≥
          ∑' j : ℕ, ∫⁻ x in A j, ‖f x (u j x)‖ₑ ^ q.toReal ∂volume := by
        rw [lintegral_iUnion]
        · refine ENNReal.tsum_le_tsum fun j : ℕ => setLIntegral_mono' (A_meas j) ?_
          intro x hx
          rw [tsum_eq_single j]
          · simp [*]
          · exact fun i hij => Set.indicator_of_notMem (fun hi' => hij <| False.elim <|
              (hA hij).le_bot ⟨hi', hx⟩) _
        · exact A_meas
        · exact hA
      exact output.trans (setLIntegral_le_lintegral _ _)
    refine absurd (output.trans' (ENNReal.tsum_le_tsum h1)) ?_
    convert hfAq.eLpNorm_lt_top.ne using 1
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal _ _ hfAq.aestronglyMeasurable]
    · rw [ENNReal.rpow_eq_top_iff]
      norm_num
      exact ⟨(Or.inr ⟨·, ENNReal.toReal_pos (ne_zero_of_ge_one h1q) hq.ne⟩), (·.elim (by aesop)
        And.left)⟩
    · exact ne_zero_of_ge_one h1q
    · exact ne_of_lt hq

private lemma exists_pairwise_disjoint_and_all_of_all_all {α : Type*}
    (P : Set α → Prop) (hP0 : P ∅)
    (R : ℕ → Set α → Prop) (hPR : ∀ k : ℕ, ∀ U : Set α, P U → ∃ A : Set α, Disjoint A U ∧ P (U ∪ A)
      ∧ R k A) :
    ∃ A : ℕ → Set α, Pairwise (Function.onFun Disjoint A) ∧ (∀ k : ℕ, R k (A k)) := by
  choose! A hAU hAP hAR using hPR
  obtain ⟨s, hs⟩ : ∃ s : ℕ → Set α, (∀ k : ℕ, P (s k)) ∧ (∀ k : ℕ, s (k + 1) = s k ∪ A k (s k)) ∧ s
    0 = ∅ :=
    ⟨fun k : ℕ => k.recOn ∅ (fun B : Set α => B ∪ A · B), fun k : ℕ => k.recOn hP0 (hAP · _ ·),
      ↓rfl, rfl⟩
  refine ⟨fun k : ℕ => A k (s k), ?_, fun k : ℕ => hAR k (s k) (hs.left k)⟩
  intro i j hij
  have : ∀ i j : ℕ, i ≤ j → s i ⊆ s j := by
    intro i j hij
    induction hij <;> simp_all [Set.subset_def]
  cases lt_or_gt_of_ne hij <;> simp_all [Set.disjoint_left] <;> grind

private lemma exists_pairwise_disjoint_and_all_measurableSet_and_subset_and_pos_volume
    {S : Set ℝ} (hS : MeasurableSet S) (h0S : 0 < volume S) :
    ∃ A : ℕ → Set ℝ,
      Pairwise (Function.onFun Disjoint A) ∧
      (∀ j : ℕ, MeasurableSet (A j)) ∧
      (∀ j : ℕ, A j ⊆ S) ∧
      (∀ j : ℕ, 0 < volume (A j)) := by
  obtain ⟨n, hSn⟩ : ∃ n : ℕ, 0 < volume (S ∩ (Set.Icc (-n : ℝ) n)) := by
    contrapose! h0S
    rw [show S = ⋃ n : ℕ, S ∩ Set.Icc (-n : ℝ) n from ?_]
    · exact le_trans (measure_iUnion_le _) (tsum_nonpos h0S)
    · ext x
      constructor
      · intro hx
        refine Set.mem_iUnion.mpr ⟨⌈|x|⌉₊, hx, ?_⟩
        constructor <;> cases abs_cases x <;> linarith [Nat.le_ceil |x|]
      · aesop
  set S' := S ∩ (Set.Icc (-n : ℝ) n)
  have S'_meas : MeasurableSet S' :=
    hS.inter measurableSet_Icc
  have S'_lt_top : volume S' < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_right) measure_Icc_lt_top
  set P : Set ℝ → Prop := fun U => MeasurableSet U ∧ U ⊆ S' ∧ 0 < volume (S' \ U)
  set R : ℕ → Set ℝ → Prop := fun k A => MeasurableSet A ∧ A ⊆ S ∧ 0 < volume A
  have hP0 : P ∅ := by
    simp [P, S', hSn]
  have hPR : ∀ k : ℕ, ∀ U : Set ℝ, P U → ∃ A : Set ℝ, Disjoint A U ∧ P (U ∪ A) ∧ R k A := by
    intro k U hU
    obtain ⟨A, A_meas, A_subset, A_volume⟩ : ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ S' \ U ∧ volume A =
      volume (S' \ U) / 2 := by
      have h1 : volume (S' \ U) / 2 < ∫⁻ x : ℝ in S' \ U, 1 := by
        convert_to volume (S' \ U) < volume (S' \ U) + volume (S' \ U) using 0
        · simp [ENNReal.div_lt_iff, mul_two]
        apply ENNReal.lt_add_right
        · exact ne_of_lt <| lt_of_le_of_lt (measure_mono ↓And.left) S'_lt_top
        · exact ne_of_gt hU.right.right
      have := exists_measurable_subset_lintegral_eq_lt_lintegral measurable_const (S'_meas.diff
        hU.left) ENNReal.one_ne_top (by norm_num) h1
      aesop
    refine ⟨A, ?_, ?_, ?_⟩ <;> simp_all only [Set.subset_def,
        Set.mem_sdiff,
        Set.disjoint_left,
        not_false_eq_true,
        implies_true]
    · refine ⟨hU.left.union A_meas, ?_, ?_⟩
      · exact Set.union_subset hU.right.left (A_subset · · |>.left)
      · rw [show S' \ (U ∪ A) = (S' \ U) \ A by aesop, measure_sdiff] <;> norm_num [A_meas,
        A_subset, A_volume, hU.right.right]
        · exact ENNReal.half_lt_self (ne_of_gt hU.right.right) (ne_of_lt (lt_of_le_of_lt
          (measure_mono ↓And.left) S'_lt_top))
        · exact A_subset
        · exact ne_of_lt (ENNReal.div_lt_top (ne_of_lt (lt_of_le_of_lt (measure_mono ↓And.left)
          S'_lt_top)) two_ne_zero)
    · exact ⟨A_meas, (A_subset · · |>.left.left), A_volume.symm ▸ ENNReal.half_pos (ne_of_gt
      hU.right.right)⟩
  obtain ⟨A, hA, hRA⟩ := exists_pairwise_disjoint_and_all_of_all_all P hP0 R hPR
  use A
  aesop

private lemma two_mul_ofReal_rpow_le
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {C : ℝ} (h1C : 1 ≤ C)
    {k : ℕ} (hkC : (2 : ℝ) ^ (k + 1) ≤ C) :
    2 * ↱(C ^ (-q.toReal)) ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
  have hCqk : C ^ (-q.toReal) ≤ 1 / (2 ^ (k + 1)) := by
    rw [Real.rpow_neg (by positivity)]
    rw [inv_eq_one_div, div_le_div_iff₀] <;> norm_num
    · exact le_trans hkC (le_trans (by norm_num) (Real.rpow_le_rpow_of_exponent_le h1C (show
      q.toReal ≥ 1 from ENNReal.toReal_mono hq.ne_top h1q)))
    · positivity
  rw [←ENNReal.toReal_le_toReal] <;> norm_num
  · convert! mul_le_mul_of_nonneg_left hCqk zero_le_two using 1
    all_goals norm_num [ENNReal.toReal_ofReal (Real.rpow_nonneg (zero_le_one.trans h1C) _)]
    ring_nf
    norm_num [ENNReal.inv_pow]
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top

private lemma IsCaratheodory.exists_exists_of_volume_growthSup_eq_zero
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    {p q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    (hfpq : ∀ C : ℝ, 0 ≤ C → ∫⁻ x : ℝ, (growthSup f (p / q).toReal C x) ^ q.toReal ∂volume = ⊤)
    (h0 : ∃ C₀ : ℝ, 1 ≤ C₀ ∧ volume { x : ℝ | growthSup f (p / q).toReal C₀ x = ⊤ } = 0) :
    ∃ A : ℕ → Set ℝ, ∃ u : ℕ → ℝ → ℝ^m,
      (∀ j : ℕ, MeasurableSet (A j)) ∧
      Pairwise (Function.onFun Disjoint A) ∧
      (∀ j : ℕ, Measurable (u j)) ∧
      (∀ j : ℕ, ∀ x : ℝ, x ∉ A j → u j x = 0) ∧
      (∀ j : ℕ, 1 ≤ ∫⁻ x in A j, ‖f x (u j x)‖ₑ ^ q.toReal ∂volume) ∧
      (∀ j : ℕ, ∫⁻ x in A j, ‖u j x‖ₑ ^ p.toReal ∂volume ≤ (2 : ℝ≥0∞)⁻¹ ^ j) := by
  obtain ⟨C₀, h1C₀, hC0⟩ := h0
  have hh :=
    exists_pairwise_disjoint_and_all_of_all_all
      (fun U : Set ℝ => MeasurableSet U ∧ ∫⁻ x in U, (growthSup f (p / q).toReal C₀ x) ^ q.toReal
        ∂volume < ⊤)
      ?_
      (fun k : ℕ => fun U : Set ℝ => MeasurableSet U ∧ ∃ u : ℝ → ℝ^m,
          Measurable u ∧
          (∀ x : ℝ, x ∉ U → u x = 0) ∧
          1 ≤ ∫⁻ x in U, ‖f x (u x)‖ₑ ^ q.toReal ∂volume ∧
          ∫⁻ x in U, ‖u x‖ₑ ^ p.toReal ∂volume ≤ (2 : ℝ≥0∞) ⁻¹ ^ k)
      ?_
  · obtain ⟨A, _, hA⟩ := hh
    choose u hu using (hA · |>.right)
    use A, u
    aesop
  · norm_num
  · intro k U hU
    obtain ⟨M, hM⟩ :
      ∃ M : ℕ,
        2 ^ q.toReal <
        ∫⁻ x in (Uᶜ ∩ { x : ℝ | growthSup f (p / q).toReal C₀ x ≤ M }),
          (growthSup f (p / q).toReal (C₀ + 2 ^ (k + 1)) x) ^ q.toReal ∂volume := by
      have hfpq2 :
        Tendsto
          (fun M : ℕ => ∫⁻ x in (Uᶜ ∩ { x : ℝ | growthSup f (p / q).toReal C₀ x ≤ M }),
            (growthSup f (p / q).toReal (C₀ + 2 ^ (k + 1)) x) ^ q.toReal ∂volume)
          atTop
          (𝓝 (∫⁻ x in Uᶜ, (growthSup f (p / q).toReal (C₀ + 2 ^ (k + 1)) x) ^ q.toReal ∂volume)) :=
            by
        have hfpq2k :
          Tendsto
            (fun M : ℕ => ∫⁻ x in Uᶜ,
              (growthSup f (p / q).toReal (C₀ + 2 ^ (k + 1)) x) ^ q.toReal * (if growthSup f (p /
                q).toReal C₀ x ≤ M then 1 else 0) ∂volume)
            atTop
            (𝓝 (∫⁻ x in Uᶜ, (growthSup f (p / q).toReal (C₀ + 2 ^ (k + 1)) x) ^ q.toReal ∂volume))
              := by
          apply lintegral_tendsto_of_tendsto_of_monotone
          · intro
            apply AEMeasurable.mul
            · exact (Measurable.pow_const (hf.measurable_growthSup _ _) _).aemeasurable
            · apply Measurable.aemeasurable
              apply Measurable.ite (measurableSet_le (hf.measurable_growthSup _ _)
                measurable_const) <;> apply measurable_const
          · filter_upwards [] with x n m hnm
            dsimp only
            split_ifs with hfn hfm <;> norm_num
            exfalso
            exact hfm <| le_trans hfn <| Nat.cast_le.← hnm
          · filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.→ hC0)] with x hx
            rw [ENNReal.tendsto_nhds] at *
            · intro ε hε
              obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt hx
              filter_upwards [eventually_ge_atTop M] with n hn
              rw [ite_eq_left (le_trans hM.le (mod_cast hn))]
              simp
            · refine ne_of_lt (ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt ?_))
              refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.← hx)
              apply iSup_mono
              intro n
              apply ENNReal.ofReal_le_ofReal
              apply sub_le_sub_left
              apply mul_le_mul_of_nonneg_right (by
                linarith [pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2) (k + 1)])
              positivity
        convert hfpq2k using 2
        rw [←lintegral_indicator]
        · rw [←lintegral_indicator] <;> norm_num [Set.indicator]
          · congr
            aesop
          · exact hU.left
        · exact MeasurableSet.inter (hU.left.compl) (measurableSet_le (hf.measurable_growthSup _ _)
          measurable_const)
      have lim_inf : ∫⁻ x in Uᶜ, (growthSup f (p / q).toReal (C₀ + 2 ^ (k + 1)) x) ^ q.toReal
        ∂volume = ⊤ := by
        have lim_inf : ∫⁻ x, (growthSup f (p / q).toReal (C₀ + 2 ^ (k + 1)) x) ^ q.toReal ∂volume =
          ⊤ := by
          apply hfpq
          positivity
        contrapose! lim_inf
        rw [←lintegral_add_compl _ hU.left]
        refine ne_of_lt (ENNReal.add_lt_top.← ⟨?_, ?_⟩)
        · refine lt_of_le_of_lt ?_ hU.right
          refine setLIntegral_mono' hU.left ?_
          intros
          gcongr
          apply iSup_mono
          intro
          apply ENNReal.ofReal_le_ofReal
          apply sub_le_sub_left
          apply mul_le_mul_of_nonneg_right (by linarith [pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2) (k
            + 1)])
          positivity
        · rwa [lt_top_iff_ne_top]
      rw [lim_inf] at hfpq2
      exact (hfpq2.eventually (lt_mem_nhds <| ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
        ENNReal.top_ne_ofNat.symm)).exists
    obtain ⟨A, A_meas, hA, hA_fin, u, u_meas, u_supp, hu_out, hu_in⟩ :
      ∃ A : Set ℝ,
        MeasurableSet A ∧
        A ⊆ Uᶜ ∩ { x : ℝ | growthSup f (p / q).toReal C₀ x ≤ M } ∧
        volume A < ⊤ ∧ ∃ u : ℝ → ℝ^m, Measurable u ∧
        (∀ x : ℝ, x ∉ A → u x = 0) ∧
        1 ≤ ∫⁻ x in A, ‖f x (u x)‖ₑ ^ q.toReal ∂volume ∧
        ∫⁻ x in A, ‖f x (u x)‖ₑ ^ q.toReal ∂volume ≤ 2 ∧
        ∫⁻ x in A, ‖u x‖ₑ ^ p.toReal ∂volume ≤ 2 * ↱((C₀ + 2 ^ (k + 1)) ^ (-q.toReal)) := by
      apply_rules [IsCaratheodory.exists_bad_subset_measurableSet]
      · apply le_add_of_le_of_nonneg h1C₀
        positivity
      · exact MeasurableSet.inter hU.left.compl (measurableSet_le (hf.measurable_growthSup _ _)
        measurable_const)
    refine ⟨A, Set.disjoint_left.← ↓(hA · |>.left ·), ?_, ?_⟩
    · refine ⟨hU.left.union A_meas, ?_⟩
      refine lt_of_le_of_lt (lintegral_union_le _ _ _) ?_
      refine ENNReal.add_lt_top.← ⟨hU.right, ?_⟩
      refine lt_of_le_of_lt (setLIntegral_mono' A_meas
        (g := fun _ => ↱(M ^ q.toReal)) ?_) ?_
      · intro x hx
        specialize hA hx
        simp_all only [ENNReal.toReal_div]
        convert ENNReal.rpow_le_rpow hA.right _ using 1
        · norm_num [ENNReal.ofReal]
          norm_num [ENNReal.coe_rpow_of_nonneg, Real.toNNReal_rpow_of_nonneg, Nat.cast_nonneg]
        · positivity
      · simpa using ENNReal.mul_lt_top (by norm_num) hA_fin
    · refine ⟨A_meas, u, u_meas, u_supp, hu_out, hu_in.right.trans ?_⟩
      exact two_mul_ofReal_rpow_le h1q hq
        (show 1 ≤ C₀ + 2 ^ (k + 1) by linarith [pow_pos (zero_lt_two' ℝ) (k + 1)])
        (show (2 : ℝ) ^ (k + 1) ≤ C₀ + 2 ^ (k + 1) by linarith)

private lemma IsCaratheodory.exists_exists_of_volume_growthSup_ne_zero
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    {p q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    (h0 : ∀ C : ℝ, 1 ≤ C → volume { x : ℝ | growthSup f (p / q).toReal C x = ⊤ } ≠ 0) :
    ∃ A : ℕ → Set ℝ, ∃ u : ℕ → ℝ → ℝ^m,
      (∀ j : ℕ, MeasurableSet (A j)) ∧
      Pairwise (Function.onFun Disjoint A) ∧
      (∀ j : ℕ, Measurable (u j)) ∧
      (∀ j : ℕ, ∀ x : ℝ, x ∉ A j → u j x = 0) ∧
      (∀ j : ℕ, 1 ≤ ∫⁻ x in A j, ‖f x (u j x)‖ₑ ^ q.toReal ∂volume) ∧
      (∀ j : ℕ, ∫⁻ x in A j, ‖u j x‖ₑ ^ p.toReal ∂volume ≤ (2 : ℝ≥0∞)⁻¹ ^ j) := by
  set r := (p / q).toReal
  set Q := q.toReal
  set T : ℕ → Set ℝ := fun j : ℕ => { x : ℝ | growthSup f r (2 ^ (j+1)) x = ⊤ }
  have T_meas : ∀ j : ℕ, MeasurableSet (T j) :=
    ↓(measurableSet_eq_fun (hf.measurable_growthSup _ _) measurable_const)
  have T_antitone : Antitone T := by
    apply antitone_nat_of_succ_le
    intro n x hx
    simp_all only [growthSup,
        ne_eq]
    refine top_unique <| hx ▸ iSup_mono ↓?_
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (mul_le_mul_of_nonneg_right (pow_le_pow_right₀
      one_le_two (by omega)) (by positivity)) _)
  have T_pos : ∀ j : ℕ, 0 < volume (T j) :=
    ↓(lt_of_le_of_ne zero_le (Ne.symm (h0 _ (one_le_pow₀ one_le_two))))
  by_cases T_inf : 0 < volume (⋂ j, T j)
  · obtain ⟨P, P_meas, P_disj, P_subset, P_pos⟩ :
      ∃ P : ℕ → Set ℝ,
        Pairwise (Function.onFun Disjoint P) ∧
        (∀ j : ℕ, MeasurableSet (P j)) ∧
        (∀ j : ℕ, P j ⊆ ⋂ j, T j) ∧
        (∀ j : ℕ, 0 < volume (P j)) :=
      exists_pairwise_disjoint_and_all_measurableSet_and_subset_and_pos_volume
        (MeasurableSet.iInter T_meas) T_inf
    have per_piece :
      ∀ k : ℕ, ∃ Aₖ : Set ℝ,
        MeasurableSet Aₖ ∧
        Aₖ ⊆ P k ∧
        volume Aₖ < ⊤ ∧
        ∃ uₖ : ℝ → ℝ^m,
          Measurable uₖ ∧
          (∀ x : ℝ, x ∉ Aₖ → uₖ x = 0) ∧
          1 ≤ ∫⁻ x in Aₖ, ‖f x (uₖ x)‖ₑ ^ Q ∂volume ∧
          ∫⁻ x in Aₖ, ‖f x (uₖ x)‖ₑ ^ Q ∂volume ≤ 2 ∧
          ∫⁻ x in Aₖ, ‖uₖ x‖ₑ ^ p.toReal ∂volume ≤ 2 * ↱((2^(k+1)) ^ (-Q)) := by
      intro k
      have int_pos : (2 : ℝ≥0∞) ^ Q < ∫⁻ x in P k, (growthSup f r (2^(k+1)) x) ^ Q ∂volume := by
        have int_pos : ∫⁻ x in P k, (growthSup f r (2^(k+1)) x) ^ Q ∂volume = ∫⁻ x in P k, ⊤ ^ Q
          ∂volume := by
          apply setLIntegral_congr_fun (P_disj k)
          intro x hx
          specialize P_subset k hx
          aesop
        rw [int_pos, ENNReal.top_rpow_of_pos] <;> norm_num
        · rw [ENNReal.top_mul] <;> norm_num [P_pos k]
          · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.top_ne_ofNat.symm
          · exact ne_of_gt (P_pos k)
        · exact ENNReal.toReal_pos (ne_zero_of_ge_one h1q) hq.ne_top
      exact hf.exists_bad_subset_measurableSet h1q hq (show 1 ≤ (2 : ℝ) ^ (k + 1) from one_le_pow₀
        (by norm_num)) (P_disj k) int_pos
    choose A A_meas A_subset A_finite u u_meas u_supp hu_out hu_in using per_piece
    refine ⟨A, u, A_meas, ?_, u_meas, u_supp, hu_out, ?_⟩
    · exact fun i j hij => Disjoint.mono (A_subset i) (A_subset j) (P_meas hij)
    · intro j
      apply le_trans (hu_in j).right
      exact two_mul_ofReal_rpow_le h1q hq (one_le_pow₀ one_le_two) le_rfl
  · have infinite : Set.Infinite { j : ℕ | 0 < volume (T j \ T (j + 1)) } := by
      contrapose! T_inf
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j ≥ N, volume (T j \ T (j + 1)) = 0 :=
        ⟨T_inf.bddAbove.some + 1, fun j hj => le_antisymm (le_of_not_gt fun h0 => not_lt_of_ge
          (T_inf.bddAbove.choose_spec h0) hj) zero_le⟩
      have union_zero : volume (T N \ ⋂ j, T j) = 0 := by
        have hTN : T N \ ⋂ j, T j ⊆ ⋃ j ≥ N, (T j \ T (j + 1)) := by
          intro x hx
          simp_all only [ge_iff_le, Set.mem_iUnion, Set.mem_iInter, not_forall,
            Set.mem_sdiff, exists_and_left, exists_prop]
          obtain ⟨j, hj⟩ := hx.right
          induction j with
          | zero =>
            exfalso
            exact hj <| T_antitone (Nat.zero_le _) hx.left
          | succ j ih =>
            by_cases h : x ∈ T j <;> simp_all only [ne_eq,
              not_true_eq_false,
              not_isEmpty_of_nonempty,
              IsEmpty.exists_iff,
              implies_true,
              not_false_eq_true,
              forall_const]
            exact ⟨j, h, le_of_not_gt fun hj' => hj <| T_antitone (by linarith) hx.left, hj⟩
        exact measure_mono_null hTN (measure_iUnion_null fun j : ℕ => measure_iUnion_null (hN j))
      have volume_eq : volume (T N) = volume (⋂ j, T j) := by
        rw [←measure_sdiff_null union_zero]
        rw [Set.sdiff_sdiff_cancel_left (Set.iInter_subset _ _)]
      exact volume_eq ▸ T_pos N
    obtain ⟨s, s_inc, s_pos, le_s⟩ :
      ∃ s : ℕ → ℕ,
        StrictMono s ∧
        (∀ k : ℕ, 0 < volume (T (s k) \ T (s k + 1))) ∧
        (∀ k : ℕ, k ≤ s k) := ⟨
      (·.recOn (Nat.find <| infinite.exists_gt 0) fun n ih => Nat.find <| infinite.exists_gt ih),
      strictMono_nat_of_lt_succ ↓(Nat.find_spec (infinite.exists_gt _)).right,
      (·.recOn (Nat.find_spec (infinite.exists_gt 0)).left ↓↓(Nat.find_spec (infinite.exists_gt
        _)).left),
      (·.recOn (Nat.zero_le _) ↓(Nat.succ_le_of_lt <| Nat.lt_of_le_of_lt · <| Nat.find_spec
        (infinite.exists_gt _) |>.right))⟩
    have D_disjoint : Pairwise (Function.onFun Disjoint (fun k : ℕ => T (s k) \ T (s k + 1))) := by
      intros k l hkl
      cases lt_or_gt_of_ne hkl with
      | inl hkl =>
        simp only [Set.disjoint_left,
            Set.mem_sdiff,
            not_and,
            Decidable.not_not,
            and_imp]
        exact ↓↓(False.elim <| · <| T_antitone (by linarith [s_inc hkl]) ·)
      | inr hlk =>
        simp only [Set.disjoint_left,
            Set.mem_sdiff,
            not_and,
            Decidable.not_not,
            and_imp]
        intro x hx _ _
        exact T_antitone (by linarith [s_inc hlk]) hx
    have per_piece : ∀ k : ℕ, ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ T (s k) \ T (s k + 1) ∧ volume A <
      ⊤ ∧ ∃ u : ℝ → ℝ^m, Measurable u ∧ (∀ x : ℝ, x ∉ A → u x = 0) ∧ 1 ≤ ∫⁻ x in A, ‖f x (u x)‖ₑ ^
      Q ∂volume ∧ ∫⁻ x in A, ‖f x (u x)‖ₑ ^ Q ∂volume ≤ 2 ∧ ∫⁻ x in A, ‖u x‖ₑ ^ p.toReal ∂volume ≤
      (2 : ℝ≥0∞)⁻¹ ^ k := by
      intro k
      have per_piece : 2 ^ Q < ∫⁻ x in T (s k) \ T (s k + 1), (growthSup f r (2^(s k + 1)) x) ^ Q
        ∂volume := by
        have per_piece : ∀ x ∈ T (s k) \ T (s k + 1), (growthSup f r (2^(s k + 1)) x) ^ Q = ⊤ := by
          simp +zetaDelta only [Set.mem_sdiff, ENNReal.rpow_eq_top_iff, and_imp] at *
          intro x h1x _
          right
          constructor
          · exact h1x
          · exact ENNReal.toReal_pos (ne_zero_of_ge_one h1q) hq.ne_top
        rw [setLIntegral_congr_fun]
        any_goals exact per_piece
        · simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
            Set.univ_inter, gt_iff_lt]
          rw [ENNReal.top_mul] <;> norm_num [s_pos k]
          · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.top_ne_ofNat.symm
          · exact ne_of_gt (s_pos k)
        · exact MeasurableSet.diff (T_meas _) (T_meas _)
      obtain ⟨A, hA₁, hA₂, hA₃, u, hu₁, hu₂, hu₃, hu₄, hu₅⟩ :=
        hf.exists_bad_subset_measurableSet h1q hq
          (show 1 ≤ (2 : ℝ) ^ (s k + 1) from one_le_pow₀ one_le_two)
          (show MeasurableSet (T (s k) \ T (s k + 1)) from MeasurableSet.diff (T_meas _) (T_meas _))
          per_piece
      refine ⟨A, hA₁, hA₂, hA₃, u, hu₁, hu₂, hu₃, hu₄, hu₅.trans ?_⟩
      exact two_mul_ofReal_rpow_le h1q hq
        (show 1 ≤ (2 : ℝ) ^ (s k + 1) from one_le_pow₀ one_le_two)
        (show (2 : ℝ) ^ (k + 1) ≤ 2 ^ (s k + 1) from pow_le_pow_right₀ one_le_two
          (Nat.add_le_add_right (le_s k) 1))
    choose A A_meas A_subset A_finite u u_meas u_zero hu_out hu_in using per_piece
    exact ⟨A, u, A_meas, fun i j hij => Set.disjoint_left.← fun x hx hx' => Set.disjoint_left.→
      (D_disjoint hij) (A_subset i hx) (A_subset j hx'), u_meas, u_zero, hu_out, (hu_in · |>.right)⟩

private lemma IsCaratheodory.disjoint_counterexample_pieces
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    {p q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    (hfpq : ∀ C : ℝ, 0 ≤ C → ∫⁻ x : ℝ, (growthSup f (p / q).toReal C x) ^ q.toReal ∂volume = ⊤) :
    ∃ A : ℕ → Set ℝ, ∃ u : ℕ → ℝ → ℝ^m,
      (∀ j : ℕ, MeasurableSet (A j)) ∧ Pairwise (Function.onFun Disjoint A) ∧
      (∀ j : ℕ, Measurable (u j)) ∧ (∀ j : ℕ, ∀ x : ℝ, x ∉ A j → u j x = 0) ∧
      (∀ j : ℕ, 1 ≤ ∫⁻ x in A j, ‖f x (u j x)‖ₑ ^ q.toReal ∂volume) ∧
      (∀ j : ℕ, ∫⁻ x in A j, ‖u j x‖ₑ ^ p.toReal ∂volume ≤ (2 : ℝ≥0∞)⁻¹ ^ j) := by
  by_cases hcase : ∃ C₀ : ℝ, 1 ≤ C₀ ∧ volume { x : ℝ | growthSup f (p / q).toReal C₀ x = ⊤ } = 0
  · exact hf.exists_exists_of_volume_growthSup_eq_zero h1q hq hfpq hcase
  · push Not at hcase
    exact hf.exists_exists_of_volume_growthSup_ne_zero h1q hq hcase

private lemma IsCaratheodory.counterexample_of_infinite_growth_integral
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    (hfpq : ∀ C : ℝ, 0 ≤ C → ∫⁻ x : ℝ, (growthSup f (p / q).toReal C x) ^ q.toReal ∂volume = ⊤) :
    ∃ u : ℝ → ℝ^m, MemLp u p volume ∧ ¬ MemLp (fun x : ℝ => f x (u x)) q volume := by
  obtain ⟨A, u, A_meas, hA, u_meas, u_supp, h1, h2⟩ :=
    hf.disjoint_counterexample_pieces h1q hq hfpq
  exact exists_memLp_and_not_memLp_nemytskii_of_pairwise_disjoint_measurableSet h1p hp h1q hq hA
    A_meas u_meas h1 h2

lemma IsCaratheodory.growth_of_memLp_nemytskii_volume
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    (hpqf : ∀ u : ℝ → ℝ^m, MemLp u p volume → MemLp (fun x : ℝ => f x (u x)) q volume) :
    ∃ a : ℝ → ℝ, MemLp a q volume ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ x : ℝ ∂volume, ∀ ξ : ℝ^m, ‖f x ξ‖ ≤ |a x| + C * ‖ξ‖ ^ (p / q).toReal := by
  by_contra hcon
  have hfpq : ∀ C : ℝ, 0 ≤ C →
      ∫⁻ x : ℝ, (growthSup f (p / q).toReal C x) ^ q.toReal ∂volume = ⊤ := by
    intro C hC
    by_contra hfpqC
    obtain ⟨a, ha, hlK⟩ := growth_of_lintegral_growthSup_rpow_toReal_ne_top hf h1q hq hfpqC
    exact hcon ⟨a, ha, C, hC, hlK⟩
  obtain ⟨u, hu, hfu⟩ := hf.counterexample_of_infinite_growth_integral h1p hp h1q hq hfpq
  exact hfu (hpqf u hu)

theorem IsCaratheodory.memLp_nemytskii_volume_iff_growth
    {m k : ℕ} {f : ℝ → ℝ^m → ℝ^k} (hf : IsCaratheodory f volume)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤) :
    (∀ u : ℝ → ℝ^m, MemLp u p volume → MemLp (fun x : ℝ => f x (u x)) q volume) ↔
    (∃ a : ℝ → ℝ, MemLp a q volume ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ x : ℝ ∂volume, ∀ ξ : ℝ^m, ‖f x ξ‖ ≤ |a x| + C * ‖ξ‖ ^ (p / q).toReal) :=
  ⟨hf.growth_of_memLp_nemytskii_volume h1p hp h1q hq,
  fun ⟨_, ha, _, hC, haCpq⟩ _ => hf.memLp_nemytskii_of_growth_real h1p hp h1q hq ha hC haCpq⟩

end NemytskiiLebesgue
