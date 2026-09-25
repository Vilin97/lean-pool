/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KaltonEndpoint

/-!
# Countable block suprema followed by the paper's Kalton summation

The block outputs are extended nonnegative real functions, so the genuine
supremum and sum retain infinite values. We prove the block union bound and
apply the existing countable Kalton theorem to measurable, finitely supported,
capped approximations. Their monotone limit recovers the exact countable
expression, without assuming pointwise convergence of the original series.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace QuadraticCarleson
namespace KaltonPaperApplication

open KaltonEndpoint


/-- The distribution-function weak bound for an extended nonnegative output. -/
def HasExtendedWeakL1Bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : ℝ) (F : X → ℝ≥0∞) : Prop :=
  0 ≤ A ∧ ∀ a : ℝ, 0 < a →
    ENNReal.ofReal a * μ {x | ENNReal.ofReal a < F x} ≤ ENNReal.ofReal A

/-- The pointwise supremum of a family of extended nonnegative outputs. -/
noncomputable def blockSupremum {X ι : Type*} (F : ι → X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ⨆ τ, F τ x

theorem measurable_blockSupremum {X ι : Type*} [MeasurableSpace X] [Countable ι]
    {F : ι → X → ℝ≥0∞} (hF : ∀ τ, Measurable (F τ)) :
    Measurable (blockSupremum F) := Measurable.iSup hF

/-- The countable supremum costs only the sum of the individual weak
constants. No pointwise boundedness of that supremum is assumed. -/
theorem hasExtendedWeakL1Bound_blockSupremum
    {X ι : Type*} [MeasurableSpace X] [Countable ι] {μ : Measure X}
    {F : ι → X → ℝ≥0∞} {A : ι → ℝ}
    (hweak : ∀ τ, HasExtendedWeakL1Bound μ (A τ) (F τ)) (hA : Summable A) :
    HasExtendedWeakL1Bound μ (∑' τ, A τ) (blockSupremum F) := by
  refine ⟨tsum_nonneg (fun τ ↦ (hweak τ).1), ?_⟩
  intro a ha
  have hs : {x | ENNReal.ofReal a < blockSupremum F x} =
      ⋃ τ, {x | ENNReal.ofReal a < F τ x} := by
    ext x
    simp only [blockSupremum, mem_ofPred_eq, lt_iSup_iff, mem_iUnion]
  rw [hs]
  calc
    _ ≤ ENNReal.ofReal a * ∑' τ, μ {x | ENNReal.ofReal a < F τ x} :=
      mul_le_mul' le_rfl (measure_iUnion_le _)
    _ = ∑' τ, ENNReal.ofReal a * μ {x | ENNReal.ofReal a < F τ x} :=
      (ENNReal.tsum_mul_left).symm
    _ ≤ ∑' τ, ENNReal.ofReal (A τ) :=
      ENNReal.tsum_le_tsum fun τ ↦ (hweak τ).2 a ha
    _ = ENNReal.ofReal (∑' τ, A τ) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun τ ↦ (hweak τ).1) hA).symm

/-- Real-valued finite cap used solely inside the checked Kalton theorem. -/
noncomputable def capOutput {X : Type*} (F : X → ℝ≥0∞) (M : ℕ) (x : X) : ℝ :=
  (min (M : ℝ≥0∞) (F x)).toReal

theorem measurable_capOutput {X : Type*} [MeasurableSpace X]
    {F : X → ℝ≥0∞} (hF : Measurable F) (M : ℕ) : Measurable (capOutput F M) :=
  (measurable_const.min hF).ennreal_toReal

theorem capOutput_nonneg {X : Type*} (F : X → ℝ≥0∞) (M : ℕ) (x : X) :
    0 ≤ capOutput F M x := ENNReal.toReal_nonneg

theorem ofReal_capOutput {X : Type*} (F : X → ℝ≥0∞) (M : ℕ) (x : X) :
    ENNReal.ofReal (capOutput F M x) = min (M : ℝ≥0∞) (F x) :=
  ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by finiteness) (min_le_left _ _))

theorem hasWeakL1Bound_capOutput {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F : X → ℝ≥0∞} {A : ℝ}
    (hweak : HasExtendedWeakL1Bound μ A F) (M : ℕ) :
    HasWeakL1Bound μ A (capOutput F M) := by
  refine ⟨hweak.1, ?_⟩
  intro a ha
  apply le_trans _ (hweak.2 a ha)
  apply mul_le_mul' le_rfl
  apply measure_mono
  intro x hx
  have hlt : a < (min (M : ℝ≥0∞) (F x)).toReal := hx
  exact ((ENNReal.ofReal_lt_iff_lt_toReal ha.le
    (ne_top_of_le_ne_top (by finiteness) (min_le_left _ _))).mpr hlt).trans_le
      (min_le_right _ _)

/-- The first `N` outputs capped at height `M` and converted to real values, extended by zero to
later indices. -/
noncomputable def finiteCapSequence {X : Type*}
    (F : ℕ → X → ℝ≥0∞) (N M k : ℕ) (x : X) : ℝ :=
  if k < N then capOutput (F k) M x else 0

theorem measurable_finiteCapSequence {X : Type*} [MeasurableSpace X]
    {F : ℕ → X → ℝ≥0∞} (hF : ∀ k, Measurable (F k)) (N M k : ℕ) :
    Measurable (finiteCapSequence F N M k) := by
  change Measurable (fun x ↦ if k < N then capOutput (F k) M x else 0)
  by_cases hk : k < N
  · simpa only [ite_eq_left hk] using measurable_capOutput (hF k) M
  · simpa only [ite_eq_right hk] using
      (measurable_const : Measurable (fun _ : X ↦ (0 : ℝ)))

theorem finiteCapSequence_nonneg {X : Type*} (F : ℕ → X → ℝ≥0∞)
    (N M k : ℕ) (x : X) : 0 ≤ finiteCapSequence F N M k x := by
  unfold finiteCapSequence
  split_ifs
  · exact capOutput_nonneg _ _ _
  · exact le_rfl

theorem summable_finiteCapSequence {X : Type*} (F : ℕ → X → ℝ≥0∞)
    (N M : ℕ) (x : X) : Summable (fun k ↦ finiteCapSequence F N M k x) := by
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro k hk
  simp only [Finset.mem_range] at hk
  simp only [finiteCapSequence, ite_eq_right hk]

theorem hasWeakL1Bound_finiteCapSequence {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F : ℕ → X → ℝ≥0∞} {A : ℕ → ℝ}
    (hweak : ∀ k, HasExtendedWeakL1Bound μ (A k) (F k)) (N M k : ℕ) :
    HasWeakL1Bound μ (A k) (finiteCapSequence F N M k) := by
  change HasWeakL1Bound μ (A k) (fun x ↦ if k < N then capOutput (F k) M x else 0)
  by_cases hk : k < N
  · simpa only [ite_eq_left hk] using hasWeakL1Bound_capOutput (hweak k) M
  · refine ⟨(hweak k).1, ?_⟩
    intro a ha
    simp only [ite_eq_right hk, not_lt_of_ge ha.le,
      ofPred_false, measure_empty, mul_zero]
    exact bot_le

/-- The sum of the first `N` extended nonnegative outputs, each capped at height `M`. -/
noncomputable def partialCap {X : Type*} (F : ℕ → X → ℝ≥0∞)
    (N M : ℕ) (x : X) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range N, min (M : ℝ≥0∞) (F k x)

theorem ofReal_tsum_finiteCapSequence {X : Type*} (F : ℕ → X → ℝ≥0∞)
    (N M : ℕ) (x : X) :
    ENNReal.ofReal (∑' k, finiteCapSequence F N M k x) = partialCap F N M x := by
  rw [tsum_eq_sum (s := Finset.range N) (fun k hk ↦ by
    simp only [Finset.mem_range] at hk
    simp only [finiteCapSequence, ite_eq_right hk])]
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ finiteCapSequence_nonneg F N M k x)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [finiteCapSequence, ite_eq_left (Finset.mem_range.mp hk), ofReal_capOutput]

/-- Pointwise summability and measurability of the approximants are proved
above, so this invokes the existing countable Kalton theorem without an
additional convergence hypothesis. -/
theorem partialCap_levelSet_mul_le_paperLog
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : ℕ → X → ℝ≥0∞} {A : ℕ → ℝ}
    (hF : ∀ k, Measurable (F k))
    (hweak : ∀ k, HasExtendedWeakL1Bound μ (A k) (F k))
    (hA : Summable (fun k : ℕ ↦ paperLog 1 ((k : ℝ) + 2) * A k))
    (N M : ℕ) {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal a * μ {x | ENNReal.ofReal a < partialCap F N M x} ≤
      ENNReal.ofReal (24 * ∑' k : ℕ, paperLog 1 ((k : ℝ) + 2) * A k) := by
  have h := hasWeakL1Bound_tsum_paperLog (finiteCapSequence F N M) A
    (measurable_finiteCapSequence hF N M) (finiteCapSequence_nonneg F N M)
    (hasWeakL1Bound_finiteCapSequence hweak N M) hA (summable_finiteCapSequence F N M)
  have hs : {x | ENNReal.ofReal a < partialCap F N M x} =
      {x | a < ∑' k, finiteCapSequence F N M k x} := by
    ext x
    change (ENNReal.ofReal a < partialCap F N M x) ↔
      a < ∑' k, finiteCapSequence F N M k x
    rw [← ofReal_tsum_finiteCapSequence]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le
  rw [hs]
  exact h.2 a ha

theorem monotone_partialCap_levels {X : Type*} (F : ℕ → X → ℝ≥0∞)
    (M : ℕ) (x : X) : Monotone (fun N ↦ partialCap F N M x) := by
  intro N N' hN
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hN)

theorem monotone_partialCap_cap {X : Type*} (F : ℕ → X → ℝ≥0∞)
    (N : ℕ) (x : X) : Monotone (fun M ↦ partialCap F N M x) := by
  intro M M' hM
  apply Finset.sum_le_sum
  intro k hk
  exact min_le_min_right _ (Nat.cast_le.mpr hM)

theorem tendsto_partialCap {X : Type*} (F : ℕ → X → ℝ≥0∞) (N : ℕ) (x : X) :
    Tendsto (fun M ↦ partialCap F N M x) atTop
      (𝓝 (∑ k ∈ Finset.range N, F k x)) := by
  apply tendsto_finsetSum
  intro k hk
  simpa only [min_top_left] using
    ENNReal.tendsto_nat_nhds_top.min (tendsto_const_nhds (x := F k x))

/-- Exact recovery of every strict level set, even where the series diverges
to infinity. Both approximation parameters are natural numbers. -/
theorem tsum_levelSet_eq_iUnion_partialCap {X : Type*}
    (F : ℕ → X → ℝ≥0∞) (a : ℝ≥0∞) :
    {x | a < ∑' k, F k x} = ⋃ N : ℕ, ⋃ M : ℕ, {x | a < partialCap F N M x} := by
  ext x
  constructor
  · intro hx
    change a < ∑' k, F k x at hx
    rw [ENNReal.tsum_eq_iSup_nat] at hx
    obtain ⟨N, hN⟩ := lt_iSup_iff.mp hx
    obtain ⟨M, hM⟩ := ((tendsto_order.mp (tendsto_partialCap F N x)).1 a hN).exists
    exact mem_iUnion.mpr ⟨N, mem_iUnion.mpr ⟨M, hM⟩⟩
  · intro hx
    obtain ⟨N, hN⟩ := mem_iUnion.mp hx
    obtain ⟨M, hM⟩ := mem_iUnion.mp hN
    have hbound : partialCap F N M x ≤ ∑' k, F k x :=
      (Finset.sum_le_sum (fun k _ ↦ min_le_right (M : ℝ≥0∞) (F k x))).trans
        (ENNReal.sum_le_tsum (Finset.range N))
    exact hM.trans_le hbound

/-- Countable Kalton summation for the genuine extended-real sum. This
removes the pointwise-summability requirement by an explicit monotone passage
from the already checked countable theorem on finite-cap approximants. -/
theorem hasExtendedWeakL1Bound_tsum_paperLog
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : ℕ → X → ℝ≥0∞} {A : ℕ → ℝ}
    (hF : ∀ k, Measurable (F k))
    (hweak : ∀ k, HasExtendedWeakL1Bound μ (A k) (F k))
    (hA : Summable (fun k : ℕ ↦ paperLog 1 ((k : ℝ) + 2) * A k)) :
    HasExtendedWeakL1Bound μ
      (24 * ∑' k : ℕ, paperLog 1 ((k : ℝ) + 2) * A k)
      (fun x ↦ ∑' k, F k x) := by
  refine ⟨mul_nonneg (by norm_num) (tsum_nonneg fun k ↦ ?_), ?_⟩
  · apply mul_nonneg _ (hweak k).1
    rw [paper_outer_weight_eq]
    exact Real.log_nonneg (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  intro a ha
  let E : ℕ → ℕ → Set X := fun N M ↦ {x | ENNReal.ofReal a < partialCap F N M x}
  have hM (N : ℕ) : Monotone (E N) := by
    intro M M' hMM' x hx
    exact hx.trans_le (monotone_partialCap_cap F N x hMM')
  have hN : Monotone (fun N ↦ ⋃ M, E N M) := by
    intro N N' hNN' x hx
    obtain ⟨M, hMx⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨M, hMx.trans_le (monotone_partialCap_levels F M x hNN')⟩
  rw [tsum_levelSet_eq_iUnion_partialCap]
  change ENNReal.ofReal a * μ (⋃ N, ⋃ M, E N M) ≤ _
  rw [hN.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro N
  rw [(hM N).measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun M ↦ partialCap_levelSet_mul_le_paperLog hF hweak hA N M ha

/-- The paper's exact nonnegative outer expression `∑ₖ sup_τ F_{k,τ}`. -/
noncomputable def paperBlockOutput {X ι : Type*} (F : ℕ → ι → X → ℝ≥0∞)
    (x : X) : ℝ≥0∞ := ∑' k, blockSupremum (F k) x

theorem measurable_paperBlockOutput {X ι : Type*} [MeasurableSpace X] [Countable ι]
    {F : ℕ → ι → X → ℝ≥0∞} (hF : ∀ k τ, Measurable (F k τ)) :
    Measurable (paperBlockOutput F) :=
  Measurable.tsum fun k ↦ measurable_blockSupremum (hF k)

/-- Countable union in the block parameter, then Kalton in the magnitude
level, with precisely the paper's `log₁(k+2)` weight and constant 24. -/
theorem hasExtendedWeakL1Bound_paperBlockOutput
    {X ι : Type*} [MeasurableSpace X] [Countable ι] {μ : Measure X}
    {F : ℕ → ι → X → ℝ≥0∞} {A : ℕ → ι → ℝ}
    (hF : ∀ k τ, Measurable (F k τ))
    (hweak : ∀ k τ, HasExtendedWeakL1Bound μ (A k τ) (F k τ))
    (hrow : ∀ k, Summable (A k))
    (hA : Summable (fun k : ℕ ↦
      paperLog 1 ((k : ℝ) + 2) * ∑' τ, A k τ)) :
    HasExtendedWeakL1Bound μ
      (24 * ∑' k : ℕ, paperLog 1 ((k : ℝ) + 2) * ∑' τ, A k τ)
      (paperBlockOutput F) :=
  hasExtendedWeakL1Bound_tsum_paperLog
    (fun k ↦ measurable_blockSupremum (hF k))
    (fun k ↦ hasExtendedWeakL1Bound_blockSupremum (hweak k) (hrow k)) hA

/-- Distribution form ready for the actual block operators. The measure
space can already be restricted to the stopping exceptional-set complement. -/
theorem paperBlockOutput_levelSet_mul_le
    {X ι : Type*} [MeasurableSpace X] [Countable ι] {μ : Measure X}
    {F : ℕ → ι → X → ℝ≥0∞} {A : ℕ → ι → ℝ}
    (hF : ∀ k τ, Measurable (F k τ))
    (hweak : ∀ k τ, HasExtendedWeakL1Bound μ (A k τ) (F k τ))
    (hrow : ∀ k, Summable (A k))
    (hA : Summable (fun k : ℕ ↦
      paperLog 1 ((k : ℝ) + 2) * ∑' τ, A k τ))
    {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal a * μ {x | ENNReal.ofReal a < paperBlockOutput F x} ≤
      ENNReal.ofReal (24 * ∑' k : ℕ,
        paperLog 1 ((k : ℝ) + 2) * ∑' τ, A k τ) :=
  (hasExtendedWeakL1Bound_paperBlockOutput hF hweak hrow hA).2 a ha

theorem paperBlockOutput_levelSet_one_le
    {X ι : Type*} [MeasurableSpace X] [Countable ι] {μ : Measure X}
    {F : ℕ → ι → X → ℝ≥0∞} {A : ℕ → ι → ℝ}
    (hF : ∀ k τ, Measurable (F k τ))
    (hweak : ∀ k τ, HasExtendedWeakL1Bound μ (A k τ) (F k τ))
    (hrow : ∀ k, Summable (A k))
    (hA : Summable (fun k : ℕ ↦
      paperLog 1 ((k : ℝ) + 2) * ∑' τ, A k τ)) :
    μ {x | 1 < paperBlockOutput F x} ≤
      ENNReal.ofReal (24 * ∑' k : ℕ,
        paperLog 1 ((k : ℝ) + 2) * ∑' τ, A k τ) := by
  simpa only [ENNReal.ofReal_one, one_mul] using
    paperBlockOutput_levelSet_mul_le hF hweak hrow hA (by norm_num : (0 : ℝ) < 1)

/-- Existing real-valued weak bounds feed the extended-output formulation
without a new analytic estimate. -/
theorem hasExtendedWeakL1Bound_ofReal
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {A : ℝ} {F : X → ℝ}
    (hweak : HasWeakL1Bound μ A F) :
    HasExtendedWeakL1Bound μ A (fun x ↦ ENNReal.ofReal (F x)) := by
  refine ⟨hweak.1, ?_⟩
  intro a ha
  simpa only [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le] using hweak.2 a ha

theorem paperOuterWeight_one_le (k : ℕ) : 1 ≤ paperLog 1 ((k : ℝ) + 2) := by
  rw [paper_outer_weight_eq, ← Real.exp_le_exp,
    Real.exp_log (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)]
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- The weighted budget is an extended-real nonnegative sum, so an infinite
budget is represented honestly and no convergence assumptions are hidden in
the real-valued `tsum` convention. -/
noncomputable def paperBlockBudget {ι : Type*} (A : ℕ → ι → ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (paperLog 1 ((k : ℝ) + 2)) *
    ∑' τ, ENNReal.ofReal (A k τ)

/-- Finiteness of the explicit nonnegative budget proves both row
summability and outer weighted summability. -/
theorem summability_of_paperBlockBudget_ne_top
    {ι : Type*} {A : ℕ → ι → ℝ} (hA : ∀ k τ, 0 ≤ A k τ)
    (hbudget : paperBlockBudget A ≠ ∞) :
    (∀ k, Summable (A k)) ∧
      Summable (fun k : ℕ ↦ paperLog 1 ((k : ℝ) + 2) * ∑' τ, A k τ) := by
  have hrow (k : ℕ) : Summable (A k) := by
    have hterm : ENNReal.ofReal (paperLog 1 ((k : ℝ) + 2)) *
        (∑' τ, ENNReal.ofReal (A k τ)) ≠ ∞ :=
      ENNReal.ne_top_of_tsum_ne_top hbudget k
    have hrowfin : (∑' τ, ENNReal.ofReal (A k τ)) ≠ ∞ := by
      apply ne_top_of_le_ne_top hterm
      calc
        _ = 1 * ∑' τ, ENNReal.ofReal (A k τ) := (one_mul _).symm
        _ ≤ _ := mul_le_mul' (by
          simpa only [ENNReal.ofReal_one] using
            ENNReal.ofReal_le_ofReal (paperOuterWeight_one_le k)) le_rfl
    have hs := ENNReal.summable_toReal hrowfin
    simpa only [ENNReal.toReal_ofReal (hA k _)] using hs
  have hidentity : (∑' k : ℕ,
      ENNReal.ofReal (paperLog 1 ((k : ℝ) + 2) * ∑' τ, A k τ)) =
        paperBlockBudget A := by
    apply tsum_congr
    intro k
    rw [ENNReal.ofReal_mul (le_trans zero_le_one (paperOuterWeight_one_le k)),
      ENNReal.ofReal_tsum_of_nonneg (hA k) (hrow k)]
  refine ⟨hrow, ?_⟩
  have hs := ENNReal.summable_toReal (hidentity.symm ▸ hbudget)
  simpa only [ENNReal.toReal_ofReal (mul_nonneg
    (le_trans zero_le_one (paperOuterWeight_one_le _)) (tsum_nonneg (hA _)))] using hs

/-- The unrestricted paper-form estimate. All summability needed for Kalton
is derived from the budget when finite; an infinite right side is handled
directly. Only the individual block weak bounds are hypotheses. -/
theorem paperBlockOutput_levelSet_mul_le_budget
    {X ι : Type*} [MeasurableSpace X] [Countable ι] {μ : Measure X}
    {F : ℕ → ι → X → ℝ≥0∞} {A : ℕ → ι → ℝ}
    (hF : ∀ k τ, Measurable (F k τ))
    (hweak : ∀ k τ, HasExtendedWeakL1Bound μ (A k τ) (F k τ))
    {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal a * μ {x | ENNReal.ofReal a < paperBlockOutput F x} ≤
      24 * paperBlockBudget A := by
  by_cases hbudget : paperBlockBudget A = ∞
  · simp [hbudget]
  have hA : ∀ k τ, 0 ≤ A k τ := fun k τ ↦ (hweak k τ).1
  obtain ⟨hrow, hsum⟩ := summability_of_paperBlockBudget_ne_top hA hbudget
  apply (paperBlockOutput_levelSet_mul_le hF hweak hrow hsum ha).trans_eq
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 24),
    ENNReal.ofReal_tsum_of_nonneg (fun k ↦ mul_nonneg
      (le_trans zero_le_one (paperOuterWeight_one_le k)) (tsum_nonneg (hA k))) hsum]
  simp only [ENNReal.ofReal_ofNat]
  congr 1
  apply tsum_congr
  intro k
  rw [ENNReal.ofReal_mul (le_trans zero_le_one (paperOuterWeight_one_le k)),
    ENNReal.ofReal_tsum_of_nonneg (hA k) (hrow k)]

theorem paperBlockOutput_levelSet_one_le_budget
    {X ι : Type*} [MeasurableSpace X] [Countable ι] {μ : Measure X}
    {F : ℕ → ι → X → ℝ≥0∞} {A : ℕ → ι → ℝ}
    (hF : ∀ k τ, Measurable (F k τ))
    (hweak : ∀ k τ, HasExtendedWeakL1Bound μ (A k τ) (F k τ)) :
    μ {x | 1 < paperBlockOutput F x} ≤ 24 * paperBlockBudget A := by
  simpa only [ENNReal.ofReal_one, one_mul] using
    paperBlockOutput_levelSet_mul_le_budget hF hweak (by norm_num : (0 : ℝ) < 1)

/-- Direct interface for the real-valued nonnegative block outputs used in
the existing weak-L¹ estimates. No extra summability hypothesis is needed. -/
theorem realBlockOutput_levelSet_one_le_budget
    {X ι : Type*} [MeasurableSpace X] [Countable ι] {μ : Measure X}
    {F : ℕ → ι → X → ℝ} {A : ℕ → ι → ℝ}
    (hF : ∀ k τ, Measurable (F k τ))
    (hweak : ∀ k τ, HasWeakL1Bound μ (A k τ) (F k τ)) :
    μ {x | 1 < ∑' k : ℕ, ⨆ τ, ENNReal.ofReal (F k τ x)} ≤
      24 * paperBlockBudget A :=
  paperBlockOutput_levelSet_one_le_budget (fun k τ ↦ (hF k τ).ennreal_ofReal)
    (fun k τ ↦ hasExtendedWeakL1Bound_ofReal (hweak k τ))

/-- A finite distribution-function bound excludes infinite output on a set
of positive measure, without assuming output finiteness beforehand. -/
theorem HasExtendedWeakL1Bound.ae_lt_top
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {A : ℝ} {F : X → ℝ≥0∞}
    (hweak : HasExtendedWeakL1Bound μ A F) : ∀ᵐ x ∂μ, F x < ∞ := by
  have hn (n : ℕ) : (n : ℝ≥0∞) * μ {x | F x = ∞} ≤ ENNReal.ofReal A := by
    by_cases hn : n = 0
    · simp [hn]
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    calc
      _ ≤ ENNReal.ofReal (n : ℝ) * μ {x | ENNReal.ofReal (n : ℝ) < F x} := by
        simp only [ENNReal.ofReal_natCast]
        apply mul_le_mul' le_rfl
        apply measure_mono
        intro x hx
        change F x = ∞ at hx
        change (n : ℝ≥0∞) < F x
        rw [hx]
        exact ENNReal.natCast_lt_top n
      _ ≤ _ := hweak.2 n hnpos
  have hsup : ∞ * μ {x | F x = ∞} ≤ ENNReal.ofReal A := by
    have hsup' : (⨆ n : ℕ, (n : ℝ≥0∞)) * μ {x | F x = ∞} ≤ ENNReal.ofReal A := by
      rw [ENNReal.iSup_mul]
      exact iSup_le hn
    simpa only [ENNReal.iSup_natCast] using hsup'
  have hzero : μ {x | F x = ∞} = 0 := by
    by_contra hne
    rw [ENNReal.top_mul hne] at hsup
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hsup)
  apply ae_iff.mpr
  simpa only [not_lt_top_iff] using hzero

theorem ae_paperBlockOutput_lt_top
    {X ι : Type*} [MeasurableSpace X] [Countable ι] {μ : Measure X}
    {F : ℕ → ι → X → ℝ≥0∞} {A : ℕ → ι → ℝ}
    (hF : ∀ k τ, Measurable (F k τ))
    (hweak : ∀ k τ, HasExtendedWeakL1Bound μ (A k τ) (F k τ))
    (hbudget : paperBlockBudget A ≠ ∞) :
    ∀ᵐ x ∂μ, paperBlockOutput F x < ∞ := by
  obtain ⟨hrow, hsum⟩ := summability_of_paperBlockBudget_ne_top
    (fun k τ ↦ (hweak k τ).1) hbudget
  exact (hasExtendedWeakL1Bound_paperBlockOutput hF hweak hrow hsum).ae_lt_top

/-- In particular, the real-valued magnitude-level series is genuinely
summable almost everywhere; this is a conclusion, not an input assumption. -/
theorem ae_summable_blockSupremum_toReal
    {X ι : Type*} [MeasurableSpace X] [Countable ι] {μ : Measure X}
    {F : ℕ → ι → X → ℝ≥0∞} {A : ℕ → ι → ℝ}
    (hF : ∀ k τ, Measurable (F k τ))
    (hweak : ∀ k τ, HasExtendedWeakL1Bound μ (A k τ) (F k τ))
    (hbudget : paperBlockBudget A ≠ ∞) :
    ∀ᵐ x ∂μ, Summable (fun k ↦ (blockSupremum (F k) x).toReal) := by
  filter_upwards [ae_paperBlockOutput_lt_top hF hweak hbudget] with x hx
  exact ENNReal.summable_toReal hx.ne


end KaltonPaperApplication
end QuadraticCarleson
