/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleOperator

/-!
# The genuine frozen block input belongs to the paper's test domain

Every stopping cell meets the support of the original input and has length
at most the data-dependent root length. Thus all stopping cells lie in one
bounded enlargement of a compact set supporting the original input. Exact
disjointness also gives a pointwise `2 A_k` bound for any frozen scale block,
with no factor depending on its number of scales.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace LacunaryFrozenInputL0

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CalderonZygmundLevelAtoms CanonicalScaleAtoms
open PositiveEndpointOptimization LacunaryMiddleRange LacunaryMiddleOperator


/-- A selected cell cannot be disjoint from the actual support of the
original input: otherwise its norm average would be zero. -/
theorem stoppingCell_exists_mem_support {f : ℝ → ℂ} (c : stoppingCell f) :
    ∃ y : ℝ, y ∈ c.1.interval (rootLength f) ∧ f y ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz : (∫ y in c.1.interval (rootLength f), ‖f y‖) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun y hy ↦ by rw [hn y hy, norm_zero]
  have hc := stoppingCell_lower_average c
  rw [DyadicCell.normAverage, dyadicNormAverage_eq rootLength_pos] at hc
  change 1 < (∫ y in c.1.interval (rootLength f), ‖f y‖) /
    dyadicLength (rootLength f) c.1.depth at hc
  rw [hz, zero_div] at hc
  exact (by norm_num : ¬ (1 : ℝ) < 0) hc

theorem stoppingCell_length_le_rootLength {f : ℝ → ℂ} (c : stoppingCell f) :
    dyadicLength (rootLength f) c.1.depth ≤ rootLength f := by
  unfold dyadicLength
  exact div_le_self rootLength_pos.le (one_le_pow₀ (by norm_num))

/-- A concrete bounded enlargement contains the entire canonical stopping
union, not merely almost every point of it. -/
theorem stoppingBadUnion_subset_Icc_of_support_subset
    {f : ℝ → ℂ} {R : ℝ} (hR : ∀ y, f y ≠ 0 → |y| ≤ R) :
    stoppingBadUnion f ⊆ Icc (-R - rootLength f) (R + rootLength f) := by
  intro x hx
  obtain ⟨c, hc⟩ := mem_iUnion.mp hx
  obtain ⟨y, hy, hfy⟩ := stoppingCell_exists_mem_support c
  have hyR := abs_le.mp (hR y hfy)
  have hlen := stoppingCell_length_le_rootLength c
  change (c.1.index : ℝ) * dyadicLength (rootLength f) c.1.depth ≤ x ∧
    x < ((c.1.index : ℝ) + 1) * dyadicLength (rootLength f) c.1.depth at hc
  change (c.1.index : ℝ) * dyadicLength (rootLength f) c.1.depth ≤ y ∧
    y < ((c.1.index : ℝ) + 1) * dyadicLength (rootLength f) c.1.depth at hy
  constructor <;> nlinarith

/-- Compact support of the original input confines every function supported
in its canonical stopping union to a common compact interval. -/
theorem hasCompactSupport_of_support_subset_stoppingBadUnion
    (f : L0Infinity) {g : ℝ → ℂ}
    (hg : Function.support g ⊆ stoppingBadUnion f) : HasCompactSupport g := by
  obtain ⟨R, hR⟩ := f.hasCompactSupport_toFun.isBounded.exists_norm_le
  have hfR : ∀ y, f y ≠ 0 → |y| ≤ R := by
    intro y hy
    simpa only [Real.norm_eq_abs] using hR y (subset_tsupport f hy)
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (hg.trans (stoppingBadUnion_subset_Icc_of_support_subset hfR))

theorem norm_canonicalLevelBadPart_le_two_mul
    {A : ℕ → ℝ} (f : ℝ → ℂ) {k : ℕ} (hAk : 0 ≤ A k) (x : ℝ) :
    ‖canonicalLevelBadPart A f k x‖ ≤ 2 * A k := by
  by_cases hx : x ∈ stoppingBadUnion f
  · obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    rw [canonicalLevelBadPart_eq_atom_of_mem A c hc]
    exact norm_levelAtom_le_two_mul hAk (stoppingLength_pos c) x
  · rw [canonicalLevelBadPart_eq_zero_of_notMem A hx, norm_zero]
    positivity

/-- A finite frozen block either keeps the single active spatial scale or
removes it. This uses the exact canonical disjointness, not a triangle loss. -/
theorem frozenBlockInput_eq_zero_or_canonicalLevelBadPart
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (τ : ℤ) (x : ℝ) :
    frozenBlockInput A f k B c τ x = 0 ∨
      frozenBlockInput A f k B c τ x = canonicalLevelBadPart A f k x := by
  classical
  obtain ⟨j₀, hj₀⟩ := stoppingScaleLevelBadPart_eq_single_scale A f k x
  unfold frozenBlockInput
  simp_rw [hj₀]
  by_cases hj : j₀ ∈ R B c τ
  · right
    simp [hj]
  · left
    simp [hj]

theorem norm_frozenBlockInput_le_two_mul
    {A : ℕ → ℝ} (f : ℝ → ℂ) {k : ℕ} (hAk : 0 ≤ A k)
    (B c : ℕ) (τ : ℤ) (x : ℝ) :
    ‖frozenBlockInput A f k B c τ x‖ ≤ 2 * A k := by
  rcases frozenBlockInput_eq_zero_or_canonicalLevelBadPart A f k B c τ x with h | h
  · rw [h, norm_zero]
    positivity
  · rw [h]
    exact norm_canonicalLevelBadPart_le_two_mul f hAk x

theorem support_frozenBlockInput_subset_stoppingBadUnion
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (τ : ℤ) :
    Function.support (frozenBlockInput A f k B c τ) ⊆ stoppingBadUnion f := by
  intro x hx
  by_contra hnot
  apply hx
  unfold frozenBlockInput
  simp only [stoppingScaleLevelBadPart_eq_zero_of_notMem A hnot, Finset.sum_const_zero]

theorem hasCompactSupport_frozenBlockInput
    (A : ℕ → ℝ) (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    HasCompactSupport (frozenBlockInput A f k B c τ) :=
  hasCompactSupport_of_support_subset_stoppingBadUnion f
    (support_frozenBlockInput_subset_stoppingBadUnion A f k B c τ)

/-- The actual frozen input for the paper's lacunary magnitude amplitudes,
packaged in the domain of the finite-modulation sparse theorem. No condition
on the block size or auxiliary geometric parameter is needed. -/
noncomputable def frozenBlockInputL0
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) : L0Infinity where
  toFun := frozenBlockInput lacunaryAmplitude f k B c τ
  measurable_toFun := measurable_frozenBlockInput f.measurable_toFun k B c τ
  bounded_toFun := ⟨2 * lacunaryAmplitude k,
    norm_frozenBlockInput_le_two_mul f (lacunaryAmplitude_pos k).le B c τ⟩
  hasCompactSupport_toFun := hasCompactSupport_frozenBlockInput lacunaryAmplitude f k B c τ

@[simp] theorem frozenBlockInputL0_apply
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) (x : ℝ) :
    frozenBlockInputL0 f k B c τ x = frozenBlockInput lacunaryAmplitude f k B c τ x := rfl

theorem coe_frozenBlockInputL0
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    (frozenBlockInputL0 f k B c τ : ℝ → ℂ) =
      frozenBlockInput lacunaryAmplitude f k B c τ := rfl

theorem measurable_frozenBlockInputL0
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    Measurable (frozenBlockInputL0 f k B c τ : ℝ → ℂ) :=
  (frozenBlockInputL0 f k B c τ).measurable_toFun

theorem integrable_frozenBlockInputL0
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    Integrable (frozenBlockInputL0 f k B c τ : ℝ → ℂ) :=
  (frozenBlockInputL0 f k B c τ).integrable

theorem norm_frozenBlockInputL0_le
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) (x : ℝ) :
    ‖frozenBlockInputL0 f k B c τ x‖ ≤ 2 * lacunaryAmplitude k :=
  norm_frozenBlockInput_le_two_mul f (lacunaryAmplitude_pos k).le B c τ x

/-- The wrapper preserves the exact `L¹` mass used by the block budget. -/
theorem lintegral_enorm_frozenBlockInputL0_eq
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    (∫⁻ x, ‖frozenBlockInputL0 f k B c τ x‖ₑ) =
      frozenBlockInputL1Mass lacunaryAmplitude f k B c τ := rfl

theorem eLpNorm_one_frozenBlockInputL0_eq
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    eLpNorm (frozenBlockInputL0 f k B c τ : ℝ → ℂ) 1 volume =
      frozenBlockInputL1Mass lacunaryAmplitude f k B c τ := by
  rw [eLpNorm_one_eq_lintegral_enorm
    (frozenBlockInputL0 f k B c τ).measurable_toFun.aestronglyMeasurable]
  exact lintegral_enorm_frozenBlockInputL0_eq f k B c τ

theorem integral_norm_frozenBlockInputL0_eq
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    (∫ x, ‖frozenBlockInputL0 f k B c τ x‖) =
      (frozenBlockInputL1Mass lacunaryAmplitude f k B c τ).toReal := by
  rw [integral_norm_eq_lintegral_enorm
    (frozenBlockInputL0 f k B c τ).measurable_toFun.aestronglyMeasurable]
  rfl

theorem ofReal_integral_norm_frozenBlockInputL0_eq
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    ENNReal.ofReal (∫ x, ‖frozenBlockInputL0 f k B c τ x‖) =
      frozenBlockInputL1Mass lacunaryAmplitude f k B c τ :=
  ofReal_integral_norm_eq_lintegral_enorm (frozenBlockInputL0 f k B c τ).integrable

theorem frozenBlockInputL1Mass_lt_top
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    frozenBlockInputL1Mass lacunaryAmplitude f k B c τ < ∞ :=
  (frozenBlockInputL0 f k B c τ).integrable.hasFiniteIntegral

/-- The finite maximally truncated operator used in the sparse application
acts on exactly this wrapper, with pointwise equality and no a.e. transport. -/
theorem frozenBlockHilbertMaxEnorm_eq_wrapper
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) (x : ℝ) :
    frozenBlockHilbertMaxEnorm lacunaryAmplitude f k B c τ x =
      (Q B τ).sup fun m ↦ quadraticHilbertMaximalTruncation (dyadicModulation m)
        (frozenBlockInputL0 f k B c τ) x := rfl


end LacunaryFrozenInputL0
end QuadraticCarleson
