/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyRemovedCarlesonMass
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPrunedPhysicalMaximal

/-!
# Actual active-family pruning at an exponential cutoff

The source cutoff has size `O((s+1)2^s)`. At the explicit choice below
the exceptional measure is at most `2^(-8(s+1))` times the root length;
the total discarded interval length has the corresponding exponential
bound. The retained genuine physical maximal operator has the proved
linear-in-`s` Rademacher--Menshov loss.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyGenerationLayers

attribute [local instance] Classical.propDecidable

def activeOverlapBlock (s : ℕ) : ℕ := 2 * (1 + 2 ^ s)

def activeExponentialCutoff (s : ℕ) : ℕ := 16 * activeOverlapCutoff s

theorem activeOverlapBlock_pred_add_one (s : ℕ) :
    activeOverlapBlock s - 1 + 1 = activeOverlapBlock s := by
  apply Nat.sub_add_cancel
  have hpos : 0 < activeOverlapBlock s := by unfold activeOverlapBlock; positivity
  omega

theorem activeExponentialCutoff_eq_blocks (s : ℕ) :
    activeExponentialCutoff s = 8 * (s + 1) * (activeOverlapBlock s - 1 + 1) := by
  rw [activeOverlapBlock_pred_add_one]
  unfold activeExponentialCutoff activeOverlapCutoff activeOverlapBlock
  ring

theorem activeOverlapBlock_real_bound (s : ℕ) :
    2 * (1 + (2 : ℝ) ^ (s : ℤ)) ≤ (activeOverlapBlock s - 1 : ℕ) + 1 := by
  have he : ((activeOverlapBlock s - 1 : ℕ) : ℝ) + 1 =
      (2 : ℝ) * (1 + (2 : ℝ) ^ s) := by
    rw [← Nat.cast_add_one, activeOverlapBlock_pred_add_one]
    simp only [activeOverlapBlock, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one, Nat.cast_pow]
  simpa only [zpow_natCast] using he.ge

theorem volume_active_overlap_blocks_le_half_pow
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ) (s t : ℕ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    volume {x | t * activeOverlapBlock s <
      overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x} ≤
      (1 / 2 : ℝ≥0∞) ^ t * ENNReal.ofReal K.length := by
  have hAS := (activeBadIntervals_subset S f I₀ k₀ s scale N).trans
    (hN.trans (nonstandardIntervals_subset S f I₀ k₀ s scale))
  simpa only [activeOverlapBlock_pred_add_one] using
    volume_overlap_blocks_le_half_pow t (activeBadIntervals S f I₀ k₀ s scale N) K
      (activeOverlapBlock s - 1) (1 + (2 : ℝ) ^ (s : ℤ))
      (activeOverlapBlock_real_bound s)
      (fun I hI J hJ hne ↦ hlam (hAS hI) (hAS hJ) hne)
      (fun I hI ↦ hsub I (activeBadIntervals_subset S f I₀ k₀ s scale N hI))
      (sum_activeBadIntervals_descendants_length_le f I₀ k₀ s scale hlam N hN)

theorem volume_active_exponentialCutoff_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    volume {x | activeExponentialCutoff s <
      overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x} ≤
      (1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal K.length := by
  rw [activeExponentialCutoff_eq_blocks, activeOverlapBlock_pred_add_one]
  exact volume_active_overlap_blocks_le_half_pow f I₀ k₀ s (8 * (s + 1)) scale
    hlam N hN K hsub

theorem ofReal_sum_active_removed_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    ENNReal.ofReal (∑ I ∈ activeBadIntervals S f I₀ k₀ s scale N \
      overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) (activeExponentialCutoff s),
      I.length) ≤
      ENNReal.ofReal (1 + (2 : ℝ) ^ (s : ℤ)) *
        ((1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal K.length) := by
  have hAS := (activeBadIntervals_subset S f I₀ k₀ s scale N).trans
    (hN.trans (nonstandardIntervals_subset S f I₀ k₀ s scale))
  apply (ofReal_sum_removed_length_le_carleson_mul_highOverlap
    (activeBadIntervals S f I₀ k₀ s scale N) (activeExponentialCutoff s)
    (1 + (2 : ℝ) ^ (s : ℤ)) (by positivity)
    (fun I hI J hJ hne ↦ hlam (hAS hI) (hAS hJ) hne)
    (sum_activeBadIntervals_descendants_length_le f I₀ k₀ s scale hlam N hN)).trans
  exact mul_le_mul_right
    (volume_active_exponentialCutoff_le f I₀ k₀ s scale hlam N hN K hsub) _

theorem activeExponentialCutoff_le (s : ℕ) :
    activeExponentialCutoff s ≤ 32 * (s + 1) * 2 ^ s := by
  have h := Nat.mul_le_mul_left 16 (activeOverlapCutoff_le s)
  calc
    _ ≤ 16 * (2 * (s + 1) * 2 ^ s) := h
    _ = _ := by ring

theorem log2_activeExponentialCutoff_le (s : ℕ) :
    Nat.log2 (activeExponentialCutoff s) ≤ 2 * s + 5 := by
  have hp : activeExponentialCutoff s ≤ (2 : ℕ) ^ (2 * s + 5) := by
    calc
      _ ≤ 16 * 2 ^ (2 * s + 1) := Nat.mul_le_mul_left 16 (activeOverlapCutoff_le_pow s)
      _ = _ := by
        rw [show 2 * s + 5 = 4 + (2 * s + 1) by omega,
          pow_add (2 : ℕ) 4 (2 * s + 1)]
        norm_num
  have h := Nat.log_mono_right (b := 2) hp
  simpa only [Nat.log2_eq_log_two, Nat.log_pow (by norm_num : 1 < (2 : ℕ))] using h

theorem eLpNorm_exponentiallyPruned_badLengthTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) :
    eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale
      (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N)
        (activeExponentialCutoff s))) 2 volume ≤
      ENNReal.ofReal ((4 * (s : ℝ) + 12) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  apply (eLpNorm_pruned_badLengthTailMaximal_le hf I₀ k₀ s hk₀ (by omega) scale
    hlam hparent hsub N hN (activeExponentialCutoff s)).trans
  apply ENNReal.ofReal_le_ofReal
  have hr : (Nat.log2 (activeExponentialCutoff s) : ℝ) ≤ 2 * (s : ℝ) + 5 := by
    exact_mod_cast log2_activeExponentialCutoff_le s
  nlinarith [Real.sqrt_nonneg (nonstandardSignedEnergyBudget f I₀ s)]


end KrauseLaceyBadScale
end QuadraticCarleson
