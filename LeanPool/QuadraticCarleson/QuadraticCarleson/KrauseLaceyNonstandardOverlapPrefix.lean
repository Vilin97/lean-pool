/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardSubcollectionPrefix
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyGenerationOverlap

/-!
# Actual overlap bounds replace cardinality in the nonstandard prefix estimate

The geometric hypothesis below is the literal a.e. interval overlap count.
The transition from that count to a complete maximal-prefix bound is proved,
including exact truncation of all higher generations. This is a composable
consequence, not an assertion that the source's analytic pruning is finished.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyGenerationLayers


theorem badSubcollectionPrefixMaximal_nonneg
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (M : ℕ) (x : ℝ) :
    0 ≤ badSubcollectionPrefixMaximal S f I₀ k₀ s scale N M x := by
  have h := le_ciSup (Set.finite_range
    (fun n : Fin (M + 1) ↦ ‖∑ i ∈ Finset.range n.val,
      krauseLaceyCollectionAction (generation N i) scale
        (fun I ↦ badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖)).bddAbove
    (0 : Fin (M + 1))
  simpa [badSubcollectionPrefixMaximal] using h

/-- An actual a.e. overlap bound controls every finite generation prefix,
not merely the first `M` prefixes. -/
theorem badSubcollectionPrefixMaximal_le_of_ae_overlapCount_le
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (L M : ℕ)
    (hbound : ∀ᵐ x ∂volume, overlapCount N x ≤ M) (x : ℝ) :
    badSubcollectionPrefixMaximal S f I₀ k₀ s scale N L x ≤
      badSubcollectionPrefixMaximal S f I₀ k₀ s scale N M x := by
  let v (i : ℕ) := krauseLaceyCollectionAction (generation N i) scale
    (fun I ↦ badScaleInput S f I₀ k₀ (scale I + 2 - s)) x
  have hv (i : ℕ) (hi : M ≤ i) : v i = 0 := by
    simp only [v, krauseLaceyCollectionAction,
      generation_eq_empty_of_ae_overlapCount_le N hbound hi, Finset.sum_empty]
  change (⨆ n : Fin (L + 1), ‖∑ i ∈ Finset.range n.val, v i‖) ≤
    ⨆ n : Fin (M + 1), ‖∑ i ∈ Finset.range n.val, v i‖
  apply ciSup_le
  intro n
  rw [sum_range_eq_sum_range_min_of_eq_zero v M n.val hv]
  exact le_ciSup (Set.finite_range
    (fun n : Fin (M + 1) ↦ ‖∑ i ∈ Finset.range n.val, v i‖)).bddAbove
    ⟨min n.val M, by omega⟩

/-- The full actual subcollection maximal prefix has the RM bound with
the geometric overlap cutoff, uniformly in the number of intervals. -/
theorem eLpNorm_badSubcollectionPrefixMaximal_le_of_ae_overlapCount_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (L M : ℕ)
    (hbound : ∀ᵐ x ∂volume, overlapCount N x ≤ M) :
    eLpNorm (badSubcollectionPrefixMaximal S f I₀ k₀ s scale N L) 2 volume ≤
      ENNReal.ofReal ((Nat.log2 M + 1 : ℝ) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  apply le_trans _ (eLpNorm_badSubcollectionPrefixMaximal_le hf I₀ k₀ s hk₀ hs scale
    hlam hparent hsub N hN M)
  apply eLpNorm_mono
  intro x
  rw [Real.norm_of_nonneg (badSubcollectionPrefixMaximal_nonneg S f I₀ k₀ s scale N L x),
    Real.norm_of_nonneg (badSubcollectionPrefixMaximal_nonneg S f I₀ k₀ s scale N M x)]
  exact badSubcollectionPrefixMaximal_le_of_ae_overlapCount_le S f I₀ k₀ s scale N L M hbound x


end KrauseLaceyBadScale
end QuadraticCarleson
