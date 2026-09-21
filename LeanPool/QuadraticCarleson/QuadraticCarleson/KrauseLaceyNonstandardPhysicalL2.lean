/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyRemovedOperatorL2

/-!
# Unrestricted nonstandard physical maximal `L²` bound

The active family splits exactly into retained and removed intervals.
The retained estimate and the genuine exponentially small removed
estimate are combined here, so no overlap or exceptional-set hypothesis
remains on the actual nonstandard maximal operator.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyGenerationLayers

attribute [local instance] Classical.propDecidable

noncomputable def badRemovedEnergyBudget (f : ℝ → ℂ) (I₀ : RealInterval) (s : ℕ) : ℝ :=
  badPieceUniformBound f I₀ ^ 2 *
    (2 * (1 + (2 : ℝ) ^ (s : ℤ)) ^ 2 * ((1 / 2 : ℝ) ^ (8 * (s + 1)) * I₀.length))

theorem badRemovedEnergyBudget_nonneg (f : ℝ → ℂ) (I₀ : RealInterval) (s : ℕ) :
    0 ≤ badRemovedEnergyBudget f I₀ s := by
  have hI := I₀.length_pos
  unfold badRemovedEnergyBudget
  positivity

theorem ofReal_badRemovedEnergyBudget (f : ℝ → ℂ) (I₀ : RealInterval) (s : ℕ) :
    ENNReal.ofReal (badRemovedEnergyBudget f I₀ s) =
      ENNReal.ofReal (badPieceUniformBound f I₀) ^ 2 *
        (2 * ENNReal.ofReal (1 + (2 : ℝ) ^ (s : ℤ)) ^ 2 *
          ((1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal I₀.length)) := by
  have hC := badPieceUniformBound_nonneg f I₀
  simp (disch := positivity) only [badRemovedEnergyBudget, ENNReal.ofReal_mul,
    ENNReal.ofReal_pow, ENNReal.ofReal_div_of_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

theorem eLpNorm_removed_badLengthTailMaximal_le_sqrt
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) :
    eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale
      (activeBadIntervals S f I₀ k₀ s scale N \
        overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N)
          (activeExponentialCutoff s))) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (badRemovedEnergyBudget f I₀ s)) := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  rw [ENNReal.rpow_two, ENNReal.rpow_two,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,
    Real.sq_sqrt (badRemovedEnergyBudget_nonneg f I₀ s), ofReal_badRemovedEnergyBudget]
  exact eLpNorm_removed_badLengthTailMaximal_sq_le hf I₀ k₀ s scale hlam hsub N hN

theorem badLengthTailAction_eq_pruned_add_removed
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval)
    (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (M : ℕ) (ell : ℤ) (x : ℝ) :
    badLengthTailAction S f I₀ k₀ s scale N ell x =
      badLengthTailAction S f I₀ k₀ s scale
        (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) ell x +
      badLengthTailAction S f I₀ k₀ s scale
        (activeBadIntervals S f I₀ k₀ s scale N \
          overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) ell x := by
  unfold badLengthTailAction
  rw [sum_lengthTail_localizedBadPiece_eq_active S f I₀ k₀ s scale N ell x]
  rw [← Finset.sum_sdiff (overlapPrunedFamily_subset _ M)]
  ring

theorem badLengthTailMaximal_le_pruned_add_removed
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (M : ℕ) (x : ℝ) :
    badLengthTailMaximal S f I₀ k₀ s scale N x ≤
      badLengthTailMaximal S f I₀ k₀ s scale
        (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) x +
      badLengthTailMaximal S f I₀ k₀ s scale
        (activeBadIntervals S f I₀ k₀ s scale N \
          overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) x := by
  have hbound (Q : Finset RealInterval)
      (hQ : Q ⊆ nonstandardIntervals S f I₀ k₀ s scale) :
      BddAbove (Set.range fun ell : ℤ ↦ ‖badLengthTailAction S f I₀ k₀ s scale Q ell x‖) := by
    refine ⟨2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale Q Q.card x, ?_⟩
    rintro _ ⟨ell, rfl⟩
    exact norm_badLengthTailAction_le_prefix f I₀ k₀ s scale hlam Q hQ ell x
  have hA := (activeBadIntervals_subset S f I₀ k₀ s scale N).trans hN
  apply ciSup_le
  intro ell
  rw [badLengthTailAction_eq_pruned_add_removed S f I₀ k₀ s scale N hN M ell x]
  apply (norm_add_le _ _).trans
  exact add_le_add (le_ciSup (hbound _ ((overlapPrunedFamily_subset _ M).trans hA)) ell)
    (le_ciSup (hbound _ (Finset.sdiff_subset.trans hA)) ell)

/-- The actual unrestricted finite nonstandard physical maximal operator
now has its complete quantitative `L²` estimate. The first term decays
like `(s+1)2^(-s/2)` and the second like `2^(-3s)`, with explicit constants. -/
theorem eLpNorm_nonstandard_badLengthTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) :
    eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale N) 2 volume ≤
      ENNReal.ofReal ((4 * (s : ℝ) + 12) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s) +
          Real.sqrt (badRemovedEnergyBudget f I₀ s)) := by
  let P := overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N)
    (activeExponentialCutoff s)
  let R := activeBadIntervals S f I₀ k₀ s scale N \ P
  have hA := (activeBadIntervals_subset S f I₀ k₀ s scale N).trans hN
  have hP : P ⊆ nonstandardIntervals S f I₀ k₀ s scale :=
    (overlapPrunedFamily_subset _ _).trans hA
  have hR : R ⊆ nonstandardIntervals S f I₀ k₀ s scale := Finset.sdiff_subset.trans hA
  calc
    _ ≤ eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale P +
        badLengthTailMaximal S f I₀ k₀ s scale R) 2 volume := by
      apply eLpNorm_mono
      intro x
      simp only [Pi.add_apply]
      rw [Real.norm_of_nonneg (badLengthTailMaximal_nonneg f I₀ k₀ s scale hlam N hN x),
        Real.norm_of_nonneg (add_nonneg
          (badLengthTailMaximal_nonneg f I₀ k₀ s scale hlam P hP x)
          (badLengthTailMaximal_nonneg f I₀ k₀ s scale hlam R hR x))]
      exact badLengthTailMaximal_le_pruned_add_removed f I₀ k₀ s scale hlam N hN _ x
    _ ≤ eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale P) 2 volume +
        eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale R) 2 volume :=
      eLpNorm_add_le (aemeasurable_badLengthTailMaximal S hf I₀ k₀ s scale P).aestronglyMeasurable
        (aemeasurable_badLengthTailMaximal S hf I₀ k₀ s scale R).aestronglyMeasurable (by norm_num)
    _ ≤ ENNReal.ofReal ((4 * (s : ℝ) + 12) * Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) +
        ENNReal.ofReal (Real.sqrt (badRemovedEnergyBudget f I₀ s)) :=
      add_le_add (eLpNorm_exponentiallyPruned_badLengthTailMaximal_le hf I₀ k₀ s hk₀
        scale hlam hparent hsub N hN)
        (eLpNorm_removed_badLengthTailMaximal_le_sqrt hf I₀ k₀ s scale hlam hsub N hN)
    _ = _ := (ENNReal.ofReal_add (by positivity) (Real.sqrt_nonneg _)).symm


end KrauseLaceyBadScale
end QuadraticCarleson
