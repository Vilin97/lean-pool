/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPhysicalTailPrefix

/-!
# The genuine pruned physical-truncation maximal operator

Physical length tails are compared to the regenerated prefixes of the
same pruned family. The factor two comes from subtracting two prefixes.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyGenerationLayers

attribute [local instance] Classical.propDecidable

noncomputable def badLengthTailAction
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (ell : ℤ) (x : ℝ) : ℂ :=
  ∑ I ∈ N, if (2 : ℝ) ^ ell ≤ I.length then krauseLaceyLocalizedPiece 1 (scale I) I
    (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x else 0

noncomputable def badLengthTailMaximal
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (x : ℝ) : ℝ :=
  ⨆ ell : ℤ, ‖badLengthTailAction S f I₀ k₀ s scale N ell x‖

theorem norm_badLengthTailAction_le_prefix
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale)
    (ell : ℤ) (x : ℝ) :
    ‖badLengthTailAction S f I₀ k₀ s scale N ell x‖ ≤
      2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale N N.card x := by
  have hNS := hN.trans (nonstandardIntervals_subset S f I₀ k₀ s scale)
  apply norm_lengthTail_le_two_generationPrefixNormMax N
    (fun I hI J hJ hne ↦ hlam (hNS hI) (hNS hJ) hne) _ ((2 : ℝ) ^ ell) x
  intro I hI hxI
  exact krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 (scale I) I _
    (Finset.mem_filter.mp (hN hI)).2.1 hxI

theorem badLengthTailMaximal_le_prefix
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (x : ℝ) :
    badLengthTailMaximal S f I₀ k₀ s scale N x ≤
      2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale N N.card x :=
  ciSup_le fun ell ↦ norm_badLengthTailAction_le_prefix f I₀ k₀ s scale hlam N hN ell x

theorem badLengthTailMaximal_nonneg
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (x : ℝ) :
    0 ≤ badLengthTailMaximal S f I₀ k₀ s scale N x := by
  have hb : BddAbove (Set.range (fun ell : ℤ ↦
      ‖badLengthTailAction S f I₀ k₀ s scale N ell x‖)) :=
    ⟨2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale N N.card x, by
      rintro _ ⟨ell, rfl⟩
      exact norm_badLengthTailAction_le_prefix f I₀ k₀ s scale hlam N hN ell x⟩
  exact (norm_nonneg _).trans (le_ciSup hb (0 : ℤ))

theorem aemeasurable_badLengthTailMaximal
    (S : Finset RealInterval) {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ) (N : Finset RealInterval) :
    AEMeasurable (badLengthTailMaximal S f I₀ k₀ s scale N) volume := by
  apply AEMeasurable.iSup
  intro ell
  apply AEStronglyMeasurable.aemeasurable
  apply AEStronglyMeasurable.norm
  apply Finset.aestronglyMeasurable_fun_sum
  intro I hI
  by_cases he : (2 : ℝ) ^ ell ≤ I.length
  · simpa only [ite_eq_left he] using
      (memLp_localizedPiece_of_integrable (scale I) I
        (integrable_badScaleInput S hf I₀ k₀ (scale I + 2 - s))).aestronglyMeasurable
  · simp only [ite_eq_right he]
    exact aestronglyMeasurable_const

theorem badLengthTailMaximal_eq_pruned_of_lowOverlap
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval)
    (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (M : ℕ) (x : ℝ)
    (hx : overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x ≤ M) :
    badLengthTailMaximal S f I₀ k₀ s scale N x =
      badLengthTailMaximal S f I₀ k₀ s scale
        (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) x := by
  apply iSup_congr
  intro ell
  congr 1
  simpa only [badLengthTailAction, ite_mul, one_mul, zero_mul] using
    sum_weighted_localizedBadPiece_eq_pruned_of_lowOverlap S f I₀ k₀ s scale N hN M
      (fun I ↦ if (2 : ℝ) ^ ell ≤ I.length then 1 else 0) x hx

/-- The actual physical maximal operator of the concretely pruned family
inherits the proved prefix estimate with the precise factor two. -/
theorem eLpNorm_pruned_badLengthTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (M : ℕ) :
    eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale
      (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M)) 2 volume ≤
      ENNReal.ofReal (2 * ((Nat.log2 M + 1 : ℝ) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s))) := by
  let P := overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M
  have hP : P ⊆ nonstandardIntervals S f I₀ k₀ s scale :=
    (overlapPrunedFamily_subset _ M).trans
      ((activeBadIntervals_subset S f I₀ k₀ s scale N).trans hN)
  have hmono : eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale P) 2 volume ≤
      eLpNorm (fun x ↦ (2 : ℝ) • badSubcollectionPrefixMaximal S f I₀ k₀ s scale P P.card x)
        2 volume := by
    apply eLpNorm_mono
      (aemeasurable_badLengthTailMaximal S hf I₀ k₀ s scale P).aestronglyMeasurable
    intro x
    rw [Real.norm_of_nonneg (badLengthTailMaximal_nonneg f I₀ k₀ s scale hlam P hP x),
      smul_eq_mul, Real.norm_of_nonneg (mul_nonneg (by norm_num)
        (badSubcollectionPrefixMaximal_nonneg S f I₀ k₀ s scale P P.card x))]
    exact badLengthTailMaximal_le_prefix f I₀ k₀ s scale hlam P hP x
  apply hmono.trans
  change eLpNorm ((2 : ℝ) • badSubcollectionPrefixMaximal S f I₀ k₀ s scale P P.card)
    2 volume ≤ _
  rw [eLpNorm_const_smul, show ‖(2 : ℝ)‖ₑ = ENNReal.ofReal 2 by
      exact Real.enorm_of_nonneg (by norm_num),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_right (eLpNorm_prunedActivePrefixMaximal_le hf I₀ k₀ s hk₀ hs scale
    hlam hparent hsub N hN P.card M) _


end KrauseLaceyBadScale
end QuadraticCarleson
