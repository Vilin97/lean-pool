/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module

public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyScalarNearSignedSum
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardSourceMaximal

/-!
# Physical-suffix maximal bounds for the scalar near-energy branch

The actual functions, generation prefixes, active-family restriction,
overlap pruning, and source-oriented physical tails are those already
defined in the project. This module proves their estimates for
`KrauseLaceyScalarNear.intervals`, which is exactly the energy classifier's
near family. The signed-sum input is supplied by the scalar diagonal
estimate proved in `KrauseLaceyScalarNearSignedSum`.

The geometric and measure-theoretic estimates use the shared grouped-scale
geometry. The classifier-specific signed-sum proof remains separate; both
branches discharge their own energy bound without assuming a Carleson budget.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyScalarNear

open KrauseLaceyBadScale KrauseLaceyStoppingExtraction
  KrauseLaceyGenerationLayers KrauseLaceyRademacherMenshov

attribute [local instance] Classical.propDecidable

theorem hasSignedSumSquareBound_badSubcollectionGenerations
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (M : ℕ) :
    HasSignedSumSquareBound M (badSubcollectionGenerationLp S f hf I₀ k₀ s scale N)
      (nonstandardSignedEnergyBudget f I₀ s) := by
  intro c hc
  change ‖∑ n ∈ Finset.range M, c n • ∑ I ∈ generation N n,
    badPieceLp S f hf I₀ k₀ s scale I‖ ^ 2 ≤ _
  rw [sum_smul_generations_range_eq]
  apply norm_signed_badPieceLp_sq_le hf I₀ k₀ s (by omega) scale hlam hparent hsub N hN _ _ _
  · intro I hI
    have hi := (Finset.mem_filter.mp (hN hI)).2.2.1
    omega
  · intro I hI
    split_ifs with hi
    · rcases hc _ hi with h | h | h <;> rw [h] <;> norm_num
    · norm_num

theorem eLpNorm_badSubcollectionPrefixMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (M : ℕ) :
    eLpNorm (badSubcollectionPrefixMaximal S f I₀ k₀ s scale N M) 2 volume ≤
      ENNReal.ofReal ((Nat.log2 M + 1 : ℝ) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  rw [eLpNorm_congr_ae (badSubcollectionPrefixMaximal_ae_eq S f hf I₀ k₀ s scale N M)]
  apply eLpNorm_finitePrefixMaximal_le_log2 _ _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (nonstandardSignedEnergyBudget_nonneg f I₀ s)]
  exact hasSignedSumSquareBound_badSubcollectionGenerations hf I₀ k₀ s hk₀ hs scale
    hlam hparent hsub N hN M

theorem eLpNorm_badSubcollectionPrefixMaximal_le_of_ae_overlapCount_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (L M : ℕ)
    (hbound : ∀ᵐ x ∂volume, overlapCount N x ≤ M) :
    eLpNorm (badSubcollectionPrefixMaximal S f I₀ k₀ s scale N L) 2 volume ≤
      ENNReal.ofReal ((Nat.log2 M + 1 : ℝ) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  apply le_trans _ (eLpNorm_badSubcollectionPrefixMaximal_le hf I₀ k₀ s hk₀ hs scale
    hlam hparent hsub N hN M)
  apply eLpNorm_mono
    (memLp_badSubcollectionPrefixMaximal S f hf I₀ k₀ s scale N L).aestronglyMeasurable
  intro x
  rw [Real.norm_of_nonneg (badSubcollectionPrefixMaximal_nonneg S f I₀ k₀ s scale N L x),
    Real.norm_of_nonneg (badSubcollectionPrefixMaximal_nonneg S f I₀ k₀ s scale N M x)]
  exact badSubcollectionPrefixMaximal_le_of_ae_overlapCount_le S f I₀ k₀ s scale N L M hbound x

/-- The scalar classifier has the same grouped-scale geometry as the original family. -/
theorem intervals_subset_geometric
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) :
    intervals S f I₀ k₀ s scale ⊆ geometricIntervals S f I₀ k₀ s scale := by
  intro I hI
  have h := Finset.mem_filter.mp hI
  exact Finset.mem_filter.mpr ⟨h.1, h.2.1, h.2.2.1⟩

theorem exists_chargedCell_of_active_above_base
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    {I : RealInterval} (hI : I ∈ intervals S f I₀ k₀ s scale)
    (hbase : k₀ < scale I + 2 - s)
    (hactive : ∃ x, intervalBadInput S f I₀ k₀ s scale I x ≠ 0) :
    ∃ J ∈ stoppingChildren S f 0 I₀,
      J.carrier ⊆ I.carrier ∧ I.length = (2 : ℝ) ^ s * J.length := by
  exact KrauseLaceyBadScale.exists_chargedCell_of_active_above_base_of_geometry
    f I₀ k₀ s scale hlam (intervals_subset_geometric S f I₀ k₀ s scale hI) hbase hactive

theorem sum_active_aboveBase_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (hactive : ∀ I ∈ N, ∃ x, intervalBadInput S f I₀ k₀ s scale I x ≠ 0)
    (hbase : ∀ I ∈ N, k₀ < scale I + 2 - s)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    (∑ I ∈ N, I.length) ≤ (2 : ℝ) ^ s * K.length := by
  exact KrauseLaceyBadScale.sum_active_aboveBase_length_le_of_geometry f I₀ k₀ s scale hlam N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) hactive hbase K hsub

theorem sum_baseScale_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (hbase : ∀ I ∈ N, scale I + 2 - s ≤ k₀)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    (∑ I ∈ N, I.length) ≤ K.length := by
  exact KrauseLaceyBadScale.sum_baseScale_length_le_of_geometry f I₀ k₀ s scale hlam N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) hbase K hsub

theorem sum_activeBadIntervals_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    (∑ I ∈ activeBadIntervals S f I₀ k₀ s scale N, I.length) ≤
      (1 + (2 : ℝ) ^ s) * K.length := by
  exact KrauseLaceyBadScale.sum_activeBadIntervals_length_le_of_geometry f I₀ k₀ s scale hlam N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) K hsub

theorem sum_activeBadIntervals_descendants_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (K : RealInterval) :
    (∑ I ∈ (activeBadIntervals S f I₀ k₀ s scale N).filter
      (fun I ↦ I.carrier ⊆ K.carrier), I.length) ≤ (1 + (2 : ℝ) ^ s) * K.length := by
  exact KrauseLaceyBadScale.sum_activeBadIntervals_descendants_length_le_of_geometry
    f I₀ k₀ s scale hlam N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) K

theorem volume_active_highOverlap_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) (M : ℕ) :
    volume {x | M < overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x} ≤
      ENNReal.ofReal ((1 + (2 : ℝ) ^ s) * K.length) / (M + 1 : ℝ≥0∞) := by
  exact KrauseLaceyBadScale.volume_active_highOverlap_le_of_geometry
    f I₀ k₀ s scale hlam N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) K hsub M

theorem sum_weighted_localizedBadPiece_eq_pruned_of_lowOverlap
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval)
    (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (M : ℕ) (c : RealInterval → ℂ) (x : ℝ)
    (hx : overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x ≤ M) :
    (∑ I ∈ N, c I * krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x) =
    ∑ I ∈ overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M,
      c I * krauseLaceyLocalizedPiece 1 (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x := by
  exact KrauseLaceyBadScale.sum_weighted_localizedBadPiece_eq_pruned_of_lowOverlap_of_geometry
    S f I₀ k₀ s scale N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) M c x hx

theorem eLpNorm_prunedActivePrefixMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (L M : ℕ) :
    eLpNorm (badSubcollectionPrefixMaximal S f I₀ k₀ s scale
      (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) L) 2 volume ≤
      ENNReal.ofReal ((Nat.log2 M + 1 : ℝ) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  have hAS := (activeBadIntervals_subset S f I₀ k₀ s scale N).trans
    (hN.trans (intervals_subset S f I₀ k₀ s scale))
  apply eLpNorm_badSubcollectionPrefixMaximal_le_of_ae_overlapCount_le hf I₀ k₀ s hk₀ hs
    scale hlam hparent hsub _
    ((overlapPrunedFamily_subset _ M).trans
      ((activeBadIntervals_subset S f I₀ k₀ s scale N).trans hN)) L M
  exact Filter.Eventually.of_forall (overlapCount_overlapPrunedFamily_le _ M
    (fun I hI J hJ hne ↦ hlam (hAS hI) (hAS hJ) hne))

theorem eLpNorm_paperPrunedActivePrefixMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (L : ℕ) :
    eLpNorm (badSubcollectionPrefixMaximal S f I₀ k₀ s scale
      (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) (activeOverlapCutoff s)) L)
      2 volume ≤ ENNReal.ofReal ((2 * (s : ℝ) + 2) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  apply (eLpNorm_prunedActivePrefixMaximal_le hf I₀ k₀ s hk₀ (by omega) scale
    hlam hparent hsub N hN L (activeOverlapCutoff s)).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have h := log2_activeOverlapCutoff_le s
  have hr : (Nat.log2 (activeOverlapCutoff s) : ℝ) ≤ 2 * (s : ℝ) + 1 := by exact_mod_cast h
  linarith

theorem norm_badLengthTailAction_le_prefix
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (ell : ℤ) (x : ℝ) :
    ‖badLengthTailAction S f I₀ k₀ s scale N ell x‖ ≤
      2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale N N.card x := by
  exact KrauseLaceyBadScale.norm_badLengthTailAction_le_prefix_of_geometry
    f I₀ k₀ s scale hlam N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) ell x

theorem badLengthTailMaximal_le_prefix
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (x : ℝ) :
    badLengthTailMaximal S f I₀ k₀ s scale N x ≤
      2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale N N.card x  := by
  exact KrauseLaceyBadScale.badLengthTailMaximal_le_prefix_of_geometry
    f I₀ k₀ s scale hlam N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) x

theorem badLengthTailMaximal_nonneg
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (x : ℝ) :
    0 ≤ badLengthTailMaximal S f I₀ k₀ s scale N x := by
  exact KrauseLaceyBadScale.badLengthTailMaximal_nonneg_of_geometry
    f I₀ k₀ s scale hlam N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) x

theorem badLengthTailMaximal_eq_pruned_of_lowOverlap
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval)
    (hN : N ⊆ intervals S f I₀ k₀ s scale) (M : ℕ) (x : ℝ)
    (hx : overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x ≤ M) :
    badLengthTailMaximal S f I₀ k₀ s scale N x =
      badLengthTailMaximal S f I₀ k₀ s scale
        (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) x := by
  exact KrauseLaceyBadScale.badLengthTailMaximal_eq_pruned_of_lowOverlap_of_geometry
    S f I₀ k₀ s scale N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) M x hx

theorem eLpNorm_pruned_badLengthTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (M : ℕ) :
    eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale
      (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M)) 2 volume ≤
      ENNReal.ofReal (2 * ((Nat.log2 M + 1 : ℝ) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s))) := by
  let P := overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M
  have hP : P ⊆ intervals S f I₀ k₀ s scale :=
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

theorem volume_active_overlap_blocks_le_half_pow
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ) (s t : ℕ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    volume {x | t * activeOverlapBlock s <
      overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x} ≤
      (1 / 2 : ℝ≥0∞) ^ t * ENNReal.ofReal K.length := by
  exact KrauseLaceyBadScale.volume_active_overlap_blocks_le_half_pow_of_geometry
    f I₀ k₀ s t scale hlam N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) K hsub

theorem volume_active_exponentialCutoff_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    volume {x | activeExponentialCutoff s <
      overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x} ≤
      (1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal K.length := by
  exact KrauseLaceyBadScale.volume_active_exponentialCutoff_le_of_geometry
    f I₀ k₀ s scale hlam N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) K hsub

theorem ofReal_sum_active_removed_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    ENNReal.ofReal (∑ I ∈ activeBadIntervals S f I₀ k₀ s scale N \
      overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) (activeExponentialCutoff s),
      I.length) ≤
      ENNReal.ofReal (1 + (2 : ℝ) ^ (s : ℤ)) *
        ((1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal K.length) := by
  exact KrauseLaceyBadScale.ofReal_sum_active_removed_length_le_of_geometry
    f I₀ k₀ s scale hlam N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) K hsub

theorem eLpNorm_exponentiallyPruned_badLengthTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) :
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

theorem lintegral_active_removed_overlap_sq_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    (∫⁻ x, (overlapCount (activeBadIntervals S f I₀ k₀ s scale N \
      overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N)
        (activeExponentialCutoff s)) x : ℝ≥0∞) ^ 2) ≤
      2 * ENNReal.ofReal (1 + (2 : ℝ) ^ (s : ℤ)) ^ 2 *
        ((1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal K.length) := by
  exact KrauseLaceyBadScale.lintegral_active_removed_overlap_sq_le_of_geometry
    f I₀ k₀ s scale hlam N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) K hsub

theorem norm_localizedBadPiece_le_uniform
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    {I : RealInterval} (hI : I ∈ intervals S f I₀ k₀ s scale) (x : ℝ) :
    ‖krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖ ≤ badPieceUniformBound f I₀ := by
  exact KrauseLaceyBadScale.norm_localizedBadPiece_le_uniform_of_geometry
    hf I₀ k₀ s scale hlam hsub (intervals_subset_geometric S f I₀ k₀ s scale hI) x

theorem badLengthTailMaximal_le_uniform_mul_overlapCount
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (x : ℝ) :
    badLengthTailMaximal S f I₀ k₀ s scale N x ≤
      badPieceUniformBound f I₀ * overlapCount N x := by
  exact KrauseLaceyBadScale.badLengthTailMaximal_le_uniform_mul_overlapCount_of_geometry
    hf I₀ k₀ s scale hlam hsub N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) x

theorem eLpNorm_removed_badLengthTailMaximal_sq_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) :
    eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale
      (activeBadIntervals S f I₀ k₀ s scale N \
        overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N)
          (activeExponentialCutoff s))) 2 volume ^ 2 ≤
      ENNReal.ofReal (badPieceUniformBound f I₀) ^ 2 *
        (2 * ENNReal.ofReal (1 + (2 : ℝ) ^ (s : ℤ)) ^ 2 *
          ((1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal I₀.length)) := by
  exact KrauseLaceyBadScale.eLpNorm_removed_badLengthTailMaximal_sq_le_of_geometry
    hf I₀ k₀ s scale hlam hsub N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale))

theorem eLpNorm_removed_badLengthTailMaximal_le_sqrt
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) :
    eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale
      (activeBadIntervals S f I₀ k₀ s scale N \
        overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N)
          (activeExponentialCutoff s))) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (badRemovedEnergyBudget f I₀ s)) := by
  exact KrauseLaceyBadScale.eLpNorm_removed_badLengthTailMaximal_le_sqrt_of_geometry
    hf I₀ k₀ s scale hlam hsub N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale))

theorem badLengthTailAction_eq_pruned_add_removed
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval)
    (_hN : N ⊆ intervals S f I₀ k₀ s scale) (M : ℕ) (ell : ℤ) (x : ℝ) :
    badLengthTailAction S f I₀ k₀ s scale N ell x =
      badLengthTailAction S f I₀ k₀ s scale
        (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) ell x +
      badLengthTailAction S f I₀ k₀ s scale
        (activeBadIntervals S f I₀ k₀ s scale N \
          overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) ell x := by
  exact KrauseLaceyBadScale.badLengthTailAction_eq_pruned_add_removed_of_geometry
    S f I₀ k₀ s scale N M ell x

theorem badLengthTailMaximal_le_pruned_add_removed
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (M : ℕ) (x : ℝ) :
    badLengthTailMaximal S f I₀ k₀ s scale N x ≤
      badLengthTailMaximal S f I₀ k₀ s scale
        (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) x +
      badLengthTailMaximal S f I₀ k₀ s scale
        (activeBadIntervals S f I₀ k₀ s scale N \
          overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) x := by
  exact KrauseLaceyBadScale.badLengthTailMaximal_le_pruned_add_removed_of_geometry
    f I₀ k₀ s scale hlam N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) M x

theorem eLpNorm_nonstandard_badLengthTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) :
    eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale N) 2 volume ≤
      ENNReal.ofReal ((4 * (s : ℝ) + 12) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s) +
          Real.sqrt (badRemovedEnergyBudget f I₀ s)) := by
  let P := overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N)
    (activeExponentialCutoff s)
  let R := activeBadIntervals S f I₀ k₀ s scale N \ P
  have hA := (activeBadIntervals_subset S f I₀ k₀ s scale N).trans hN
  have hP : P ⊆ intervals S f I₀ k₀ s scale :=
    (overlapPrunedFamily_subset _ _).trans hA
  have hR : R ⊆ intervals S f I₀ k₀ s scale := Finset.sdiff_subset.trans hA
  calc
    _ ≤ eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale P +
        badLengthTailMaximal S f I₀ k₀ s scale R) 2 volume := by
      apply eLpNorm_mono
        (aemeasurable_badLengthTailMaximal S hf I₀ k₀ s scale N).aestronglyMeasurable
      intro x
      simp only [Pi.add_apply]
      rw [Real.norm_of_nonneg (badLengthTailMaximal_nonneg f I₀ k₀ s scale hlam N hN x),
        Real.norm_of_nonneg (add_nonneg
          (badLengthTailMaximal_nonneg f I₀ k₀ s scale hlam P hP x)
          (badLengthTailMaximal_nonneg f I₀ k₀ s scale hlam R hR x))]
      exact badLengthTailMaximal_le_pruned_add_removed f I₀ k₀ s scale hlam N hN _ x
    _ ≤ eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale P) 2 volume +
        eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale R) 2 volume :=
      eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal ((4 * (s : ℝ) + 12) * Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) +
        ENNReal.ofReal (Real.sqrt (badRemovedEnergyBudget f I₀ s)) :=
      add_le_add (eLpNorm_exponentiallyPruned_badLengthTailMaximal_le hf I₀ k₀ s hk₀
        scale hlam hparent hsub N hN)
        (eLpNorm_removed_badLengthTailMaximal_le_sqrt hf I₀ k₀ s scale hlam hsub N hN)
    _ = _ := (ENNReal.ofReal_add (by positivity) (Real.sqrt_nonneg _)).symm

theorem badLengthTailAction_eq_at_max_lower_endpoint
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval)
    (hN : N ⊆ intervals S f I₀ k₀ s scale) (ell : ℤ) (x : ℝ) :
    badLengthTailAction S f I₀ k₀ s scale N ell x =
      badLengthTailAction S f I₀ k₀ s scale N (max ell (k₀ + s)) x := by
  exact KrauseLaceyBadScale.badLengthTailAction_eq_at_max_lower_endpoint_of_geometry
    S f I₀ k₀ s scale N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) ell x

theorem nonstandardSourceTailMaximal_eq_badLengthTailMaximal
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (x : ℝ) :
    nonstandardSourceTailMaximal S f I₀ k₀ s scale N x =
      badLengthTailMaximal S f I₀ k₀ s scale N x := by
  exact KrauseLaceyBadScale.nonstandardSourceTailMaximal_eq_badLengthTailMaximal_of_geometry
    f I₀ k₀ s scale hlam N
    (hN.trans (intervals_subset_geometric S f I₀ k₀ s scale)) x

theorem eLpNorm_nonstandardSourceTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) :
    eLpNorm (nonstandardSourceTailMaximal S f I₀ k₀ s scale N) 2 volume ≤
      ENNReal.ofReal ((4 * (s : ℝ) + 12) * Real.sqrt (nonstandardSignedEnergyBudget f I₀ s) +
        Real.sqrt (badRemovedEnergyBudget f I₀ s)) := by
  have he : nonstandardSourceTailMaximal S f I₀ k₀ s scale N =
      badLengthTailMaximal S f I₀ k₀ s scale N := funext
    (nonstandardSourceTailMaximal_eq_badLengthTailMaximal f I₀ k₀ s scale hlam N hN)
  rw [he]
  exact eLpNorm_nonstandard_badLengthTailMaximal_le hf I₀ k₀ s hk₀ scale hlam hparent hsub N hN

/-- The unrestricted physical-suffix maximal estimate directly on the
energy classifier's near family, without overlap or cardinality hypotheses. -/
theorem eLpNorm_energyNonstandardSourceTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyNonstandardIntervals S f I₀ k₀ s scale) :
    eLpNorm (nonstandardSourceTailMaximal S f I₀ k₀ s scale N) 2 volume ≤
      ENNReal.ofReal ((4 * (s : ℝ) + 12) * Real.sqrt (nonstandardSignedEnergyBudget f I₀ s) +
        Real.sqrt (badRemovedEnergyBudget f I₀ s)) := by
  apply eLpNorm_nonstandardSourceTailMaximal_le hf I₀ k₀ s hk₀ scale hlam hparent hsub N
  rw [intervals_eq_energyNonstandardIntervals]
  exact hN

end KrauseLaceyScalarNear
end QuadraticCarleson
