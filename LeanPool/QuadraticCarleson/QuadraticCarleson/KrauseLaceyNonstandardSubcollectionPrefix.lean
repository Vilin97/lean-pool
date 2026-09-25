/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardMaximalPrefix

/-!
# Prefix bounds for arbitrary genuine nonstandard subcollections

This is the form needed after overlap pruning: the finite family is any
literal subset of the actual nonstandard collection, and the prefix length
is arbitrary. No estimate for the pruning operation is assumed or claimed.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyGenerationLayers KrauseLaceyRademacherMenshov

attribute [local instance] Classical.propDecidable

/-- The `L²` sum of the bad pieces in generation `n` of the subcollection `N`. -/
noncomputable def badSubcollectionGenerationLp
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (N : Finset RealInterval) (n : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  badPieceGenerationLp S f hf I₀ k₀ s scale N n

theorem badSubcollectionGenerationLp_ae_eq
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (N : Finset RealInterval) (n : ℕ) :
    badSubcollectionGenerationLp S f hf I₀ k₀ s scale N n =ᵐ[volume]
      krauseLaceyCollectionAction (generation N n) scale
        (fun I ↦ badScaleInput S f I₀ k₀ (scale I + 2 - s)) :=
  badPieceGenerationLp_ae_eq S f hf I₀ k₀ s scale N n

/-- A prefix of any length inherits the genuinely proved signed-sum
estimate, including when there are more or fewer intervals than levels. -/
theorem hasSignedSumSquareBound_badSubcollectionGenerations
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (M : ℕ) :
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

/-- The largest norm of a prefix containing at most `M` generations of bad pieces from `N`. -/
noncomputable def badSubcollectionPrefixMaximal
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (M : ℕ) (x : ℝ) : ℝ :=
  ⨆ n : Fin (M + 1), ‖∑ i ∈ Finset.range n.val,
    krauseLaceyCollectionAction (generation N i) scale
      (fun I ↦ badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖

theorem badSubcollectionPrefixMaximal_ae_eq
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (N : Finset RealInterval) (M : ℕ) :
    badSubcollectionPrefixMaximal S f I₀ k₀ s scale N M =ᵐ[volume]
      finitePrefixMaximal M (badSubcollectionGenerationLp S f hf I₀ k₀ s scale N) := by
  have hall : ∀ᵐ x ∂volume, ∀ n : ℕ,
      badSubcollectionGenerationLp S f hf I₀ k₀ s scale N n x =
        krauseLaceyCollectionAction (generation N n) scale
          (fun I ↦ badScaleInput S f I₀ k₀ (scale I + 2 - s)) x :=
    ae_all_iff.mpr fun n ↦ badSubcollectionGenerationLp_ae_eq S f hf I₀ k₀ s scale N n
  filter_upwards [hall] with x hx
  unfold badSubcollectionPrefixMaximal finitePrefixMaximal
  apply iSup_congr
  intro n
  congr 1
  exact Finset.sum_congr rfl fun i hi ↦ (hx i).symm

theorem memLp_badSubcollectionPrefixMaximal
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (N : Finset RealInterval) (M : ℕ) :
    MemLp (badSubcollectionPrefixMaximal S f I₀ k₀ s scale N M) 2 :=
  (memLp_congr_ae (badSubcollectionPrefixMaximal_ae_eq S f hf I₀ k₀ s scale N M)).mpr
    (memLp_finitePrefixMaximal _ _)

/-- The exact finite RM estimate for the actual prunable subcollection.
In particular, the constant depends on the specified layer cutoff `M`, not
on the total number of candidate intervals. -/
theorem eLpNorm_badSubcollectionPrefixMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (M : ℕ) :
    eLpNorm (badSubcollectionPrefixMaximal S f I₀ k₀ s scale N M) 2 volume ≤
      ENNReal.ofReal ((Nat.log2 M + 1 : ℝ) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  rw [eLpNorm_congr_ae (badSubcollectionPrefixMaximal_ae_eq S f hf I₀ k₀ s scale N M)]
  apply eLpNorm_finitePrefixMaximal_le_log2 _ _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (nonstandardSignedEnergyBudget_nonneg f I₀ s)]
  exact hasSignedSumSquareBound_badSubcollectionGenerations hf I₀ k₀ s hk₀ hs scale
    hlam hparent hsub N hN M


end KrauseLaceyBadScale
end QuadraticCarleson
