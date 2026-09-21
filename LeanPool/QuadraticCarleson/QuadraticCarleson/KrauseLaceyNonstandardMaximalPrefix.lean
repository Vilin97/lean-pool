/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardSignedSum
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyGenerationRecombination
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyThreeShiftTreeInterface

/-!
# The actual nonstandard generation maximal-prefix estimate

The signed-sum input to Rademacher--Menshov is proved from the genuine
bad-scale pieces. The last theorem specializes all geometric hypotheses to
the concrete complete finite shifted-grid tree.

The logarithm here still records the number of finite generations. Removing
that dependence in the source's uniform sparse theorem requires the separate
Carleson overlap pruning; that further conclusion is not asserted here.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction KrauseLaceyGenerationLayers
  KrauseLaceyRademacherMenshov KrauseLaceyThreeShiftGrid

attribute [local instance] Classical.propDecidable

/-- The explicit energy bound for signed sums of nonstandard generations, with decay factor
`2^(-s)`. -/
noncomputable def nonstandardSignedEnergyBudget
    (f : ℝ → ℂ) (I₀ : RealInterval) (s : ℤ) : ℝ :=
  (311040 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
    (2 : ℝ) ^ (-s)) * ∫ x, ‖f x‖

theorem nonstandardSignedEnergyBudget_nonneg (f : ℝ → ℂ) (I₀ : RealInterval) (s : ℤ) :
    0 ≤ nonstandardSignedEnergyBudget f I₀ s := by
  unfold nonstandardSignedEnergyBudget
  have hmass : 0 ≤ ∫ x, ‖f x‖ := integral_nonneg fun x ↦ norm_nonneg (f x)
  positivity [intervalL1Average_nonneg f I₀]

/-- Every signed sum of the actual minimal generations has the uniform
`2^(-s)` energy decay. This discharges, rather than assumes, the RM input. -/
theorem hasSignedSumSquareBound_nonstandardGenerations
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier) :
    HasSignedSumSquareBound (nonstandardIntervals S f I₀ k₀ s scale).card
      (nonstandardGenerationLp S f hf I₀ k₀ s scale)
      (nonstandardSignedEnergyBudget f I₀ s) := by
  intro c hc
  change ‖∑ n ∈ Finset.range (nonstandardIntervals S f I₀ k₀ s scale).card,
    c n • ∑ I ∈ generation (nonstandardIntervals S f I₀ k₀ s scale) n,
      badPieceLp S f hf I₀ k₀ s scale I‖ ^ 2 ≤ _
  rw [sum_smul_generations_eq]
  apply norm_signed_badPieceLp_sq_le hf I₀ k₀ s (by omega) scale hlam hparent hsub
    _ Finset.Subset.rfl _ _ _
  · intro I hI
    have hi := (Finset.mem_filter.mp hI).2.2.1
    omega
  · intro I hI
    rcases hc _ (generationIndex_spec hI).1 with h | h | h <;> rw [h] <;> norm_num

/-- The actual maximal finite prefix of the actual integral-operator
generation functions, with no choice of `Lp` representative in its definition. -/
noncomputable def nonstandardGenerationPrefixMaximal
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (x : ℝ) : ℝ :=
  ⨆ n : Fin ((nonstandardIntervals S f I₀ k₀ s scale).card + 1),
    ‖∑ i ∈ Finset.range n.val,
      krauseLaceyCollectionAction (generation (nonstandardIntervals S f I₀ k₀ s scale) i)
        scale (fun I ↦ badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖

theorem nonstandardGenerationPrefixMaximal_ae_eq
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ) :
    nonstandardGenerationPrefixMaximal S f I₀ k₀ s scale =ᵐ[volume]
      finitePrefixMaximal (nonstandardIntervals S f I₀ k₀ s scale).card
        (nonstandardGenerationLp S f hf I₀ k₀ s scale) := by
  have hall : ∀ᵐ x ∂volume, ∀ n : ℕ,
      nonstandardGenerationLp S f hf I₀ k₀ s scale n x =
        krauseLaceyCollectionAction (generation (nonstandardIntervals S f I₀ k₀ s scale) n)
          scale (fun I ↦ badScaleInput S f I₀ k₀ (scale I + 2 - s)) x :=
    ae_all_iff.mpr fun n ↦ nonstandardGenerationLp_ae_eq S f hf I₀ k₀ s scale n
  filter_upwards [hall] with x hx
  unfold nonstandardGenerationPrefixMaximal finitePrefixMaximal
  apply iSup_congr
  intro n
  congr 1
  exact Finset.sum_congr rfl fun i hi ↦ (hx i).symm

theorem memLp_nonstandardGenerationPrefixMaximal
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ) :
    MemLp (nonstandardGenerationPrefixMaximal S f I₀ k₀ s scale) 2 :=
  (memLp_congr_ae (nonstandardGenerationPrefixMaximal_ae_eq S f hf I₀ k₀ s scale)).mpr
    (memLp_finitePrefixMaximal _ _)

theorem integral_nonstandardGenerationPrefixMaximal_sq_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier) :
    (∫ x, nonstandardGenerationPrefixMaximal S f I₀ k₀ s scale x ^ 2) ≤
      (Nat.log2 (nonstandardIntervals S f I₀ k₀ s scale).card + 1 : ℝ) ^ 2 *
        nonstandardSignedEnergyBudget f I₀ s := by
  have heq := (nonstandardGenerationPrefixMaximal_ae_eq S f hf I₀ k₀ s scale).fun_comp
    (fun t : ℝ ↦ t ^ 2)
  simp only [Function.comp_def] at heq
  rw [integral_congr_ae heq]
  exact integral_finitePrefixMaximal_sq_le_log2 _ _
    (hasSignedSumSquareBound_nonstandardGenerations hf I₀ k₀ s hk₀ hs scale hlam hparent hsub)

theorem eLpNorm_nonstandardGenerationPrefixMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier) :
    eLpNorm (nonstandardGenerationPrefixMaximal S f I₀ k₀ s scale) 2 volume ≤
      ENNReal.ofReal ((Nat.log2 (nonstandardIntervals S f I₀ k₀ s scale).card + 1 : ℝ) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  rw [eLpNorm_congr_ae (nonstandardGenerationPrefixMaximal_ae_eq S f hf I₀ k₀ s scale)]
  apply eLpNorm_finitePrefixMaximal_le_log2 _ _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (nonstandardSignedEnergyBudget_nonneg f I₀ s)]
  exact hasSignedSumSquareBound_nonstandardGenerations hf I₀ k₀ s hk₀ hs scale hlam hparent hsub

/-- A completely concrete finite shifted-grid application: only the
integrable input and the source's numeric scale restrictions remain. -/
theorem completeFiniteShiftGridTree_nonstandardPrefix_eLpNorm_le
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ)
    (f : ℝ → ℂ) (hf : Integrable f) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s) :
    let S := completeFiniteShiftGridTree topScale shift maxDepth q₀
    let I₀ := finiteShiftGridInterval topScale shift 0 q₀
    let scale := finiteShiftGridScale topScale shift
    eLpNorm (nonstandardGenerationPrefixMaximal S f I₀ k₀ s scale) 2 volume ≤
      ENNReal.ofReal ((Nat.log2 (nonstandardIntervals S f I₀ k₀ s scale).card + 1 : ℝ) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  dsimp only
  exact eLpNorm_nonstandardGenerationPrefixMaximal_le hf _ k₀ s hk₀ hs _
    (completeFiniteShiftGridTree_laminar topScale shift maxDepth q₀)
    (completeFiniteShiftGridTree_hasDyadicParents topScale shift maxDepth q₀)
    (completeFiniteShiftGridTree_subset_root topScale shift maxDepth q₀)


end KrauseLaceyBadScale
end QuadraticCarleson
