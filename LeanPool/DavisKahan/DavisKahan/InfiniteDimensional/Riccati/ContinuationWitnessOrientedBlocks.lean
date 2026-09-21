/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.ContinuationWitnessEffectiveBlocks
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Continuation Witness Oriented Blocks -/

open TauCeti.DavisKahan.Sylvester

/-!
# Oriented effective blocks of a continuation-selected branch

The continuation witness selects a genuine target spectral subspace.  This
leaf uses the orthogonal decomposition by that subspace, rather than an
arbitrary Riccati diagonalization, to define the two branch-oriented effective
blocks.  It proves:

* exact coordinate conjugation of an ambient bounded self-adjoint operator;
* exact spectrum union across any reducing subspace and its orthogonal
  complement;
* equality between the effective-block spectrum and the actual restricted
  spectrum;
* oriented half-line enclosures from branchwise `SpectrumIn` hypotheses;
* full spectral gap exclusion and pointwise restricted-spectrum separation.

The only remaining input from branch preservation is the oriented target
placement itself.  In the parallel decomposition, C1 supplies those two
`SpectrumIn` hypotheses from the sharp continuation threshold; all transport
from that placement to effective blocks and genuine spectral repulsion is
proved here.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set
open scoped InnerProductSpace

universe v

section OrthogonalCoordinates

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Synthesis from the orthogonal coordinates `U ⊕ Uᗮ` to the ambient
Hilbert space. -/
noncomputable def subspaceCoordinateSynthesis
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    WithLp 2 (U × Uᗮ) →L[ℂ] H :=
  U.subtypeL ∘L WithLp.fstL 2 ℂ U Uᗮ +
    Uᗮ.subtypeL ∘L WithLp.sndL 2 ℂ U Uᗮ

/-- Analysis into the orthogonal coordinates `U ⊕ Uᗮ`. -/
noncomputable def subspaceCoordinateAnalysis
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    H →L[ℂ] WithLp 2 (U × Uᗮ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ U Uᗮ).symm :
      (U × Uᗮ) →L[ℂ] WithLp 2 (U × Uᗮ)) ∘L
    U.orthogonalProjectionOnto.prod Uᗮ.orthogonalProjectionOnto

omit [CompleteSpace H] in
/-- Synthesis reassembles a pair of components into their sum in the ambient space. -/
@[simp]
theorem subspaceCoordinateSynthesis_apply
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (z : WithLp 2 (U × Uᗮ)) :
    subspaceCoordinateSynthesis U z =
      ((WithLp.fst z : U) : H) + ((WithLp.snd z : Uᗮ) : H) := by
  rfl

omit [CompleteSpace H] in
/-- Analysis splits a vector into its orthogonal projections onto `U` and `Uᗮ`. -/
@[simp]
theorem subspaceCoordinateAnalysis_apply
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] (x : H) :
    subspaceCoordinateAnalysis U x =
      WithLp.toLp 2
        (U.orthogonalProjectionOnto x,
          Uᗮ.orthogonalProjectionOnto x) := by
  rfl

omit [CompleteSpace H] in
/-- Analysis followed by synthesis is the identity on the ambient space. -/
theorem subspaceCoordinateSynthesis_comp_analysis
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    subspaceCoordinateSynthesis U ∘L subspaceCoordinateAnalysis U =
      ContinuousLinearMap.id ℂ H := by
  apply ContinuousLinearMap.ext
  intro x
  change U.starProjection x + Uᗮ.starProjection x = x
  exact U.starProjection_add_starProjection_orthogonal x

omit [CompleteSpace H] in
/-- Synthesis followed by analysis is the identity on the orthogonal direct
sum. -/
theorem subspaceCoordinateAnalysis_comp_synthesis
    (U : Submodule ℂ H) [U.HasOrthogonalProjection] :
    subspaceCoordinateAnalysis U ∘L subspaceCoordinateSynthesis U =
      ContinuousLinearMap.id ℂ (WithLp 2 (U × Uᗮ)) := by
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ U Uᗮ).injective
  apply Prod.ext
  · apply Subtype.ext
    change U.starProjection (((WithLp.fst z : U) : H) + ((WithLp.snd z : Uᗮ) : H)) =
      ((WithLp.fst z : U) : H)
    rw [map_add,
      Submodule.starProjection_eq_self_iff.mpr (WithLp.fst z : U).property,
      (Submodule.starProjection_apply_eq_zero_iff U).mpr
        (WithLp.snd z : Uᗮ).property, add_zero]
  · apply Subtype.ext
    change Uᗮ.starProjection (((WithLp.fst z : U) : H) + ((WithLp.snd z : Uᗮ) : H)) =
      ((WithLp.snd z : Uᗮ) : H)
    have hQfst : Uᗮ.starProjection ((WithLp.fst z : U) : H) = 0 := by
      rw [Submodule.starProjection_orthogonal_apply,
        Submodule.starProjection_eq_self_iff.mpr (WithLp.fst z : U).property,
        sub_self]
    rw [map_add, hQfst,
      Submodule.starProjection_eq_self_iff.mpr (WithLp.snd z : Uᗮ).property,
      zero_add]

/-- Orthogonal-coordinate conjugation gives exactly the four compressed blocks
of the ambient operator. -/
theorem subspaceCoordinate_conjugation_eq_blockOperator
    (T : H →L[ℂ] H) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (hT : T.IsSymmetric) :
    subspaceCoordinateAnalysis U ∘L T ∘L subspaceCoordinateSynthesis U =
      blockOperator (subspaceBlockOperatorData T U hT) := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  apply ContinuousLinearMap.ext
  intro z
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ U Uᗮ).injective
  apply Prod.ext <;> apply Subtype.ext
  · change U.starProjection
        (T (((WithLp.fst z : U) : H) + ((WithLp.snd z : Uᗮ) : H))) =
      U.starProjection (T ((WithLp.fst z : U) : H)) +
        U.starProjection (T ((WithLp.snd z : Uᗮ) : H))
    rw [map_add, map_add]
  · change Uᗮ.starProjection
        (T (((WithLp.fst z : U) : H) + ((WithLp.snd z : Uᗮ) : H))) =
      Uᗮ.starProjection (T ((WithLp.fst z : U) : H)) +
        Uᗮ.starProjection (T ((WithLp.snd z : Uᗮ) : H))
    rw [map_add, map_add]

/-- The ambient operator and its orthogonal-coordinate block operator have the
same complex spectrum. -/
theorem spectrum_subspaceBlockOperatorData
    (T : H →L[ℂ] H) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (hT : T.IsSymmetric) :
    spectrum ℂ T = spectrum ℂ (blockOperator (subspaceBlockOperatorData T U hT)) := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let e : H ≃L[ℂ] WithLp 2 (U × Uᗮ) :=
    ContinuousLinearEquiv.equivOfInverse'
      (subspaceCoordinateAnalysis U) (subspaceCoordinateSynthesis U)
      (subspaceCoordinateAnalysis_comp_synthesis U)
      (subspaceCoordinateSynthesis_comp_analysis U)
  have he : e.conjContinuousAlgEquiv.toAlgEquiv T =
      blockOperator (subspaceBlockOperatorData T U hT) := by
    ext z
    change subspaceCoordinateAnalysis U
        (T (subspaceCoordinateSynthesis U z)) =
      blockOperator (subspaceBlockOperatorData T U hT) z
    have h := congrArg
      (fun R : WithLp 2 (U × Uᗮ) →L[ℂ] WithLp 2 (U × Uᗮ) => R z)
      (subspaceCoordinate_conjugation_eq_blockOperator T U hT)
    simpa only [ContinuousLinearMap.comp_apply] using h
  calc
    spectrum ℂ T = spectrum ℂ (e.conjContinuousAlgEquiv.toAlgEquiv T) :=
      (AlgEquiv.spectrum_eq e.conjContinuousAlgEquiv.toAlgEquiv T).symm
    _ = spectrum ℂ (blockOperator (subspaceBlockOperatorData T U hT)) :=
      congrArg (spectrum ℂ) he

/-- Reduction kills the upper-right cross block. -/
theorem subspaceBlockOperatorData_B01_eq_zero_of_reduces
    (T : H →L[ℂ] H) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (hT : T.IsSymmetric) (hred : T.Reduces U) :
    (subspaceBlockOperatorData T U hT).B01 = 0 := by
  apply ContinuousLinearMap.ext
  intro w
  apply Subtype.ext
  change U.starProjection (T (w : H)) = 0
  exact (Submodule.starProjection_apply_eq_zero_iff U).mpr
    (hred.2 (w : H) w.property)

/-- Reduction kills the lower-left cross block. -/
theorem subspaceBlockOperatorData_B10_eq_zero_of_reduces
    (T : H →L[ℂ] H) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (hT : T.IsSymmetric) (hred : T.Reduces U) :
    (subspaceBlockOperatorData T U hT).B10 = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change Uᗮ.starProjection (T (u : H)) = 0
  rw [Submodule.starProjection_orthogonal_apply,
    Submodule.starProjection_eq_self_iff.mpr
      (hred.1 (u : H) u.property), sub_self]

/-- Relative to a reducing subspace, the coordinate block operator is exactly
the direct sum of the two ambient compressions. -/
theorem blockOperator_subspaceBlockOperatorData_eq_blockDiagonal_of_reduces
    (T : H →L[ℂ] H) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (hT : T.IsSymmetric) (hred : T.Reduces U) :
    blockOperator (subspaceBlockOperatorData T U hT) =
      blockDiagonalOperator (compressOperator U T) (compressOperator Uᗮ T) := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have h01 := subspaceBlockOperatorData_B01_eq_zero_of_reduces T U hT hred
  have h10 := subspaceBlockOperatorData_B10_eq_zero_of_reduces T U hT hred
  apply ContinuousLinearMap.ext
  intro z
  rw [blockOperator_apply, blockDiagonalOperator_apply]
  rw [h01, h10]
  simp only [zero_apply, zero_add, add_zero, subspaceBlockOperatorData]

/-- Exact real-spectrum union of an ambient bounded self-adjoint operator over
any reducing orthogonal decomposition. -/
theorem realSpectrum_eq_union_compressions_of_reduces
    (T : H →L[ℂ] H) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (hT : T.IsSymmetric) (hred : T.Reduces U) :
    realSpectrum T =
      realSpectrum (compressOperator U T) ∪
        realSpectrum (compressOperator Uᗮ T) := by
  let : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hspec : spectrum ℂ T =
      spectrum ℂ (blockDiagonalOperator
        (compressOperator U T) (compressOperator Uᗮ T)) := by
    calc
      spectrum ℂ T =
          spectrum ℂ (blockOperator (subspaceBlockOperatorData T U hT)) :=
        spectrum_subspaceBlockOperatorData T U hT
      _ = spectrum ℂ (blockDiagonalOperator
          (compressOperator U T) (compressOperator Uᗮ T)) :=
        congrArg (spectrum ℂ)
          (blockOperator_subspaceBlockOperatorData_eq_blockDiagonal_of_reduces
            T U hT hred)
  exact realSpectrum_eq_union_of_spectrum_eq_union T
    (compressOperator U T) (compressOperator Uᗮ T)
    (hspec.trans
      (spectrum_blockDiagonalOperator
        (compressOperator U T) (compressOperator Uᗮ T)))

omit [CompleteSpace H] in
/-- The real spectrum of the compression is exactly the actual restricted
spectrum. -/
theorem realSpectrum_compressOperator_eq_restrictedSpectrum
    (T : H →L[ℂ] H) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (hU : InvariantFor T U) :
    realSpectrum (compressOperator U T) = restrictedSpectrum T U := by
  rw [compressOperator_eq_restrict_of_invariant T U hU]
  change
    {r : ℝ | (r : ℂ) ∈ spectrum ℂ (T.restrict hU)} =
      DavisKahan.Foundation.restrictedSpectrum T U
  exact
    (DavisKahan.Foundation.restrictedSpectrum_eq_restrictionSpectrum
      T U hU).symm

omit [CompleteSpace H] in
/-- A branchwise `SpectrumIn` statement becomes an actual half-line enclosure
of the corresponding effective compression. -/
theorem realSpectrum_compressOperator_subset_of_spectrumIn
    (T : H →L[ℂ] H) (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    {q : Set ℝ} (hU : SpectrumIn T U q) :
    realSpectrum (compressOperator U T) ⊆ q := by
  rw [realSpectrum_compressOperator_eq_restrictedSpectrum T U hU.invariant]
  exact hU.subset

end OrthogonalCoordinates

section WitnessOrientedBlocks

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A V : H →L[ℂ] H} {s : Set ℝ}

namespace SpectralContinuationWitness

/-- The selected effective block is the compression of the perturbed operator
to the continuation-selected target spectral subspace. -/
noncomputable def targetEffectiveBlock0
    (C : SpectralContinuationWitness A V s) :
    C.targetSelectedSpectralSubspace →L[ℂ]
      C.targetSelectedSpectralSubspace :=
  compressOperator C.targetSelectedSpectralSubspace (A + V)

/-- The complementary effective block is the compression of the perturbed
operator to the orthogonal target branch. -/
noncomputable def targetEffectiveBlock1
    (C : SpectralContinuationWitness A V s) :
    C.targetSelectedSpectralSubspaceᗮ →L[ℂ]
      C.targetSelectedSpectralSubspaceᗮ :=
  compressOperator C.targetSelectedSpectralSubspaceᗮ (A + V)

/-- The target selected spectral subspace reduces the perturbed operator. -/
theorem targetSelectedSpectralSubspace_reduces
    (C : SpectralContinuationWitness A V s) :
    ContinuousLinearMap.Reduces (A + V) C.targetSelectedSpectralSubspace := by
  unfold targetSelectedSpectralSubspace
  exact boundedSelfAdjointSpectralSubspace_reduces (A + V)
    C.targetSeparatingContour.selfAdjoint s
    C.targetSeparatingContour.measurable_selected

/-- Exact spectrum union of the two continuation-selected effective blocks. -/
theorem realSpectrum_eq_union_targetEffectiveBlocks
    (C : SpectralContinuationWitness A V s) :
    realSpectrum (A + V) =
      realSpectrum C.targetEffectiveBlock0 ∪
        realSpectrum C.targetEffectiveBlock1 := by
  simpa only [targetEffectiveBlock0, targetEffectiveBlock1] using
    realSpectrum_eq_union_compressions_of_reduces
      (A + V) C.targetSelectedSpectralSubspace
      C.targetSeparatingContour.selfAdjoint
      C.targetSelectedSpectralSubspace_reduces

/-- Oriented branch placement gives the lower effective-block enclosure. -/
theorem targetEffectiveBlock0_realSpectrum_subset_Iic
    (C : SpectralContinuationWitness A V s) {a : ℝ}
    (h0 : SpectrumIn (A + V) C.targetSelectedSpectralSubspace (Set.Iic a)) :
    realSpectrum C.targetEffectiveBlock0 ⊆ Set.Iic a := by
  simpa only [targetEffectiveBlock0] using
    realSpectrum_compressOperator_subset_of_spectrumIn
      (A + V) C.targetSelectedSpectralSubspace h0

/-- Oriented complementary placement gives the upper effective-block
enclosure. -/
theorem targetEffectiveBlock1_realSpectrum_subset_Ici
    (C : SpectralContinuationWitness A V s) {b : ℝ}
    (h1 : SpectrumIn (A + V) C.targetSelectedSpectralSubspaceᗮ (Set.Ici b)) :
    realSpectrum C.targetEffectiveBlock1 ⊆ Set.Ici b := by
  simpa only [targetEffectiveBlock1] using
    realSpectrum_compressOperator_subset_of_spectrumIn
      (A + V) C.targetSelectedSpectralSubspaceᗮ h1

/-- The two branch-placement hypotheses are exactly the oriented effective
block enclosures needed by spectral repulsion. -/
theorem targetEffectiveBlocks_oriented_halfLines
    (C : SpectralContinuationWitness A V s) {a b : ℝ}
    (h0 : SpectrumIn (A + V) C.targetSelectedSpectralSubspace (Set.Iic a))
    (h1 : SpectrumIn (A + V) C.targetSelectedSpectralSubspaceᗮ (Set.Ici b)) :
    realSpectrum C.targetEffectiveBlock0 ⊆ Set.Iic a ∧
      realSpectrum C.targetEffectiveBlock1 ⊆ Set.Ici b :=
  ⟨C.targetEffectiveBlock0_realSpectrum_subset_Iic h0,
    C.targetEffectiveBlock1_realSpectrum_subset_Ici h1⟩

/-- Genuine bounded spectral repulsion: oriented selected and complementary
branch placement excludes the open gap from the full perturbed spectrum. -/
theorem realSpectrum_add_subset_exterior_of_target_branch
    (C : SpectralContinuationWitness A V s) {a b : ℝ}
    (h0 : SpectrumIn (A + V) C.targetSelectedSpectralSubspace (Set.Iic a))
    (h1 : SpectrumIn (A + V) C.targetSelectedSpectralSubspaceᗮ (Set.Ici b)) :
    realSpectrum (A + V) ⊆ Set.Iic a ∪ Set.Ici b := by
  rw [C.realSpectrum_eq_union_targetEffectiveBlocks]
  intro r hr
  rcases hr with hr0 | hr1
  · exact Or.inl (C.targetEffectiveBlock0_realSpectrum_subset_Iic h0 hr0)
  · exact Or.inr (C.targetEffectiveBlock1_realSpectrum_subset_Ici h1 hr1)

/-- The same oriented placement gives pointwise separation of the two actual
restricted target spectra. -/
theorem targetSelectedSpectraSeparated_of_halfLines
    (C : SpectralContinuationWitness A V s) {a b d : ℝ}
    (hgap : a + d ≤ b)
    (h0 : SpectrumIn (A + V) C.targetSelectedSpectralSubspace (Set.Iic a))
    (h1 : SpectrumIn (A + V) C.targetSelectedSpectralSubspaceᗮ (Set.Ici b)) :
    SpectraSeparated (A + V) C.targetSelectedSpectralSubspace
      (A + V) C.targetSelectedSpectralSubspaceᗮ d := by
  refine ⟨h0.invariant, h1.invariant, ?_⟩
  intro x hx y hy
  have hxa : x ≤ a := h0.subset hx
  have hby : b ≤ y := h1.subset hy
  have hdist : d ≤ y - x := by linarith
  calc
    d ≤ y - x := hdist
    _ ≤ |y - x| := le_abs_self (y - x)
    _ = |x - y| := abs_sub_comm y x

/-- Effective-block form of the same ordered separation. -/
theorem targetEffectiveBlocks_realSpectra_separated_of_branch
    (C : SpectralContinuationWitness A V s) {a b d : ℝ}
    (hgap : a + d ≤ b)
    (h0 : SpectrumIn (A + V) C.targetSelectedSpectralSubspace (Set.Iic a))
    (h1 : SpectrumIn (A + V) C.targetSelectedSpectralSubspaceᗮ (Set.Ici b)) :
    ∀ x ∈ realSpectrum C.targetEffectiveBlock0,
      ∀ y ∈ realSpectrum C.targetEffectiveBlock1, d ≤ |x - y| := by
  let : CompleteSpace C.targetSelectedSpectralSubspace :=
    (C.targetSelectedSpectralSubspace.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace
      (C.targetSelectedSpectralSubspaceᗮ : Submodule ℂ H) :=
    (C.targetSelectedSpectralSubspaceᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  exact realSpectra_blocks_separated_of_halfLines
    C.targetEffectiveBlock0 C.targetEffectiveBlock1 hgap
    (C.targetEffectiveBlock0_realSpectrum_subset_Iic h0)
    (C.targetEffectiveBlock1_realSpectrum_subset_Ici h1)

end SpectralContinuationWitness

end WitnessOrientedBlocks

end DavisKahanExt
end TauCeti
