/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.RationalTriangularPreprocess
import Mathlib.GroupTheory.DivisibleHull
import Mathlib.GroupTheory.OreLocalization.Cardinality
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Coordinatizing continuum-sized torsion-free Abelian groups

This file formalizes the coordinatization lemma used in Section 2 of the paper.  A torsion-free
Abelian group of cardinality continuum embeds in the rational direct sum of continuum rank in a
way whose image contains every standard basis vector.
-/

open Cardinal Module

namespace Wallace

noncomputable section

/-- The witness form of the paper's coordinatization lemma. -/
structure RationalCoordinatization (G : Type) [AddCommGroup G] where
  embedding : G →+ RationalTriangularPreprocess.ContinuumRationalGroup
  embedding_injective : Function.Injective embedding
  basisPreimage : TriangularPreprocess.ContinuumIndex → G
  embedding_basisPreimage : ∀ i,
    embedding (basisPreimage i) = Finsupp.single i 1

namespace RationalCoordinatization

variable {G : Type} [AddCommGroup G]

/-- The coordinatewise inclusion `ℤ^(𝔠) → ℚ^(𝔠)` occurring in the paper's
coordinatization lemma. -/
def integerCoordinateEmbedding :
    TriangularPreprocess.ContinuumFreeGroup →+
      RationalTriangularPreprocess.ContinuumRationalGroup :=
  Finsupp.mapRange.addMonoidHom (Int.castAddHom ℚ)

theorem integerCoordinateEmbedding_injective :
    Function.Injective integerCoordinateEmbedding := by
  intro z w h
  ext i
  have hi := congrArg (fun q : RationalTriangularPreprocess.ContinuumRationalGroup ↦ q i) h
  change (z i : ℚ) = (w i : ℚ) at hi
  exact_mod_cast hi

/-- Integer linear combinations of the distinguished preimages in `G`. -/
def integerCoordinatePreimage (K : RationalCoordinatization G) :
    TriangularPreprocess.ContinuumFreeGroup →+ G :=
  Finsupp.liftAddHom (fun i ↦ zmultiplesHom G (K.basisPreimage i))

/-- The embedding of a coordinatized group contains the whole canonical copy of
`ℤ^(𝔠)`, not merely its individual basis vectors. -/
theorem embedding_integerCoordinatePreimage (K : RationalCoordinatization G) :
    K.embedding.comp K.integerCoordinatePreimage = integerCoordinateEmbedding := by
  ext i z
  simp [integerCoordinatePreimage, integerCoordinateEmbedding,
    K.embedding_basisPreimage]

theorem integerCoordinatePreimage_injective (K : RationalCoordinatization G) :
    Function.Injective K.integerCoordinatePreimage := by
  intro z w h
  apply integerCoordinateEmbedding_injective
  rw [← K.embedding_integerCoordinatePreimage]
  simpa using congrArg K.embedding h

variable [IsAddTorsionFree G]

omit [IsAddTorsionFree G] in
private theorem exists_divisibleHull_mk (x : DivisibleHull G) :
    ∃ g : G, ∃ d : ℕ+, DivisibleHull.mk g d = x := by
  induction x using DivisibleHull.ind with
  | mk g d => exact ⟨g, d, rfl⟩

/-- Localizing a continuum-sized torsion-free group by the positive integers does not change its
cardinality. -/
theorem mk_divisibleHull (hcard : #G = 𝔠) : #(DivisibleHull G) = 𝔠 := by
  apply le_antisymm
  · refine (OreLocalization.cardinalMk_le_max (nonZeroDivisors ℕ) G).trans ?_
    rw [hcard]
    refine max_le ?_ (by simp)
    have hsub : #(↥(nonZeroDivisors ℕ)) ≤ 𝔠 :=
      (Cardinal.mk_subtype_le (nonZeroDivisors ℕ : Set ℕ)).trans
        (by simpa using Cardinal.aleph0_le_continuum)
    simpa using hsub
  · rw [← hcard]
    exact Cardinal.mk_le_of_injective DivisibleHull.coe_injective

/-- The divisible hull has rational dimension continuum. -/
theorem rank_divisibleHull (hcard : #G = 𝔠) :
    Module.rank ℚ (DivisibleHull G) = 𝔠 := by
  rw [Module.Free.rank_eq_mk_of_infinite_lt ℚ (DivisibleHull G)]
  · exact mk_divisibleHull hcard
  · rw [mk_divisibleHull hcard]
    simpa using Cardinal.aleph0_lt_continuum

/-- A rational basis of the divisible hull indexed by the canonical continuum type. -/
def continuumBasis (hcard : #G = 𝔠) :
    Basis TriangularPreprocess.ContinuumIndex ℚ (DivisibleHull G) := by
  let b := Module.Free.chooseBasis ℚ (DivisibleHull G)
  have hindex : #(Module.Free.ChooseBasisIndex ℚ (DivisibleHull G)) =
      #TriangularPreprocess.ContinuumIndex := by
    rw [b.mk_eq_rank'', rank_divisibleHull hcard,
      TriangularPreprocess.mk_continuumIndex]
  exact b.reindex (Classical.choice (Cardinal.eq.mp hindex))

/-- A numerator in `G` representing a vector of the chosen basis of the divisible hull. -/
def basisNumerator (hcard : #G = 𝔠) (i : TriangularPreprocess.ContinuumIndex) : G :=
  Classical.choose (exists_divisibleHull_mk (G := G) (continuumBasis hcard i))

/-- The positive denominator attached to `basisNumerator`. -/
def basisDenominator (hcard : #G = 𝔠) (i : TriangularPreprocess.ContinuumIndex) : ℕ+ :=
  Classical.choose (Classical.choose_spec
    (exists_divisibleHull_mk (G := G) (continuumBasis hcard i)))

theorem basisFraction (hcard : #G = 𝔠) (i : TriangularPreprocess.ContinuumIndex) :
    DivisibleHull.mk (basisNumerator hcard i) (basisDenominator hcard i) =
      continuumBasis hcard i :=
  Classical.choose_spec (Classical.choose_spec
    (exists_divisibleHull_mk (G := G) (continuumBasis hcard i)))

theorem denominator_smul_basis (hcard : #G = 𝔠)
    (i : TriangularPreprocess.ContinuumIndex) :
    ((basisDenominator (G := G) hcard i : ℕ) : ℚ) • continuumBasis hcard i =
      (basisNumerator (G := G) hcard i : DivisibleHull G) := by
  rw [← basisFraction hcard i, Nat.cast_smul_eq_nsmul,
    DivisibleHull.nsmul_mk, DivisibleHull.mk_eq_mk_iff_smul_eq_smul]
  simp

/-- Rescale the chosen rational basis so that every basis vector is literally the image of an
element of the original group. -/
def integralBasis (hcard : #G = 𝔠) :
    Basis TriangularPreprocess.ContinuumIndex ℚ (DivisibleHull G) :=
  (continuumBasis hcard).isUnitSMul
    (fun i ↦ (isUnit_iff_ne_zero.mpr (by
      positivity : ((basisDenominator (G := G) hcard i : ℕ) : ℚ) ≠ 0)))

theorem integralBasis_apply (hcard : #G = 𝔠)
    (i : TriangularPreprocess.ContinuumIndex) :
    integralBasis hcard i = (basisNumerator (G := G) hcard i : DivisibleHull G) := by
  simp only [integralBasis, Basis.isUnitSMul_apply]
  exact denominator_smul_basis hcard i

/-- The additive embedding furnished by the rescaled basis. -/
def canonicalEmbedding (hcard : #G = 𝔠) :
    G →+ RationalTriangularPreprocess.ContinuumRationalGroup :=
  (integralBasis hcard).repr.toLinearMap.toAddMonoidHom.comp
    (DivisibleHull.coeAddMonoidHom G)

theorem canonicalEmbedding_injective (hcard : #G = 𝔠) :
    Function.Injective (canonicalEmbedding hcard) :=
  (integralBasis hcard).repr.injective.comp DivisibleHull.coe_injective

theorem canonicalEmbedding_basisNumerator (hcard : #G = 𝔠)
    (i : TriangularPreprocess.ContinuumIndex) :
    canonicalEmbedding hcard (basisNumerator (G := G) hcard i) =
      Finsupp.single i 1 := by
  change (integralBasis hcard).repr
    (basisNumerator (G := G) hcard i : DivisibleHull G) = _
  rw [← integralBasis_apply hcard i]
  simp

/-- **Torsion-free coordinatization lemma (paper, Section 2).**  Every torsion-free Abelian
group of cardinality continuum embeds in `ℚ^(𝔠)` and its image contains `ℤ^(𝔠)`, expressed by
the preimage of every standard basis vector. -/
def ofCardinalityContinuum (hcard : #G = 𝔠) : RationalCoordinatization G where
  embedding := canonicalEmbedding hcard
  embedding_injective := canonicalEmbedding_injective hcard
  basisPreimage := basisNumerator (G := G) hcard
  embedding_basisPreimage := canonicalEmbedding_basisNumerator hcard

/-- A proposition-level form of the paper's coordinatization lemma: the map is
injective and its image contains the canonical copy of `ℤ^(𝔠)` in `ℚ^(𝔠)`. -/
theorem exists_coordinatization (hcard : #G = 𝔠) :
    ∃ (embedding : G →+ RationalTriangularPreprocess.ContinuumRationalGroup)
      (preimage : TriangularPreprocess.ContinuumFreeGroup →+ G),
      Function.Injective embedding ∧
        Function.Injective preimage ∧
        embedding.comp preimage = integerCoordinateEmbedding := by
  let K := ofCardinalityContinuum (G := G) hcard
  exact ⟨K.embedding, K.integerCoordinatePreimage, K.embedding_injective,
    K.integerCoordinatePreimage_injective,
    K.embedding_integerCoordinatePreimage⟩

end RationalCoordinatization

end

end Wallace
