/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusSemigroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.PrimeChoice

/-! # Reciprocity Definition -/

@[expose] public section
universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction, the reciprocity construction: the reciprocity map

For a Frobenius element `σ`, let `Σ` be its fixed field.  The reciprocity
class is the class of `N_{Σ|K}(π_Σ)` in
`A_K / N_{\widetilde L|K} A_{\widetilde L}`.  Independence of the prime
element is proved separately from the unit-cohomology axiom.
-/

noncomputable section

section frobeniusFixedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- A finite intermediate-field package for the fixed field `Σ` of a
Frobenius element. -/
def frobeniusFixedIntermediateField (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements K L hLK) :
    FiniteIntermediateField (D.maximalUnramifiedField L) K.field where
  field := D.frobeniusFixedField K L hLK σ
  above := D.fieldInertia_le_frobeniusFixedField K L hLK σ
  below := D.frobeniusFixedField_le K L hLK σ
  finite := D.frobeniusFixedField_finite K L hLK σ

/-- Finiteness of `Σ | k`, obtained from the finite tower `Σ | K | k`. -/
theorem frobeniusFixedField_absoluteFinite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := by
        simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal)) :
    Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
          (hLnormal := by
            simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal) σ)
        (le_baseField
          (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
            (hLnormal := by
              simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal) σ)))
                := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let : Finite (K.field.toSubgroup ⧸
      extensionSubgroup K.field (D.frobeniusFixedField KR L hLK σ)
        (D.frobeniusFixedField_le KR L hLK σ)) :=
    D.frobeniusFixedField_finite KR L hLK σ
  exact relativeTowerQuotientFinite (baseField G) K.field
    (D.frobeniusFixedField KR L hLK σ)
    (D.frobeniusFixedField_le KR L hLK σ) (le_baseField K.field)

end DegreeData

end frobeniusFixedFields

section reciprocityValues

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace DegreeData

/-- The reciprocity construction with an explicit prime element `π_Σ`. -/
def reciprocityValueOfPrime (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements K L hLK)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    D.MaximalUnramifiedNormQuotient A K.field L := by
  letI : Finite (K.field.toSubgroup ⧸
      extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ)) :=
    D.frobeniusFixedField_finite K L hLK σ
  exact D.maximalUnramifiedNormClass A K.field L
    (relativeNorm A K.field (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ) π)

/-- **the reciprocity construction.** The reciprocity map on the Frobenius semigroup,
using the canonical chosen prime supplied by surjectivity of `v_Σ`.
The following independence theorem identifies this value with the formula
for every prime element. -/
def reciprocityMap (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
        (hLnormal := by
          simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal) →
      D.MaximalUnramifiedNormQuotient A K.field L :=
  fun σ => by
    let KR := K.toFiniteResidueAbstractField D
    letI hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
      simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
    letI hLfiniteKR : Finite
        (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
      simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
    letI : Finite ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G)
          (D.frobeniusFixedField KR L hLK σ)
          (le_baseField (D.frobeniusFixedField KR L hLK σ))) :=
      D.frobeniusFixedField_absoluteFinite K L hLK σ
    let Sigma : FiniteAbstractField G :=
      ⟨D.frobeniusFixedField KR L hLK σ, inferInstance⟩
    exact D.reciprocityValueOfPrime A KR L hLK σ
      (v.chosenPrimeElement Sigma)

/--
The reciprocity map at a Frobenius element is represented by the chosen prime element in its
Frobenius fixed field.
-/
theorem reciprocityMap_eq_chosenPrime (D : DegreeData G) (A : Rep ℤ G)
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := by
        simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal)) :
    D.reciprocityMap A v K L hLK σ = by
      let KR := K.toFiniteResidueAbstractField D
      letI : (extensionSubgroup KR.field L hLK).Normal := by
        simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
      letI hLfiniteKR : Finite
          (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
        simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
      letI : Finite ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G)
            (D.frobeniusFixedField KR L hLK σ)
            (le_baseField (D.frobeniusFixedField KR L hLK σ))) :=
        D.frobeniusFixedField_absoluteFinite K L hLK σ
      let Sigma : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ, inferInstance⟩
      simpa only [Sigma, KR, FiniteAbstractField.toFiniteResidueAbstractField] using
        (D.reciprocityValueOfPrime A KR L hLK σ
          (v.chosenPrimeElement Sigma)) :=
  rfl

end DegreeData

end reciprocityValues

end
end ClassFormation
