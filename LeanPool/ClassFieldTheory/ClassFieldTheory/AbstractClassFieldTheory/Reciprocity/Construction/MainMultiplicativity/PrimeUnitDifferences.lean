/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusActionRemainder
/-!
# Finite-stage unit differences of Frobenius primes

This file proves that differences of Frobenius fixed-field primes, including
differences from quotient-action translates, come from finite-stage units.
-/

@[expose] public section

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Two prime elements coming from Frobenius fixed fields differ by a
finite-stage unit after inclusion in `A_{\widetilde L}`. The common stage is
their finite compositum, which is unramified over both fixed fields. -/
theorem frobeniusPrimeDifference_mem_infiniteUnitAddSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ τ : D.FrobeniusElements
      (K.toFiniteResidueAbstractField D) L hLK)
    (πσ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (πτ : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK τ))
    (hπσ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ,
          D.frobeniusFixedField_absoluteFinite K L hLK σ⟩
      v.IsPrimeElement Sigma πσ)
    (hπτ :
      let KR := K.toFiniteResidueAbstractField D
      let Tau : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK τ,
          D.frobeniusFixedField_absoluteFinite K L hLK τ⟩
      v.IsPrimeElement Tau πτ) :
    let KR := K.toFiniteResidueAbstractField D
    let E := D.maximalUnramifiedField L
    let pσ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ) E
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ) πσ
    let pτ := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK τ) E
      (D.fieldInertia_le_frobeniusFixedField KR L hLK τ) πτ
    pσ - pτ ∈ v.infiniteUnitAddSubgroup E K
      (D.maximalUnramifiedField_le_of_le hLK) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let E := D.maximalUnramifiedField L
  let S := D.frobeniusFixedField KR L hLK σ
  let T := D.frobeniusFixedField KR L hLK τ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let hTK : T.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK τ
  let M := D.frobeniusFixedIntermediateField KR L hLK σ
  let N := D.frobeniusFixedIntermediateField KR L hLK τ
  let P := M.compositum N
  let hPS : P.field.toSubgroup ≤ S.toSubgroup :=
    M.compositum_le_left N
  let hPT : P.field.toSubgroup ≤ T.toSubgroup :=
    M.compositum_le_right N
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let hTabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) T (le_baseField T)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK τ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let Tau : FiniteAbstractField G := ⟨T, hTabsolute⟩
  let hPfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) := P.finite
  let Pi : FiniteAbstractField G := P.toFiniteAbstractField K
  let hPSfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S P.field hPS) :=
    FiniteIntermediateField.finite_extension_of_le P.below hSK hPS
  let hPTfinite : Finite
      (T.toSubgroup ⧸ extensionSubgroup T P.field hPT) :=
    FiniteIntermediateField.finite_extension_of_le P.below hTK hPT
  let EPS : FiniteAbstractFieldExtension G :=
    { field := Pi
      base := Sigma
      below := hPS
      finiteQuotient := hPSfinite }
  let EPT : FiniteAbstractFieldExtension G :=
    { field := Pi
      base := Tau
      below := hPT
      finiteQuotient := hPTfinite }
  have hPSunramified :
      EPS.IsUnramified D := by
    change D.fieldInertia S ≤ P.field.toSubgroup
    have hSI : D.fieldInertia S = D.fieldInertia L := by
      simpa [S] using
        D.frobeniusFixedField_fieldInertia KR L hLK σ
    rw [hSI]
    exact P.above
  have hPTunramified :
      EPT.IsUnramified D := by
    change D.fieldInertia T ≤ P.field.toSubgroup
    have hTI : D.fieldInertia T = D.fieldInertia L := by
      simpa [T] using
        D.frobeniusFixedField_fieldInertia KR L hLK τ
    rw [hTI]
    exact P.above
  let πσP := fixedFieldInclusion A S P.field hPS πσ
  let πτP := fixedFieldInclusion A T P.field hPT πτ
  have hπσP : v.IsPrimeElement Pi πσP := by
    exact v.prime_of_unramified EPS hPSunramified πσ hπσ
  have hπτP : v.IsPrimeElement Pi πτP := by
    exact v.prime_of_unramified EPT hPTunramified πτ hπτ
  let uP : v.unitAddSubgroup Pi :=
    ⟨πσP - πτP,
      v.sub_mem_unitAddSubgroup_of_prime Pi hπτP hπσP⟩
  rw [v.mem_infiniteUnitAddSubgroup_iff]
  refine ⟨P, uP, ?_⟩
  apply Subtype.ext
  rfl

/-- The difference between a prime and any `G(\widetilde L/K)`-translate
of it is a finite-stage unit.  A finite Galois refinement of the prime's
fixed field supplies a stage stable under the chosen quotient
representative. -/
theorem frobeniusPrime_actionDifference_mem_infiniteUnitAddSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let KR := K.toFiniteResidueAbstractField D
      let Sigma : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L hLK σ,
          D.frobeniusFixedField_absoluteFinite K L hLK σ⟩
      v.IsPrimeElement Sigma π)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) :
    let KR := K.toFiniteResidueAbstractField D
    let E := D.maximalUnramifiedField L
    let p := fixedFieldInclusion A
      (D.frobeniusFixedField KR L hLK σ) E
      (D.fieldInertia_le_frobeniusFixedField KR L hLK σ) π
    p - D.frobeniusQuotientAction A K.field L hLK q p ∈
      v.infiniteUnitAddSubgroup E K
        (D.maximalUnramifiedField_le_of_le hLK) := by
  dsimp only
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let E := D.maximalUnramifiedField L
  let S := D.frobeniusFixedField KR L hLK σ
  let hSK : S.toSubgroup ≤ K.field.toSubgroup :=
    D.frobeniusFixedField_le KR L hLK σ
  let M := D.frobeniusFixedIntermediateField KR L hLK σ
  let hEnormal : (extensionSubgroup K.field E
      (D.maximalUnramifiedField_le_of_le hLK)).Normal :=
    D.extensionSubgroup_maximalUnramifiedField_normal K.field L hLK
  let P := M.galoisRefinement
  let hPS : P.field.toSubgroup ≤ S.toSubgroup :=
    M.galoisRefinement_le_field
  let hSabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) S (le_baseField S)) :=
    D.frobeniusFixedField_absoluteFinite K L hLK σ
  let Sigma : FiniteAbstractField G := ⟨S, hSabsolute⟩
  let hPfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) := P.finite
  let Pi : FiniteAbstractField G := P.toFiniteAbstractField K
  let hPSfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S P.field hPS) :=
    FiniteIntermediateField.finite_extension_of_le P.below hSK hPS
  let hPnormal : (extensionSubgroup K.field P.field P.below).Normal := by
    exact FiniteIntermediateField.galoisRefinement_normal M
  let EPS : FiniteAbstractFieldExtension G :=
    { field := Pi
      base := Sigma
      below := hPS
      finiteQuotient := hPSfinite }
  let EPK : FiniteAbstractFieldExtension G :=
    { field := Pi
      base := K
      below := P.below
      finiteQuotient := hPfinite }
  have hPSunramified :
      EPS.IsUnramified D := by
    change D.fieldInertia S ≤ P.field.toSubgroup
    have hSI : D.fieldInertia S = D.fieldInertia L := by
      simpa [S] using
        D.frobeniusFixedField_fieldInertia KR L hLK σ
    rw [hSI]
    exact P.above
  let πP := fixedFieldInclusion A S P.field hPS π
  have hπP : v.IsPrimeElement Pi πP := by
    exact v.prime_of_unramified EPS hPSunramified π hπ
  let k : K.field.toSubgroup := Quotient.out q
  let πqP := normalExtensionAction A K.field P.field P.below hPnormal k πP
  have hπqP : v.IsPrimeElement Pi πqP := by
    change v.valuationAt Pi πP = v.oneValue at hπP
    change v.valuationAt Pi πqP = v.oneValue
    calc
      v.valuationAt Pi πqP = v.valuationAt Pi πP := by
        have hvaluation :=
          v.valuationAt_normalExtensionAction EPK hPnormal k πP
        change v.valuationAt Pi
            (normalExtensionAction A K.field P.field P.below hPnormal k πP) =
          v.valuationAt Pi πP at hvaluation
        exact hvaluation
      _ = v.oneValue := hπP
  let uP : v.unitAddSubgroup Pi :=
    ⟨πP - πqP,
      v.sub_mem_unitAddSubgroup_of_prime Pi hπqP hπP⟩
  rw [v.mem_infiniteUnitAddSubgroup_iff]
  refine ⟨P, uP, ?_⟩
  have hkq : (QuotientGroup.mk k :
      K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  rw [← hkq, D.frobeniusQuotientAction_mk]
  apply Subtype.ext
  rfl

end DegreeData

end

end ClassFormation
