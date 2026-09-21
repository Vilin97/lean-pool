/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws

/-! # Valuation Laws -/
namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# normalized degree and Frobenius theory: functoriality of normalized valuations

This file proves the two functorial assertions of normalized-valuation functoriality from the
source norm laws.
-/

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- Conjugating an abstract field does not change its degree image. -/
theorem DegreeData.fieldImage_conjugate
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (D : DegreeData G) (K : ClosedSubgroup G) (σ : G) :
    D.fieldImage (conjugateClosedSubgroup K σ) = D.fieldImage K := by
  rw [D.fieldImage_eq_map, D.fieldImage_eq_map]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    let k : K.toSubgroup :=
      ⟨σ * x * σ⁻¹, (conjugateClosedSubgroup_mem K σ x).mp hx⟩
    refine ⟨k.1, k.2, ?_⟩
    simp [k, map_mul, mul_assoc]
  · rintro ⟨k, hk, rfl⟩
    let x : G := σ⁻¹ * k * σ
    have hx : x ∈ conjugateClosedSubgroup K σ := by
      rw [conjugateClosedSubgroup_mem]
      change σ * x * σ⁻¹ ∈ K.toSubgroup
      simpa [x, mul_assoc] using hk
    refine ⟨x, hx, ?_⟩
    simp [x, map_mul, mul_assoc, mul_comm]

/-- Conjugate a field whose actual absolute residue quotient is finite.
The transported field remains in the same residue-finite boundary because
conjugation does not change the degree image. -/
noncomputable def DegreeData.FiniteResidueAbstractField.conjugate
    {G : Type*} [Group G] [TopologicalSpace G] {D : DegreeData G}
    [ContinuousMul G] (K : DegreeData.FiniteResidueAbstractField D) (σ : G) :
    DegreeData.FiniteResidueAbstractField D where
  field := conjugateClosedSubgroup K.field σ
  finiteResidueQuotient := by
    unfold DegreeData.residueQuotient
    rw [D.fieldImage_conjugate K.field σ]
    exact K.finiteResidueQuotient

/-- Conjugation preserves the positive absolute residue degree at the
residue-finite boundary. -/
theorem DegreeData.FiniteResidueAbstractField.residueDegree_conjugate
    {G : Type*} [Group G] [TopologicalSpace G] {D : DegreeData G}
    [ContinuousMul G] (K : DegreeData.FiniteResidueAbstractField D) (σ : G) :
    (K.conjugate σ).residueDegree = K.residueDegree := by
  apply PNat.eq
  change Nat.card
      (D.residueQuotient (conjugateClosedSubgroup K.field σ)) =
    Nat.card (D.residueQuotient K.field)
  unfold DegreeData.residueQuotient
  have himage := D.fieldImage_conjugate K.field σ
  apply Nat.card_congr
  exact Subgroup.quotientEquivOfEq
    (congrArg
      (fun H : Subgroup ZHatMul => H.subgroupOf (⊤ : Subgroup ZHatMul))
      himage)

/-- Conjugate a finite abstract field without separating the transported
finiteness proof from the field. -/
noncomputable def FiniteAbstractField.conjugate
    {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (K : FiniteAbstractField G) (σ : G) :
    FiniteAbstractField G where
  field := conjugateClosedSubgroup K.field σ
  finite := Finite.of_equiv
    ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K.field (le_baseField K.field))
    (absoluteConjugateCosetEquiv K.field σ).symm

/-- Conjugation preserves the positive absolute residue degree. -/
theorem FiniteAbstractField.residueDegree_conjugate
    {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (K : FiniteAbstractField G)
    (D : DegreeData G) (σ : G) :
    (K.conjugate σ).residueDegree D = K.residueDegree D := by
  apply PNat.eq
  change Nat.card
      (D.residueQuotient (conjugateClosedSubgroup K.field σ)) =
    Nat.card (D.residueQuotient K.field)
  unfold DegreeData.residueQuotient
  have himage := D.fieldImage_conjugate K.field σ
  apply Nat.card_congr
  exact Subgroup.quotientEquivOfEq
    (congrArg
      (fun H : Subgroup ZHatMul => H.subgroupOf (⊤ : Subgroup ZHatMul))
      himage)

namespace ValuationData

/-- **conjugation compatibility of normalized valuations.** The normalized valuations are compatible with
conjugation: `v_{K^σ}(a^σ) = v_K(a)` (the right-action notation). -/
theorem normalizedValuation_conjugate [ContinuousMul G]
    (v : ValuationData D A) (K : FiniteAbstractField G) (σ : G)
    (a : ambientFixedAddSubgroup A K.field) :
    v.valuationAt (K.conjugate σ)
        (conjugateFixedElement A K.field σ a) =
      v.valuationAt K a := by
  let : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) (conjugateClosedSubgroup K.field σ)
        (le_baseField (conjugateClosedSubgroup K.field σ))) :=
    (K.conjugate σ).finite
  apply Subtype.ext
  apply zHatMulNat_injective (K.residueDegree D).property
  calc
    (K.residueDegree D : ℕ) •
        v.dividedAt (K.conjugate σ)
          (conjugateFixedElement A K.field σ a) =
      ((K.conjugate σ).residueDegree D : ℕ) •
        v.dividedAt (K.conjugate σ)
          (conjugateFixedElement A K.field σ a) := by
            rw [K.residueDegree_conjugate D σ]
    _ = v.normCompositeAt (K.conjugate σ)
        (conjugateFixedElement A K.field σ a) :=
      v.residueDegree_nsmul_dividedAt (K.conjugate σ) _
    _ = v.normCompositeAt K a := by
      change v.toAddMonoidHom
          (normToBase A (conjugateClosedSubgroup K.field σ)
            (conjugateFixedElement A K.field σ a)) =
        v.toAddMonoidHom (normToBase A K.field a)
      congr 1
      apply Subtype.ext
      calc
        ((normToBase A (conjugateClosedSubgroup K.field σ)
            (conjugateFixedElement A K.field σ a) :
              ambientFixedAddSubgroup A (baseField G)) : A.V) =
          A.ρ σ⁻¹
            ((normToBase A K.field a :
              ambientFixedAddSubgroup A (baseField G)) : A.V) := by
                simpa [normToBase] using
                  (relativeNorm_absoluteConjugate_apply A K.field σ a)
        _ = ((normToBase A K.field a :
              ambientFixedAddSubgroup A (baseField G)) : A.V) := by
                exact (normToBase A K.field a).2 ⟨σ⁻¹, trivial⟩
    _ = (K.residueDegree D : ℕ) • v.dividedAt K a :=
      (v.residueDegree_nsmul_dividedAt K a).symm

/-- **the norm--valuation formula.** For a finite tower `L | K`,
`v_K ∘ N_{L|K} = f_{L|K} v_L`. -/
theorem normalizedValuation_tower (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (a : ambientFixedAddSubgroup A E.field.field) :
    let ER := E.toFiniteResidueAbstractExtension D
    (ER.residueDegree : ℕ) •
        ((v.valuationAt E.field a : v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below a) : v.valueGroup) : ZHat) := by
  let ER := E.toFiniteResidueAbstractExtension D
  apply zHatMulNat_injective (E.base.residueDegree D).property
  change (ER.base.residueDegree : ℕ) •
      ((ER.residueDegree : ℕ) • v.dividedAt E.field a) =
    (ER.base.residueDegree : ℕ) •
      v.dividedAt E.base
        (relativeNorm A E.base.field E.field.field E.below a)
  rw [smul_smul, Nat.mul_comm (ER.base.residueDegree : ℕ),
    ER.residueDegree_mul_absoluteResidueDegree D]
  change (E.field.residueDegree D : ℕ) • v.dividedAt E.field a =
    (E.base.residueDegree D : ℕ) •
      v.dividedAt E.base
        (relativeNorm A E.base.field E.field.field E.below a)
  rw [v.residueDegree_nsmul_dividedAt E.field,
    v.residueDegree_nsmul_dividedAt E.base]
  change v.toAddMonoidHom (normToBase A E.field.field a) =
    v.toAddMonoidHom
      (normToBase A E.base.field
        (relativeNorm A E.base.field E.field.field E.below a))
  let T : DegreeData.FiniteTower G := {
    top := E.field.field
    middle := E.base.field
    base := baseField G
    top_le_middle := E.below
    middle_le_base := le_baseField E.base.field
    finiteTopQuotient := E.finiteQuotient
    finiteBaseQuotient := E.base.finite }
  exact congrArg v.toAddMonoidHom
    (by simpa [T, normToBase] using (T.norm_trans_apply A a).symm)

end ValuationData

end
end ClassFormation
