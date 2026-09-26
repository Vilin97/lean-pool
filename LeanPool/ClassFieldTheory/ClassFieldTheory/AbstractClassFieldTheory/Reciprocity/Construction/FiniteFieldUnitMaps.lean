/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusFixedFieldTower
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusClosureCommutation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusFixedFieldAction

/-! # Finite Field Unit Maps -/

@[expose] public section
universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Finite-field unit maps

This module proves valuation invariance on Frobenius fixed fields and
constructs the induced actions, inclusions, and relative norms on the
corresponding finite unit groups.
-/

noncomputable
section

open CategoryTheory
open scoped BigOperators

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteAbstractField

/-- Normality transports across the canonical residue-field enrichment. -/
instance toFiniteResidueAbstractField_extensionNormal
    (K : FiniteAbstractField G) (D : DegreeData G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal] :
    (extensionSubgroup (K.toFiniteResidueAbstractField D).field L hLK).Normal := by
  change (extensionSubgroup K.field L hLK).Normal
  exact hnormal

/-- Relative finiteness transports across the canonical residue-field enrichment. -/
instance toFiniteResidueAbstractField_extensionFinite
    (K : FiniteAbstractField G) (D : DegreeData G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    Finite ((K.toFiniteResidueAbstractField D).field.toSubgroup ⧸
      extensionSubgroup (K.toFiniteResidueAbstractField D).field L hLK) := by
  change Finite
    (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)
  exact hfinite

end FiniteAbstractField

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

private theorem ambientFixedAddSubgroup_transport_coe
    (K L : FiniteAbstractField G) (h : K = L)
    (a : ambientFixedAddSubgroup A K.field) :
    (((h ▸ a : ambientFixedAddSubgroup A L.field) : A.V)) = a.1 := by
  cases h
  rfl

private theorem valuationAt_transport
    (v : ValuationData D A) (K L : FiniteAbstractField G) (h : K = L)
    (a : ambientFixedAddSubgroup A K.field) :
    v.valuationAt L (h ▸ a) = v.valuationAt K a := by
  cases h
  rfl

/-- A quotient element stabilizing a Frobenius fixed field preserves its
normalized valuation. -/
theorem valuationAt_frobeniusFixedFieldAction
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : DegreeData.FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (D.frobeniusFixedField K L hLK σ)
        (le_baseField (D.frobeniusFixedField K L hLK σ)))]
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    v.valuationAt (D.frobeniusFixedAbstractField K L hLK σ)
        (D.frobeniusFixedFieldAction A K L hLK σ q hq a) =
      v.valuationAt (D.frobeniusFixedAbstractField K L hLK σ) a := by
  let TF := D.frobeniusFixedAbstractField K L hLK σ
  let k : K.field.toSubgroup := Quotient.out q
  let hstable : conjugateClosedSubgroup TF.field k.1⁻¹ = TF.field :=
    D.conjugate_frobeniusFixedField_eq_of_commutes K L hLK σ q hq
  let CF := TF.conjugate k.1⁻¹
  let C := CF.field
  have hconj := v.normalizedValuation_conjugate TF k.1⁻¹ a
  let bC : ambientFixedAddSubgroup A C :=
    conjugateFixedElement A TF.field k.1⁻¹ a
  have hCFTF : CF = TF := by
    exact FiniteAbstractField.eq_of_field_eq CF TF hstable
  let bT : ambientFixedAddSubgroup A TF.field := hCFTF ▸ bC
  have hbTcoe : bT.1 = bC.1 := by
    exact ambientFixedAddSubgroup_transport_coe CF TF hCFTF bC
  have hvaluationTransport : v.valuationAt TF bT = v.valuationAt CF bC := by
    exact v.valuationAt_transport CF TF hCFTF bC
  have hbT : bT = D.frobeniusFixedFieldAction
      A K L hLK σ q hq a := by
    apply Subtype.ext
    change bT.1 =
      (D.frobeniusFixedFieldAction A K L hLK σ q hq a).1
    calc
      bT.1 = bC.1 := hbTcoe
      _ = A.ρ k.1 a.1 :=
        (conjugateFixedElement_coe A TF.field k.1⁻¹ a).trans
          (congrArg (fun s : G => A.ρ s a.1) (inv_inv k.1))
      _ = (D.frobeniusFixedFieldAction A K L hLK σ q hq a).1 := by rfl
  calc
    v.valuationAt TF (D.frobeniusFixedFieldAction A K L hLK σ q hq a) =
        v.valuationAt TF bT := congrArg (v.valuationAt TF) hbT.symm
    _ = v.valuationAt CF bC := hvaluationTransport
    _ = v.valuationAt TF a := by simpa [CF, C, bC] using hconj

/-- The stabilizing action restricted to the unit group of a Frobenius
fixed field. -/
noncomputable def frobeniusFixedFieldUnitAction
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : DegreeData.FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (D.frobeniusFixedField K L hLK σ)
        (le_baseField (D.frobeniusFixedField K L hLK σ)))] :
    v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σ) →+
      v.unitAddSubgroup (D.frobeniusFixedAbstractField K L hLK σ) where
  toFun u := ⟨D.frobeniusFixedFieldAction A K L hLK σ q hq u.1, by
    exact (v.mem_unitAddSubgroup_iff
      (D.frobeniusFixedAbstractField K L hLK σ)
      (D.frobeniusFixedFieldAction A K L hLK σ q hq u.1)).2
        ((v.valuationAt_frobeniusFixedFieldAction K L hLK σ q hq u.1).trans u.2)⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _

/-- Units stay units after inclusion into any finite extension.  The construction
uses this silently when all finitely many terms of `(*)` are placed in one
finite Galois field. -/
theorem fixedFieldInclusion_mem_unitAddSubgroup
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (u : v.unitAddSubgroup E.base) :
    fixedFieldInclusion A E.base.field E.field.field E.below u.1 ∈
      v.unitAddSubgroup E.field := by
  rw [v.mem_unitAddSubgroup_iff]
  apply Subtype.ext
  let ER := E.toFiniteResidueAbstractExtension D
  apply zHatMulNat_injective ER.residueDegree.property
  change (ER.residueDegree : ℕ) •
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below u.1) :
        v.valueGroup) : ZHat) =
    (ER.residueDegree : ℕ) • ((0 : v.valueGroup) : ZHat)
  have htower :=
    v.normalizedValuation_tower E
      (fixedFieldInclusion A E.base.field E.field.field E.below u.1)
  have htower' :
      (ER.residueDegree : ℕ) •
          ((v.valuationAt E.field
            (fixedFieldInclusion A E.base.field E.field.field E.below u.1) :
            v.valueGroup) : ZHat) =
        ((v.valuationAt E.base
          (relativeNorm A E.base.field E.field.field E.below
            (fixedFieldInclusion A E.base.field E.field.field E.below u.1)) :
              v.valueGroup) : ZHat) := by
    simpa [ER] using htower
  rw [htower']
  rw [show relativeNorm A E.base.field E.field.field E.below
      (fixedFieldInclusion A E.base.field E.field.field E.below u.1) =
        (E.degree : ℕ) • u.1 by
    exact relativeNorm_fixedFieldInclusion A E.toFiniteAbstractExtension u.1]
  rw [map_nsmul]
  have hu : v.valuationAt E.base u.1 = 0 := u.2
  simp [hu]

/-- Inclusion of units along an arbitrary finite extension. -/
def finiteUnitInclusion
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G) :
    v.unitAddSubgroup E.base →+ v.unitAddSubgroup E.field where
  toFun u := ⟨fixedFieldInclusion A E.base.field E.field.field E.below u.1,
    v.fixedFieldInclusion_mem_unitAddSubgroup E u⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl

/-- Transporting a finite-unit inclusion along equality of its target field
does not change its ambient coefficient. -/
theorem finiteUnitInclusion_transport_coe
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (F : FiniteAbstractField G) (h : E.field = F)
    (u : v.unitAddSubgroup E.base) :
    (((h ▸ v.finiteUnitInclusion E u : v.unitAddSubgroup F).1 :
        ambientFixedAddSubgroup A F.field) : A.V) = u.1.1 := by
  cases h
  rfl

/-- The norm of a unit through an arbitrary finite extension is a unit.
This is the valuation-theoretic step used when a finite Galois refinement
is pushed back down to the originally prescribed intermediate field. -/
theorem relativeNorm_mem_unitAddSubgroup
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (u : v.unitAddSubgroup E.field) :
    relativeNorm A E.base.field E.field.field E.below u.1 ∈
      v.unitAddSubgroup E.base := by
  rw [v.mem_unitAddSubgroup_iff]
  apply Subtype.ext
  have h := v.normalizedValuation_tower E u.1
  let ER := E.toFiniteResidueAbstractExtension D
  change (ER.residueDegree : ℕ) •
      ((v.valuationAt E.field u.1 : v.valueGroup) : ZHat) =
    ((v.valuationAt E.base
      (relativeNorm A E.base.field E.field.field E.below u.1) :
        v.valueGroup) : ZHat) at h
  have hu : v.valuationAt E.field u.1 = 0 := u.2
  simpa [hu] using h.symm

/-- Relative norm restricted to the finite unit groups. -/
def finiteUnitNorm
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G) :
    v.unitAddSubgroup E.field →+ v.unitAddSubgroup E.base where
  toFun u := ⟨relativeNorm A E.base.field E.field.field E.below u.1,
    v.relativeNorm_mem_unitAddSubgroup E u⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' _ _ := by apply Subtype.ext; exact map_add _ _ _

end ValuationData
end

end ClassFormation
