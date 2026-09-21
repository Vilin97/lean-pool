/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.RestrictionCosets
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FrobeniusLift
/-!
# The lower Galois group in the totally ramified auxiliary tower

This file identifies the lower Galois group with the original totally
ramified quotient and constructs its cyclic generator.
-/

noncomputable section

namespace ClassFormation

open KummerTheory
open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Restriction identifies the actual lower Galois group `G(M/M⁰)` with
the original totally ramified group `G(L/K)`. -/
noncomputable def abstractReciprocityTotallyRamifiedRestrictionEquiv
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let S := M.inertiaImage D
    let N := M.lowerFiniteGalois S
    letI : (extensionSubgroup
        (M.maximalUnramifiedSubextension D) M.field N.below).Normal :=
      N.normal
    N.extensionQuotient ≃* L.extensionQuotient := by
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let hML := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension_le_L
    K L hTot q
  have hInertia : ∀ i : K.field.toSubgroup,
      i ∈ D.fieldInertiaWithin K.field →
      i.1 ∈ L.field.toSubgroup → i.1 ∈ M.field.toSubgroup := by
    intro i hiI hiL
    apply D.maximalUnramifiedField_le_abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    exact ⟨hiL, (D.mem_fieldInertiaWithin_iff K.field i).1 hiI⟩
  letI : (extensionSubgroup K.field L.field L.below).Normal := L.normal
  let EL := L.toFiniteAbstractExtension.toAbstractExtension
  letI : (extensionSubgroup EL.base EL.field EL.below).Normal := by
    change (extensionSubgroup K.field L.field L.below).Normal
    exact L.normal
  letI : Group EL.quotient := by
    change Group
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below)
    infer_instance
  exact (M.abstractReciprocityRestrictionMulEquiv
    D EL
      hML hTot hInertia).trans
      L.extensionQuotientMulEquiv.symm

/-- Restriction identifies the degree of the totally ramified lower
extension `M/M⁰` with the original cyclic degree `[L:K]`. -/
theorem abstractReciprocityTotallyRamifiedLowerDegree_eq
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let N := M.lowerFiniteGalois (M.inertiaImage D)
  (N.toFiniteAbstractExtension.degree : ℕ) =
    (L.toFiniteAbstractExtension.degree : ℕ) := by
  let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
    K L hTot q
  let S := M.inertiaImage D
  let M₀ := M.maximalUnramifiedSubextension D
  let hMM₀ : M.field.toSubgroup ≤ M₀.toSubgroup :=
    M.field_le_intermediateField S
  let N := M.lowerFiniteGalois S
  let E := L.toFiniteAbstractExtension
  let e := D.abstractReciprocityTotallyRamifiedRestrictionEquiv
    K L hTot q
  calc
    (N.toFiniteAbstractExtension.degree : ℕ) =
        (extensionSubgroup M₀ M.field hMM₀).index :=
      N.toFiniteAbstractExtension.extensionSubgroup_index_eq_degree.symm
    _ = Nat.card N.extensionQuotient :=
      Subgroup.index_eq_card (extensionSubgroup M₀ M.field hMM₀)
    _ = Nat.card L.extensionQuotient :=
      Nat.card_congr e.toEquiv
    _ = (extensionSubgroup K.field L.field L.below).index :=
      (Subgroup.index_eq_card (extensionSubgroup K.field L.field L.below)).symm
    _ = (E.degree : ℕ) := by
      have h := E.extensionSubgroup_index_eq_degree
      change (extensionSubgroup K.field L.field L.below).index =
        (E.degree : ℕ) at h
      exact h

/-- The generator of `G(M/M⁰)` corresponding to the prescribed generator
of `G(L/K)`. -/
noncomputable def abstractReciprocityTotallyRamifiedLowerGenerator
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    let M := D.abstractReciprocityTotallyRamifiedFiniteGaloisExtension
      K L hTot q
    let S := M.inertiaImage D
    let N := M.lowerFiniteGalois S
    letI : (extensionSubgroup
        (M.maximalUnramifiedSubextension D) M.field N.below).Normal :=
      N.normal
    N.extensionQuotient := by
  exact (D.abstractReciprocityTotallyRamifiedRestrictionEquiv
    K L hTot q).symm q

/-- The restriction equivalence sends the constructed lower generator to the target generator. -/
@[simp]
theorem abstractReciprocityTotallyRamifiedRestrictionEquiv_lowerGenerator
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) :
    D.abstractReciprocityTotallyRamifiedRestrictionEquiv K L hTot q
      (D.abstractReciprocityTotallyRamifiedLowerGenerator
        K L hTot q) = q := by
  exact MulEquiv.apply_symm_apply _ q

/-- The constructed lower automorphism generates the relevant cyclic quotient. -/
theorem abstractReciprocityTotallyRamifiedLowerGenerator_generates
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D)
    (L : FiniteGaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient)
    (hq : ∀ x, x ∈ Subgroup.zpowers q) :
    ∀ x, x ∈ Subgroup.zpowers
      (D.abstractReciprocityTotallyRamifiedLowerGenerator
        K L hTot q) := by
  let e := D.abstractReciprocityTotallyRamifiedRestrictionEquiv
    K L hTot q
  let g := D.abstractReciprocityTotallyRamifiedLowerGenerator
    K L hTot q
  intro x
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hq (e x))
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  apply e.injective
  rw [map_zpow,
    D.abstractReciprocityTotallyRamifiedRestrictionEquiv_lowerGenerator, hn]

end DegreeData

end ClassFormation
