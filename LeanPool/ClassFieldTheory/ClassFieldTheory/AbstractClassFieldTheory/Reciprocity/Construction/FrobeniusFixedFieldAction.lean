/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusClosureCommutation

/-! # Frobenius Fixed Field Action -/
universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Actions on Frobenius fixed fields

This module defines the action induced on a Frobenius fixed field and proves
its compatibility with conjugate-stable actions, relative norms, inclusions,
and Frobenius power sums.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

section fixedFieldActions

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe; `IntegralRepGroupType` names that shared boundary.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The action on a Frobenius fixed field induced by an element commuting
with its defining generator. -/
noncomputable def frobeniusFixedFieldAction (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q) :
    ambientFixedAddSubgroup A (D.frobeniusFixedField K L hLK σ) →+
      ambientFixedAddSubgroup A (D.frobeniusFixedField K L hLK σ) := by
  let k : K.field.toSubgroup := Quotient.out q
  let hstable :
      conjugateClosedSubgroup (D.frobeniusFixedField K L hLK σ) k.1⁻¹ =
        D.frobeniusFixedField K L hLK σ :=
    D.conjugate_frobeniusFixedField_eq_of_commutes K L hLK σ q hq
  exact
    { toFun := fun a => ⟨A.ρ k.1 a.1, by
        intro t
        have htConj : t.1 ∈ conjugateClosedSubgroup
            (D.frobeniusFixedField K L hLK σ) k.1⁻¹ := by
          rw [hstable]
          exact t.2
        have hcMem : k.1⁻¹ * t.1 * k.1 ∈
            D.frobeniusFixedField K L hLK σ := by
          simpa using (conjugateClosedSubgroup_mem
            (D.frobeniusFixedField K L hLK σ) k.1⁻¹ t.1).mp htConj
        let c : (D.frobeniusFixedField K L hLK σ).toSubgroup :=
          ⟨k.1⁻¹ * t.1 * k.1, hcMem⟩
        calc
          A.ρ t.1 (A.ρ k.1 a.1) = A.ρ (t.1 * k.1) a.1 := by
            rw [map_mul]
            rfl
          _ = A.ρ (k.1 * c.1) a.1 := by simp [c, mul_assoc]
          _ = A.ρ k.1 (A.ρ c.1 a.1) := by rw [map_mul]; rfl
          _ = A.ρ k.1 a.1 := by rw [a.2 c]⟩
      map_zero' := by apply Subtype.ext; exact map_zero _
      map_add' := by
        intro a b
        apply Subtype.ext
        exact map_add _ _ _ }

/-- The fixed-field action has the expected ambient automorphism after coercion. -/
@[simp]
theorem frobeniusFixedFieldAction_coe (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    (a : ambientFixedAddSubgroup A (D.frobeniusFixedField K L hLK σ)) :
    ((D.frobeniusFixedFieldAction A K L hLK σ q hq a :
      ambientFixedAddSubgroup A (D.frobeniusFixedField K L hLK σ)) : A.V) =
      A.ρ (Quotient.out q).1 a.1 := by
  rfl

/-- On a quotient representative, the fixed-field action coerces to the represented action. -/
theorem frobeniusFixedFieldAction_coe_of_mk (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    (k : K.field.toSubgroup) (hkq : QuotientGroup.mk k = q)
    (a : ambientFixedAddSubgroup A (D.frobeniusFixedField K L hLK σ)) :
    ((D.frobeniusFixedFieldAction A K L hLK σ q hq a :
      ambientFixedAddSubgroup A (D.frobeniusFixedField K L hLK σ)) : A.V) =
      A.ρ k.1 a.1 := by
  let t : K.field.toSubgroup := Quotient.out q
  have htq :
      (QuotientGroup.mk t :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  have hrel : t⁻¹ * k ∈ D.extensionInertiaWithin K.field L hLK :=
    QuotientGroup.eq.mp (htq.trans hkq.symm)
  have hrField : (t⁻¹ * k).1 ∈
      (D.frobeniusFixedField K L hLK σ).toSubgroup := by
    let rI : (D.fieldInertia L).toSubgroup :=
      ⟨(t⁻¹ * k).1, ⟨
        (mem_extensionSubgroup_iff K.field L hLK (t⁻¹ * k)).1 hrel.1,
        hrel.2⟩⟩
    exact D.fieldInertia_le_frobeniusFixedField K L hLK σ rI.2
  let r : (D.frobeniusFixedField K L hLK σ).toSubgroup :=
    ⟨(t⁻¹ * k).1, hrField⟩
  rw [D.frobeniusFixedFieldAction_coe]
  calc
    A.ρ t.1 a.1 = A.ρ t.1 (A.ρ r.1 a.1) := by rw [a.2 r]
    _ = A.ρ (t.1 * r.1) a.1 := by rw [map_mul]; rfl
    _ = A.ρ k.1 a.1 := by simp [r, t]

/-- The fixed-field action coincides with the conjugation-stable action. -/
theorem frobeniusFixedFieldAction_eq_conjugateStableAction
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    (a : ambientFixedAddSubgroup A (D.frobeniusFixedField K L hLK σ)) :
    let k : K.field.toSubgroup := Quotient.out q
    let hstable : conjugateClosedSubgroup
        (D.frobeniusFixedField K L hLK σ) k.1⁻¹ =
      D.frobeniusFixedField K L hLK σ :=
      D.conjugate_frobeniusFixedField_eq_of_commutes K L hLK σ q hq
    D.frobeniusFixedFieldAction A K L hLK σ q hq a =
      conjugateStableAction A (D.frobeniusFixedField K L hLK σ)
        k.1⁻¹ hstable a := by
  dsimp only
  apply Subtype.ext
  rw [D.frobeniusFixedFieldAction_coe, conjugateStableAction_coe]
  simp

/-- Relative norm in a power-fixed-field tower is equivariant for every
quotient element commuting with both defining powers. -/
theorem relativeNorm_frobeniusFixedFieldAction (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ σ' : D.FrobeniusElements K L hLK)
    (hTS : (D.frobeniusFixedField K L hLK σ').toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ).toSubgroup)
    [Finite ((D.frobeniusFixedField K L hLK σ).toSubgroup ⧸
      extensionSubgroup (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σ') hTS)]
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    (hq' : q * σ'.1 = σ'.1 * q)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ')) :
    relativeNorm A (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σ') hTS
        (D.frobeniusFixedFieldAction A K L hLK σ' q hq' a) =
      D.frobeniusFixedFieldAction A K L hLK σ q hq
        (relativeNorm A (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField K L hLK σ') hTS a) := by
  let k : K.field.toSubgroup := Quotient.out q
  let hSstable := D.conjugate_frobeniusFixedField_eq_of_commutes
    K L hLK σ q hq
  let hTstable := D.conjugate_frobeniusFixedField_eq_of_commutes
    K L hLK σ' q hq'
  rw [D.frobeniusFixedFieldAction_eq_conjugateStableAction
    A K L hLK σ' q hq' a]
  rw [relativeNorm_conjugateStableAction]
  rw [D.frobeniusFixedFieldAction_eq_conjugateStableAction
    A K L hLK σ q hq]

/-- Inclusion of a stabilized Frobenius fixed field intertwines its action
with the actual quotient action on the maximal unramified field. -/
theorem frobeniusFixedFieldAction_inclusion (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
        (D.maximalUnramifiedField L)
        (D.fieldInertia_le_frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedFieldAction A K L hLK σ q hq a) =
      D.frobeniusQuotientAction A K.field L hLK q
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) := by
  apply Subtype.ext
  refine (D.frobeniusFixedFieldAction_coe A K L hLK σ q hq a).trans ?_
  let k : K.field.toSubgroup := Quotient.out q
  have hkq : (QuotientGroup.mk k :
      K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  calc
    A.ρ (Quotient.out q).1 a.1 = A.ρ k.1 a.1 := rfl
    _ = (D.frobeniusQuotientAction A K.field L hLK (QuotientGroup.mk k)
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a)).1 := rfl
    _ = _ := congrArg (fun z =>
      (D.frobeniusQuotientAction A K.field L hLK z
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a)).1) hkq

/-- A Frobenius power sum commutes with the relative norm in a fixed-field
tower whenever the quotient element stabilizes both fields. -/
theorem fixedFieldPowerSum_relativeNorm (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ σ' : D.FrobeniusElements K L hLK)
    (hTS : (D.frobeniusFixedField K L hLK σ').toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ).toSubgroup)
    [Finite ((D.frobeniusFixedField K L hLK σ).toSubgroup ⧸
      extensionSubgroup (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σ') hTS)]
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q) (hq' : q * σ'.1 = σ'.1 * q)
    (n : ℕ)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ')) :
    relativeNorm A (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField K L hLK σ') hTS
        (∑ i : Fin n,
          D.frobeniusFixedFieldAction A K L hLK σ'
            (q ^ i.1) (Commute.pow_left hq' i.1) a) =
      ∑ i : Fin n,
        D.frobeniusFixedFieldAction A K L hLK σ
          (q ^ i.1) (Commute.pow_left hq i.1)
          (relativeNorm A (D.frobeniusFixedField K L hLK σ)
            (D.frobeniusFixedField K L hLK σ') hTS a) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact D.relativeNorm_frobeniusFixedFieldAction A K L hLK
    σ σ' hTS (q ^ i.1) (Commute.pow_left hq i.1)
      (Commute.pow_left hq' i.1) a

/-- The fixed-field power sum becomes the global Frobenius power sum after
inclusion into the maximal unramified field. -/
theorem fixedFieldPowerSum_inclusion (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q) (n : ℕ)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
        (D.maximalUnramifiedField L)
        (D.fieldInertia_le_frobeniusFixedField K L hLK σ)
        (∑ i : Fin n,
          D.frobeniusFixedFieldAction A K L hLK σ
            (q ^ i.1) (Commute.pow_left hq i.1) a) =
      D.frobeniusPowerSum A K.field L hLK q n
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) := by
  apply Subtype.ext
  rw [D.frobeniusPowerSum_coe]
  change
    (AddSubgroup.subtype (ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)))
        (∑ i : Fin n,
          D.frobeniusFixedFieldAction A K L hLK σ
            (q ^ i.1) (Commute.pow_left hq i.1) a) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg Subtype.val
    (D.frobeniusFixedFieldAction_inclusion A K L hLK σ
      (q ^ i.1) (Commute.pow_left hq i.1) a)

end DegreeData

end fixedFieldActions

end

end ClassFormation
