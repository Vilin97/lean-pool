/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.ValuationLaws

/-! # Prime Elements -/

@[expose] public section
namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# normalized degree and Frobenius theory: prime elements and units

This file formalizes the prime-element definition and its two immediate consequences for
unramified and totally ramified extensions.
-/

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- Inclusion `A_K → A_L` for an extension `L | K`. -/
def fixedFieldInclusion (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    ambientFixedAddSubgroup A K →+ ambientFixedAddSubgroup A L where
  toFun a := ⟨a.1, fun l => a.2 ⟨l.1, hLK l.2⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/--
Establishes the identity `((fixedFieldInclusion A K L hLK a : ambientFixedAddSubgroup A L) : A.V)
= a.1`.
-/
@[simp]
theorem fixedFieldInclusion_coe (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A K) :
    ((fixedFieldInclusion A K L hLK a : ambientFixedAddSubgroup A L) : A.V) = a.1 :=
  rfl

/-- The norm of an element already fixed over `K` is its `[L:K]`-fold sum. -/
theorem relativeNorm_fixedFieldInclusion
    (A : Rep ℤ G) (E : DegreeData.FiniteAbstractExtension G)
    (a : ambientFixedAddSubgroup A E.base) :
    relativeNorm A E.base E.field E.below
        (fixedFieldInclusion A E.base E.field E.below a) =
      (E.degree : ℕ) • a := by
  apply Subtype.ext
  let := Fintype.ofFinite
    (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below)
  have hterm : ∀ q : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below,
      relativeCosetAction A E.base E.field E.below
        (fixedFieldInclusion A E.base E.field E.below a) q = a.1 := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro k
    rw [relativeCosetAction_mk, fixedFieldInclusion_coe]
    exact a.2 k
  simp only [relativeNorm_apply_coe, relativeNormValue]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ]
  change Fintype.card
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) • a.1 =
    (E.degree : ℕ) • a.1
  rw [← E.extensionSubgroup_index_eq_degree,
    Subgroup.index, Nat.card_eq_fintype_card]

/-- The norm of the trivial extension is the identity. -/
@[simp]
theorem relativeNorm_self
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K K le_rfl)]
    (a : ambientFixedAddSubgroup A K) :
    relativeNorm A K K le_rfl a = a := by
  apply Subtype.ext
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K K le_rfl)
  have hterm : ∀ q : K.toSubgroup ⧸ extensionSubgroup K K le_rfl,
      relativeCosetAction A K K le_rfl a q = a.1 := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro k
    rw [relativeCosetAction_mk]
    exact a.2 k
  simp only [relativeNorm_apply_coe, relativeNormValue]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ]
  have htop : extensionSubgroup K K le_rfl = ⊤ := by
    change K.toSubgroup.subgroupOf K.toSubgroup = ⊤
    exact Subgroup.subgroupOf_self _
  have hcard :
      Fintype.card (K.toSubgroup ⧸ extensionSubgroup K K le_rfl) = 1 := by
    rw [← Nat.card_eq_fintype_card,
      ← Subgroup.index_eq_card (extensionSubgroup K K le_rfl),
      htop, Subgroup.index_top]
  rw [hcard, one_nsmul]

namespace ValuationData

/-- The value `1` belongs to `Z`, by the valuation-quotient axiom. -/
def oneValue (v : ValuationData D A) : v.valueGroup :=
  ⟨1, by
    obtain ⟨a, ha⟩ := v.integers_mem 1
    exact ⟨a, by simpa using ha⟩⟩

/-- Establishes the identity `(v.oneValue : ZHat) = 1`. -/
@[simp]
theorem oneValue_coe (v : ValuationData D A) :
    (v.oneValue : ZHat) = 1 :=
  rfl

/-- **the prime-element definition.** A prime element has normalized value `1`. -/
def IsPrimeElement (v : ValuationData D A) (K : FiniteAbstractField G)
    (π : ambientFixedAddSubgroup A K.field) : Prop :=
  v.valuationAt K π = v.oneValue

/-- **the prime-element definition.** The additive form of the unit group
`U_K = {u | v_K(u)=0}`. -/
def unitAddSubgroup (v : ValuationData D A) (K : FiniteAbstractField G) :
    AddSubgroup (ambientFixedAddSubgroup A K.field) :=
  (v.valuationAt K).ker

/-- Characterizes `u ∈ v.unitAddSubgroup K` by the equivalent condition `v.valuationAt K u = 0`. -/
@[simp]
theorem mem_unitAddSubgroup_iff (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (u : ambientFixedAddSubgroup A K.field) :
    u ∈ v.unitAddSubgroup K ↔ v.valuationAt K u = 0 :=
  Iff.rfl

/-- Over an unramified extension, the normalized valuation restricts to the
valuation below. -/
theorem valuationAt_fixedFieldInclusion_of_unramified
    (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hUn : E.IsUnramified D)
    (a : ambientFixedAddSubgroup A E.base.field) :
    v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below a) =
      v.valuationAt E.base a := by
  let EF := E.toFiniteAbstractExtension
  have hfeq : (E.residueDegree D : ℕ) = (E.degree : ℕ) :=
    E.residueDegree_eq_degree_of_isUnramified D hUn
  apply Subtype.ext
  apply zHatMulNat_injective (E.residueDegree D).property
  calc
    (E.residueDegree D : ℕ) •
        ((v.valuationAt E.field
          (fixedFieldInclusion A E.base.field E.field.field E.below a) :
          v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below
          (fixedFieldInclusion A E.base.field E.field.field E.below a)) :
          v.valueGroup) : ZHat) :=
        v.normalizedValuation_tower E
          (fixedFieldInclusion A E.base.field E.field.field E.below a)
    _ = ((v.valuationAt E.base ((E.degree : ℕ) • a) :
          v.valueGroup) : ZHat) := by
        rw [show relativeNorm A E.base.field E.field.field E.below
            (fixedFieldInclusion A E.base.field E.field.field E.below a) =
              (E.degree : ℕ) • a by
          simpa [EF, FiniteAbstractFieldExtension.toFiniteAbstractExtension,
              FiniteAbstractFieldExtension.degree] using
                relativeNorm_fixedFieldInclusion A EF a]
    _ = (E.degree : ℕ) •
        ((v.valuationAt E.base a : v.valueGroup) : ZHat) := by
          exact congrArg Subtype.val
            (map_nsmul (v.valuationAt E.base) (E.degree : ℕ) a)
    _ = (E.residueDegree D : ℕ) •
        ((v.valuationAt E.base a : v.valueGroup) : ZHat) := by
          rw [hfeq]

/-- A prime element remains prime in an unramified extension. -/
theorem prime_of_unramified (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hUn : E.IsUnramified D)
    (π : ambientFixedAddSubgroup A E.base.field)
    (hπ : v.IsPrimeElement E.base π) :
    v.IsPrimeElement E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below π) := by
  rw [IsPrimeElement,
    v.valuationAt_fixedFieldInclusion_of_unramified E hUn π]
  exact hπ

/-- The norm of a prime element is prime in a totally ramified extension. -/
theorem norm_prime_of_totallyRamified (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (π : ambientFixedAddSubgroup A E.field.field) :
    v.IsPrimeElement E.field π →
      v.IsPrimeElement E.base
        (relativeNorm A E.base.field E.field.field E.below π) := by
  intro hπ
  have htower := v.normalizedValuation_tower E π
  have hresidue : (E.residueDegree D : ℕ) = 1 :=
    E.toFiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified D hTot
  change (E.residueDegree D : ℕ) •
      ((v.valuationAt E.field π : v.valueGroup) : ZHat) =
    ((v.valuationAt E.base
      (relativeNorm A E.base.field E.field.field E.below π) :
        v.valueGroup) : ZHat) at htower
  rw [hresidue, one_nsmul] at htower
  rw [IsPrimeElement] at hπ ⊢
  apply Subtype.ext
  exact htower.symm.trans (congrArg Subtype.val hπ)

end ValuationData

end
end ClassFormation
