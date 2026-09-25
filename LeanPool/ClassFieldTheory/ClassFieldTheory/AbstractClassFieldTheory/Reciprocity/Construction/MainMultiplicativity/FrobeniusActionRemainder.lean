/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusDescent
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.Universal
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.TransferOrbitClosure
/-!
# Frobenius action remainders

This file develops the Frobenius exponent, conjugation, quotient-action, and
action-remainder identities used by reciprocity-map multiplicativity.
-/

@[expose] public section

universe u

namespace ClassFormation

open KummerTheory
open CyclicCohomology

noncomputable section

open CategoryTheory

section frobeniusAlgebra

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The exponent is additive under multiplication in the Frobenius
semigroup. -/
@[simp]
theorem frobeniusExponent_mul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ₁ σ₂ : D.FrobeniusElements K L hLK) :
    D.frobeniusExponent K L hLK (σ₁ * σ₂) =
      D.frobeniusExponent K L hLK σ₁ +
      D.frobeniusExponent K L hLK σ₂ := by
  apply proCIntegerOne_pow_nat_injective
  calc
    (Multiplicative.ofAdd (1 : ZHat)) ^
        D.frobeniusExponent K L hLK (σ₁ * σ₂) =
      D.extensionNormalizedDegree K L hLK (σ₁ * σ₂).1 :=
        (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
          (σ₁ * σ₂)).symm
    _ = D.extensionNormalizedDegree K L hLK σ₁.1 *
        D.extensionNormalizedDegree K L hLK σ₂.1 := by
      rw [frobeniusMul_coe, map_mul]
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^
            D.frobeniusExponent K L hLK σ₁ *
        (Multiplicative.ofAdd (1 : ZHat)) ^
            D.frobeniusExponent K L hLK σ₂ := by
      rw [D.extensionNormalizedDegree_frobenius_eq_pow,
        D.extensionNormalizedDegree_frobenius_eq_pow]
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^
            (D.frobeniusExponent K L hLK σ₁ +
              D.frobeniusExponent K L hLK σ₂) := by
      rw [pow_add]

end DegreeData

end frobeniusAlgebra

section frobeniusQuotientActions

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe, so this representation-bearing portion has `G : IntegralRepGroupType`.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- A Frobenius element fixes the elements of its actual fixed field,
viewed inside `A_{\widetilde L}`. -/
theorem frobeniusQuotientAction_fixedFieldInclusion (D : DegreeData G)
    (A : Rep ℤ G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    D.frobeniusQuotientAction A K.field L hLK σ.1
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) =
      fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
        (D.maximalUnramifiedField L)
        (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a := by
  let k : K.field.toSubgroup := Quotient.out σ.1
  have hσk : σ.1 = QuotientGroup.mk k := (Quotient.out_eq' σ.1).symm
  have hσClosure : σ.1 ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup := by
    exact Subgroup.le_topologicalClosure _
      (Subgroup.subset_closure (by simp))
  have hkFixed : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
    change QuotientGroup.mk k ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup
    rw [← hσk]
    exact hσClosure
  rw [← D.extensionSubgroup_frobeniusFixedField K L hLK σ] at hkFixed
  obtain ⟨s, hs⟩ := hkFixed
  rw [hσk]
  apply Subtype.ext
  change A.ρ k.1 a.1 = a.1
  let sFixed : (D.frobeniusFixedField K L hLK σ).toSubgroup :=
    ⟨s.1, ⟨s, hs.1, rfl⟩⟩
  have hsval : sFixed.1 = k.1 := hs.2
  rw [← hsval]
  exact a.2 sFixed

end DegreeData

end frobeniusQuotientActions

section actionRemainderAlgebra

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- For the left `Rep` action, the remainder corresponding to the
right-action notation is `φⁿσ⁻¹`. -/
def frobeniusActionRemainder (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) :
    K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK :=
  φ.1 ^ D.frobeniusExponent K L hLK σ * σ.1⁻¹

/-- If `φ` has Frobenius exponent one, its action remainder has normalized
degree zero. -/
theorem frobeniusActionRemainder_mem_degreeKernel (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    D.frobeniusActionRemainder K L hLK φ σ ∈
      (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker := by
  change D.extensionNormalizedDegree K L hLK
      (φ.1 ^ D.frobeniusExponent K L hLK σ * σ.1⁻¹) = 1
  rw [map_mul, map_pow, map_inv,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ, hφ]
  simp

/-- Conjugate adapted to the left action:
`σ₄ˡ = φⁿ²σ₁φ⁻ⁿ²`. -/
def frobeniusActionConjugate (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) (m : ℕ) :
    D.FrobeniusElements K L hLK := by
  let n := D.frobeniusExponent K L hLK σ
  refine ⟨φ.1 ^ m * σ.1 * φ.1⁻¹ ^ m, n,
    D.frobeniusExponent_pos K L hLK σ, ?_⟩
  rw [map_mul, map_mul, map_pow, map_pow, map_inv,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ]
  simp [n, mul_assoc]

/-- The underlying quotient element of the Frobenius action conjugate. -/
@[simp]
theorem frobeniusActionConjugate_coe (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) (m : ℕ) :
    (D.frobeniusActionConjugate K L hLK φ σ m).1 =
      φ.1 ^ m * σ.1 * φ.1⁻¹ ^ m := by
  simp [frobeniusActionConjugate]

/-- Frobenius action conjugation preserves the Frobenius exponent. -/
@[simp]
theorem frobeniusExponent_actionConjugate (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) (m : ℕ) :
    D.frobeniusExponent K L hLK
        (D.frobeniusActionConjugate K L hLK φ σ m) =
      D.frobeniusExponent K L hLK σ := by
  apply proCIntegerOne_pow_nat_injective
  calc
    (Multiplicative.ofAdd (1 : ZHat)) ^
        D.frobeniusExponent K L hLK
          (D.frobeniusActionConjugate K L hLK φ σ m) =
      D.extensionNormalizedDegree K L hLK
        (D.frobeniusActionConjugate K L hLK φ σ m).1 :=
          (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
            (D.frobeniusActionConjugate K L hLK φ σ m)).symm
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^
          D.frobeniusExponent K L hLK σ := by
      rw [frobeniusActionConjugate_coe, map_mul, map_mul, map_pow, map_pow,
        map_inv,
        D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ]
      simp [mul_assoc]

/-- The fixed field of the left-action conjugate
`φᵐσφ⁻ᵐ` is the corresponding conjugate of the fixed field of
`σ`.  The representative is only used to express the quotient
conjugation in the ambient absolute Galois group. -/
theorem conjugate_frobeniusFixedField_actionConjugate
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) (m : ℕ) :
    let q := φ.1 ^ m
    let k : K.field.toSubgroup := Quotient.out q
    conjugateClosedSubgroup
        (D.frobeniusFixedField K L hLK σ) k.1⁻¹ =
      D.frobeniusFixedField K L hLK
        (D.frobeniusActionConjugate K L hLK φ σ m) := by
  dsimp only
  let q := φ.1 ^ m
  let k : K.field.toSubgroup := Quotient.out q
  let σ' := D.frobeniusActionConjugate K L hLK φ σ m
  have hkq :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  have hσ' : σ'.1 = q * σ.1 * q⁻¹ := by
    simp [σ', q, frobeniusActionConjugate_coe]
  ext x
  change x ∈ conjugateClosedSubgroup
      (D.frobeniusFixedField K L hLK σ) k.1⁻¹ ↔
    x ∈ D.frobeniusFixedField K L hLK σ'
  rw [conjugateClosedSubgroup_mem]
  constructor
  · intro hx
    obtain ⟨t, htClosure, htx⟩ := hx
    let xK : K.field.toSubgroup := ⟨x, by
      have htK : t.1 ∈ K.field.toSubgroup := t.2
      have htxval : t.1 = k.1⁻¹ * x * k.1 := by simpa using htx
      have hxval : x = k.1 * t.1 * k.1⁻¹ := by
        calc
          x = k.1 * (k.1⁻¹ * x * k.1) * k.1⁻¹ := by
            simp [mul_assoc]
          _ = k.1 * t.1 * k.1⁻¹ := by rw [htxval]
      rw [hxval]
      exact K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem k.2 htK) (K.field.toSubgroup.inv_mem k.2)⟩
    have htClosure' : QuotientGroup.mk t ∈
        (closedSubgroupGenerated ({σ.1} : Set
          (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK))).toSubgroup := by
      simpa [DegreeData.frobeniusClosure] using htClosure
    have hxClosure' : q * QuotientGroup.mk t * q⁻¹ ∈
        (closedSubgroupGenerated ({σ'.1} : Set
          (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK))).toSubgroup := by
      rw [hσ']
      exact (mem_closedSubgroupGenerated_conjugate_iff
        q σ.1 (QuotientGroup.mk t)).mp htClosure'
    have hxClosure : QuotientGroup.mk xK ∈
        (D.frobeniusClosure K L hLK σ').toSubgroup := by
      have hxK : xK = k * t * k⁻¹ := by
        apply Subtype.ext
        dsimp [xK]
        have htxval : t.1 = k.1⁻¹ * x * k.1 := by simpa using htx
        calc
          x = k.1 * (k.1⁻¹ * x * k.1) * k.1⁻¹ := by
            simp [mul_assoc]
          _ = k.1 * t.1 * k.1⁻¹ := by rw [htxval]
      rw [hxK]
      change (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) *
          QuotientGroup.mk t * (QuotientGroup.mk k)⁻¹ ∈ _
      rw [hkq]
      simpa [DegreeData.frobeniusClosure] using hxClosure'
    exact ⟨xK, hxClosure, rfl⟩
  · intro hx
    obtain ⟨t, htClosure, htx⟩ := hx
    let yK : K.field.toSubgroup := ⟨k.1⁻¹ * x * k.1, by
      have htK : t.1 ∈ K.field.toSubgroup := t.2
      rw [← htx]
      exact K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem (K.field.toSubgroup.inv_mem k.2) htK) k.2⟩
    have htClosure' : QuotientGroup.mk t ∈
        (closedSubgroupGenerated ({σ'.1} : Set
          (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK))).toSubgroup := by
      simpa [DegreeData.frobeniusClosure] using htClosure
    have hyClosure' : QuotientGroup.mk yK ∈
        (closedSubgroupGenerated ({σ.1} : Set
          (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK))).toSubgroup := by
      apply (mem_closedSubgroupGenerated_conjugate_iff
        q σ.1 (QuotientGroup.mk yK)).mpr
      have hyK : k * yK * k⁻¹ = t := by
        apply Subtype.ext
        dsimp [yK]
        simpa [mul_assoc] using htx.symm
      have hyKq : q * QuotientGroup.mk yK * q⁻¹ =
          (QuotientGroup.mk t :
            K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) := by
        rw [← hkq]
        simpa using congrArg
          (fun z : K.field.toSubgroup =>
            (QuotientGroup.mk z :
              K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)) hyK
      rw [hyKq]
      rw [← hσ']
      exact htClosure'
    exact ⟨yK, by simpa [DegreeData.frobeniusClosure] using hyClosure', by simp [yK]⟩

end DegreeData

end actionRemainderAlgebra

section actionRemainderMultiplication

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Left-action translation of `τ₃=τ₂τ₄`: conjugation moves to
the second factor and the order reverses. -/
theorem frobeniusActionRemainder_mul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ₁ σ₂ : D.FrobeniusElements K L hLK) :
    D.frobeniusActionRemainder K L hLK φ (σ₁ * σ₂) =
      D.frobeniusActionRemainder K L hLK φ
          (D.frobeniusActionConjugate K L hLK φ σ₂
            (D.frobeniusExponent K L hLK σ₁)) *
        D.frobeniusActionRemainder K L hLK φ σ₁ := by
  simp only [frobeniusActionRemainder, frobeniusExponent_mul, pow_add, frobeniusMul_coe,
    mul_inv_rev, mul_assoc, frobeniusExponent_actionConjugate, frobeniusActionConjugate_coe,
    inv_pow, inv_inv, inv_mul_cancel_left]
  have hp : φ.1 ^ D.frobeniusExponent K L hLK σ₁ *
      φ.1 ^ D.frobeniusExponent K L hLK σ₂ =
      φ.1 ^ D.frobeniusExponent K L hLK σ₂ *
        φ.1 ^ D.frobeniusExponent K L hLK σ₁ := by
    rw [← pow_add, ← pow_add, Nat.add_comm]
  calc
    φ.1 ^ D.frobeniusExponent K L hLK σ₁ *
          (φ.1 ^ D.frobeniusExponent K L hLK σ₂ *
            (σ₂.1⁻¹ * σ₁.1⁻¹)) =
        (φ.1 ^ D.frobeniusExponent K L hLK σ₁ *
          φ.1 ^ D.frobeniusExponent K L hLK σ₂) *
            (σ₂.1⁻¹ * σ₁.1⁻¹) := by rw [mul_assoc]
    _ = (φ.1 ^ D.frobeniusExponent K L hLK σ₂ *
          φ.1 ^ D.frobeniusExponent K L hLK σ₁) *
            (σ₂.1⁻¹ * σ₁.1⁻¹) := by rw [hp]
    _ = φ.1 ^ D.frobeniusExponent K L hLK σ₂ *
          (φ.1 ^ D.frobeniusExponent K L hLK σ₁ *
            (σ₂.1⁻¹ * σ₁.1⁻¹)) := by rw [mul_assoc]

end DegreeData

end actionRemainderMultiplication

section fixedFieldRemainderActions

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe, so this representation-bearing portion has `G : IntegralRepGroupType`.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- On the fixed field of `σ`, the left-action remainder acts exactly as
the `n`-th power of `φ`. -/
theorem frobeniusActionRemainder_apply_fixedField (D : DegreeData G)
    (A : Rep ℤ G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    D.frobeniusQuotientAction A K.field L hLK
        (D.frobeniusActionRemainder K L hLK φ σ)
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) =
      D.frobeniusQuotientAction A K.field L hLK
        (φ.1 ^ D.frobeniusExponent K L hLK σ)
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) := by
  let aI := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a
  let B := D.frobeniusQuotientRepresentation A K.field L hLK
  have hfix : B.ρ σ.1 aI = aI := by
    change D.frobeniusQuotientAction A K.field L hLK σ.1 aI = aI
    exact D.frobeniusQuotientAction_fixedFieldInclusion A K L hLK σ a
  have hinv : B.ρ σ.1⁻¹ aI = aI := by
    have hmul : B.ρ (σ.1⁻¹ * σ.1) aI = aI := by
      rw [inv_mul_cancel, map_one]
      rfl
    rw [map_mul] at hmul
    change B.ρ σ.1⁻¹ (B.ρ σ.1 aI) = aI at hmul
    rw [hfix] at hmul
    exact hmul
  change B.ρ
      (φ.1 ^ D.frobeniusExponent K L hLK σ * σ.1⁻¹) aI =
    B.ρ (φ.1 ^ D.frobeniusExponent K L hLK σ) aI
  rw [map_mul]
  change B.ρ (φ.1 ^ D.frobeniusExponent K L hLK σ) (B.ρ σ.1⁻¹ aI) =
    B.ρ (φ.1 ^ D.frobeniusExponent K L hLK σ) aI
  rw [hinv]

end DegreeData

end fixedFieldRemainderActions

end

end ClassFormation
