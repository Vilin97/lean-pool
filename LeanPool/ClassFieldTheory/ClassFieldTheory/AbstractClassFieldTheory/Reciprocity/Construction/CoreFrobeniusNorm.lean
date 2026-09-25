/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateCompositum
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormConjugation

/-! # Core Frobenius Norm -/
universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction, the Frobenius norm-identity lemma

The operator `φ_n` is written additively as the sum of the first
`n` powers of the actual quotient action.  This file compares that sum with
the relative norm through the Frobenius fixed field `Σ` constructed in
the Frobenius fixed-field theorem.
-/

noncomputable section

open scoped BigOperators

section inertiaQuotients

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The inclusion of inertia cosets into the finite extension cosets. -/
private noncomputable def inertiaCosetToExtensionCoset (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    ((D.maximalUnramifiedField K).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) →
      (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
  Quotient.map'
    (fun x : (D.maximalUnramifiedField K).toSubgroup =>
      (⟨x.1, x.2.1⟩ : K.toSubgroup))
    (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      exact hxy.1)

private theorem inertiaCosetToExtensionCoset_injective (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    Function.Injective (D.inertiaCosetToExtensionCoset K L hLK) := by
  intro x y hxy
  refine Quotient.inductionOn₂' x y ?_ hxy
  intro a b hab
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply]
  have habE :
      (⟨a.1, a.2.1⟩ : K.toSubgroup)⁻¹ * ⟨b.1, b.2.1⟩ ∈
        extensionSubgroup K L hLK := by
    exact QuotientGroup.leftRel_apply.mp (Quotient.exact' hab)
  refine ⟨habE, ?_⟩
  change D.degree (a.1⁻¹ * b.1) = 1
  rw [map_mul, map_inv]
  change (D.degree a.1)⁻¹ * D.degree b.1 = 1
  rw [show D.degree a.1 = 1 from a.2.2,
    show D.degree b.1 = 1 from b.2.2]
  simp

/-- Finiteness of `\widetilde L | \widetilde K`, derived from the finite
Galois extension `L | K`; no separate finiteness assumption is introduced. -/
theorem maximalUnramifiedExtension_finite (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Finite
      ((D.maximalUnramifiedField K).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
  Finite.of_injective (D.inertiaCosetToExtensionCoset K L hLK)
    (D.inertiaCosetToExtensionCoset_injective K L hLK)

/-- The actual quotient `G(\widetilde L/\widetilde K)` is the kernel of
`d_K` inside `G(\widetilde L/K)`. -/
private noncomputable def inertiaCosetToDegreeKernel (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) →
      (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker :=
  fun r => Quotient.liftOn' r
    (fun x : (D.maximalUnramifiedField K.field).toSubgroup => by
      let k : K.field.toSubgroup := ⟨x.1, x.2.1⟩
      refine ⟨QuotientGroup.mk k, ?_⟩
      change D.normalizedDegree K k = 1
      change k ∈ (D.normalizedDegree K).toMonoidHom.ker
      rw [D.normalizedDegree_ker K]
      exact x.2.2)
    (by
      intro x y hxy
      apply Subtype.ext
      apply QuotientGroup.eq.mpr
      rw [← D.extensionSubgroup_maximalUnramifiedField K.field L hLK]
      rw [QuotientGroup.leftRel_apply] at hxy
      exact hxy)

private theorem inertiaCosetToDegreeKernel_bijective (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    Function.Bijective (D.inertiaCosetToDegreeKernel K L hLK) := by
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    have hq : QuotientGroup.mk (⟨a.1, a.2.1⟩ : K.field.toSubgroup) =
        QuotientGroup.mk (⟨b.1, b.2.1⟩ : K.field.toSubgroup) :=
      congrArg Subtype.val hab
    have hkN :
        (⟨a.1, a.2.1⟩ : K.field.toSubgroup)⁻¹ * ⟨b.1, b.2.1⟩ ∈
          D.extensionInertiaWithin K.field L hLK :=
      QuotientGroup.eq.mp hq
    refine ⟨hkN.1, ?_⟩
    change D.degree (a.1⁻¹ * b.1) = 1
    rw [map_mul, map_inv]
    change (D.degree a.1)⁻¹ * D.degree b.1 = 1
    rw [show D.degree a.1 = 1 from a.2.2,
      show D.degree b.1 = 1 from b.2.2]
    simp
  · intro z
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
      (D.extensionInertiaWithin K.field L hLK) z.1
    have hkNorm : D.normalizedDegree K k = 1 := by
      change D.extensionNormalizedDegreeContinuous K L hLK
          ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) k) = 1
      exact (congrArg
        (D.extensionNormalizedDegreeContinuous K L hLK) hk).trans z.2
    have hkI : k ∈ D.fieldInertiaWithin K.field := by
      rw [← D.normalizedDegree_ker K]
      exact hkNorm
    let x : (D.maximalUnramifiedField K.field).toSubgroup :=
      ⟨k.1, ⟨k.2, hkI⟩⟩
    refine ⟨QuotientGroup.mk x, ?_⟩
    apply Subtype.ext
    exact hk

/-- Canonical actual-group identification used in the Frobenius norm-identity lemma. -/
noncomputable def inertiaQuotientDegreeKernelEquiv (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) ≃
      (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker :=
  Equiv.ofBijective (D.inertiaCosetToDegreeKernel K L hLK)
    (D.inertiaCosetToDegreeKernel_bijective K L hLK)

end DegreeData

end inertiaQuotients

section quotientActions

/-!
Mathlib's `Rep ℤ G` requires the coefficient ring and acting group to share
a universe; `IntegralRepGroupType` names that shared boundary.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The actual action of `G(\widetilde L/K)` on `A_{\widetilde L}`. -/
def frobeniusQuotientAction (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ambientFixedAddSubgroup A (D.maximalUnramifiedField L) :=
  Quotient.liftOn' q
    (fun k : K.toSubgroup =>
      normalExtensionAction A K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK)
        (D.extensionSubgroup_maximalUnramifiedField_normal K L hLK) k a)
    (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy
      rw [← D.extensionSubgroup_maximalUnramifiedField K L hLK] at hxy
      let l : (D.maximalUnramifiedField L).toSubgroup :=
        ⟨x.1⁻¹ * y.1, hxy⟩
      have hy : y = x * Subgroup.inclusion
          (D.maximalUnramifiedField_le_of_le hLK) l := by
        apply Subtype.ext
        simp [l]
      apply Subtype.ext
      change A.ρ x.1 a.1 = A.ρ y.1 a.1
      rw [hy]
      change A.ρ x.1 a.1 = A.ρ (x.1 * l.1) a.1
      rw [map_mul]
      change A.ρ x.1 a.1 = A.ρ x.1 (A.ρ l.1 a.1)
      rw [a.2 l])

/--
Establishes the identity `D.frobeniusQuotientAction A K L hLK (QuotientGroup.mk k) a =
normalExtensionAction A K (D.maximalUnramifiedField L) (D.maximalUnramifiedField_le_of_le hLK)
(D.extensionSubgroup_maximalUnramifiedField_normal K L hLK) k a`.
-/
@[simp]
theorem frobeniusQuotientAction_mk (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    D.frobeniusQuotientAction A K L hLK (QuotientGroup.mk k) a =
      normalExtensionAction A K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK)
        (D.extensionSubgroup_maximalUnramifiedField_normal K L hLK) k a :=
  rfl

/-- Conjugation by an element of `G_K` preserves the inertia group `I_K`.
The inverse convention is chosen so that the resulting coset permutation
rewrites `τ·φ` as `φ·(φ⁻¹τφ)`. -/
private def inertiaConjugationEquiv (D : DegreeData G) (K : ClosedSubgroup G)
    (k : K.toSubgroup) :
    (D.maximalUnramifiedField K).toSubgroup ≃
      (D.maximalUnramifiedField K).toSubgroup where
  toFun x := ⟨k.1⁻¹ * x.1 * k.1, ⟨by
    exact K.toSubgroup.mul_mem
      (K.toSubgroup.mul_mem (K.toSubgroup.inv_mem k.2) x.2.1) k.2, by
    change D.degree (k.1⁻¹ * x.1 * k.1) = 1
    have hx : D.degree x.1 = 1 := x.2.2
    rw [map_mul, map_mul, map_inv, hx]
    simp⟩⟩
  invFun x := ⟨k.1 * x.1 * k.1⁻¹, ⟨by
    exact K.toSubgroup.mul_mem
      (K.toSubgroup.mul_mem k.2 x.2.1) (K.toSubgroup.inv_mem k.2), by
    change D.degree (k.1 * x.1 * k.1⁻¹) = 1
    have hx : D.degree x.1 = 1 := x.2.2
    rw [map_mul, map_mul, map_inv, hx]
    simp⟩⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]

/-- Conjugation by `G_K` also preserves `I_L` when `L/K` is Galois. -/
private theorem conjugate_mem_maximalUnramifiedField (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup) (l : (D.maximalUnramifiedField L).toSubgroup) :
    k.1⁻¹ * l.1 * k.1 ∈ (D.maximalUnramifiedField L).toSubgroup := by
  let lK : K.toSubgroup := ⟨l.1, hLK l.2.1⟩
  have hcK : k⁻¹ * lK * k ∈ extensionSubgroup K L hLK := by
    simpa [lK] using hLnormal.conj_mem lK l.2.1 k⁻¹
  refine ⟨?_, ?_⟩
  · exact hcK
  · change D.degree (k.1⁻¹ * l.1 * k.1) = 1
    have hlDegree : D.degree l.1 = 1 := l.2.2
    rw [map_mul, map_mul, map_inv, hlDegree]
    simp

/-- The coset permutation `τ ↦ φ⁻¹τφ` of
`G(\widetilde L/\widetilde K)`. -/
private noncomputable def inertiaConjugationCosetEquiv (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup) :
    ((D.maximalUnramifiedField K).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) ≃
      ((D.maximalUnramifiedField K).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
  Quotient.congr (D.inertiaConjugationEquiv K k) (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    constructor
    · intro hxy
      let l : (D.maximalUnramifiedField L).toSubgroup :=
        ⟨x.1⁻¹ * y.1, hxy⟩
      have hl := D.conjugate_mem_maximalUnramifiedField K L hLK k l
      change (k.1⁻¹ * x.1 * k.1)⁻¹ * (k.1⁻¹ * y.1 * k.1) ∈
        (D.maximalUnramifiedField L).toSubgroup
      simpa [l, mul_assoc] using hl
    · intro hxy
      let l : (D.maximalUnramifiedField L).toSubgroup :=
        ⟨(k.1⁻¹ * x.1 * k.1)⁻¹ * (k.1⁻¹ * y.1 * k.1), hxy⟩
      have hl := D.conjugate_mem_maximalUnramifiedField K L hLK k⁻¹ l
      change x.1⁻¹ * y.1 ∈ (D.maximalUnramifiedField L).toSubgroup
      simpa [l, mul_assoc] using hl)

@[simp]
private theorem inertiaConjugationCosetEquiv_mk (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup) (x : (D.maximalUnramifiedField K).toSubgroup) :
    D.inertiaConjugationCosetEquiv K L hLK k (QuotientGroup.mk x) =
      QuotientGroup.mk (D.inertiaConjugationEquiv K k x) :=
  rfl

private theorem relativeCosetAction_inertiaConjugation (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (k : K.toSubgroup)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (r : (D.maximalUnramifiedField K).toSubgroup ⧸
      extensionSubgroup (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK)) :
    relativeCosetAction A (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        (normalExtensionAction A K (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_le_of_le hLK)
          (D.extensionSubgroup_maximalUnramifiedField_normal K L hLK) k a) r =
      A.ρ k.1
        (relativeCosetAction A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          a (D.inertiaConjugationCosetEquiv K L hLK k r)) := by
  refine Quotient.inductionOn' r ?_
  intro x
  rw [relativeCosetAction_mk, D.inertiaConjugationCosetEquiv_mk,
    relativeCosetAction_mk, normalExtensionAction_coe]
  calc
    A.ρ x.1 (A.ρ k.1 a.1) = A.ρ (x.1 * k.1) a.1 := by
      rw [map_mul]
      rfl
    _ = A.ρ (k.1 * (k.1⁻¹ * x.1 * k.1)) a.1 := by
      simp [mul_assoc]
    _ = A.ρ k.1 (A.ρ (k.1⁻¹ * x.1 * k.1) a.1) := by
      rw [map_mul]
      rfl

/-- The norm `N_{\widetilde L/\widetilde K}` is equivariant for the
normalizing `G_K`-action. -/
private theorem relativeNorm_normalizingAction (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [Finite ((D.maximalUnramifiedField K).toSubgroup ⧸
      extensionSubgroup (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK))]
    (k : K.toSubgroup)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ((relativeNorm A (D.maximalUnramifiedField K)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      (normalExtensionAction A K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK)
        (D.extensionSubgroup_maximalUnramifiedField_normal K L hLK) k a) :
      ambientFixedAddSubgroup A (D.maximalUnramifiedField K)) : A.V) =
      A.ρ k.1
        ((relativeNorm A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) a :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField K)) : A.V) := by
  let R := (D.maximalUnramifiedField K).toSubgroup ⧸
    extensionSubgroup (D.maximalUnramifiedField K)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
  let e := D.inertiaConjugationCosetEquiv K L hLK k
  let := Fintype.ofFinite R
  simp only [relativeNorm_apply_coe, relativeNormValue]
  calc
    ∑ r : R, relativeCosetAction A (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        (normalExtensionAction A K (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_le_of_le hLK)
          (D.extensionSubgroup_maximalUnramifiedField_normal K L hLK) k a) r =
      ∑ r : R, A.ρ k.1
        (relativeCosetAction A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          a (e r)) := by
      apply Finset.sum_congr rfl
      intro r _
      exact D.relativeCosetAction_inertiaConjugation A K L hLK k a r
    _ = A.ρ k.1
        (∑ r : R, relativeCosetAction A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          a (e r)) := by
      rw [map_sum]
    _ = A.ρ k.1
        (∑ r : R, relativeCosetAction A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          a r) := by
      rw [e.sum_comp]

/--
Relative norm commutes with the Frobenius quotient action after including the norm into the upper
fixed field.
-/
theorem relativeNorm_frobeniusQuotientAction (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [Finite ((D.maximalUnramifiedField K).toSubgroup ⧸
      extensionSubgroup (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK))]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ((relativeNorm A (D.maximalUnramifiedField K)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      (D.frobeniusQuotientAction A K L hLK q a) :
      ambientFixedAddSubgroup A (D.maximalUnramifiedField K)) : A.V) =
      ((D.frobeniusQuotientAction A K L hLK q
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
            a)) : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
        A.V) := by
  let k : K.toSubgroup := Quotient.out q
  have hq : q = QuotientGroup.mk k := (Quotient.out_eq' q).symm
  rw [hq]
  exact D.relativeNorm_normalizingAction A K L hLK k a

/-- Additive form of the `φ_n = 1 + φ + ⋯ + φ^{n-1}`. -/
def frobeniusPowerSum (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ambientFixedAddSubgroup A (D.maximalUnramifiedField L) :=
  ∑ i : Fin n, D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a

/--
Establishes the identity `((D.frobeniusPowerSum A K L hLK φ n a : ambientFixedAddSubgroup A
(D.maximalUnramifiedField L)) : A.V) = ∑ i : Fin n, (D.frobeniusQuotientAction A K L hLK (φ ^ i.1)
a : A.V)`.
-/
@[simp]
theorem frobeniusPowerSum_coe (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ((D.frobeniusPowerSum A K L hLK φ n a :
      ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) =
      ∑ i : Fin n,
        (D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a : A.V) :=
  by
    change (ambientFixedAddSubgroup A
        (D.maximalUnramifiedField L)).subtype
      (∑ i : Fin n,
        D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rfl

end DegreeData

end quotientActions

section frobeniusCosetEquivalences

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Quotient projection identifies the actual cosets `G_K/G_Σ` with
the cosets of `Γ` in `G(\widetilde L/K)`. -/
private noncomputable def frobeniusFixedCosetToClosureCoset
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) →
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) :=
  Quotient.map'
    (QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK))
    (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ] at hxy
      exact hxy)

private theorem frobeniusFixedCosetToClosureCoset_bijective
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    Function.Bijective
      (D.frobeniusFixedCosetToClosureCoset K L hLK σ) := by
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ]
    have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact' hab)
    exact hrel
  · intro z
    refine Quotient.inductionOn' z ?_
    intro q
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
      (D.extensionInertiaWithin K.field L hLK) q
    refine ⟨QuotientGroup.mk k, ?_⟩
    change QuotientGroup.mk
        ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) k) =
      QuotientGroup.mk q
    rw [hk]

/-- Defines `frobeniusFixedCosetClosureEquiv`. -/
noncomputable def frobeniusFixedCosetClosureEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) ≃
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) :=
  Equiv.ofBijective
    (D.frobeniusFixedCosetToClosureCoset K L hLK σ)
    (D.frobeniusFixedCosetToClosureCoset_bijective K L hLK σ)

/-- The procyclic degree isomorphism says that `Γ` meets the inertia kernel trivially. -/
private theorem frobeniusClosure_inf_degreeKernel (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusClosure K L hLK σ).toSubgroup ⊓
        (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker =
      ⊥ := by
  ext q
  constructor
  · intro hq
    let a : D.frobeniusClosure K L hLK σ := ⟨q, hq.1⟩
    have hclosure : D.frobeniusClosureDegree K L hLK σ a = 1 := hq.2
    have hfixed : D.fixedFieldNormalizedDegree K L hLK σ a = 1 := by
      apply Multiplicative.ext
      apply zHatMulNat_injective
        (D.frobeniusExponent_pos K L hLK σ)
      change D.frobeniusExponent K L hLK σ •
          (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd =
        D.frobeniusExponent K L hLK σ • (1 : ZHatMul).toAdd
      rw [D.frobeniusExponent_nsmul_fixedFieldNormalizedDegree]
      rw [hclosure]
      simp
    have ha : a = 1 :=
      D.frobeniusFixedField_normalizedDegree_injective K L hLK σ (by
        simpa using hfixed)
    exact congrArg Subtype.val ha
  · intro hq
    have : q = 1 := hq
    subst q
    exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

/-- Candidate enumeration of the cosets of `Γ`: an inertia element followed
by one of the first `n=d_K(σ)` powers of a degree-one Frobenius. -/
private def kernelPowerCosetMap (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) :
    (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker ×
        Fin (D.frobeniusExponent K L hLK σ) →
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) :=
  fun p => QuotientGroup.mk (φ.1 ^ p.2.1 * p.1.1)

private theorem kernelPowerCosetMap_injective (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    Function.Injective (D.kernelPowerCosetMap K L hLK φ σ) := by
  rintro ⟨h, i⟩ ⟨h', j⟩ hij
  let n := D.frobeniusExponent K L hLK σ
  let dQ := D.extensionNormalizedDegreeContinuous K L hLK
  have hn : 0 < n := D.frobeniusExponent_pos K L hLK σ
  have hdφ : dQ φ.1 =
      Multiplicative.ofAdd (1 : ZHat) := by
    change D.extensionNormalizedDegree K L hLK φ.1 = _
    rw [D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ, hφ]
    simp
  have hrel : (φ.1 ^ i.1 * h.1)⁻¹ * (φ.1 ^ j.1 * h'.1) ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup :=
    QuotientGroup.leftRel_apply.mp (Quotient.exact' hij)
  let γ : D.frobeniusClosure K L hLK σ :=
    ⟨(φ.1 ^ i.1 * h.1)⁻¹ * (φ.1 ^ j.1 * h'.1), hrel⟩
  have hdegreeRange :
      (D.frobeniusClosureDegree K L hLK σ γ).toAdd ∈
        (zHatMulNat n).toAddMonoidHom.range := by
    have hmem : D.frobeniusClosureDegree K L hLK σ γ ∈
        (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range :=
      ⟨γ, rfl⟩
    rw [D.frobeniusClosureDegree_range K L hLK σ] at hmem
    exact hmem
  have hred : zHatReduction n hn
      (D.frobeniusClosureDegree K L hLK σ γ).toAdd = 0 := by
    have hker :
        (D.frobeniusClosureDegree K L hLK σ γ).toAdd ∈
          (zHatReduction n hn).ker := by
      rw [← zHatMulNat_range_eq_ker_reduction n hn]
      exact hdegreeRange
    exact hker
  have hredOne : zHatReduction n hn (1 : ZHat) = 1 := rfl
  have hmod : (j.1 : ZMod n) - (i.1 : ZMod n) = 0 := by
    have hdh : dQ h.1 = 1 := h.2
    have hdh' : dQ h'.1 = 1 := h'.2
    have hdegMul :
        dQ ((φ.1 ^ i.1 * h.1)⁻¹ * (φ.1 ^ j.1 * h'.1)) =
          (Multiplicative.ofAdd (1 : ZHat) ^ i.1)⁻¹ *
            Multiplicative.ofAdd (1 : ZHat) ^ j.1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_pow, map_pow,
        hdφ, hdh, hdh', mul_one, mul_one]
    have hdegAdd := congrArg Multiplicative.toAdd hdegMul
    change (D.frobeniusClosureDegree K L hLK σ γ).toAdd =
      -(i.1 • (1 : ZHat)) + j.1 • (1 : ZHat) at hdegAdd
    rw [hdegAdd] at hred
    rw [map_add, map_neg, map_nsmul, map_nsmul, hredOne] at hred
    simpa [sub_eq_add_neg, add_comm] using hred
  have hijCast : (i.1 : ZMod n) = (j.1 : ZMod n) := by
    exact (sub_eq_zero.mp hmod).symm
  have hijVal : i.1 = j.1 := by
    have hv := congrArg ZMod.val hijCast
    simpa [ZMod.val_natCast_of_lt i.2, ZMod.val_natCast_of_lt j.2] using hv
  have hijFin : i = j := Fin.ext hijVal
  subst j
  have hkernel : h.1⁻¹ * h'.1 ∈ dQ.toMonoidHom.ker := by
    have hdh : dQ h.1 = 1 := h.2
    have hdh' : dQ h'.1 = 1 := h'.2
    change dQ (h.1⁻¹ * h'.1) = 1
    rw [map_mul, map_inv, hdh, hdh', inv_one, one_mul]
  have hgamma : h.1⁻¹ * h'.1 ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup := by
    simpa [mul_assoc] using hrel
  have hone : h.1⁻¹ * h'.1 = 1 := by
    have hm : h.1⁻¹ * h'.1 ∈ (⊥ : Subgroup
        (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)) := by
      rw [← D.frobeniusClosure_inf_degreeKernel K L hLK σ]
      exact ⟨hgamma, hkernel⟩
    exact hm
  have hh : h = h' := by
    apply Subtype.ext
    exact inv_mul_eq_one.mp hone
  subst h'
  rfl

private theorem kernelPowerCosetMap_bijective (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    Function.Bijective (D.kernelPowerCosetMap K L hLK φ σ) := by
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let dQ := D.extensionNormalizedDegreeContinuous K L hLK
  let H : Subgroup Q := dQ.toMonoidHom.ker
  let Γ : Subgroup Q := (D.frobeniusClosure K L hLK σ).toSubgroup
  let n := D.frobeniusExponent K L hLK σ
  let j := D.extensionDegreeKernelRestriction K L hLK
  let : Finite H :=
    Finite.of_injective j
      (D.extensionDegreeKernelRestriction_injective K L hLK)
  let : Finite (Q ⧸ Γ) := by
    simpa [Q, Γ] using D.frobeniusFixedField_finiteIndex K L hLK σ
  have hΓmap : Γ.map dQ.toMonoidHom =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q.1, q.2, rfl⟩
  have htopmap : (⊤ : Subgroup Q).map dQ.toMonoidHom = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨q, hq⟩ :=
      D.extensionNormalizedDegreeContinuous_surjective K L hLK z
    exact ⟨q, trivial, hq⟩
  have himage : (Γ.map dQ.toMonoidHom).relIndex
      ((⊤ : Subgroup Q).map dQ.toMonoidHom) = n := by
    rw [hΓmap, htopmap, Subgroup.relIndex_top_right,
      D.frobeniusClosureDegree_range K L hLK σ,
      AddSubgroup.index_toSubgroup,
      zHatMulNat_range_index _
        (D.frobeniusExponent_pos K L hLK σ)]
  have hkernel : (Γ ⊓ dQ.toMonoidHom.ker).relIndex
      ((⊤ : Subgroup Q) ⊓ dQ.toMonoidHom.ker) = Nat.card H := by
    rw [show Γ ⊓ dQ.toMonoidHom.ker = ⊥ by
      simpa [Γ, dQ, Q] using
        D.frobeniusClosure_inf_degreeKernel K L hLK σ]
    rw [top_inf_eq]
    change (⊥ : Subgroup Q).relIndex H = Nat.card H
    rw [Subgroup.relIndex_bot_left]
  have hindex : Γ.index = n * Nat.card H := by
    rw [← Subgroup.relIndex_top_right]
    rw [relIndex_eq_map_relIndex_mul_inf_ker_relIndex dQ.toMonoidHom le_top,
      himage, hkernel]
  have hcard :
      Nat.card (H × Fin n) = Nat.card (Q ⧸ Γ) := by
    calc
      Nat.card (H × Fin n) =
          Nat.card H * Nat.card (Fin n) := Nat.card_prod _ _
      _ = Nat.card H * n := by
        have hfin : Nat.card (Fin n) = n := by
          calc
            Nat.card (Fin n) = Fintype.card (Fin n) :=
              Nat.card_eq_fintype_card
            _ = n := Fintype.card_fin n
        rw [hfin]
      _ = n * Nat.card H := Nat.mul_comm _ _
      _ = Γ.index := hindex.symm
      _ = Nat.card (Q ⧸ Γ) := Subgroup.index_eq_card Γ
  apply (Nat.bijective_iff_injective_and_card
    (D.kernelPowerCosetMap K L hLK φ σ)).2
  exact ⟨D.kernelPowerCosetMap_injective K L hLK φ σ hφ,
    by simpa [H, n, Q, Γ, dQ] using hcard⟩

/-- The coset decomposition used in the proof of the Frobenius norm-identity lemma. -/
noncomputable def kernelPowerCosetEquiv (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker ×
        Fin (D.frobeniusExponent K L hLK σ) ≃
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) :=
  Equiv.ofBijective (D.kernelPowerCosetMap K L hLK φ σ)
    (D.kernelPowerCosetMap_bijective K L hLK φ σ hφ)

/-- Explicit version of the coset decomposition, with representatives in
the order `φ^i · τ`; this is the order occurring in `φ_n ∘ N`. -/
private noncomputable def frobeniusNormIdentityCosetMap (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) :
    ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) ×
        Fin (D.frobeniusExponent K L hLK σ) →
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) :=
  fun p =>
    let kφ : K.field.toSubgroup := Quotient.out (φ.1 ^ p.2.1)
    let kI : (D.maximalUnramifiedField K.field).toSubgroup := Quotient.out p.1
    QuotientGroup.mk (kφ * (⟨kI.1, kI.2.1⟩ : K.field.toSubgroup))

private theorem frobeniusNormIdentityCosetMap_commutes (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (p : ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) ×
      Fin (D.frobeniusExponent K L hLK σ)) :
    D.frobeniusFixedCosetToClosureCoset K L hLK σ
        (D.frobeniusNormIdentityCosetMap K L hLK φ σ p) =
      D.kernelPowerCosetMap K L hLK φ σ
        (D.inertiaQuotientDegreeKernelEquiv K L hLK p.1, p.2) := by
  let kφ : K.field.toSubgroup := Quotient.out (φ.1 ^ p.2.1)
  let kI : (D.maximalUnramifiedField K.field).toSubgroup := Quotient.out p.1
  let kIK : K.field.toSubgroup := ⟨kI.1, kI.2.1⟩
  have hkφ : (QuotientGroup.mk'
      (D.extensionInertiaWithin K.field L hLK)) kφ = φ.1 ^ p.2.1 :=
    Quotient.out_eq' (φ.1 ^ p.2.1)
  have hkI :
      (D.inertiaQuotientDegreeKernelEquiv K L hLK p.1).1 =
        (QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) kIK := by
    change (D.inertiaCosetToDegreeKernel K L hLK p.1).1 = _
    calc
      (D.inertiaCosetToDegreeKernel K L hLK p.1).1 =
          (D.inertiaCosetToDegreeKernel K L hLK
            (QuotientGroup.mk kI)).1 := by
        exact congrArg
          (fun r => (D.inertiaCosetToDegreeKernel K L hLK r).1)
          (Quotient.out_eq' p.1).symm
      _ = _ := rfl
  change QuotientGroup.mk
      ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK))
        (kφ * kIK)) =
    QuotientGroup.mk
      (φ.1 ^ p.2.1 *
        (D.inertiaQuotientDegreeKernelEquiv K L hLK p.1).1)
  rw [map_mul, hkφ, hkI]

private theorem frobeniusNormIdentityCosetMap_bijective (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    Function.Bijective (D.frobeniusNormIdentityCosetMap K L hLK φ σ) := by
  let eI := D.inertiaQuotientDegreeKernelEquiv K L hLK
  let eP := D.kernelPowerCosetEquiv K L hLK φ σ hφ
  let eSigma := D.frobeniusFixedCosetClosureEquiv K L hLK σ
  have hinj : Function.Injective (D.frobeniusNormIdentityCosetMap K L hLK φ σ) := by
    intro p q hpq
    apply (Equiv.prodCongr eI (Equiv.refl _)).injective
    apply eP.injective
    calc
      eP (eI p.1, p.2) =
          eSigma (D.frobeniusNormIdentityCosetMap K L hLK φ σ p) :=
        (D.frobeniusNormIdentityCosetMap_commutes K L hLK φ σ p).symm
      _ = eSigma (D.frobeniusNormIdentityCosetMap K L hLK φ σ q) :=
        congrArg eSigma hpq
      _ = eP (eI q.1, q.2) :=
        D.frobeniusNormIdentityCosetMap_commutes K L hLK φ σ q
  have hsurj : Function.Surjective (D.frobeniusNormIdentityCosetMap K L hLK φ σ) := by
    intro q
    obtain ⟨p, hp⟩ := eP.surjective (eSigma q)
    obtain ⟨r, hr⟩ := (Equiv.prodCongr eI (Equiv.refl _)).surjective p
    refine ⟨r, ?_⟩
    apply eSigma.injective
    calc
      eSigma (D.frobeniusNormIdentityCosetMap K L hLK φ σ r) =
          eP (eI r.1, r.2) :=
        D.frobeniusNormIdentityCosetMap_commutes K L hLK φ σ r
      _ = eP p := by
        apply congrArg eP
        exact hr
      _ = eSigma q := hp
  exact ⟨hinj, hsurj⟩

/-- Defines `frobeniusNormIdentityCosetEquiv`. -/
noncomputable def frobeniusNormIdentityCosetEquiv (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) ×
        Fin (D.frobeniusExponent K L hLK σ) ≃
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) :=
  Equiv.ofBijective (D.frobeniusNormIdentityCosetMap K L hLK φ σ)
    (D.frobeniusNormIdentityCosetMap_bijective K L hLK φ σ hφ)

end DegreeData

end frobeniusCosetEquivalences

section frobeniusNormIdentities

/-!
Mathlib's `Rep ℤ G` requires the coefficient ring and acting group to share
a universe; `IntegralRepGroupType` names that shared boundary.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

private theorem relativeCosetAction_frobeniusNormIdentityCosetEquiv
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ))
    (r : (D.maximalUnramifiedField K.field).toSubgroup ⧸
      extensionSubgroup (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK))
    (i : Fin (D.frobeniusExponent K L hLK σ)) :
    relativeCosetAction A K.field (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ) a
        (D.frobeniusNormIdentityCosetEquiv K L hLK φ σ hφ (r, i)) =
      A.ρ (Quotient.out (φ.1 ^ i.1)).1
        (relativeCosetAction A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          (fixedFieldInclusion A
            (D.frobeniusFixedField K L hLK σ)
            (D.maximalUnramifiedField L)
            (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) r) := by
  let kφ : K.field.toSubgroup := Quotient.out (φ.1 ^ i.1)
  let kI : (D.maximalUnramifiedField K.field).toSubgroup := Quotient.out r
  let kIK : K.field.toSubgroup := ⟨kI.1, kI.2.1⟩
  change relativeCosetAction A K.field
      (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ) a
      (QuotientGroup.mk (kφ * kIK)) = _
  rw [relativeCosetAction_mk]
  have hr : r = QuotientGroup.mk kI := (Quotient.out_eq' r).symm
  rw [hr, relativeCosetAction_mk]
  change A.ρ (kφ.1 * kI.1) a.1 = A.ρ kφ.1 (A.ρ kI.1 a.1)
  rw [map_mul]
  rfl

private theorem frobeniusQuotientAction_relativeNorm (D : DegreeData G)
    (A : Rep ℤ G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hInertiaFintype : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK))]
    (φ : D.FrobeniusElements K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (i : ℕ) :
    ((D.frobeniusQuotientAction A K.field L hLK (φ.1 ^ i)
      (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK)
        (relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) a)) :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) =
      (@Finset.univ
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK))
        (Fintype.ofFinite _)).sum (fun r =>
          A.ρ (Quotient.out (φ.1 ^ i)).1
            (relativeCosetAction A (D.maximalUnramifiedField K.field)
              (D.maximalUnramifiedField L)
              (D.maximalUnramifiedField_mono hLK) a r)) := by
  let kφ : K.field.toSubgroup := Quotient.out (φ.1 ^ i)
  have hkφ : φ.1 ^ i = QuotientGroup.mk kφ :=
    (Quotient.out_eq' (φ.1 ^ i)).symm
  let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
    (relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) a)
  calc
    ((D.frobeniusQuotientAction A K.field L hLK (φ.1 ^ i) b :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) =
      (D.frobeniusQuotientAction A K.field L hLK
        (QuotientGroup.mk kφ) b : A.V) := by
          exact congrArg
            (fun q => (D.frobeniusQuotientAction A K.field L hLK q b : A.V)) hkφ
    _ = A.ρ kφ.1 b.1 := rfl
    _ = A.ρ kφ.1
        ((relativeNorm A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) a :
            ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field)) : A.V) := by
          rw [fixedFieldInclusion_coe]
    _ = A.ρ kφ.1
        (relativeNormValue A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) a) := by
          rw [relativeNorm_apply_coe]
    _ = A.ρ kφ.1
        ((@Finset.univ
          ((D.maximalUnramifiedField K.field).toSubgroup ⧸
            extensionSubgroup (D.maximalUnramifiedField K.field)
              (D.maximalUnramifiedField L)
              (D.maximalUnramifiedField_mono hLK))
          (Fintype.ofFinite _)).sum (fun r =>
            relativeCosetAction A (D.maximalUnramifiedField K.field)
              (D.maximalUnramifiedField L)
              (D.maximalUnramifiedField_mono hLK) a r)) := by
          rfl
    _ = (@Finset.univ
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK))
        (Fintype.ofFinite _)).sum (fun r => A.ρ kφ.1
          (relativeCosetAction A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK) a r)) := by
          rw [map_sum]

/-- The first norm identity of the Frobenius norm-identity lemma, in the order `φ_n ∘ N`. -/
theorem frobeniusNormIdentity_norm_eq_powerSum_norm (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
            (D.frobeniusFixedField_le K L hLK σ)) :=
      D.frobeniusFixedField_finite K L hLK σ
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K.field L hLK
    ((relativeNorm A K.field (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ) a :
        ambientFixedAddSubgroup A K.field) : A.V) =
      ((D.frobeniusPowerSum A K.field L hLK φ.1
        (D.frobeniusExponent K L hLK σ)
        (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)
            (fixedFieldInclusion A
              (D.frobeniusFixedField K L hLK σ)
              (D.maximalUnramifiedField L)
              (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a))) :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) :=
    D.frobeniusFixedField_finite K L hLK σ
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  let R := (D.maximalUnramifiedField K.field).toSubgroup ⧸
    extensionSubgroup (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
  let n := D.frobeniusExponent K L hLK σ
  let e := D.frobeniusNormIdentityCosetEquiv K L hLK φ σ hφ
  let aI := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a
  let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
    (relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI)
  let := Fintype.ofFinite R
  let := Fintype.ofFinite
    (K.field.toSubgroup ⧸
      extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ))
  rw [relativeNorm_apply_coe, relativeNormValue,
    D.frobeniusPowerSum_coe]
  calc
    ∑ q, relativeCosetAction A K.field
        (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ) a q =
      ∑ p : R × Fin n,
        relativeCosetAction A K.field
          (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ) a (e p) :=
      (e.sum_comp _).symm
    _ = ∑ p : R × Fin n,
        A.ρ (Quotient.out (φ.1 ^ p.2.1)).1
          (relativeCosetAction A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
            aI p.1) := by
      apply Finset.sum_congr rfl
      intro p _
      exact D.relativeCosetAction_frobeniusNormIdentityCosetEquiv
        A K L hLK φ σ hφ a p.1 p.2
    _ = ∑ i : Fin n, ∑ r : R,
        A.ρ (Quotient.out (φ.1 ^ i.1)).1
          (relativeCosetAction A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
            aI r) := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ = ∑ i : Fin n,
        (D.frobeniusQuotientAction A K.field L hLK (φ.1 ^ i.1) b : A.V) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (D.frobeniusQuotientAction_relativeNorm
        A K L hLK φ aI i.1).symm

/-- The second identity of the Frobenius norm-identity lemma:
`N_{\widetilde L/\widetilde K} ∘ φ_n =
  φ_n ∘ N_{\widetilde L/\widetilde K}`. -/
theorem frobeniusNormIdentity_norm_powerSum_eq_powerSum_norm (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hLfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    letI : Finite
        ((D.maximalUnramifiedField K).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K L hLK
    ((relativeNorm A (D.maximalUnramifiedField K)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      (D.frobeniusPowerSum A K L hLK φ n a) :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField K)) : A.V) =
      ((D.frobeniusPowerSum A K L hLK φ n
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
            a)) : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
        A.V) := by
  let : Finite
      ((D.maximalUnramifiedField K).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K L hLK
  change
    ((relativeNorm A (D.maximalUnramifiedField K)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK))
      (∑ i : Fin n, D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a)).1 =
      (∑ i : Fin n, D.frobeniusQuotientAction A K L hLK (φ ^ i.1)
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
            a))).1
  simp only [map_sum]
  change (ambientFixedAddSubgroup A
      (D.maximalUnramifiedField K)).subtype
      (∑ i : Fin n, relativeNorm A (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        (D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a)) =
    (ambientFixedAddSubgroup A
      (D.maximalUnramifiedField L)).subtype
      (∑ i : Fin n, D.frobeniusQuotientAction A K L hLK (φ ^ i.1)
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
            a)))
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact D.relativeNorm_frobeniusQuotientAction A K L hLK (φ ^ i.1) a

/-- **The Frobenius norm-identity lemma.**  For `d_K(φ)=1`, `d_K(σ)=n` and the
fixed field `Σ` of `σ`, the three actual norm expressions agree:
`N_{Σ/K}(a) = (N_{\widetilde L/\widetilde K} ∘ φ_n)(a) =
(φ_n ∘ N_{\widetilde L/\widetilde K})(a)`. -/
theorem frobeniusNormIdentities (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    letI : Finite
        (K.field.toSubgroup ⧸
          extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
            (D.frobeniusFixedField_le K L hLK σ)) :=
      D.frobeniusFixedField_finite K L hLK σ
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K.field L hLK
    let n := D.frobeniusExponent K L hLK σ
    let aI := fixedFieldInclusion A
      (D.frobeniusFixedField K L hLK σ)
      (D.maximalUnramifiedField L)
      (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a
    let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      (relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI)
    let φnAI := D.frobeniusPowerSum A K.field L hLK φ.1 n aI
    (((relativeNorm A K.field (D.frobeniusFixedField K L hLK σ)
      (D.frobeniusFixedField_le K L hLK σ) a :
        ambientFixedAddSubgroup A K.field) : A.V) =
      ((relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        φnAI : ambientFixedAddSubgroup A
          (D.maximalUnramifiedField K.field)) : A.V)) ∧
    (((relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      φnAI : ambientFixedAddSubgroup A
        (D.maximalUnramifiedField K.field)) : A.V) =
      ((D.frobeniusPowerSum A K.field L hLK φ.1 n b :
        ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V)) := by
  let : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field (D.frobeniusFixedField K L hLK σ)
          (D.frobeniusFixedField_le K L hLK σ)) :=
    D.frobeniusFixedField_finite K L hLK σ
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  let n := D.frobeniusExponent K L hLK σ
  let aI := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a
  let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
    (relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI)
  let φnAI := D.frobeniusPowerSum A K.field L hLK φ.1 n aI
  have hFirst :
      ((relativeNorm A K.field (D.frobeniusFixedField K L hLK σ)
        (D.frobeniusFixedField_le K L hLK σ) a :
          ambientFixedAddSubgroup A K.field) : A.V) =
        ((D.frobeniusPowerSum A K.field L hLK φ.1 n b :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) := by
    simpa [n, aI, b] using
      D.frobeniusNormIdentity_norm_eq_powerSum_norm A K L hLK φ σ hφ a
  have hCommute :
      ((relativeNorm A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        φnAI : ambientFixedAddSubgroup A
          (D.maximalUnramifiedField K.field)) : A.V) =
        ((D.frobeniusPowerSum A K.field L hLK φ.1 n b :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) := by
    simpa [n, aI, b, φnAI] using
      D.frobeniusNormIdentity_norm_powerSum_eq_powerSum_norm
        A K.field L hLK φ.1 n aI
  exact ⟨hFirst.trans hCommute.symm, hCommute⟩

end DegreeData
end frobeniusNormIdentities
end

end ClassFormation
