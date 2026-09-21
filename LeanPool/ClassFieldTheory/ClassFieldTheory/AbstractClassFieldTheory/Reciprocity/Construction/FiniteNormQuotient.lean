/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.IntegralRepUniverse

/-! # Finite Norm Quotient -/
universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction: passage to a finite norm quotient

For finite `L | K`, the universal norm subgroup from `\widetilde L` is
contained in the single norm image from `L`.  Hence the reciprocity construction descends
canonically to `A_K / N_{L|K}A_L`, the target in the finite reciprocity equivalence.
-/

noncomputable section

section finiteNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The finite norm subgroup `N_{L|K}A_L`. -/
def finiteNormSubgroup (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    AddSubgroup (ambientFixedAddSubgroup A K) :=
  (relativeNorm A K L hLK).range

/-- The finite norm quotient in the finite reciprocity equivalence.

This is a stable public object rather than an `abbrev`: downstream APIs do
not acquire a reducibility dependency on the concrete quotient
representation. -/
def FiniteNormQuotient (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :=
  ambientFixedAddSubgroup A K ⧸ finiteNormSubgroup A K L hLK

/-- The additive group structure of the finite norm quotient.  It is
exported explicitly so typeclass search does not unfold the stable public
type synonym. -/
instance finiteNormQuotientAddCommGroup
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    AddCommGroup (FiniteNormQuotient A K L hLK) := by
  unfold FiniteNormQuotient
  infer_instance

/-- The canonical equivalence with the concrete quotient implementation.
Clients that genuinely need quotient-level operations can use this boundary
without relying on reducible unfolding. -/
def finiteNormQuotientConcreteEquiv
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    FiniteNormQuotient A K L hLK ≃+
      ambientFixedAddSubgroup A K ⧸ finiteNormSubgroup A K L hLK := by
  unfold FiniteNormQuotient
  exact AddEquiv.refl _

/-- The canonical class map into the finite norm quotient. -/
def finiteNormClassHom
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    ambientFixedAddSubgroup A K →+ FiniteNormQuotient A K L hLK := by
  unfold FiniteNormQuotient
  exact QuotientAddGroup.mk' (finiteNormSubgroup A K L hLK)

/-- The class of an element modulo the finite norm subgroup. -/
def finiteNormClass
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A K) :
    FiniteNormQuotient A K L hLK :=
  finiteNormClassHom A K L hLK a

/-- The finite norm-class map sends zero to the trivial quotient class. -/
@[simp]
theorem finiteNormClass_zero
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    finiteNormClass A K L hLK 0 = 0 := by
  exact map_zero (finiteNormClassHom A K L hLK)

/-- Finite norm classes preserve addition of representatives. -/
@[simp]
theorem finiteNormClass_add
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a b : ambientFixedAddSubgroup A K) :
    finiteNormClass A K L hLK (a + b) =
      finiteNormClass A K L hLK a + finiteNormClass A K L hLK b := by
  exact map_add (finiteNormClassHom A K L hLK) a b

/-- Finite norm classes preserve subtraction of representatives. -/
@[simp]
theorem finiteNormClass_sub
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a b : ambientFixedAddSubgroup A K) :
    finiteNormClass A K L hLK (a - b) =
      finiteNormClass A K L hLK a - finiteNormClass A K L hLK b := by
  exact map_sub (finiteNormClassHom A K L hLK) a b

/-- Finite norm classes commute with natural scalar multiplication. -/
@[simp]
theorem finiteNormClass_nsmul
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (n : ℕ) (a : ambientFixedAddSubgroup A K) :
    finiteNormClass A K L hLK (n • a) =
      n • finiteNormClass A K L hLK a := by
  exact map_nsmul (finiteNormClassHom A K L hLK) n a

/-- The concrete quotient equivalence sends a finite norm class to its canonical coset. -/
@[simp]
theorem finiteNormQuotientConcreteEquiv_finiteNormClass
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A K) :
    finiteNormQuotientConcreteEquiv A K L hLK
        (finiteNormClass A K L hLK a) =
      QuotientAddGroup.mk' (finiteNormSubgroup A K L hLK) a := by
  rfl

/-- A finite norm class vanishes exactly when its representative lies in the norm subgroup. -/
@[simp]
theorem finiteNormClass_eq_zero_iff
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A K) :
    finiteNormClass A K L hLK a = 0 ↔
      a ∈ finiteNormSubgroup A K L hLK := by
  unfold finiteNormClass finiteNormClassHom FiniteNormQuotient
  exact QuotientAddGroup.eq_zero_iff _

/-- Every finite norm-quotient class has an ambient representative. -/
theorem finiteNormClass_surjective
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Function.Surjective (finiteNormClass A K L hLK) := by
  intro q
  change ambientFixedAddSubgroup A K ⧸
    finiteNormSubgroup A K L hLK at q
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
    (finiteNormSubgroup A K L hLK) q
  exact ⟨a, rfl⟩

/-- Eliminate a finite norm-quotient class through an ambient representative. -/
@[elab_as_elim]
theorem FiniteNormQuotient.induction_on
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    {motive : FiniteNormQuotient A K L hLK → Prop}
    (q : FiniteNormQuotient A K L hLK)
    (h : ∀ a, motive (finiteNormClass A K L hLK a)) : motive q := by
  obtain ⟨a, rfl⟩ := finiteNormClass_surjective A K L hLK q
  exact h a

/-- Descend an additive homomorphism that kills the finite norm subgroup. -/
def finiteNormQuotientLift
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : finiteNormSubgroup A K L hLK ≤ f.ker) :
    FiniteNormQuotient A K L hLK →+ B := by
  unfold FiniteNormQuotient
  exact QuotientAddGroup.lift (finiteNormSubgroup A K L hLK) f hf

/-- The quotient lift evaluates on a finite norm class by the chosen representative. -/
@[simp]
theorem finiteNormQuotientLift_finiteNormClass
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : finiteNormSubgroup A K L hLK ≤ f.ker)
    (a : ambientFixedAddSubgroup A K) :
    finiteNormQuotientLift A K L hLK f hf
        (finiteNormClass A K L hLK a) = f a := by
  rfl

/-- Every class in the finite norm quotient is killed by `[L : K]`.
This is the actual norm identity
`N_{L/K}(a) = [L : K] a` for an element already fixed by `G_K`. -/
theorem finiteNormQuotient_degree_nsmul_eq_zero
    (A : Rep ℤ G) (E : DegreeData.FiniteAbstractExtension G)
    (q : FiniteNormQuotient A E.base E.field E.below) :
    (E.degree : ℕ) • q = 0 := by
  refine FiniteNormQuotient.induction_on A E.base E.field E.below q ?_
  intro a
  unfold finiteNormClass
  rw [← map_nsmul]
  apply (finiteNormClass_eq_zero_iff A E.base E.field E.below _).2
  refine ⟨fixedFieldInclusion A E.base E.field E.below a, ?_⟩
  exact relativeNorm_fixedFieldInclusion A E a

end finiteNorms

section finiteIntermediateField

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- `L` itself is a finite intermediate field of `\widetilde L | K`. -/
def fieldAsMaximalUnramifiedIntermediate (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    FiniteIntermediateField (D.maximalUnramifiedField L) K where
  field := L
  above := D.maximalUnramifiedField_le L
  below := hLK
  finite := hfinite

end DegreeData

end finiteIntermediateField

section quotientMaps

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The defining intersection for the infinite norm subgroup is contained
in the norm image from the particular finite field `L`. -/
theorem maximalUnramifiedNormSubgroup_le_finiteNormSubgroup
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    D.maximalUnramifiedNormSubgroup A K L ≤
      finiteNormSubgroup A K L hLK := by
  rw [D.maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup]
  rw [infiniteNormSubgroup]
  refine iInf_le_of_le (D.fieldAsMaximalUnramifiedIntermediate K L hLK) ?_
  rfl

private theorem maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    D.maximalUnramifiedNormSubgroup A K L ≤
      (finiteNormClassHom A K L hLK).ker := by
  intro a ha
  exact (finiteNormClass_eq_zero_iff A K L hLK a).2
    (D.maximalUnramifiedNormSubgroup_le_finiteNormSubgroup A K L hLK ha)

/-- The canonical quotient map
`A_K/N_{\widetilde L|K}A_{\widetilde L} → A_K/N_{L|K}A_L`. -/
def maximalUnramifiedToFiniteNormQuotient
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    D.MaximalUnramifiedNormQuotient A K L →+
      FiniteNormQuotient A K L hLK :=
  D.maximalUnramifiedNormQuotientLift A K L
    (finiteNormClassHom A K L hLK)
    (D.maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker A K L hLK)

/-- The comparison to a finite norm quotient carries the maximal-unramified
class to its finite-level class. -/
@[simp]
theorem maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : ambientFixedAddSubgroup A K) :
    D.maximalUnramifiedToFiniteNormQuotient A K L hLK
        (D.maximalUnramifiedNormClass A K L a) =
      finiteNormClass A K L hLK a := by
  exact D.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass
    A K L (finiteNormClassHom A K L hLK)
    (D.maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker A K L hLK) a

end DegreeData

end quotientMaps

end
end ClassFormation
