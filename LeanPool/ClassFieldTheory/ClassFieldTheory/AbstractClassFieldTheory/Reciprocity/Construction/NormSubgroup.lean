/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.IntegralRepUniverse

/-! # Norm Subgroup -/

@[expose] public section
universe u

namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity construction: norm subgroups for infinite extensions

For an infinite abstract extension `E | K`, the abstract class-field construction defines
`N_{E|K} A_E` as the intersection of the norm images from all finite
intermediate fields.  This file records that definition literally.
-/

noncomputable section

section finiteIntermediateFields

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A finite intermediate field `M` of an abstract extension `E | K`.
Contravariantly, its subgroup lies between `G_E` and `G_K`. -/
structure FiniteIntermediateField (E K : ClosedSubgroup G) where
  /-- The closed subgroup representing the intermediate field. -/
  field : ClosedSubgroup G
  /-- The extension endpoint lies below the intermediate-field subgroup. -/
  above : E.toSubgroup ≤ field.toSubgroup
  /-- The intermediate-field subgroup lies below the base endpoint. -/
  below : field.toSubgroup ≤ K.toSubgroup
  /-- The intermediate field has finite degree over the base endpoint. -/
  finite : Finite
    (K.toSubgroup ⧸ extensionSubgroup K field below)

namespace FiniteIntermediateField

/-- The base field itself is a finite intermediate field. -/
def base (E K : ClosedSubgroup G) (hEK : E.toSubgroup ≤ K.toSubgroup) :
    FiniteIntermediateField E K where
  field := K
  above := hEK
  below := le_rfl
  finite := by
    have htop : extensionSubgroup K K le_rfl = ⊤ := by
      ext x
      constructor
      · intro _
        trivial
      · intro _
        exact x.2
    rw [htop]
    infer_instance

end FiniteIntermediateField

end finiteIntermediateFields

section infiniteNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The norm image from a finite intermediate field `M` to `K`. -/
def finiteIntermediateNormRange
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (M : FiniteIntermediateField E K) :
    AddSubgroup (ambientFixedAddSubgroup A K) := by
  letI := M.finite
  exact (relativeNorm A K M.field M.below).range

/-- The norm subgroup for a possibly infinite extension:
`N_{E|K} A_E = ⋂_M N_{M|K} A_M`, where `M` runs through the finite
intermediate fields. -/
def infiniteNormSubgroup
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    AddSubgroup (ambientFixedAddSubgroup A K) :=
  ⨅ M : FiniteIntermediateField E K,
    finiteIntermediateNormRange A E K M

/-- Membership in the infinite norm subgroup is characterized by norms from every finite level. -/
@[simp]
theorem mem_infiniteNormSubgroup_iff
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    a ∈ infiniteNormSubgroup A E K ↔
      ∀ M : FiniteIntermediateField E K,
        a ∈ finiteIntermediateNormRange A E K M := by
  simp [infiniteNormSubgroup]

/-- The quotient `A_K / N_{E|K} A_E` used by the reciprocity map.

This public object is opaque: clients use `infiniteNormClass`,
`InfiniteNormQuotient.induction_on`, or `infiniteNormQuotientLift` instead of
depending on the concrete quotient representation. -/
def InfiniteNormQuotient
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :=
  ambientFixedAddSubgroup A K ⧸ infiniteNormSubgroup A E K

/-- The additive group structure on the infinite norm quotient. -/
instance infiniteNormQuotientAddCommGroup
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    AddCommGroup (InfiniteNormQuotient A E K) := by
  unfold InfiniteNormQuotient
  infer_instance

/-- The explicit boundary to the concrete quotient implementation. -/
def infiniteNormQuotientConcreteEquiv
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    InfiniteNormQuotient A E K ≃+
      ambientFixedAddSubgroup A K ⧸ infiniteNormSubgroup A E K := by
  unfold InfiniteNormQuotient
  exact AddEquiv.refl _

/-- The canonical class map into the infinite norm quotient. -/
def infiniteNormClass
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    ambientFixedAddSubgroup A K →+
      InfiniteNormQuotient A E K := by
  unfold InfiniteNormQuotient
  exact QuotientAddGroup.mk' (infiniteNormSubgroup A E K)

/-- The concrete infinite-norm quotient equivalence sends a class to its
canonical quotient class. -/
@[simp]
theorem infiniteNormQuotientConcreteEquiv_infiniteNormClass
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    infiniteNormQuotientConcreteEquiv A E K (infiniteNormClass A E K a) =
      QuotientAddGroup.mk' (infiniteNormSubgroup A E K) a := by
  rfl

/-- An infinite norm class vanishes exactly when its representative lies in the norm subgroup. -/
@[simp]
theorem infiniteNormClass_eq_zero_iff
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    infiniteNormClass A E K a = 0 ↔
      a ∈ infiniteNormSubgroup A E K := by
  unfold infiniteNormClass InfiniteNormQuotient
  exact QuotientAddGroup.eq_zero_iff a

/-- Every infinite norm-quotient class has an ambient representative. -/
theorem infiniteNormClass_surjective
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    Function.Surjective (infiniteNormClass A E K) := by
  intro q
  change ambientFixedAddSubgroup A K ⧸ infiniteNormSubgroup A E K at q
  obtain ⟨a, rfl⟩ :=
    QuotientAddGroup.mk'_surjective (infiniteNormSubgroup A E K) q
  exact ⟨a, rfl⟩

/-- Eliminate an infinite norm-quotient class through an ambient representative. -/
@[elab_as_elim]
theorem InfiniteNormQuotient.induction_on
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    {motive : InfiniteNormQuotient A E K → Prop}
    (q : InfiniteNormQuotient A E K)
    (h : ∀ a, motive (infiniteNormClass A E K a)) : motive q := by
  obtain ⟨a, rfl⟩ := infiniteNormClass_surjective A E K q
  exact h a

/-- Descend an additive homomorphism that kills the infinite norm subgroup. -/
def infiniteNormQuotientLift
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : infiniteNormSubgroup A E K ≤ f.ker) :
    InfiniteNormQuotient A E K →+ B := by
  unfold InfiniteNormQuotient
  exact QuotientAddGroup.lift (infiniteNormSubgroup A E K) f hf

/-- Lifting the canonical infinite norm class recovers its representative in the
concrete quotient. -/
@[simp]
theorem infiniteNormQuotientLift_infiniteNormClass
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : infiniteNormSubgroup A E K ≤ f.ker)
    (a : ambientFixedAddSubgroup A K) :
    infiniteNormQuotientLift A E K f hf (infiniteNormClass A E K a) = f a := by
  rfl

end infiniteNorms

section maximalUnramifiedFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The maximal unramified extension `\widetilde L`, represented by
`I_L = G_L ∩ ker(d)`. -/
def maximalUnramifiedField (D : DegreeData G) (L : ClosedSubgroup G) :
    ClosedSubgroup G :=
  D.fieldInertia L

/-- The implementation theorem identifying the maximal unramified field
with absolute inertia.  Downstream code should use this theorem instead of
unfolding `maximalUnramifiedField`. -/
theorem maximalUnramifiedField_eq_fieldInertia
    (D : DegreeData G) (L : ClosedSubgroup G) :
    D.maximalUnramifiedField L = D.fieldInertia L := by
  rfl

/-- Membership in the maximal unramified field is the expected inertia
condition. -/
@[simp]
theorem mem_maximalUnramifiedField_iff
    (D : DegreeData G) (L : ClosedSubgroup G) (g : G) :
    g ∈ D.maximalUnramifiedField L ↔ g ∈ L ∧ D.degree g = 1 := by
  rw [D.maximalUnramifiedField_eq_fieldInertia]
  exact D.mem_fieldInertia_iff L g

/-- Every finite unramified field lies below the maximal unramified field. -/
theorem maximalUnramifiedField_le (D : DegreeData G) (L : ClosedSubgroup G) :
    (D.maximalUnramifiedField L).toSubgroup ≤ L.toSubgroup := by
  rw [D.maximalUnramifiedField_eq_fieldInertia]
  exact inf_le_left

/-- A field containing all finite unramified fields contains the maximal unramified field. -/
theorem maximalUnramifiedField_le_of_le (D : DegreeData G)
    {L K : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (D.maximalUnramifiedField L).toSubgroup ≤ K.toSubgroup :=
  (D.maximalUnramifiedField_le L).trans hLK

/-- Monotonicity of maximal unramified fields. -/
theorem maximalUnramifiedField_mono (D : DegreeData G)
    {K L : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (D.maximalUnramifiedField L).toSubgroup ≤
      (D.maximalUnramifiedField K).toSubgroup := by
  intro g hg
  have hg' : g ∈ D.maximalUnramifiedField L := hg
  obtain ⟨hgL, hgd⟩ := (D.mem_maximalUnramifiedField_iff L g).1 hg'
  exact (D.mem_maximalUnramifiedField_iff K g).2 ⟨hLK hgL, hgd⟩

/-- Inside `G_K`, the absolute subgroup of `\widetilde L` is the relative
inertia subgroup. -/
theorem extensionSubgroup_maximalUnramifiedField (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    extensionSubgroup K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK) =
      D.extensionInertiaWithin K L hLK := by
  ext k
  constructor
  · intro hk
    have hkMax : k.1 ∈ D.maximalUnramifiedField L :=
      (mem_extensionSubgroup_iff K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK) k).1 hk
    have hkData := (D.mem_maximalUnramifiedField_iff L k.1).1 hkMax
    exact ⟨(mem_extensionSubgroup_iff K L hLK k).2 hkData.1,
      (D.mem_fieldInertiaWithin_iff K k).2 hkData.2⟩
  · intro hk
    apply (mem_extensionSubgroup_iff K (D.maximalUnramifiedField L)
      (D.maximalUnramifiedField_le_of_le hLK) k).2
    apply (D.mem_maximalUnramifiedField_iff L k.1).2
    exact ⟨(mem_extensionSubgroup_iff K L hLK k).1 hk.1,
      (D.mem_fieldInertiaWithin_iff K k).1 hk.2⟩

/-- The subgroup representing the maximal unramified field is normal in the base subgroup. -/
theorem extensionSubgroup_maximalUnramifiedField_normal (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    (extensionSubgroup K (D.maximalUnramifiedField L)
      (D.maximalUnramifiedField_le_of_le hLK)).Normal := by
  rw [D.extensionSubgroup_maximalUnramifiedField K L hLK]
  infer_instance

end DegreeData

end maximalUnramifiedFields

section maximalUnramifiedNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- `N_{\widetilde L|K} A_{\widetilde L}` in the reciprocity construction. -/
def maximalUnramifiedNormSubgroup (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) :
    AddSubgroup (ambientFixedAddSubgroup A K) :=
  infiniteNormSubgroup A (D.maximalUnramifiedField L) K

/-- The maximal-unramified norm subgroup is the infinite norm subgroup for
the maximal unramified field. -/
theorem maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    D.maximalUnramifiedNormSubgroup A K L =
      infiniteNormSubgroup A (D.maximalUnramifiedField L) K := by
  rfl

/-- Membership in the maximal unramified norm subgroup is characterized levelwise. -/
@[simp]
theorem mem_maximalUnramifiedNormSubgroup_iff
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    a ∈ D.maximalUnramifiedNormSubgroup A K L ↔
      a ∈ infiniteNormSubgroup A (D.maximalUnramifiedField L) K := by
  rw [D.maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup]

/-- `A_K / N_{\widetilde L|K} A_{\widetilde L}`.

This is an opaque public object, not a reducible alias for the infinite norm
quotient. -/
def MaximalUnramifiedNormQuotient (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) :=
  InfiniteNormQuotient A (D.maximalUnramifiedField L) K

/-- The additive group structure on the maximal-unramified norm quotient. -/
instance maximalUnramifiedNormQuotientAddCommGroup
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    AddCommGroup (D.MaximalUnramifiedNormQuotient A K L) := by
  unfold MaximalUnramifiedNormQuotient
  infer_instance

/-- The explicit boundary to the corresponding infinite norm quotient. -/
def maximalUnramifiedNormQuotientInfiniteEquiv
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    D.MaximalUnramifiedNormQuotient A K L ≃+
      InfiniteNormQuotient A (D.maximalUnramifiedField L) K := by
  unfold MaximalUnramifiedNormQuotient
  exact AddEquiv.refl _

/-- The canonical class map into the maximal-unramified norm quotient. -/
def maximalUnramifiedNormClass
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    ambientFixedAddSubgroup A K →+
      D.MaximalUnramifiedNormQuotient A K L := by
  unfold MaximalUnramifiedNormQuotient
  exact infiniteNormClass A (D.maximalUnramifiedField L) K

/-- The infinite quotient equivalence preserves the canonical maximal-unramified norm class. -/
@[simp]
theorem maximalUnramifiedNormQuotientInfiniteEquiv_maximalUnramifiedNormClass
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    D.maximalUnramifiedNormQuotientInfiniteEquiv A K L
        (D.maximalUnramifiedNormClass A K L a) =
      infiniteNormClass A (D.maximalUnramifiedField L) K a := by
  rfl

/-- A maximal-unramified norm class vanishes exactly on its defining norm subgroup. -/
@[simp]
theorem maximalUnramifiedNormClass_eq_zero_iff
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    D.maximalUnramifiedNormClass A K L a = 0 ↔
      a ∈ D.maximalUnramifiedNormSubgroup A K L := by
  unfold maximalUnramifiedNormClass MaximalUnramifiedNormQuotient
  exact infiniteNormClass_eq_zero_iff A (D.maximalUnramifiedField L) K a

/-- Every maximal-unramified norm class has an ambient representative. -/
theorem maximalUnramifiedNormClass_surjective
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    Function.Surjective (D.maximalUnramifiedNormClass A K L) := by
  intro q
  change InfiniteNormQuotient A (D.maximalUnramifiedField L) K at q
  obtain ⟨a, ha⟩ :=
    infiniteNormClass_surjective A (D.maximalUnramifiedField L) K q
  exact ⟨a, ha⟩

/-- Eliminate a maximal-unramified norm class through an ambient representative. -/
@[elab_as_elim]
theorem MaximalUnramifiedNormQuotient.induction_on
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    {motive : D.MaximalUnramifiedNormQuotient A K L → Prop}
    (q : D.MaximalUnramifiedNormQuotient A K L)
    (h : ∀ a, motive (D.maximalUnramifiedNormClass A K L a)) : motive q := by
  obtain ⟨a, rfl⟩ := D.maximalUnramifiedNormClass_surjective A K L q
  exact h a

/-- Descend an additive homomorphism that kills the maximal-unramified norm subgroup. -/
def maximalUnramifiedNormQuotientLift
    {B : Type*} [AddCommGroup B]
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : D.maximalUnramifiedNormSubgroup A K L ≤ f.ker) :
    D.MaximalUnramifiedNormQuotient A K L →+ B := by
  unfold MaximalUnramifiedNormQuotient
  refine infiniteNormQuotientLift A (D.maximalUnramifiedField L) K f ?_
  intro a ha
  exact hf ((D.mem_maximalUnramifiedNormSubgroup_iff A K L a).2 ha)

/-- The quotient lift sends a maximal-unramified norm class back to its representative. -/
@[simp]
theorem maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass
    {B : Type*} [AddCommGroup B]
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : D.maximalUnramifiedNormSubgroup A K L ≤ f.ker)
    (a : ambientFixedAddSubgroup A K) :
    D.maximalUnramifiedNormQuotientLift A K L f hf
        (D.maximalUnramifiedNormClass A K L a) = f a := by
  unfold maximalUnramifiedNormQuotientLift maximalUnramifiedNormClass
    MaximalUnramifiedNormQuotient
  exact infiniteNormQuotientLift_infiniteNormClass
    A (D.maximalUnramifiedField L) K f (by
      intro b hb
      exact hf ((D.mem_maximalUnramifiedNormSubgroup_iff A K L b).2 hb)) a

end DegreeData

end maximalUnramifiedNorms

end
end ClassFormation
