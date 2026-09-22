/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.NormTopology
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.IntegralRepUniverse
/-!
# A finite class-field candidate from a norm-open subgroup

This file isolates the source-producing part of finite-classification surjectivity.
An open subgroup `H ≤ A_K` contains an actual finite Galois
norm subgroup.  Modulo that norm subgroup, `H` gives a concrete subgroup.
Transporting this subgroup to the additive abelianization and pulling it
back along `Q → Qᵃᵇ` gives a subgroup of the actual finite Galois quotient
which contains its commutator.  The finite Galois correspondence then cuts
out an actual finite abelian intermediate extension.

The equivalence used for the transport is an explicit argument of the
construction. A later specialization supplies it from finite reciprocity for
the reciprocity map.  No existence statement, norm-kernel equality, or
classification conclusion depending on that specialization is
asserted here.
-/

noncomputable section

namespace ClassFormation

open CyclicCohomology KummerTheory
open scoped commutatorElement

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ## The finite level beneath an open norm-topology subgroup -/

omit [IsTopologicalGroup G] in
/-- The first step in the proof of the finite abelian classification theorem: an open subgroup
in the
norm topology contains the norm subgroup of an actual finite Galois
extension. -/
theorem normOpenAddSubgroup_contains_finiteNormSubgroup
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (hH : IsNormOpen A K H) :
    ∃ E : FiniteGaloisSubextension K, ClassFormation.FiniteGaloisSubextension.normSubgroup A E ≤
      H :=
  (normTopology_addSubgroup_isOpen_iff A K H).1 hH

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

local instance normQuotient_extensionQuotient_finite
    (E : FiniteGaloisSubextension K) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K E.field E.below) :=
  E.finite

/-- The subgroup `H / N_E` of the actual norm quotient, represented as
the image of `H` under the quotient map. -/
def normQuotientSubgroup
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K)) :
    AddSubgroup (FiniteNormQuotient A K E.field E.below) := by
  letI : Finite (K.toSubgroup ⧸
      extensionSubgroup K E.field E.below) := E.finite
  exact H.map (finiteNormClassHom A K E.field E.below)

omit [IsTopologicalGroup G] in
/-- If `N_E ⊆ H`, then `H` is exactly the full inverse image of
`H / N_E`.  This is the group-theoretic fact used in the middle of the
finite-classification surjectivity proof. -/
theorem finiteNormClass_mem_normQuotientSubgroup_iff
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (hEH : ClassFormation.FiniteGaloisSubextension.normSubgroup A E ≤ H)
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite (K.toSubgroup ⧸
        extensionSubgroup K E.field E.below) := E.finite
    finiteNormClass A K E.field E.below a ∈
        normQuotientSubgroup A E H ↔
      a ∈ H := by
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K E.field E.below) := E.finite
  constructor
  · rintro ⟨b, hb, hba⟩
    have hba' : finiteNormClass A K E.field E.below b =
        finiteNormClass A K E.field E.below a := by
      simpa [finiteNormClass] using hba
    have hzero : finiteNormClass A K E.field E.below (b - a) = 0 := by
      rw [finiteNormClass_sub, hba', sub_self]
    have hsub : b - a ∈ ClassFormation.FiniteGaloisSubextension.normSubgroup A E :=
      (finiteNormClass_eq_zero_iff A K E.field E.below (b - a)).1 hzero
    have hsubH : b - a ∈ H := hEH hsub
    have ha : a = b - (b - a) := by abel
    rw [ha]
    exact H.sub_mem hb hsubH
  · intro ha
    exact ⟨a, ha, rfl⟩

/-! ## Transport to the abelianized finite quotient -/

/-- Transport `H / N_E` through a specified finite reciprocity
equivalence and forget additive notation.  This is a genuine subgroup of
the actual abelianization `G(E/K)ᵃᵇ`.

The argument `rE` is kept explicit: this definition does not construct the
finite reciprocity equivalence. -/
def reciprocityAbelianizedSubgroup
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    Subgroup (Abelianization E.extensionQuotient) := by
  letI : Finite (K.toSubgroup ⧸
      extensionSubgroup K E.field E.below) := E.finite
  exact AddSubgroup.toSubgroup'
    ((normQuotientSubgroup A E H).map rE.toAddMonoidHom)

omit [IsTopologicalGroup G] in
/-- Membership in the transported subgroup is literal membership of the
corresponding reciprocity class in the image of `H / N_E`. -/
theorem mem_reciprocityAbelianizedSubgroup_iff
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (q : Abelianization E.extensionQuotient) :
    q ∈ reciprocityAbelianizedSubgroup A E H rE ↔
      ∃ z ∈ normQuotientSubgroup A E H,
        rE z = Additive.ofMul q := by
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K E.field E.below) := E.finite
  rfl

/-- The representative-level abelianized class map obtained by first
passing to `A_K / N_E` and then applying the specified equivalence. -/
def reciprocityAbelianizedClassHom
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    ambientFixedAddSubgroup A K →+
      Additive (Abelianization E.extensionQuotient) :=
  rE.toAddMonoidHom.comp (finiteNormClassHom A K E.field E.below)

omit [IsTopologicalGroup G] in
/-- If `N_E ⊆ H`, the transported subgroup has exactly `H` as its
inverse image under the abelianized class map.  This is the precise
full-preimage statement used before taking the fixed field in the finite classification argument. -/
theorem reciprocityClass_mem_abelianizedSubgroup_iff
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (hEH : ClassFormation.FiniteGaloisSubextension.normSubgroup A E ≤ H)
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (a : ambientFixedAddSubgroup A K) :
    Additive.toMul (reciprocityAbelianizedClassHom A E rE a) ∈
        reciprocityAbelianizedSubgroup A E H rE ↔
      a ∈ H := by
  change rE (finiteNormClass A K E.field E.below a) ∈
      (normQuotientSubgroup A E H).map rE.toAddMonoidHom ↔
    a ∈ H
  constructor
  · rintro ⟨z, hz, hza⟩
    have hzEq : z = finiteNormClass A K E.field E.below a :=
      rE.injective hza
    rw [hzEq] at hz
    exact (finiteNormClass_mem_normQuotientSubgroup_iff A E H hEH a).1 hz
  · intro ha
    refine ⟨finiteNormClass A K E.field E.below a, ?_, rfl⟩
    exact (finiteNormClass_mem_normQuotientSubgroup_iff A E H hEH a).2 ha

end FiniteGaloisSubextension

/-! ## From a subgroup above the commutator to an abelian field -/

/-- Pull a subgroup of an abelianization back to the original finite
Galois group. -/
def abelianizationPreimageSubgroup
    {Q : Type*} [Group Q] (T : Subgroup (Abelianization Q)) :
    Subgroup Q :=
  T.comap (Abelianization.of : Q →* Abelianization Q)

/-- Every such pullback contains the commutator subgroup. -/
theorem commutator_le_abelianizationPreimageSubgroup
    {Q : Type*} [Group Q] (T : Subgroup (Abelianization Q)) :
    commutator Q ≤ abelianizationPreimageSubgroup T := by
  intro q hq
  change Abelianization.of q ∈ T
  have hk : q ∈
      MonoidHom.ker (Abelianization.of : Q →* Abelianization Q) :=
    Abelianization.commutator_subset_ker
      (Abelianization.of : Q →* Abelianization Q) hq
  rw [MonoidHom.mem_ker.mp hk]
  exact T.one_mem

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

local instance candidate_extensionQuotient_finite
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : ClosedSubgroup G} (E : FiniteGaloisSubextension K) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K E.field E.below) :=
  E.finite

/-- The actual finite abelian intermediate extension cut out by a subgroup
`S ≤ G(E/K)` containing the commutator. -/
def intermediateFiniteAbelianOfCommutatorLe
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : ClosedSubgroup G}
    (E : FiniteGaloisSubextension K)
    (S : Subgroup E.extensionQuotient)
    (hS : commutator E.extensionQuotient ≤ S) :
    FiniteAbelianSubextension K := by
  let hnormal : S.Normal :=
    Subgroup.Normal.of_commutator_le E.extensionQuotient hS
  letI : S.Normal := hnormal
  let M := E.intermediateFiniteGalois S hnormal
  refine
    { toFiniteGaloisExtension := M
      commutative := ?_ }
  let e := E.upperQuotientEquiv S
  let : IsMulCommutative (E.extensionQuotient ⧸ S) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 hS
  refine ⟨⟨?_⟩⟩
  intro x y
  obtain ⟨x', rfl⟩ := e.surjective x
  obtain ⟨y', rfl⟩ := e.surjective y
  calc
    e x' * e y' = e (x' * y') := (map_mul e x' y').symm
    _ = e (y' * x') := congrArg e
      (Std.Commutative.comm
        (op := fun a b : E.extensionQuotient ⧸ S => a * b) x' y')
    _ = e y' * e x' := map_mul e y' x'

/-- The field underlying the preceding package is the literal fixed field
of `S`. -/
@[simp]
theorem intermediateFiniteAbelianOfCommutatorLe_field
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : ClosedSubgroup G}
    (E : FiniteGaloisSubextension K)
    (S : Subgroup E.extensionQuotient)
    (hS : commutator E.extensionQuotient ≤ S) :
    (intermediateFiniteAbelianOfCommutatorLe E S hS).field =
      E.intermediateField S :=
  rfl

/-- The subgroup obtained from `H / N_E` on the abelianization side,
pulled back to the actual finite Galois quotient. -/
def reciprocityPreimageSubgroup
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    Subgroup E.extensionQuotient :=
  abelianizationPreimageSubgroup
    (reciprocityAbelianizedSubgroup A E H rE)

omit [IsTopologicalGroup G] in
/-- The actual subgroup used to define the intermediate field contains
the commutator, independently of any kernel assertion for `rE`. -/
theorem commutator_le_reciprocityPreimageSubgroup
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    commutator E.extensionQuotient ≤
      reciprocityPreimageSubgroup A E H rE :=
  commutator_le_abelianizationPreimageSubgroup _

omit [IsTopologicalGroup G] in
/-- The pulled-back subgroup has exactly `H` as the inverse image of the
representative-level reciprocity class.  This is the group-side form of the
full-preimage assertion used in the finite-classification surjectivity proof. -/
theorem reciprocityClass_mem_preimageSubgroup_iff
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (hEH : ClassFormation.FiniteGaloisSubextension.normSubgroup A E ≤ H)
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (a : ambientFixedAddSubgroup A K) :
    Quotient.out (Additive.toMul
        (reciprocityAbelianizedClassHom A E rE a)) ∈
        reciprocityPreimageSubgroup A E H rE ↔
      a ∈ H := by
  change Abelianization.of (Quotient.out (Additive.toMul
      (reciprocityAbelianizedClassHom A E rE a))) ∈
        reciprocityAbelianizedSubgroup A E H rE ↔ a ∈ H
  rw [show Abelianization.of (Quotient.out (Additive.toMul
      (reciprocityAbelianizedClassHom A E rE a))) =
        Additive.toMul (reciprocityAbelianizedClassHom A E rE a) by
      exact Quotient.out_eq' _]
  exact reciprocityClass_mem_abelianizedSubgroup_iff A E H hEH rE a

omit [IsTopologicalGroup G] in
/-- Equivalently, the representative of the transported reciprocity class
restricts trivially to the quotient cut out by the candidate precisely for
the elements of `H`. -/
theorem candidateQuotient_eq_one_iff
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (hEH : ClassFormation.FiniteGaloisSubextension.normSubgroup A E ≤ H)
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (a : ambientFixedAddSubgroup A K) :
    let S := reciprocityPreimageSubgroup A E H rE
    letI : S.Normal := Subgroup.Normal.of_commutator_le E.extensionQuotient
      (commutator_le_reciprocityPreimageSubgroup A E H rE)
    QuotientGroup.mk' S
        (Quotient.out (Additive.toMul
          (reciprocityAbelianizedClassHom A E rE a))) = 1 ↔
      a ∈ H := by
  dsimp only
  let : (reciprocityPreimageSubgroup A E H rE).Normal :=
    Subgroup.Normal.of_commutator_le E.extensionQuotient
      (commutator_le_reciprocityPreimageSubgroup A E H rE)
  constructor
  · intro h
    apply (reciprocityClass_mem_preimageSubgroup_iff
      A E H hEH rE a).1
    exact (QuotientGroup.eq_one_iff _).1 h
  · intro ha
    apply (QuotientGroup.eq_one_iff _).2
    exact (reciprocityClass_mem_preimageSubgroup_iff
      A E H hEH rE a).2 ha

/-- The finite abelian intermediate extension determined by the subgroup
transported from `H / N_E`.  This is the field candidate in the
surjectivity proof of the finite abelian classification theorem.  No claim that its norm
  subgroup equals
`H` is made before finite reciprocity is available. -/
def classFieldCandidate
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    FiniteAbelianSubextension K :=
  intermediateFiniteAbelianOfCommutatorLe E
    (reciprocityPreimageSubgroup A E H rE)
    (commutator_le_reciprocityPreimageSubgroup A E H rE)

/-- The candidate is cut out by the explicit pulled-back subgroup, not by
an opaque correspondence object. -/
@[simp]
theorem classFieldCandidate_field
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    (classFieldCandidate A E H rE).field =
      E.intermediateField
        (reciprocityPreimageSubgroup A E H rE) :=
  by
    exact intermediateFiniteAbelianOfCommutatorLe_field E
      (reciprocityPreimageSubgroup A E H rE)
      (commutator_le_reciprocityPreimageSubgroup A E H rE)

end FiniteGaloisSubextension

end ClassFormation
