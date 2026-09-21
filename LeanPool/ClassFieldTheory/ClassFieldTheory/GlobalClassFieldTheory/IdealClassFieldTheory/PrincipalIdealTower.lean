/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormConjugation
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldCandidate
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction
/-!
# Galois structure on a conjugate-stable abelian tower

The principal ideal theorem uses two successive finite abelian class fields.
The upper field is Galois over the original base once its absolute Galois
subgroup is stable under conjugation by the base subgroup.  This file packages
that actual subgroup statement as a finite Galois subextension, so that the
commutator-intermediate-field and transfer APIs can be applied to the tower.
-/

noncomputable section

universe u

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation KummerTheory

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {K : ClosedSubgroup G}

section Conjugation

variable [ContinuousMul G]

/-- Conjugation by an element of a closed subgroup preserves that
subgroup.  This is the subgroup form of the fact that every field
automorphism over the base fixes the base field setwise. -/
theorem conjugateClosedSubgroup_eq_self_of_mem
    (K : ClosedSubgroup G) {s : G} (hs : s ∈ K) :
    conjugateClosedSubgroup K s = K := by
  ext x
  change x ∈ conjugateClosedSubgroup K s ↔ x ∈ K
  rw [conjugateClosedSubgroup_mem]
  constructor
  · intro hx
    have hmem :=
      K.mul_mem (K.mul_mem (K.inv_mem hs) hx) hs
    change x ∈ K.toSubgroup
    simpa [mul_assoc] using hmem
  · intro hx
    exact K.mul_mem (K.mul_mem hs hx) (K.inv_mem hs)

/-- Conjugating both endpoints of a finite abelian extension produces
the actual conjugate finite abelian extension. -/
def conjugateFiniteAbelianSubextension
    (L : FiniteAbelianSubextension K) (s : G) :
    FiniteAbelianSubextension (conjugateClosedSubgroup K s) where
  toFiniteGaloisExtension :=
    { field := conjugateClosedSubgroup L.field s
      below := conjugateClosedSubgroup_mono L.below s
      normal := by
        let :
            (CyclicCohomology.extensionSubgroup K L.field L.below).Normal :=
          L.normal
        infer_instance
      finite := by
        let : Finite
            (K.toSubgroup ⧸
              CyclicCohomology.extensionSubgroup K L.field L.below) :=
          L.finite
        exact finite_conjugateExtension K L.field L.below s }
  commutative := by
    let : (CyclicCohomology.extensionSubgroup K L.field L.below).Normal :=
      L.normal
    let e :=
      finiteReciprocityNaturalityConjugation K L.field L.below s
    refine ⟨⟨?_⟩⟩
    intro x y
    obtain ⟨x', rfl⟩ := e.surjective x
    obtain ⟨y', rfl⟩ := e.surjective y
    calc
      e x' * e y' = e (x' * y') := (map_mul e x' y').symm
      _ = e (y' * x') := congrArg e (L.commutative.is_comm.comm _ _)
      _ = e y' * e x' := map_mul e y' x'

@[simp]
theorem conjugateFiniteAbelianSubextension_field
    (L : FiniteAbelianSubextension K) (s : G) :
    (conjugateFiniteAbelianSubextension L s).field =
      conjugateClosedSubgroup L.field s :=
  rfl

/-- Two successive finite abelian extensions form a finite Galois extension
over the original base when the top-field subgroup is stable under conjugation
by every element of the base subgroup. -/
def galoisSubextensionOfConjugateStableAbelianTower
    (L : FiniteAbelianSubextension K)
    (M : FiniteAbelianSubextension L.field)
    (hstable : ∀ s : K.toSubgroup,
      conjugateClosedSubgroup M.field s.1 = M.field) :
    FiniteGaloisSubextension K where
  field := M.field
  below := M.below.trans L.below
  normal := by
    refine Subgroup.Normal.mk ?_
    intro q hq r
    apply
      (mem_extensionSubgroup_iff
        K M.field (M.below.trans L.below) _).2
    have hqM : (q : G) ∈ M.field :=
      (mem_extensionSubgroup_iff
        K M.field (M.below.trans L.below) q).1 hq
    have hqConj :
        (q : G) ∈ conjugateClosedSubgroup M.field (r : G) := by
      rw [hstable r]
      exact hqM
    exact
      (conjugateClosedSubgroup_mem M.field (r : G) (q : G)).1 hqConj
  finite := by
    let : Finite
        (L.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup L.field M.field M.below) :=
      M.finite
    let : Finite
        (K.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup K L.field L.below) :=
      L.finite
    exact
      FiniteGaloisSubextension.finite_extension_trans M.below L.below

@[simp]
theorem galoisSubextensionOfConjugateStableAbelianTower_field
    (L : FiniteAbelianSubextension K)
    (M : FiniteAbelianSubextension L.field)
    (hstable : ∀ s : K.toSubgroup,
      conjugateClosedSubgroup M.field s.1 = M.field) :
    (galoisSubextensionOfConjugateStableAbelianTower
      L M hstable).field = M.field :=
  rfl

end Conjugation

section MaximalAbelianIntermediate

variable [IsTopologicalGroup G]

/-- The intermediate field fixed by the commutator of a finite Galois
extension, bundled as the actual maximal finite abelian subextension. -/
def maximalAbelianSubextension
    (P : FiniteGaloisSubextension K) :
    FiniteAbelianSubextension K :=
  FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe
    P (commutator P.extensionQuotient) le_rfl

@[simp]
theorem maximalAbelianSubextension_field
    (P : FiniteGaloisSubextension K) :
    (maximalAbelianSubextension P).field =
      P.abelianIntermediateField :=
  FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field
    P (commutator P.extensionQuotient) le_rfl

/-- Every finite abelian intermediate extension of a finite Galois
extension is contained in the commutator-fixed intermediate field.

In subgroup order the displayed inclusion is reversed: the subgroup
representing the maximal abelian intermediate field lies inside the
subgroup representing the given abelian intermediate field. -/
theorem abelianIntermediateField_le_of_finiteAbelianIntermediate
    (P : FiniteGaloisSubextension K)
    (L : FiniteAbelianSubextension K)
    (hPL : P.field.toSubgroup ≤ L.field.toSubgroup) :
    P.abelianIntermediateField.toSubgroup ≤
      L.field.toSubgroup := by
  let :
      (CyclicCohomology.extensionSubgroup K P.field P.below).Normal :=
    P.normal
  let :
      (CyclicCohomology.extensionSubgroup K L.field L.below).Normal :=
    L.normal
  let restriction :
      P.extensionQuotient →* L.extensionQuotient :=
    abstractReciprocityRestriction
      K L.field P.field hPL L.below
  intro x hx
  change
    x ∈
      P.intermediateField
        (commutator P.extensionQuotient) at hx
  rcases hx with ⟨k, hk, rfl⟩
  have hkcomm :
      P.extensionQuotientMk k ∈
        commutator P.extensionQuotient :=
    (P.mem_intermediateSubgroup_iff
      (commutator P.extensionQuotient) k).1 hk
  have hrestriction :
      restriction (P.extensionQuotientMk k) = 1 :=
    Abelianization.commutator_subset_ker restriction hkcomm
  change
    (QuotientGroup.mk k :
      K.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup K L.field L.below) = 1
    at hrestriction
  exact
    (mem_extensionSubgroup_iff K L.field L.below k).1
      ((QuotientGroup.eq_one_iff k).1 hrestriction)

/-- In field order, every finite abelian intermediate extension lies below
the maximal abelian subextension cut out by the commutator. -/
theorem finiteAbelianIntermediate_le_maximalAbelianSubextension
    (P : FiniteGaloisSubextension K)
    (L : FiniteAbelianSubextension K)
    (hPL : P.field.toSubgroup ≤ L.field.toSubgroup) :
    L ≤ maximalAbelianSubextension P := by
  change (maximalAbelianSubextension P).field.toSubgroup ≤ L.field.toSubgroup
  rw [maximalAbelianSubextension_field]
  exact abelianIntermediateField_le_of_finiteAbelianIntermediate P L hPL

end MaximalAbelianIntermediate

end IdealClassFieldTheory
end GlobalClassFieldTheory
