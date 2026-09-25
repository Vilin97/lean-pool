/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.NormContinuity
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.IntegralRepUniverse
/-!
# The norm-topology characterization

This file supplies part (i), whose finite-index assertion uses the actual
reciprocity isomorphism of the abstract reciprocity theorem.  Parts (ii)--(iv) are proved in the
imported valuation-, norm-, and norm-topology modules.
-/

@[expose] public section

noncomputable section

namespace ClassFormation

open ClassFormation CyclicCohomology KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The norm-subgroup basis characterization: in the norm topology, the open subgroups are
exactly the closed subgroups of finite index.  Finiteness of every defining
norm quotient is obtained from the abstract reciprocity theorem, not assumed. -/
theorem normTopology_open_iff_closed_finiteIndex
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : ClosedSubgroup G)
    [hKabsolute : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K (le_baseField K))]
    (H : AddSubgroup (ambientFixedAddSubgroup A K)) :
    IsNormOpen A K H ↔
      IsNormClosed A K H ∧
        Finite (ambientFixedAddSubgroup A K ⧸ H) := by
  apply normTopology_open_iff_closed_finiteIndex_of_finite_normQuotients
    A K _ H
  intro L
  let KF : FiniteAbstractField G := ⟨K, hKabsolute⟩
  let : (extensionSubgroup K L.field L.below).Normal := L.normal
  let : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) := L.finite
  let : Finite (Abelianization L.extensionQuotient) :=
    Finite.of_surjective Abelianization.of QuotientGroup.mk_surjective
  change Finite (FiniteNormQuotient A K L.field L.below)
  exact Finite.of_equiv
    (Additive (Abelianization L.extensionQuotient))
    (D.abstractReciprocityEquiv A v hcf KF L).toEquiv

end ValuationData
end ClassFormation
