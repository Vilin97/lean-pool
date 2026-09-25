/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
/-!
# The abstract class-field correspondence

This file gives the inverse direction of the finite abelian classification:
a norm-open subgroup produces its class field.  The construction is the
inverse of the order isomorphism proved by abstract class field theory, so
the defining norm-subgroup equality and the two lattice formulas are
consequences rather than extra assumptions.
-/

@[expose] public section

noncomputable section

namespace ClassFormation

open CyclicCohomology KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The class field belonging to a norm-open subgroup. -/
noncomputable def classField
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (N : NormOpenAddSubgroup A K.field) :
    FiniteAbelianSubextension K.field :=
  (normSubgroupOrderIso v hcf K).symm (OrderDual.toDual N)

/-- The norm subgroup of the class field of `N` is `N`. -/
@[simp]
theorem classField_normSubgroup
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (N : NormOpenAddSubgroup A K.field) :
    (classField v hcf K N).normSubgroup A = N.1 := by
  calc
    (classField v hcf K N).normSubgroup A =
        (OrderDual.ofDual
          (normSubgroupOrderIso v hcf K (classField v hcf K N))).1 := by
            exact (normSubgroupOrderIso_apply
              v hcf K (classField v hcf K N)).symm
    _ = N.1 := by
      simp [classField]

/-- Taking the class field is inverse to taking the norm subgroup. -/
@[simp]
theorem classField_normSubgroupMap
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (L : FiniteAbelianSubextension K.field) :
    classField v hcf K (normSubgroupMap A L) = L := by
  change (normSubgroupOrderIso v hcf K).symm
      (normSubgroupOrderIso v hcf K L) = L
  exact (normSubgroupOrderIso v hcf K).symm_apply_apply L

/-- Characterization of the unique class field having norm subgroup `N`. -/
theorem eq_classField_iff_normSubgroup_eq
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (L : FiniteAbelianSubextension K.field)
    (N : NormOpenAddSubgroup A K.field) :
    L = classField v hcf K N ↔ L.normSubgroup A = N.1 := by
  constructor
  · rintro rfl
    exact classField_normSubgroup v hcf K N
  · intro h
    apply normSubgroupMap_injective v hcf K
    apply Subtype.ext
    simpa using h

/-- Inclusion of class fields is reverse inclusion of their defining norm
subgroups. -/
theorem classField_le_classField_iff
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (N₁ N₂ : NormOpenAddSubgroup A K.field) :
    classField v hcf K N₁ ≤ classField v hcf K N₂ ↔ N₂.1 ≤ N₁.1 := by
  rw [le_iff_normSubgroup_le v hcf K]
  simp

/-- A finite abelian extension lies in the class field of `N` exactly when
its norm subgroup contains `N`. -/
theorem le_classField_iff
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (L : FiniteAbelianSubextension K.field)
    (N : NormOpenAddSubgroup A K.field) :
    L ≤ classField v hcf K N ↔ N.1 ≤ L.normSubgroup A := by
  rw [le_iff_normSubgroup_le v hcf K]
  simp

/-- The class field of `N` lies in `L` exactly when the norm subgroup of
`L` lies in `N`. -/
theorem classField_le_iff
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (N : NormOpenAddSubgroup A K.field)
    (L : FiniteAbelianSubextension K.field) :
    classField v hcf K N ≤ L ↔ L.normSubgroup A ≤ N.1 := by
  rw [le_iff_normSubgroup_le v hcf K]
  simp

/-- Intersection of two norm-open subgroups, with its openness produced
from finite Galois norm neighbourhoods. -/
def normOpenInf
    (K : FiniteAbstractField G)
    (N₁ N₂ : NormOpenAddSubgroup A K.field) :
    NormOpenAddSubgroup A K.field := by
  refine ⟨N₁.1 ⊓ N₂.1, ?_⟩
  rw [normTopology_addSubgroup_isOpen_iff]
  obtain ⟨E₁, hE₁⟩ :=
    (normTopology_addSubgroup_isOpen_iff A K.field N₁.1).1 N₁.2
  obtain ⟨E₂, hE₂⟩ :=
    (normTopology_addSubgroup_isOpen_iff A K.field N₂.1).1 N₂.2
  refine ⟨E₁.compositum E₂, le_inf ?_ ?_⟩
  · exact (FiniteGaloisSubextension.normSubgroup_compositum_le_left
      A E₁ E₂).trans hE₁
  · exact (FiniteGaloisSubextension.normSubgroup_compositum_le_right
      A E₁ E₂).trans hE₂

/-- Product of two norm-open subgroups, with openness produced by either
of its open factors. -/
def normOpenSup
    (K : FiniteAbstractField G)
    (N₁ N₂ : NormOpenAddSubgroup A K.field) :
    NormOpenAddSubgroup A K.field := by
  refine ⟨N₁.1 ⊔ N₂.1, ?_⟩
  rw [normTopology_addSubgroup_isOpen_iff]
  obtain ⟨E₁, hE₁⟩ :=
    (normTopology_addSubgroup_isOpen_iff A K.field N₁.1).1 N₁.2
  exact ⟨E₁, hE₁.trans le_sup_left⟩

@[simp]
theorem normOpenInf_val
    (K : FiniteAbstractField G)
    (N₁ N₂ : NormOpenAddSubgroup A K.field) :
    (normOpenInf K N₁ N₂).1 = N₁.1 ⊓ N₂.1 :=
  rfl

@[simp]
theorem normOpenSup_val
    (K : FiniteAbstractField G)
    (N₁ N₂ : NormOpenAddSubgroup A K.field) :
    (normOpenSup K N₁ N₂).1 = N₁.1 ⊔ N₂.1 :=
  rfl

/-- The class field of an intersection of norm groups is the compositum of
the two class fields. -/
theorem classField_normOpenInf
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (N₁ N₂ : NormOpenAddSubgroup A K.field) :
    classField (D := D) v hcf K (normOpenInf K N₁ N₂) =
      (classField (D := D) v hcf K N₁).compositum
        (classField (D := D) v hcf K N₂) := by
  apply normSubgroupMap_injective (D := D) v hcf K
  apply Subtype.ext
  rw [normSubgroupMap_val, normSubgroupMap_val,
    normSubgroup_compositum (D := D) v hcf K,
    classField_normSubgroup (D := D) v hcf K,
    classField_normSubgroup (D := D) v hcf K,
    classField_normSubgroup (D := D) v hcf K]
  rfl

/-- The class field of a product of norm groups is the intersection of the
two class fields. -/
theorem classField_normOpenSup
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteAbstractField G)
    (N₁ N₂ : NormOpenAddSubgroup A K.field) :
    classField (D := D) v hcf K (normOpenSup K N₁ N₂) =
      (classField (D := D) v hcf K N₁).intersection
        (classField (D := D) v hcf K N₂) := by
  apply normSubgroupMap_injective (D := D) v hcf K
  apply Subtype.ext
  rw [normSubgroupMap_val, normSubgroupMap_val,
    normSubgroup_intersection (D := D) v hcf K,
    classField_normSubgroup (D := D) v hcf K,
    classField_normSubgroup (D := D) v hcf K,
    classField_normSubgroup (D := D) v hcf K]
  rfl

end FiniteAbelianSubextension
end ClassFormation
