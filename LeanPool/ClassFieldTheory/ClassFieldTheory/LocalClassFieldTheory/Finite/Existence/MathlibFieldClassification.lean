/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.OpenFiniteIndexSubgroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.Classification
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal
/-!
# Mathlib intermediate fields and finite local class-field theory

The finite-existence theorem is formulated internally using closed subgroups
of the absolute Galois group.  Here we identify those objects with finite
abelian intermediate fields of Mathlib's chosen separable closure.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open ClassFormation RamificationTheory

variable (K : Type) [Field K]

/-- Regard a finite abelian intermediate field as an abstract subextension. -/
def abstractExtensionOfFiniteAbelianField
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
    FiniteAbelianSubextension (intrinsicAbstractBase K) :=
  finiteAbelianAbstractExtensionOfEmbedding K E.1 E.1.val

/-- Recover the intermediate field represented by an abstract finite abelian subextension. -/
def finiteAbelianFieldOfAbstractExtension
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    ClassFieldTheory.FiniteAbelianLocalExtension K :=
  ⟨abstractFixedField K (SeparableClosure K) L.field,
    abstractFixedField_finiteDimensional K (SeparableClosure K) L.field
      (finiteAbelianSubextension_finite_over_absoluteBase K L),
    finiteAbelianSubextension_fixedField_isAbelianGalois K L⟩

/-- The fixed field of the abstract package constructed from an intermediate
field is the original field. -/
theorem finiteAbelianFieldOfAbstractExtension_ofField
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
    finiteAbelianFieldOfAbstractExtension K
      (abstractExtensionOfFiniteAbelianField K E) = E := by
  apply Subtype.ext
  change IntermediateField.fixedField
      (closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange E.1.val)).toSubgroup = E.1
  rw [IntermediateField.fieldRange_val]
  exact InfiniteGalois.fixedField_fixingSubgroup E.1

/-- Abstracting the fixed field of an abstract extension recovers the same
closed subgroup, hence the same finite abelian extension. -/
theorem abstractExtensionOfFiniteAbelianField_ofAbstract
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    abstractExtensionOfFiniteAbelianField K
      (finiteAbelianFieldOfAbstractExtension K L) = L := by
  apply FiniteAbelianSubextension.ext
  change closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange
        (abstractFixedField K (SeparableClosure K) L.field).val) = L.field
  rw [IntermediateField.fieldRange_val]
  exact closedFixingSubgroup_abstractFixedField_eq K (SeparableClosure K) L.field

/-- Concrete finite abelian intermediate fields and the abstract extension
objects used by the local-existence theorem have the same order. -/
def finiteAbelianFieldAbstractOrderIso :
    ClassFieldTheory.FiniteAbelianLocalExtension K ≃o
      FiniteAbelianSubextension (intrinsicAbstractBase K) where
  toEquiv := {
    toFun := abstractExtensionOfFiniteAbelianField K
    invFun := finiteAbelianFieldOfAbstractExtension K
    left_inv := finiteAbelianFieldOfAbstractExtension_ofField K
    right_inv := abstractExtensionOfFiniteAbelianField_ofAbstract K
  }
  map_rel_iff' := by
    intro E F
    change
      (closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange F.1.val)).toSubgroup ≤
      (closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange E.1.val)).toSubgroup ↔ E.1 ≤ F.1
    simp only [IntermediateField.fieldRange_val]
    change F.1.fixingSubgroup ≤ E.1.fixingSubgroup ↔ E.1 ≤ F.1
    constructor
    · intro h
      have hf := IntermediateField.fixedField_le h
      simpa only [InfiniteGalois.fixedField_fixingSubgroup] using hf
    · intro h
      exact E.1.fixingSubgroup_le h

/-- The internal open-subgroup structure and the Mathlib-facing subtype
encode the same subgroup with the same inclusion order. -/
def openFiniteIndexSubgroupMathlibOrderIso
    [TopologicalSpace K] :
    OpenFiniteIndexSubgroup K ≃o
      ClassFieldTheory.OpenFiniteIndexSubgroup K where
  toEquiv := {
    toFun := fun H => ⟨H.subgroup, H.isOpen, H.finiteIndex⟩
    invFun := fun H => ⟨H.1, H.2.1, H.2.2⟩
    left_inv := by intro H; cases H; rfl
    right_inv := by intro H; cases H; rfl
  }
  map_rel_iff' := by intro H J; rfl

/-- The abstract norm subgroup is the actual field-norm subgroup after
identifying an abstract extension with its concrete fixed field. -/
theorem finiteAbelianFieldOfAbstractExtension_normSubgroup
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    (finiteAbelianFieldOfAbstractExtension K L).normSubgroup =
      finiteAbelianNormSubgroup K L :=
  rfl

/-- The internal order classification, expressed entirely using concrete
finite abelian intermediate fields and Mathlib's subgroup subtype. -/
def finiteAbelianFieldNormSubgroupOrderIso
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ClassFieldTheory.FiniteAbelianLocalExtension K ≃o
      (ClassFieldTheory.OpenFiniteIndexSubgroup K)ᵒᵈ :=
  (finiteAbelianFieldAbstractOrderIso K).trans
    ((finiteAbelianNormSubgroupOrderIso K).trans
      (openFiniteIndexSubgroupMathlibOrderIso K).dual)

/-- The concrete classification sends each finite abelian extension to its
field-norm subgroup. -/
theorem finiteAbelianFieldNormSubgroupOrderIso_apply
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
    (OrderDual.ofDual (finiteAbelianFieldNormSubgroupOrderIso K E)).1 =
      E.normSubgroup := by
  change finiteAbelianNormSubgroup K
      (abstractExtensionOfFiniteAbelianField K E) = E.normSubgroup
  rw [← finiteAbelianFieldOfAbstractExtension_normSubgroup K]
  rw [finiteAbelianFieldOfAbstractExtension_ofField]

end LocalClassFieldTheory
