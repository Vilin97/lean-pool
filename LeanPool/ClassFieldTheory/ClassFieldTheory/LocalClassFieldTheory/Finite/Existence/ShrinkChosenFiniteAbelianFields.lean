/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnshrinkFiniteAbelianFields
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Algebra.FiniteAbelianIntermediateFieldAlgEquiv
/-!
# Finite abelian fields in the chosen small-base separable closure

The base equivalence and the equivalence between the two chosen separable
closures together transport finite abelian intermediate fields, preserving
their inclusion order.
-/

@[expose] public section

noncomputable
section

namespace LocalFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The underlying intermediate-field order equivalence, before imposing
finite-dimensional and abelian Galois conditions. -/
def shrinkChosenIntermediateFieldOrderIso :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    IntermediateField K (SeparableClosure K) ≃o
      IntermediateField (Shrink.{0} K) (SeparableClosure (Shrink.{0} K)) := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  exact (shrinkIntermediateFieldOrderIso K).trans
    (ClassFieldTheory.intermediateFieldAlgEquivOrderIso
      (shrinkSeparableClosureEquiv K).symm)

/-- Move a finite abelian intermediate field of the chosen closure of `K`
to the chosen closure of `Shrink K`. -/
def shrinkChosenFiniteAbelianField
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    ClassFieldTheory.FiniteAbelianLocalExtension (Shrink.{0} K) := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  let M := shrinkIntermediateField K E.1
  let c := shrinkSeparableClosureEquiv K
  let : FiniteDimensional (Shrink.{0} K) M :=
    shrinkIntermediateField_finiteDimensional K E
  let : IsAbelianGalois (Shrink.{0} K) M :=
    shrinkIntermediateField_isAbelianGalois K E
  exact ⟨M.map c.symm.toAlgHom,
    ClassFieldTheory.finiteDimensional_intermediateField_map_algEquiv c.symm M,
    ClassFieldTheory.isAbelianGalois_intermediateField_map_algEquiv c.symm M⟩

/-- Undo the chosen-closure and small-base transports. -/
def unshrinkChosenFiniteAbelianField :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    ClassFieldTheory.FiniteAbelianLocalExtension (Shrink.{0} K) →
      ClassFieldTheory.FiniteAbelianLocalExtension K := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
    shrinkSeparableClosureAlgebra K
  intro F
  let c := shrinkSeparableClosureEquiv K
  let M := F.1.map c.toAlgHom
  let : FiniteDimensional (Shrink.{0} K) F.1 := F.2.1
  let : IsAbelianGalois (Shrink.{0} K) F.1 := F.2.2
  let : FiniteDimensional (Shrink.{0} K) M :=
    ClassFieldTheory.finiteDimensional_intermediateField_map_algEquiv c F.1
  let : IsAbelianGalois (Shrink.{0} K) M :=
    ClassFieldTheory.isAbelianGalois_intermediateField_map_algEquiv c F.1
  exact ⟨unshrinkIntermediateField K M,
    unshrinkIntermediateField_finiteDimensional K M inferInstance,
    unshrinkIntermediateField_isAbelianGalois K M inferInstance⟩

/-- The finite abelian fields in both chosen separable closures are
order-isomorphic. -/
def shrinkChosenFiniteAbelianOrderIso :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    ClassFieldTheory.FiniteAbelianLocalExtension K ≃o
      ClassFieldTheory.FiniteAbelianLocalExtension (Shrink.{0} K) := by
  let : Small.{0} K := nonarchimedeanLocalField_small K
  exact {
    toEquiv := {
      toFun := shrinkChosenFiniteAbelianField K
      invFun := unshrinkChosenFiniteAbelianField K
      left_inv := by
        intro E
        apply Subtype.ext
        exact (shrinkChosenIntermediateFieldOrderIso K).symm_apply_apply E.1
      right_inv := by
        intro E
        apply Subtype.ext
        exact (shrinkChosenIntermediateFieldOrderIso K).apply_symm_apply E.1
    }
    map_rel_iff' := by
      intro E F
      exact (shrinkChosenIntermediateFieldOrderIso K).le_iff_le
  }

end LocalFieldTheory
