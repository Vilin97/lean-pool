/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.SeparableClosure
/-!
# Infinite Galois base change from finite layers

This module supplies the field-theoretic passage from finite Galois layers to
their union after a change of base field.  It is stated entirely in terms of
mathlib's actual intermediate fields and uses no abstract replacement for the
compositum.
-/

@[expose] public section

noncomputable
section

namespace IntermediateField

variable {R U : Type*} [Field R] [Field U] [Algebra R U]

/-- A Galois intermediate field is the union of the lifts of its finite
Galois intermediate subfields. -/
theorem le_iSup_lift_finiteGalois
    (B : IntermediateField R U) [IsGalois R B] :
    B ≤ ⨆ E : FiniteGaloisIntermediateField R B,
      IntermediateField.lift E.toIntermediateField := by
  intro x hx
  let xB : B := ⟨x, hx⟩
  let E : FiniteGaloisIntermediateField R B :=
    FiniteGaloisIntermediateField.adjoin R {xB}
  have hxE : xB ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin R {xB}
      (Set.mem_singleton xB)
  exact
    (le_iSup
      (fun E : FiniteGaloisIntermediateField R B =>
        IntermediateField.lift E.toIntermediateField)
      E)
      ((IntermediateField.mem_lift xB).2 hxE)

/-- A compositum with a Galois intermediate field is the supremum of the
composita with its finite Galois intermediate layers. -/
theorem sup_eq_iSup_finiteGaloisComposita
    (A B : IntermediateField R U) [IsGalois R B] :
    A ⊔ B = ⨆ E : FiniteGaloisIntermediateField R B,
      A ⊔ IntermediateField.lift E.toIntermediateField := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · let E0 : FiniteGaloisIntermediateField R B := ⊥
      exact
        le_trans le_sup_left
          (le_iSup
            (fun E : FiniteGaloisIntermediateField R B =>
              A ⊔ IntermediateField.lift E.toIntermediateField)
            E0)
    · exact
        (le_iSup_lift_finiteGalois B).trans
          (iSup_mono fun E =>
            (show IntermediateField.lift E.toIntermediateField ≤
              A ⊔ IntermediateField.lift E.toIntermediateField from
              le_sup_right))
  · refine iSup_le fun E => ?_
    exact
      sup_le le_sup_left
        ((IntermediateField.lift_le E.toIntermediateField).trans le_sup_right)

/-- Base change commutes with the supremum of finite Galois composita. -/
theorem extendScalars_sup_eq_iSup_finiteGaloisComposita
    (A B : IntermediateField R U) [IsGalois R B] :
    IntermediateField.extendScalars (F := A) (E := A ⊔ B) le_sup_left =
      ⨆ E : FiniteGaloisIntermediateField R B,
        IntermediateField.extendScalars (F := A)
          (E := A ⊔ IntermediateField.lift E.toIntermediateField)
          le_sup_left := by
  apply le_antisymm
  · apply (IntermediateField.extendScalars_le_iff le_sup_left _).2
    rw [sup_eq_iSup_finiteGaloisComposita]
    refine iSup_le fun E => ?_
    exact
      (IntermediateField.extendScalars_le_iff le_sup_left _).1
        (le_iSup
          (fun E : FiniteGaloisIntermediateField R B =>
            IntermediateField.extendScalars (F := A)
              (E := A ⊔ IntermediateField.lift E.toIntermediateField)
              le_sup_left)
          E)
  · refine iSup_le fun E => ?_
    apply (IntermediateField.extendScalars_le_iff le_sup_left _).2
    rw [IntermediateField.extendScalars_restrictScalars]
    exact
      sup_le le_sup_left
        ((IntermediateField.lift_le E.toIntermediateField).trans le_sup_right)

/-- If every finite Galois layer of a compositum remains Galois after base
change, then so does the full compositum. -/
theorem isGalois_extendScalars_sup_of_forall_finiteGalois
    (A B : IntermediateField R U) [IsGalois R B]
    (hG : ∀ E : FiniteGaloisIntermediateField R B,
      IsGalois A
        (IntermediateField.extendScalars (F := A)
          (E := A ⊔ IntermediateField.lift E.toIntermediateField)
          le_sup_left)) :
    IsGalois A
      (IntermediateField.extendScalars (F := A) (E := A ⊔ B) le_sup_left) := by
  let C : IntermediateField A U :=
    IntermediateField.extendScalars (F := A) (E := A ⊔ B) le_sup_left
  let finiteLayer :
      FiniteGaloisIntermediateField R B → IntermediateField A U :=
    fun E =>
      IntermediateField.extendScalars (F := A)
        (E := A ⊔ IntermediateField.lift E.toIntermediateField)
        le_sup_left
  let : ∀ E : FiniteGaloisIntermediateField R B,
      IsGalois A (finiteLayer E) :=
    fun E => by
      simpa only [finiteLayer] using hG E
  have hC : C = ⨆ E : FiniteGaloisIntermediateField R B, finiteLayer E := by
    simpa only [C, finiteLayer] using
      extendScalars_sup_eq_iSup_finiteGaloisComposita A B
  change IsGalois A C
  rw [hC]
  exact {
    to_isSeparable := IntermediateField.isSeparable_iSup A U
    to_normal := IntermediateField.normal_iSup A U finiteLayer }

end IntermediateField
