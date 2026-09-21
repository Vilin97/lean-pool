/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.AffineCover

/-!
# List-backed affine-cover tree data

`AffineCover.CoverTree` uses a function `Fin arity → CoverTree m` for the
children of a branch.  That representation is convenient for the checker and
its soundness proof, but awkward for generated certificate files.  This module
provides a small passive input type whose branch children are ordinary lists.

Decoding is a fuelled structural traversal and returns an `Option`.
Consequently no claim about an external emitter or parser enters the trusted
argument: under-fuelled data is rejected, and an accepted value is first
converted to the already-proved `CoverTree` checker.  An emitter may use any
easy upper bound on tree depth, such as the number of witness commands.
-/

namespace Utilities.Certificate.AffineCover
open Utilities.Certificate
open Utilities.Certificate.AffineCover

open Utilities

/-- Passive, emitter-friendly covering-tree data with list-backed branches. -/
inductive CoverTreeData where
  | leaf (farkas : FarkasData)
  | empty (cone : ℕ)
  | skip (cone form : ℕ) (next : CoverTreeData)
  | branch (cone : ℕ) (children : List CoverTreeData)

namespace CoverTreeData

/-- Fuelled structural conversion from list-backed data to the function-backed
trusted tree.  Every recursive child conversion consumes one unit of fuel. -/
def decodeFuel (m : ℕ) : ℕ → CoverTreeData → Option (CoverTree m)
  | 0, _ => none
  | _fuel + 1, .leaf farkas => some (.leaf farkas)
  | _fuel + 1, .empty cone => some (.empty cone)
  | fuel + 1, .skip cone form next => do
      let decoded ← decodeFuel m fuel next
      pure (.skip cone form decoded)
  | fuel + 1, .branch cone children => do
      let decoded ← children.mapM (decodeFuel m fuel)
      pure (.branch cone decoded.length fun index => decoded.get index)

/-- Attempt to decode list-backed data using the advertised depth bound. -/
def decode (data : CoverTreeData) (m fuel : ℕ) : Option (CoverTree m) :=
  decodeFuel m fuel data

/-- Direct propositional validity of list-backed data under the currently
active rows.  Fuel is consumed once at every level, exactly as in
`decodeFuel`, but no intermediate function-backed tree is constructed. -/
private def ValidActive {m : ℕ}
    (cones : List (List (AffineForm m)))
    (active : List (AffineForm m)) : ℕ → CoverTreeData → Prop
  | 0, _ => False
  | _fuel + 1, .leaf farkas => farkas.Valid active
  | _fuel + 1, .empty cone =>
      cone < cones.length ∧ CoverTree.coneAt cones cone = []
  | fuel + 1, .skip cone form next =>
      cone < cones.length ∧
      form < (CoverTree.coneAt cones cone).length ∧
      AffineForm.violation
        (CoverTree.formAt (CoverTree.coneAt cones cone) form) ∈ active ∧
      ValidActive cones active fuel next
  | fuel + 1, .branch cone children =>
      cone < cones.length ∧
      children.length = (CoverTree.coneAt cones cone).length ∧
      ∀ index : Fin children.length,
        ValidActive cones
          (active ++ [AffineForm.violation
            (CoverTree.formAt (CoverTree.coneAt cones cone) index.val)])
          fuel (children.get index)

/-- Direct Boolean replay of list-backed data.  This deliberately fuses
decoding and checking: generated trees remain ordinary lists all the way down,
so kernel reduction never materializes a large function-backed tree. -/
private def checkActive {m : ℕ}
    (cones : List (List (AffineForm m)))
    (active : List (AffineForm m)) : ℕ → CoverTreeData → Bool
  | 0, _ => false
  | _fuel + 1, .leaf farkas => farkas.check active
  | _fuel + 1, .empty cone =>
      decide (cone < cones.length) &&
      (CoverTree.coneAt cones cone).isEmpty
  | fuel + 1, .skip cone form next =>
      decide (cone < cones.length) &&
      decide (form < (CoverTree.coneAt cones cone).length) &&
      AffineForm.mem
        (AffineForm.violation
          (CoverTree.formAt (CoverTree.coneAt cones cone) form)) active &&
      checkActive cones active fuel next
  | fuel + 1, .branch cone children =>
      decide (cone < cones.length) &&
      decide (children.length = (CoverTree.coneAt cones cone).length) &&
      allFin fun index : Fin children.length =>
        checkActive cones
          (active ++ [AffineForm.violation
            (CoverTree.formAt (CoverTree.coneAt cones cone) index.val)])
          fuel (children.get index)

/-- Propositional validity of list-backed data, stated directly on the passive
representation checked by the kernel. -/
def Valid {m : ℕ} (data : CoverTreeData) (fuel : ℕ)
    (base : List (AffineForm m))
    (cones : List (List (AffineForm m))) : Prop :=
  ValidActive cones base fuel data

/-- Executable checker for list-backed covering data. -/
def check {m : ℕ} (data : CoverTreeData) (fuel : ℕ)
    (base : List (AffineForm m))
    (cones : List (List (AffineForm m))) : Bool :=
  checkActive cones base fuel data

/-- Direct Boolean replay implements exactly the direct validity relation. -/
private theorem checkActive_eq_true_iff {m : ℕ} (data : CoverTreeData)
    (fuel : ℕ) (active : List (AffineForm m))
    (cones : List (List (AffineForm m))) :
    checkActive cones active fuel data = true ↔
      ValidActive cones active fuel data := by
  induction fuel generalizing data active with
  | zero => simp [checkActive, ValidActive]
  | succ fuel inductionHypothesis =>
      cases data with
      | leaf farkas => simp [checkActive, ValidActive]
      | empty cone => simp [checkActive, ValidActive]
      | skip cone form next =>
          simp [checkActive, ValidActive, inductionHypothesis, and_assoc]
      | branch cone children =>
          simp [checkActive, ValidActive, inductionHypothesis, and_assoc]

/-- The list-backed checker implements exactly `CoverTreeData.Valid`. -/
@[simp] theorem check_eq_true_iff {m : ℕ} (data : CoverTreeData)
    (fuel : ℕ)
    (base : List (AffineForm m))
    (cones : List (List (AffineForm m))) :
    data.check fuel base cones = true ↔ data.Valid fuel base cones := by
  exact checkActive_eq_true_iff data fuel base cones

private theorem coneAt_eq_getElem {m : ℕ}
    (cones : List (List (AffineForm m))) (index : ℕ)
    (hindex : index < cones.length) :
    CoverTree.coneAt cones index = cones[index] := by
  exact List.getD_eq_getElem _ _ hindex

private theorem formAt_eq_getElem {m : ℕ}
    (cone : List (AffineForm m)) (index : ℕ)
    (hindex : index < cone.length) :
    CoverTree.formAt cone index = cone[index] := by
  exact List.getD_eq_getElem _ _ hindex

/-- A valid direct replay cannot follow a point which satisfies the active
rows while escaping every advertised cone. -/
private theorem no_escape_of_valid {m : ℕ}
    (data : CoverTreeData) (fuel : ℕ)
    (cones : List (List (AffineForm m)))
    (active : List (AffineForm m))
    (hValid : ValidActive cones active fuel data)
    (point : Fin m → ℤ) (hActive : FormsHold active point)
    (hEscape : ∀ cone ∈ cones, ¬FormsHold cone point) : False := by
  induction fuel generalizing data active with
  | zero => simp [ValidActive] at hValid
  | succ fuel inductionHypothesis =>
      cases data with
      | leaf farkas =>
          exact farkas.not_formsHold_of_valid active hValid hActive
      | empty cone =>
          obtain ⟨hCone, hEmpty⟩ := hValid
          let advertised := cones[cone]
          have hAdvertised : advertised ∈ cones := List.getElem_mem hCone
          have hAdvertisedEmpty : advertised = [] := by
            simpa [advertised, coneAt_eq_getElem cones cone hCone] using hEmpty
          apply hEscape advertised hAdvertised
          simp [hAdvertisedEmpty, FormsHold]
      | skip cone form next =>
          exact inductionHypothesis next active hValid.2.2.2 hActive
      | branch cone children =>
          obtain ⟨hCone, hArity, hChildren⟩ := hValid
          let advertised := cones[cone]
          have hAdvertised : advertised ∈ cones := List.getElem_mem hCone
          have hNot : ¬FormsHold advertised point :=
            hEscape advertised hAdvertised
          rw [FormsHold, not_forall] at hNot
          obtain ⟨formValue, hNot⟩ := hNot
          rw [Classical.not_imp] at hNot
          obtain ⟨hFormMem, hFormFails⟩ := hNot
          obtain ⟨index, hIndex, hFormEq⟩ := List.getElem_of_mem hFormMem
          have hIndexChildren : index < children.length := by
            rw [hArity]
            simpa [advertised, coneAt_eq_getElem cones cone hCone] using hIndex
          let childIndex : Fin children.length := ⟨index, hIndexChildren⟩
          have hConeAt : CoverTree.coneAt cones cone = advertised :=
            coneAt_eq_getElem cones cone hCone
          have hFormAt :
              CoverTree.formAt (CoverTree.coneAt cones cone) childIndex.val =
                formValue := by
            rw [formAt_eq_getElem]
            · simpa [hConeAt] using hFormEq
            · simpa [hConeAt] using hIndex
          apply inductionHypothesis (children.get childIndex)
            (active ++ [AffineForm.violation
              (CoverTree.formAt (CoverTree.coneAt cones cone)
                childIndex.val)])
            (hChildren childIndex)
          · intro row hRow
            simp only [List.mem_append, List.mem_singleton] at hRow
            rcases hRow with hRow | rfl
            · exact hActive row hRow
            · rw [hFormAt, AffineForm.holds_violation_iff_not]
              exact hFormFails

/-- Soundness of the passive list-backed layer: accepted data proves integral
coverage through the existing `CoverTree` soundness theorem. -/
theorem covers_of_check_eq_true {m : ℕ} (data : CoverTreeData)
    (fuel : ℕ)
    (base : List (AffineForm m))
    (cones : List (List (AffineForm m)))
    (hCheck : data.check fuel base cones = true) :
    Covers base cones := by
  have hValid : ValidActive cones base fuel data :=
    (data.check_eq_true_iff fuel base cones).mp hCheck
  intro point hBase
  by_contra hCovered
  have hEscape : ∀ cone ∈ cones, ¬FormsHold cone point := by
    intro cone hCone hConeHolds
    exact hCovered ⟨cone, hCone, hConeHolds⟩
  exact data.no_escape_of_valid fuel cones base hValid point hBase hEscape

end CoverTreeData

/-! ## A small closed example -/

namespace Examples
open Utilities.Certificate.AffineCover.Examples

/-- List-backed spelling of the strict two-cone partition example from
`AffineCover`.  Child-list position is the corresponding cone-form index. -/
def strictPartitionTreeData : CoverTreeData :=
  .branch 0 [
    .branch 1 [
      .leaf { terms := [⟨0, 1⟩, ⟨1, 1⟩] }
    ]
  ]

theorem strictPartitionTreeData_check :
    strictPartitionTreeData.check 3 [] strictPartitionCones = true := by
  rw [CoverTreeData.check_eq_true_iff]
  have hTreeValid :=
    (CoverTree.check_eq_true_iff strictPartitionTree []
      strictPartitionCones).mp strictPartitionTree_check
  simpa [CoverTreeData.Valid, CoverTreeData.ValidActive,
    strictPartitionTreeData, strictPartitionTree, CoverTree.Valid] using
    hTreeValid

/-- Decoding is fail-closed when the advertised depth bound is too small. -/
theorem strictPartitionTreeData_underFuel_rejected :
    strictPartitionTreeData.check 2 [] strictPartitionCones = false := by
  rfl

/-- An out-of-range cone index is rejected before it can use `getD`'s
default empty cone. -/
theorem badConeIndex_rejected :
    (.empty 2 : CoverTreeData).check 1 [] strictPartitionCones = false := by
  rfl

/-- An out-of-range form index is rejected before it can use `getD`'s
default zero form. -/
theorem badFormIndex_rejected :
    (.skip 0 1 (.empty 0) : CoverTreeData).check
      2 [] strictPartitionCones = false := by
  rfl

/-- Kernel-checked coverage obtained through the list-backed data layer. -/
theorem strictPartitionDataCovers :
    Covers [] strictPartitionCones :=
  strictPartitionTreeData.covers_of_check_eq_true
    3 [] strictPartitionCones strictPartitionTreeData_check

end Examples

end Utilities.Certificate.AffineCover
