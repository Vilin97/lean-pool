/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.AffineCover

/-!
# Affine wall-decision cover certificates

`AffineCover.CoverTree` proves a union of cones by choosing a violated row from
every cone.  Highly overlapping cone families can make that proof enormous.
This file supplies the dual passive certificate: branch on one integral affine
wall and its exact strict complement, stop as soon as one advertised cone is
literally contained in the active rows, and close infeasible sign chambers by
a Farkas certificate.

The checker is deliberately small.  Generated search code is untrusted; only
the Boolean replay and the theorem below enter the proof.
-/

@[expose] public section

namespace Utilities.Certificate.AffineCover
open Utilities.Certificate
open Utilities.Certificate.AffineCover

open Utilities

/-- Passive, emitter-friendly wall decision data. -/
inductive DecisionTreeData (m : ℕ) where
  | impossible (farkas : FarkasData)
  | select (cone : ℕ)
  | branch (form : AffineForm m)
      (holds : DecisionTreeData m) (fails : DecisionTreeData m)
  deriving DecidableEq

namespace DecisionTreeData

def ValidActive {m : ℕ}
    (cones : List (List (AffineForm m)))
    (active : List (AffineForm m)) : DecisionTreeData m → Prop
  | .impossible farkas => farkas.Valid active
  | .select cone =>
      cone < cones.length ∧
        ∀ form ∈ CoverTree.coneAt cones cone, form ∈ active
  | .branch form holds fails =>
      ValidActive cones (active ++ [form]) holds ∧
        ValidActive cones (active ++ [form.violation]) fails

def checkActive {m : ℕ}
    (cones : List (List (AffineForm m)))
    (active : List (AffineForm m)) : DecisionTreeData m → Bool
  | .impossible farkas => farkas.check active
  | .select cone =>
      decide (cone < cones.length) &&
        (CoverTree.coneAt cones cone).all fun form => AffineForm.mem form active
  | .branch form holds fails =>
      checkActive cones (active ++ [form]) holds &&
        checkActive cones (active ++ [form.violation]) fails

/-- Mathematical validity of wall-decision data at the displayed base rows. -/
def Valid {m : ℕ} (data : DecisionTreeData m)
    (base : List (AffineForm m))
    (cones : List (List (AffineForm m))) : Prop :=
  ValidActive cones base data

/-- Executable exact replay of wall-decision data. -/
def check {m : ℕ} (data : DecisionTreeData m)
    (base : List (AffineForm m))
    (cones : List (List (AffineForm m))) : Bool :=
  checkActive cones base data

/-- Public one-step reduction rule, allowing large generated trees to cache
checked subtrees in separate modules instead of reducing the whole tree in one
kernel invocation. -/
@[simp] theorem check_branch {m : ℕ} (form : AffineForm m)
    (holds fails : DecisionTreeData m) (active : List (AffineForm m))
    (cones : List (List (AffineForm m))) :
    (DecisionTreeData.branch form holds fails).check active cones =
      (holds.check (active ++ [form]) cones &&
        fails.check (active ++ [form.violation]) cones) := rfl

private theorem checkActive_eq_true_iff {m : ℕ}
    (data : DecisionTreeData m)
    (active : List (AffineForm m))
    (cones : List (List (AffineForm m))) :
    checkActive cones active data = true ↔ ValidActive cones active data := by
  induction data generalizing active with
  | impossible farkas => simp [checkActive, ValidActive]
  | select cone => simp [checkActive, ValidActive, List.all_eq_true]
  | branch form holds fails ihHolds ihFails =>
      simp [checkActive, ValidActive, ihHolds, ihFails]

@[simp] theorem check_eq_true_iff {m : ℕ}
    (data : DecisionTreeData m)
    (base : List (AffineForm m))
    (cones : List (List (AffineForm m))) :
    data.check base cones = true ↔ data.Valid base cones := by
  exact checkActive_eq_true_iff data base cones

private theorem exists_cone_of_validActive {m : ℕ}
    (data : DecisionTreeData m)
    (cones : List (List (AffineForm m)))
    (active : List (AffineForm m))
    (hValid : ValidActive cones active data)
    (point : Fin m → ℤ) (hActive : FormsHold active point) :
    ∃ cone ∈ cones, FormsHold cone point := by
  induction data generalizing active with
  | impossible farkas =>
      exact (farkas.not_formsHold_of_valid active hValid hActive).elim
  | select cone =>
      obtain ⟨hCone, hRows⟩ := hValid
      refine ⟨cones[cone], List.getElem_mem hCone, ?_⟩
      rw [CoverTree.coneAt, List.getD_eq_getElem cones [] hCone] at hRows
      intro form hForm
      exact hActive form (hRows form hForm)
  | branch form holds fails ihHolds ihFails =>
      obtain ⟨hHolds, hFails⟩ := hValid
      by_cases hForm : form.Holds point
      · apply ihHolds (active ++ [form]) hHolds
        intro row hRow
        simp only [List.mem_append, List.mem_singleton] at hRow
        rcases hRow with hRow | rfl
        · exact hActive row hRow
        · exact hForm
      · apply ihFails (active ++ [form.violation]) hFails
        intro row hRow
        simp only [List.mem_append, List.mem_singleton] at hRow
        rcases hRow with hRow | rfl
        · exact hActive row hRow
        · exact (AffineForm.holds_violation_iff_not form point).mpr hForm

private theorem exists_index_of_validActive {m : ℕ}
    (data : DecisionTreeData m)
    (cones : List (List (AffineForm m)))
    (active : List (AffineForm m))
    (hValid : ValidActive cones active data)
    (point : Fin m → ℤ) (hActive : FormsHold active point) :
    ∃ cone, cone < cones.length ∧
      FormsHold (CoverTree.coneAt cones cone) point := by
  induction data generalizing active with
  | impossible farkas =>
      exact (farkas.not_formsHold_of_valid active hValid hActive).elim
  | select cone =>
      obtain ⟨hCone, hRows⟩ := hValid
      refine ⟨cone, hCone, ?_⟩
      intro form hForm
      exact hActive form (hRows form hForm)
  | branch form holds fails ihHolds ihFails =>
      obtain ⟨hHolds, hFails⟩ := hValid
      by_cases hForm : form.Holds point
      · apply ihHolds (active ++ [form]) hHolds
        intro row hRow
        simp only [List.mem_append, List.mem_singleton] at hRow
        rcases hRow with hRow | rfl
        · exact hActive row hRow
        · exact hForm
      · apply ihFails (active ++ [form.violation]) hFails
        intro row hRow
        simp only [List.mem_append, List.mem_singleton] at hRow
        rcases hRow with hRow | rfl
        · exact hActive row hRow
        · exact (AffineForm.holds_violation_iff_not form point).mpr hForm

/-- Accepted wall-decision data proves that the advertised cones cover the
base region at every integral point. -/
theorem covers_of_check_eq_true {m : ℕ}
    (data : DecisionTreeData m)
    (base : List (AffineForm m))
    (cones : List (List (AffineForm m)))
    (hCheck : data.check base cones = true) : Covers base cones := by
  have hValid := (data.check_eq_true_iff base cones).mp hCheck
  intro point hBase
  exact data.exists_cone_of_validActive cones base hValid point hBase

/-- Indexed form of `covers_of_check_eq_true`, for consumers whose semantic
payload is stored in a list parallel to the advertised cones. -/
theorem exists_index_of_check_eq_true {m : ℕ}
    (data : DecisionTreeData m)
    (base : List (AffineForm m))
    (cones : List (List (AffineForm m)))
    (hCheck : data.check base cones = true)
    (point : Fin m → ℤ) (hBase : FormsHold base point) :
    ∃ cone, cone < cones.length ∧
      FormsHold (CoverTree.coneAt cones cone) point := by
  have hValid := (data.check_eq_true_iff base cones).mp hCheck
  exact data.exists_index_of_validActive cones base hValid point hBase

end DecisionTreeData

end Utilities.Certificate.AffineCover
