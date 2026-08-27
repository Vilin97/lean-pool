/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Controls on `Boxes.lean`.

`Core.lean` has `Sanity.lean` and Lemma 9 has `Necessity.lean`; this file plays
the same role for Definitions 2-3.  Nothing here is in the paper.  Each
statement would FAIL if the corresponding definition were mis-encoded, which is
what makes the checks in `Boxes.lean` discriminating rather than merely
consistent: a position swap in `dia`, or an order flip in `boxes` /
`reachWord`, has to be OBSERVABLE somewhere or the definitions are not pinned
by anything.
-/
import LeanPool.MatchingLogic.Boxes

/-!
# MatchingLogic.BoxesControl
-/

namespace MatchingLogic
namespace BoxesControl

/-! ### Coordinates exclude constants (Definition 2). -/

/-- Every coordinate has arity at least one. -/
theorem coord_arity_pos (S : Signature) (e : Coord S) : 1 ≤ S.arity e.1 := by
  have h := e.2.isLt
  omega

/-- One binary symbol. -/
abbrev Sg : Signature := ⟨Unit, fun _ => 2⟩

/-- A signature of constants only. -/
abbrev SgConst : Signature := ⟨Unit, fun _ => 0⟩

/-- A constants-only signature has no coordinates at all, so `E* = {ε}`. -/
theorem coord_isEmpty_of_const : IsEmpty (Coord SgConst) := by
  constructor
  intro e
  exact Fin.elim0 e.2

/-- Consequently boxing is trivial there: the only word is `ε`. -/
theorem boxes_const (p : List (Coord SgConst)) (ψ : Pattern SgConst Nat) :
    boxes p ψ = ψ := by
  induction p with
  | nil => rfl
  | cons e p _ => exact Fin.elim0 e.2

/-! ### A model in which position and order are visible.

`0 ∈ f(1,1)` and `1 ∈ f(2,3)`, so from `0` the first argument leads to `1` and
so does the second, while from `1` the first argument leads to `2` and the
second to `3`.  The two coordinates therefore separate after one step. -/

/-- The four-point model that distinguishes the two argument positions. -/
abbrev Mo : Model Sg :=
  { carrier := Fin 4
    nonempty := ⟨0⟩
    interp := fun _ a =>
      if a 0 = 1 ∧ a 1 = 1 then ({0} : Set (Fin 4))
      else if a 0 = 2 ∧ a 1 = 3 then ({1} : Set (Fin 4))
      else ∅ }

/-- First coordinate of the binary symbol. -/
abbrev e0 : Coord Sg := ⟨(), 0⟩
/-- Second coordinate of the binary symbol. -/
abbrev e1 : Coord Sg := ⟨(), 1⟩

/-- **A position swap in `dia` is observable.**  If `dia` put its argument in
the wrong slot, this would fail. -/
theorem dia_position_visible :
    Mo.denote (fun _ => (2 : Fin 4)) (dia e0 (.var 0)) ≠
      Mo.denote (fun _ => (2 : Fin 4)) (dia e1 (.var (0 : Nat))) := by
  intro h
  have hmem : (1 : Fin 4) ∈
      Mo.denote (fun _ => (2 : Fin 4)) (dia e0 (.var 0)) := by
    change (1 : Fin 4) ∈ Mo.app ()
      (fun i => Mo.denote (fun _ => (2 : Fin 4))
        (if i = e0.2 then .var 0 else Pattern.tp))
    refine ⟨fun i => if i = 0 then 2 else 3, ?_, ?_⟩
    · intro i
      by_cases hi : i = 0
      · subst i
        simp
      · simp [hi]
    · simp [Mo]
  rw [h] at hmem
  change (1 : Fin 4) ∈ Mo.app ()
    (fun i => Mo.denote (fun _ => (2 : Fin 4))
      (if i = e1.2 then .var 0 else Pattern.tp)) at hmem
  rcases hmem with ⟨a, ha, hout⟩
  have ha1 : a 1 = 2 := by
    simpa [e1] using ha 1
  simp [Mo, ha1] at hout

private theorem stepAt_e0_zero (v : Fin 4) : Mo.stepAt e0 0 v ↔ v = 1 := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    by_cases h : a 0 = 1 ∧ a 1 = 1
    · exact h.1
    · simp [Mo, h] at ha
  · rintro rfl
    refine ⟨fun _ => 1, ?_, rfl⟩
    simp [Mo]

private theorem stepAt_e1_zero (v : Fin 4) : Mo.stepAt e1 0 v ↔ v = 1 := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    by_cases h : a 0 = 1 ∧ a 1 = 1
    · exact h.2
    · simp [Mo, h] at ha
  · rintro rfl
    refine ⟨fun _ => 1, ?_, rfl⟩
    simp [Mo]

private theorem stepAt_e0_one (v : Fin 4) : Mo.stepAt e0 1 v ↔ v = 2 := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    by_cases h : a 0 = 1 ∧ a 1 = 1
    · simp [Mo, h] at ha
    · by_cases h' : a 0 = 2 ∧ a 1 = 3
      · exact h'.1
      · simp [Mo, h, h'] at ha
  · rintro rfl
    refine ⟨fun i => if i = 0 then 2 else 3, ?_, rfl⟩
    simp [Mo]

private theorem stepAt_e1_one (v : Fin 4) : Mo.stepAt e1 1 v ↔ v = 3 := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    by_cases h : a 0 = 1 ∧ a 1 = 1
    · simp [Mo, h] at ha
    · by_cases h' : a 0 = 2 ∧ a 1 = 3
      · exact h'.2
      · simp [Mo, h, h'] at ha
  · rintro rfl
    refine ⟨fun i => if i = 0 then 2 else 3, ?_, rfl⟩
    simp [Mo]

/-- **The order of a word is observable**, one way … -/
theorem reachWord_order_left (v : Fin 4) :
    Mo.reachWord [e0, e1] 0 v ↔ v = 3 := by
  simp only [Model.reachWord_cons, Model.reachWord_nil]
  simp [stepAt_e0_zero, stepAt_e1_one]

/-- … and the other.  Together these two force the composition order of
`reachWord`, and through Lemma 4 the nesting order of `boxes`. -/
theorem reachWord_order_right (v : Fin 4) :
    Mo.reachWord [e1, e0] 0 v ↔ v = 2 := by
  simp only [Model.reachWord_cons, Model.reachWord_nil]
  simp [stepAt_e1_zero, stepAt_e0_one]

end BoxesControl
end MatchingLogic
