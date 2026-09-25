/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine
public import Mathlib.Data.Fintype.Sum

/-!
# Tape actions shared by Turing-machine combinators

Idle and leftward directions respect the start marker. Read-back writes preserve
off-start tape contents, providing the transition invariants used by combinators.
-/

@[expose] public section

namespace Complexity

variable {n₁ n₂ : ℕ}

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Helpers
-- ════════════════════════════════════════════════════════════════════════

/-- Direction for an idle tape: move right if reading `▷`, else stay.
    Satisfies `δ_right_of_start` for tapes not involved in the current phase. -/
def idleDir (head : Γ) : Dir3 :=
  if head = Γ.start then .right else .stay

/-- Direction for a tape we want to move left: move left unless reading `▷`,
    in which case move right to satisfy `δ_right_of_start`. During actual
    execution the tape won't be at cell 0, so this always moves left. -/
def moveLeftDir (head : Γ) : Dir3 :=
  if head = Γ.start then .right else .left

/-- `idleDir` moves right when reading the start symbol `▷`. -/
theorem idleDir_start : idleDir Γ.start = Dir3.right := rfl
private theorem moveLeftDir_start : moveLeftDir Γ.start = Dir3.right := rfl

/-- If the head reads `▷`, then `idleDir` moves right — the shape of the
    `δ_right_of_start` obligation for idle tapes. -/
theorem idleDir_right_of_start {head : Γ} (h : head = Γ.start) : idleDir head = Dir3.right := by
  subst h; rfl

/-- If the head reads `▷`, then `moveLeftDir` moves right — the shape of the
    `δ_right_of_start` obligation for tapes being rewound. -/
theorem moveLeftDir_right_of_start {head : Γ}
    (h : head = Γ.start) : moveLeftDir head = Dir3.right :=
  by subst h; rfl

/-- Write back the same symbol read from a tape, preserving cell contents.
    Maps `▷` to `□` since `Tape.write` at position 0 is a no-op anyway. -/
def readBackWrite (g : Γ) : Γw :=
  match g with
  | .zero => .zero
  | .one => .one
  | .blank => .blank
  | .start => .blank

/-- `readBackWrite` recovers the original symbol away from the left-end marker. -/
theorem toΓ_readBackWrite_of_ne_start {g : Γ} (h : g ≠ Γ.start) :
    (readBackWrite g).toΓ = g := by
  cases g <;> simp_all [readBackWrite, Γw.toΓ]

/-- Writing back the symbol under an off-start head is a no-op. -/
theorem write_readBack (t : Tape) (hread : t.read ≠ Γ.start) :
    t.write (readBackWrite t.read) = t := by
  rw [Tape.write]
  split
  · rfl
  · refine Tape.ext rfl ?_
    show Function.update t.cells t.head (readBackWrite t.read).toΓ = t.cells
    rw [toΓ_readBackWrite_of_ne_start hread, Tape.read, Function.update_eq_self]

/-- Writing back the symbol under an off-start head and moving is just the move. -/
theorem writeAndMove_readBack (t : Tape) (hread : t.read ≠ Γ.start) (d : Dir3) :
    t.writeAndMove (readBackWrite t.read) d = t.move d := by
  show (t.write _).move d = t.move d
  rw [write_readBack t hread]

/-- The "do nothing" transition output: all writes are `□`, all directions
    are `idleDir`. Used for states that only change the control state. -/
def allIdle {σ : Type} {k : ℕ}
    (newState : σ) (iHead : Γ) (wHeads : Fin k → Γ) (oHead : Γ) :
    σ × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3 :=
  (newState, fun _ => .blank, .blank, idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)

/-- The content-preserving driver action: write every currently read work and
output symbol back, and use `idleDir` on every tape. Every off-start tape is
preserved exactly; a head on `▷` takes the structurally mandatory move right. -/
def allReadBack {σ : Type} {k : ℕ}
    (newState : σ) (iHead : Γ) (wHeads : Fin k → Γ) (oHead : Γ) :
    σ × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3 :=
  (newState, fun i => readBackWrite (wHeads i), readBackWrite oHead,
    idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)

/-- Proof that all-idle directions satisfy `δ_right_of_start`. -/
theorem rightOfStart_allIdle (iHead : Γ) (wHeads : Fin k → Γ) (oHead : Γ) :
    (iHead = Γ.start → idleDir iHead = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → idleDir (wHeads i) = Dir3.right) ∧
    (oHead = Γ.start → idleDir oHead = Dir3.right) :=
  ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩

/-- `allReadBack` satisfies the one-sided-tape direction invariant. -/
theorem rightOfStart_allReadBack (iHead : Γ) (wHeads : Fin k → Γ) (oHead : Γ) :
    (iHead = Γ.start → idleDir iHead = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → idleDir (wHeads i) = Dir3.right) ∧
    (oHead = Γ.start → idleDir oHead = Dir3.right) :=
  ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩


end TM

end Complexity
