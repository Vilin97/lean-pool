/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Scanner
public import LeanPool.BeyondBethe.Complexitylib.Classes.Containments

/-!
# `lastBitOne` and `lastBitZero`: final-symbol languages

Strings whose last bit is `1` (resp. `0`); the empty string is not in
either language. Decided by a 3-state `scannerTM` instance: the scan state
is the last bit seen so far, or `none` if no bit has been read.

## Main definitions

- `Language.lastBitOne`, `Language.lastBitZero`.
- `TM.lastBitTM target` — `scannerTM` specialized to `target : Bool`.

## Main results

- `lastBitOne_in_DTIME`, `lastBitZero_in_DTIME` — both in `DTIME(n + 2)`.
- `lastBitOne_mem_P`, `lastBitZero_mem_P`.
-/


@[expose] public section

namespace Complexity

open Complexity

namespace TM

/-- Scanner for "last input bit equals `target`". Scan state: the last bit
    seen so far as an `Option Bool` (`none` initially). -/
def lastBitTM (target : Bool) : TM 0 :=
  scannerTM (S := Option Bool) none
    (fun _ b => some b)
    (fun s => if decide (s = some target) = true then Γw.one else Γw.zero)

end TM

namespace Language

/-- Strings whose last bit is `0` (empty string excluded). -/
def lastBitZero : Language := {x | x.getLast? = some false}

/-- Strings whose last bit is `1` (empty string excluded). -/
def lastBitOne : Language := {x | x.getLast? = some true}

end Language

-- ════════════════════════════════════════════════════════════════════════
-- Fold characterization
-- ════════════════════════════════════════════════════════════════════════

/-- Folding `(fun _ b => some b)` over a list with seed `s` yields
    `x.getLast?` if `x` is nonempty, else `s`. -/
private theorem lastBit_fold :
    ∀ (x : List Bool) (s : Option Bool),
      x.foldl (fun _ b => some b) s =
        (x.getLast?.orElse (fun _ => s)) := by
  intro x
  induction x with
  | nil => intro s; simp
  | cons b xs ih =>
    intro s
    rw [List.foldl_cons, ih]
    cases hxs : xs with
    | nil => simp
    | cons c cs =>
      simp [List.getLast?_cons, ← hxs]

/-- The last-bit scanner fold from `none` is exactly `List.getLast?`. -/
theorem lastBit_fold_eq_getLast? (x : List Bool) :
    x.foldl (fun _ b => some b) none = x.getLast? := by
  rw [lastBit_fold]
  cases x.getLast? <;> simp

-- ════════════════════════════════════════════════════════════════════════
-- DTIME memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`lastBitZero ∈ DTIME(n + 2)`**. -/
theorem lastBitZero_in_DTIME :
    Language.lastBitZero ∈ DTIME (fun n => n + 2) := by
  refine ⟨0, TM.lastBitTM false, fun n => n + 2, ?_, BigO.refl _⟩
  exact TM.scannerTM_decidesInTime (S := Option Bool) none
    (fun _ b => some b) (fun s => decide (s = some false))
    (L := Language.lastBitZero)
    (fun x => by
      show (x.getLast? = some false) ↔ (decide (x.foldl _ none = some false) = true)
      rw [lastBit_fold_eq_getLast?, decide_eq_true_iff])

/-- **`lastBitOne ∈ DTIME(n + 2)`**. -/
theorem lastBitOne_in_DTIME :
    Language.lastBitOne ∈ DTIME (fun n => n + 2) := by
  refine ⟨0, TM.lastBitTM true, fun n => n + 2, ?_, BigO.refl _⟩
  exact TM.scannerTM_decidesInTime (S := Option Bool) none
    (fun _ b => some b) (fun s => decide (s = some true))
    (L := Language.lastBitOne)
    (fun x => by
      show (x.getLast? = some true) ↔ (decide (x.foldl _ none = some true) = true)
      rw [lastBit_fold_eq_getLast?, decide_eq_true_iff])

-- ════════════════════════════════════════════════════════════════════════
-- P memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`lastBitZero ∈ P`**. -/
theorem lastBitZero_mem_P : Language.lastBitZero ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, DTIME_mono ?_ lastBitZero_in_DTIME⟩
  refine BigO.add ?_ (BigO.const_le_pow 2 1)
  simpa using BigO.refl (fun n : ℕ => n)

/-- **`lastBitOne ∈ P`**. -/
theorem lastBitOne_mem_P : Language.lastBitOne ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, DTIME_mono ?_ lastBitOne_in_DTIME⟩
  refine BigO.add ?_ (BigO.const_le_pow 2 1)
  simpa using BigO.refl (fun n : ℕ => n)

end Complexity
