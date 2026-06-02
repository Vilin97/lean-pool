/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import Std.Data.HashMap
import LeanPool.Polylean.ConjInvLength.LengthBound

/-!
# LeanPool.Polylean.ConjInvLength.Length
-/

namespace LeanPool.Polylean
open Letter

namespace Letter

/-- Integer code for each letter. -/
def int : Letter → Int
  | α => 1
  | β => 2
  | α! => -1
  | β! => -2

end Letter

open Letter

instance : Pow Word Nat where
  pow w n := w.pow n

/-- Array-backed words used by the memoized length computation. -/
abbrev Wrd := Array Letter

namespace Word

/-- Convert a list-backed word to an array-backed word. -/
def wrd (w : Word) : Wrd := w.toArray -- .map <| fun l => l.int

end Word

namespace Wrd

/-- Render an array-backed word by concatenating rendered letters. -/
def toString (w : Wrd) := w.foldl (fun x y => s!"{x}{y}") ""

instance : ToString Wrd := ⟨Wrd.toString⟩

/-- Repeated concatenation of an array-backed word. -/
def pow : Wrd → Nat → Wrd
  | _, 0 => #[]
  | w, Nat.succ m => w ++ (pow w m)

instance : Pow Wrd Nat where
  pow w n := w.pow n

/-- Hash function for array-backed words. -/
def hashfn (w : Wrd) : UInt64 :=
  w.foldl (fun h i => mixHash h (hash i)) 7

instance : Hashable Wrd := ⟨hashfn⟩

/-- Cache for normalized word lengths. -/
initialize normCache : IO.Ref (Std.HashMap Wrd Nat) ← IO.mkRef Std.HashMap.emptyWithCapacity

/-- All splits of an array-backed word around occurrences of a letter. -/
def splits (l : Letter) :
    (w : Wrd) → Array {p : Wrd × Wrd // p.1.size + p.2.size < w.size} := fun w =>
  match h:w.size with
  | 0 => #[]
  | m + 1  =>
    let x := w.back
    have _ : w.size -1 < w.size := by
      rw [h]
      apply Nat.le_refl
    let ys := w.pop
    have ysize : ys.size = m := by
      rw [Array.size_pop, h]
      rfl
    let tailSplits := (splits l ys).map fun ⟨(fst, snd), h⟩ =>
      ⟨(fst, snd.push x), by
        rw [Array.size_push]
        rw [ysize] at h
        simp at h
        rw [← Nat.add_assoc]
        simp [Nat.succ_lt_succ h]⟩
    if x = l then tailSplits.push ⟨(ys, #[]),
      by
        rw [ysize]
        apply Nat.le_refl⟩ else tailSplits
termination_by  w => w.size

/-- Memoized conjugation-invariant length candidate for array-backed words. -/
def length (w : Wrd) : IO Nat :=
do
  let cache ← normCache.get
  match cache.get? w with
  | some n =>
      pure n
  | none =>
    let res ←
      match h:w.size with
      | 0 => pure 0
      | m + 1 => do
        let ys := w.pop
        let x := w.back
        have lll : w.size -1 < w.size := by
          rw [h]
          apply Nat.le_refl
        let base := 1 + (← length <| ys)
        let derived ←  (splits x⁻¹ ys).mapM fun ⟨(fst, snd), h0⟩ =>
          have ysize : ys.size = m := by
            rw [Array.size_pop, h]
            rfl
          have h0 : fst.size + snd.size < w.size := by
            rw [h]
            rw [← ysize]
            apply Nat.lt_trans h0 (Nat.lt_succ_self _)
          have _ : snd.size < w.size  := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h0
          have _ : fst.size < w.size := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h0
          return (← length fst) + (← length snd)
        derived.foldl (fun x y => do return min (← x) y) (pure base)
    normCache.set <| (← normCache.get).insert w res
    return res
termination_by w.size

end Wrd

/-- Memoized length for list-backed words. -/
def wordLength (w : Word) : IO Nat :=
  Wrd.length <| Word.wrd w

namespace Wrd

/-- Conjugate an array-backed word by a letter. -/
def conj : Wrd → Letter → Wrd := fun w l => #[l] ++ w ++ #[l⁻¹]

end Wrd

instance : Pow Wrd Letter where
  pow w l := w.conj l
end LeanPool.Polylean
