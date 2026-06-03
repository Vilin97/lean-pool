/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import Std.Data.HashMap
import LeanPool.Polylean.ConjInvLength.LengthBound

/-!
# LeanPool.Polylean.ConjInvLength.MemoLength
-/

namespace LeanPool.Polylean

/-- Cache for memoized word lengths. -/
initialize normCache : IO.Ref (Std.HashMap Word Nat) ← IO.mkRef Std.HashMap.emptyWithCapacity

/-- Memoized list-backed conjugation-invariant length candidate. -/
def memoLength : Word → IO Nat := fun w => do
  let cache ← normCache.get
  match cache.get? w with
  | some n =>
      pure n
  | none =>
    match w with
    | [] => return 0
    | x :: ys => do
      have lb : (List.length ys) < List.length (x :: ys) := by
        simp [List.length_cons]
      let base := 1 + (← memoLength ys)
      let derived ←  (splits x⁻¹ ys).mapM fun ⟨(fst, snd), h⟩ => do
        have h : fst.length + snd.length < ys.length + 1 := Nat.lt_trans h (Nat.lt_succ_self _)
        have h1 : snd.length < ys.length + 1  := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h
        have h2 : fst.length < ys.length + 1 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h
        return (← memoLength fst) + (← memoLength snd)
      let res := derived.foldl min base -- minimum of base and elements of derived
      normCache.set <| (← normCache.get).insert w res
      return res
termination_by l => l.length
end LeanPool.Polylean
