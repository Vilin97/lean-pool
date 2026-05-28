/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import Mathlib.Algebra.Group.Defs

namespace LeanPool.Polylean
/-- The four generators used for words in the conjugation-invariant length example. -/
inductive Letter where
  | α : Letter
  | β : Letter
  | α! : Letter
  | β! : Letter
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace Letter

/-- Render a letter as a string. -/
def toString : Letter → String
| α => "α"
| β => "β"
| α! => "alpha!"
| β! => "beta!"

instance : ToString Letter := ⟨Letter.toString⟩

/-- The formal inverse of a letter. -/
def inv : Letter → Letter
  | α => α!
  | β  => β!
  | α! => α
  | β! => β

end Letter

@[inline] instance letInv : Inv Letter := ⟨Letter.inv⟩


open Letter

/-- A word is a list of letters. -/
abbrev Word := List Letter

namespace Word

/-- Render a word by concatenating its rendered letters. -/
def toString (w : Word) := w.foldl (fun x y => s!"{x}{y}") ""

instance : ToString Word := ⟨Word.toString⟩

/-- Repeated concatenation of a word. -/
def pow : Word → Nat → Word
  | _, 0 => []
  | w, Nat.succ m => w ++ (pow w m)

instance : Pow Word Nat where
  pow w n := w.pow n

end Word

-- The code below (with better termination) is due to Mario Carneiro
-- split a word into parts before and after each occurrence of a letter `l`
/-- All splits of a word around occurrences of a letter, with length witnesses. -/
def splits (l : Letter) : (w : Word) → List {p : Word × Word // p.1.length + p.2.length < w.length}
  | [] => []
  | x :: ys =>
    let tailSplits := (splits l ys).map fun ⟨(fst, snd), h⟩ =>
      ⟨(x :: fst, snd), by simp [Nat.succ_add, Nat.succ_lt_succ h]⟩
    if x = l then ⟨([], ys), by simp⟩ :: tailSplits else tailSplits

/-- A recursively computed conjugation-invariant length candidate. -/
def length : Word → Nat
  | [] => 0
  | x :: ys =>
    have lb : (List.length ys) < List.length (x :: ys) := by
      simp [List.length_cons]
    let base := 1 + (length ys)
    let derived := (splits x⁻¹ ys).map fun ⟨(fst, snd), h⟩ =>
      have h : fst.length + snd.length < ys.length + 1 := Nat.lt_trans h (Nat.lt_succ_self _)
      have _ : snd.length < ys.length + 1  := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h
      have _ : fst.length < ys.length + 1 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h
      length fst + length snd
    derived.foldl min base -- minimum of base and elements of derived
termination_by l => l.length

-- For proofs

namespace Word

/-- Conjugate a word by a letter. -/
def conj : Word → Letter → Word := fun w l => [l] ++ w ++ [l⁻¹]

end Word

instance : Pow Word Letter where
  pow w l := w.conj l
end LeanPool.Polylean
