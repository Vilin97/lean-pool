/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import LeanPool.Polylean.ConjInvLength.LengthBound

/-!
# LeanPool.Polylean.ConjInvLength.ProvedBound
-/

namespace LeanPool.Polylean
open Letter

/-- A split of a word around a distinguished letter, with a proof of reconstruction. -/
structure ProvedSplit (l : Letter) (w : Word) where
  /-- The part before the distinguished letter. -/
  fst : Word
  /-- The part after the distinguished letter. -/
  snd : Word
  /-- Reconstruction proof for the split. -/
  proof : w = fst ++ [l] ++ snd


-- Split with first piece empty when head matches the splitting letter.
namespace ProvedSplit

/-- Split with the first piece empty when the head matches the splitting letter. -/
def head (x : Letter) (ys : Word) : ProvedSplit x (x :: ys) :=
  ⟨[], ys, rfl⟩

-- Prepend to a proved split of the tail (`l` and `ys` implicit).
/-- Prepend a letter to the first component of a proved split. -/
def prepend {l : Letter} {ys : Word} (x : Letter)
        (ps : ProvedSplit l ys) : ProvedSplit l (x :: ys) :=
      let newFst := x :: ps.fst
      let newSnd := ps.snd
      have newProof : x :: ys = newFst ++ [l] ++ newSnd  :=
        by
          rw [ps.proof]
          simp [newFst, newSnd]
      ⟨newFst, newSnd, newProof⟩

end ProvedSplit

-- all proved splits of a word
/-- All proved splits of a word around a letter. -/
def provedSplits (z : Letter) : (w : Word) → List (ProvedSplit z w)
  | [] => []
  | x :: ys =>
    let tailSplits := (provedSplits z ys).map (ProvedSplit.prepend x)
    if c:x = z then
      let headSplit : ProvedSplit z (x :: ys) := by rw [c]; exact ProvedSplit.head z ys
      headSplit :: tailSplits
    else tailSplits

/-- A length function on words. -/
abbrev Length := Word → Nat

/-- A length function invariant under conjugation by letters. -/
def conjInv (l : Length) : Prop := (x : Letter) → (g : Word) → l (g^x) = l (g)

/-- The triangle inequality for a length function. -/
def triangIneq (l : Length) : Prop := (g h : Word) → l (g ++ h) ≤ l g + l h

/-- A length function normalized on single letters. -/
def normalized (l : Length) : Prop := (x : Letter) → l [x] = 1

/-- A length function that sends the empty word to zero. -/
def emptyWord (l : Length) : Prop := l [] = 0

/-- A certified upper bound for the length of a word. -/
structure ProvedBound (g : Word) : Type where
  /-- The numeric upper bound. -/
  bound : Nat
  /-- The proof that every normalized conjugation-invariant length is bounded by `bound`. -/
  pf : (l : Length) → emptyWord l →
           normalized l → conjInv l → triangIneq l → l g ≤ bound

theorem conj_split (x : Letter) (ys fst snd : Word) :
          ys = fst ++ [x⁻¹] ++ snd → x :: ys = fst^x ++ snd := fun hyp => by
  rw [show fst^x = [x] ++ fst ++ [x⁻¹] from rfl, hyp]
  simp

-- deducing bound using `l (xh₁x⁻¹h₂) ≤ b₁ + b₂` given `l (hᵢ) ≤ bᵢ`, `i = 1, 2`
namespace ProvedBound

/-- Combine certified bounds across a split around a conjugating letter. -/
def headMatches (x : Letter) (ys fst snd : Word)
  (eqn : ys = fst ++ [x⁻¹] ++ snd) :
  ProvedBound fst → ProvedBound snd → ProvedBound (x :: ys) :=
    fun pb1 pb2 =>
    ⟨pb1.bound + pb2.bound, fun l emp norm conj triang => by
      rw [conj_split x ys fst snd eqn]
      have h1 := triang (fst^x) snd
      have h2 : l (fst^x) = l fst := conj x fst
      exact Nat.le_trans (h2 ▸ h1)
        (Nat.add_le_add (pb1.pf l emp norm conj triang) (pb2.pf l emp norm conj triang))⟩

-- deducing `l(xh) ≤ b + 1` given `l(h) ≤ b`
/-- Prepend a letter to a certified bound. -/
def prepend {w : Word} (x : Letter)
        (ps : ProvedBound w) : ProvedBound (x :: w) :=
      let newBound := ps.bound + 1
      ⟨newBound, fun l emp norm conj triang => by
        have lemTri : l (x :: w) ≤ l [x] + l w := triang [x] w
        rw [norm x] at lemTri
        apply Nat.le_trans lemTri
        rw [Nat.add_comm]
        apply Nat.add_le_add_right (ps.pf l emp norm conj triang)⟩

-- `l(e) ≤ 0`
/-- The zero bound for the empty word. -/
def emptyWord : ProvedBound [] :=
  ⟨0, fun l emp _ _ _ => by
    rw [emp]
    apply Nat.zero_le⟩

-- the best proved bound for a word
/-- Choose the better bound from a nonempty list of alternatives. -/
def min {w : Word} : ProvedBound w → List (ProvedBound w) →
    ProvedBound w :=
        fun head tail =>
          tail.foldl (fun pb1 pb2 =>
            if pb1.bound ≤ pb2.bound then pb1 else pb2) head

end ProvedBound

theorem splitFirst {l : Letter} {w : Word} (ps : ProvedSplit l w) :
          ps.fst.length + 1 ≤ w.length := by
  have h := congr_arg List.length ps.proof
  simp [List.length_append] at h
  omega

theorem splitSecond {l : Letter} {w : Word} (ps : ProvedSplit l w) :
          ps.snd.length + 1 ≤ w.length := by
  have h := congr_arg List.length ps.proof
  simp [List.length_append] at h
  omega

-- bound with proof for words
/-- Compute a certified length bound for a word. -/
def provedBound : (w : Word) → ProvedBound w := fun w =>
  match h:w with
  | [] => ProvedBound.emptyWord
  | x :: ys =>
    let head := ProvedBound.prepend x (provedBound ys)
    let splits := provedSplits x⁻¹ ys
    let tail := splits.map (fun ps : ProvedSplit x⁻¹ ys =>
      have l1 : ps.fst.length + 1 ≤ ys.length + 1 := by
        exact Nat.le_succ_of_le (splitFirst ps)
      have l2 : ps.snd.length + 1 ≤ ys.length + 1 := by
        exact Nat.le_succ_of_le (splitSecond ps)
      ProvedBound.headMatches x ys ps.fst ps.snd ps.proof
        (provedBound ps.fst) (provedBound ps.snd))
    ProvedBound.min head tail
termination_by w => w.length
end LeanPool.Polylean
