/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import LeanPool.Polylean.ConjInvLength.ProvedBound

/-!
# LeanPool.Polylean.ConjInvLength.WordTree
-/

namespace LeanPool.Polylean

/-- A proof tree witnessing an upper bound for a word length. -/
inductive ProofTree : Word → Type where
  | emptyWord : ProofTree []
  | normalized : (l : Letter) → ProofTree [l]
  | conjugate : (l : Letter) → (w : Word) → ProofTree w → ProofTree (w^l)
  | triangleIneq : (w₁ : Word) → (w₂ : Word) →
                      ProofTree w₁ → ProofTree w₂ → ProofTree (w₁ ++ w₂)
  deriving Repr

namespace ProofTree

/-- The numeric bound represented by a proof tree. -/
def bound : (w : Word) → ProofTree w → Nat :=
  fun w t =>
    match t with
    | ProofTree.emptyWord => 0
    | ProofTree.normalized l => 1
    | ProofTree.conjugate l w t => bound w t
    | ProofTree.triangleIneq w₁ w₂ t₁ t₂ => bound w₁ t₁ + bound w₂ t₂

/-- Convert a proof tree into a certified bound. -/
def provedBound : (w : Word) → ProofTree w → ProvedBound w :=
  fun w t =>
    match t with
    | ProofTree.emptyWord => ProvedBound.emptyWord
    | ProofTree.normalized x =>
        ⟨1, fun l _ norm _ _ => by simp [norm x]⟩
    | ProofTree.conjugate x w t =>
        let pb := provedBound w t
        ⟨pb.bound, fun l emp norm conj triang =>
          conj x w ▸ pb.pf l emp norm conj triang⟩
    | ProofTree.triangleIneq w₁ w₂ t₁ t₂ =>
        let pb1 := provedBound w₁ t₁
        let pb2 := provedBound w₂ t₂
        ⟨pb1.bound + pb2.bound, fun l emp norm conj triang =>
          Nat.le_trans (triang w₁ w₂)
            (Nat.add_le_add (pb1.pf l emp norm conj triang) (pb2.pf l emp norm conj triang))⟩

/-- Combine proof trees across a split around a conjugating letter. -/
def headMatches (x : Letter) (ys fst snd : Word)
  (eqn : ys = fst ++ [x⁻¹] ++ snd) :
  ProofTree fst → ProofTree snd → ProofTree (x :: ys) := by
    intros pt1 pt2
    rw [conj_split x ys fst snd eqn]
    exact .triangleIneq _ _ (.conjugate x fst pt1) pt2

/-- Prepend a normalized letter to a proof tree. -/
def prepend {w : Word} (x : Letter)
        (pt : ProofTree w) : ProofTree (x :: w) := by
    change ProofTree ([x] ++ w)
    exact .triangleIneq [x] w (.normalized x) pt

/-- Choose the proof tree with the smallest bound from a nonempty list. -/
def min {w : Word} : ProofTree w → List (ProofTree w) →
    ProofTree w :=
        fun head tail =>
          tail.foldl (fun pt1 pt2 =>
            if pt1.bound ≤ pt2.bound then pt1 else pt2) head

end ProofTree

/-- A simple proof tree obtained by splitting a word into letters. -/
def simpleTree (w : Word) : ProofTree w :=
  match w with
  | [] => ProofTree.emptyWord
  | x :: ys => by
    change ProofTree ([x] ++ ys)
    exact .triangleIneq [x] ys (.normalized x) (simpleTree ys)


instance {w : Word} : Inhabited (ProofTree w) := ⟨simpleTree w⟩

/-- Compute a proof tree for a word. -/
def proofTree : (w : Word) → ProofTree w := fun w =>
  match h:w with
  | [] => ProofTree.emptyWord
  | x :: ys =>
    have : ys.length < (x :: ys).length := by simp
    let head := ProofTree.prepend x (proofTree ys)
    let splits := provedSplits x⁻¹ ys
    let tail := splits.map (fun ps : ProvedSplit x⁻¹ ys =>
      have l1 : ps.fst.length + 1 ≤ ys.length + 1 := by
        exact Nat.le_succ_of_le (splitFirst ps)
      have l2 : ps.snd.length + 1 ≤ ys.length + 1 := by
        exact Nat.le_succ_of_le (splitSecond ps)
      ProofTree.headMatches x ys ps.fst ps.snd ps.proof
        (proofTree ps.fst) (proofTree ps.snd))
    ProofTree.min head tail
termination_by w => w.length
decreasing_by
  · exact this
  · exact Nat.lt_of_succ_le (by simpa using l1)
  · exact Nat.lt_of_succ_le (by simpa using l2)

open Letter
end LeanPool.Polylean
