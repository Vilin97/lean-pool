/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Finite inverse automata and subgroup membership

A finite graph with inverse-labelled edges and at most one outgoing edge of
each label from each vertex is represented by its partial transition map.
This file proves that the labels of loops at a chosen basepoint form a
subgroup of the free group, and that membership in this subgroup is exactly a
finite traversal test on the canonical reduced word.
-/

@[expose] public section

namespace Stallings

/-- A letter in the rank-two free group, with a Boolean recording orientation. -/
abbrev Letter := Fin 2 × Bool

/-- A word in the signed generators `a`, `b`, `a⁻¹`, and `b⁻¹`. -/
abbrev Word := List Letter

/-- The free group on two generators. -/
abbrev Free := FreeGroup (Fin 2)

/-- Reverse the orientation of a letter. -/
def letterInv (x : Letter) : Letter := (x.1, !x.2)

@[simp]
theorem letterInv_letterInv (x : Letter) : letterInv (letterInv x) = x := by
  cases x with
  | mk i b => cases b <;> rfl

/-- The inverse word, obtained by reversing and inverting its letters. -/
def wordInv (w : Word) : Word := FreeGroup.invRev w

/-- Interpret a signed word as an element of the free group. -/
def wordEval (w : Word) : Free := FreeGroup.mk w

/-- Interpret one signed generator as an element of the free group. -/
def letterEval (x : Letter) : Free :=
  if x.2 then FreeGroup.of x.1 else (FreeGroup.of x.1)⁻¹

@[simp]
theorem wordEval_nil : wordEval [] = 1 := by
  simpa [wordEval] using (FreeGroup.one_eq_mk : (1 : Free) = FreeGroup.mk []) |>.symm

@[simp]
theorem wordEval_append (u v : Word) : wordEval (u ++ v) = wordEval u * wordEval v := by
  simp [wordEval, FreeGroup.mul_mk]

theorem wordEval_singleton (x : Letter) : wordEval [x] = letterEval x := by
  cases x with
  | mk i b => cases b <;> simp [wordEval, letterEval, FreeGroup.of, FreeGroup.invRev]

@[simp]
theorem wordEval_cons (x : Letter) (w : Word) :
    wordEval (x :: w) = letterEval x * wordEval w := by
  rw [show x :: w = [x] ++ w by rfl, wordEval_append, wordEval_singleton]

@[simp]
theorem letterEval_inv (x : Letter) : letterEval (letterInv x) = (letterEval x)⁻¹ := by
  cases x with
  | mk i b => cases b <;> simp [letterInv, letterEval]

@[simp]
theorem wordEval_wordInv (w : Word) : wordEval (wordInv w) = (wordEval w)⁻¹ := by
  simp [wordEval, wordInv, FreeGroup.inv_mk]

/-- A deterministic graph whose edges come in inverse-labelled pairs.

The transition function is partial: `none` means that no edge with that label
leaves the given vertex. -/
structure InverseAutomaton (V : Type*) where
  /-- The vertex at which accepted loops start and end. -/
  base : V
  /-- The target of a labelled edge, when that edge exists. -/
  next : V → Letter → Option V
  inverse_next : ∀ {v x w}, next v x = some w → next w (letterInv x) = some v

namespace InverseAutomaton

variable {V : Type*} (G : InverseAutomaton V)

/-- Execute a word from a starting state, stopping if a required edge is absent. -/
def run (G : InverseAutomaton V) (v : V) : Word → Option V
  | [] => some v
  | x :: w => (G.next v x).bind fun u => G.run u w

@[simp]
theorem run_nil (v : V) : G.run v [] = some v := rfl

/-- A labelled path in an inverse automaton. -/
inductive Walk : V → Word → V → Prop where
  | nil (v : V) : Walk v [] v
  | cons {v u z : V} {x : Letter} {w : Word}
      (edge : G.next v x = some u) (tail : Walk u w z) : Walk v (x :: w) z

/-- The executable traversal returns an endpoint exactly when the corresponding path exists. -/
theorem run_eq_some_iff_walk {v z : V} {w : Word} :
    G.run v w = some z ↔ G.Walk v w z := by
  induction w generalizing v z with
  | nil =>
      simp only [run, Option.some.injEq]
      constructor
      · intro h
        subst z
        exact Walk.nil v
      · intro h
        cases h
        rfl
  | cons x w ih =>
      constructor
      · intro h
        cases hnext : G.next v x with
        | none => simp [run, hnext] at h
        | some u =>
            simp only [run, hnext, Option.bind_some] at h
            exact Walk.cons hnext ((ih (v := u) (z := z)).mp h)
      · intro h
        cases h with
        | cons hnext htail =>
            simp [run, hnext, (ih (v := _) (z := _)).mpr htail]

/-- Concatenate two paths whose endpoints match. -/
theorem Walk.append {v u t : V} {w₁ w₂ : Word}
    (h₁ : G.Walk v w₁ u) (h₂ : G.Walk u w₂ t) : G.Walk v (w₁ ++ w₂) t := by
  induction h₁ with
  | nil => simpa using h₂
  | @cons v u z x w edge tail ih =>
      simpa using Walk.cons edge (ih h₂)

/-- Reversing a path and inverting every label gives the reverse path. -/
theorem Walk.invRev {v u : V} {w : Word} (h : G.Walk v w u) :
    G.Walk u (wordInv w) v := by
  induction h with
  | nil v => exact Walk.nil v
  | @cons v u z x w edge tail ih =>
      have inverseEdge : G.Walk u [letterInv x] v :=
        Walk.cons (G.inverse_next edge) (Walk.nil v)
      rw [wordInv, FreeGroup.invRev_cons]
      change G.Walk z (wordInv w ++ [letterInv x]) v
      exact Walk.append G ih inverseEdge

/-- Traversal distributes over concatenation of words. -/
theorem run_append (v : V) (u z : Word) :
    G.run v (u ++ z) = (G.run v u).bind fun t => G.run t z := by
  induction u generalizing v with
  | nil => rfl
  | cons x u ih =>
      change (G.next v x).bind (fun t => G.run t (u ++ z)) =
        ((G.next v x).bind (fun t => G.run t u)).bind (fun t => G.run t z)
      calc
        _ = (G.next v x).bind (fun t => (G.run t u).bind fun q => G.run q z) := by
          congr 1
          funext t
          exact ih t
        _ = _ := (Option.bind_assoc _ _ _).symm

/-- A successful traversal remains successful after cancelling a letter pair. -/
theorem run_success_cancel (v : V) (pre suffix : Word) (x : Letter)
    {z : V}
    (h : G.run v (pre ++ x :: letterInv x :: suffix) = some z) :
    G.run v (pre ++ suffix) = some z := by
  rw [G.run_append v pre (x :: letterInv x :: suffix)] at h
  rw [G.run_append v pre suffix]
  cases hp : G.run v pre with
  | none => simp [hp] at h
  | some s =>
      rw [hp] at h
      change G.run s (x :: letterInv x :: suffix) = some z at h
      change G.run s suffix = some z
      cases he : G.next s x with
      | none => simp [run, he] at h
      | some t =>
          have ht : G.next t (letterInv x) = some s := G.inverse_next he
          simpa [run, he, ht] using h

/-- A successful traversal remains successful under one free-reduction step. -/
theorem run_success_of_red_step (v : V) {w z : Word}
    (h : FreeGroup.Red.Step w z) {t : V}
    (hRun : G.run v w = some t) : G.run v z = some t := by
  cases h with
  | not => exact G.run_success_cancel v _ _ _ hRun

/-- A successful traversal remains successful after any sequence of free reductions. -/
theorem run_success_of_red (v : V) {w z : Word}
    (h : FreeGroup.Red w z) {t : V}
    (hRun : G.run v w = some t) : G.run v z = some t := by
  induction h generalizing t hRun with
  | refl => exact hRun
  | tail hred hstep ih =>
      exact G.run_success_of_red_step v hstep (ih hRun)

/-- A successful traversal remains successful on the canonical reduced word. -/
theorem run_success_of_reduction (v : V) (w : Word) {t : V}
    (hRun : G.run v w = some t) :
    G.run v (FreeGroup.reduce w) = some t :=
  G.run_success_of_red v (FreeGroup.reduce.red) hRun
/-- The subgroup represented by all loops at the basepoint. -/
def loopSubgroup : Subgroup Free where
  carrier := {g | ∃ w : Word, wordEval w = g ∧ G.Walk G.base w G.base}
  one_mem' := by
    exact ⟨[], by simpa [wordEval] using FreeGroup.one_eq_mk.symm, Walk.nil G.base⟩
  mul_mem' := by
    intro g h hg hh
    rcases hg with ⟨w, hw, hwalk⟩
    rcases hh with ⟨v, hv, hvwalk⟩
    refine ⟨w ++ v, ?_, Walk.append G hwalk hvwalk⟩
    rw [wordEval_append, hw, hv]
  inv_mem' := by
    intro g hg
    rcases hg with ⟨w, hw, hwalk⟩
    refine ⟨wordInv w, ?_, Walk.invRev G hwalk⟩
    rw [wordEval_wordInv, hw]

/-- Membership in the loop subgroup is decided by traversing the canonical reduced word. -/
def accepts (g : Free) : Prop := G.run G.base (FreeGroup.toWord g) = some G.base

theorem accepts_iff_mem_loopSubgroup (g : Free) :
    G.accepts g ↔ g ∈ G.loopSubgroup := by
  constructor
  · intro h
    refine ⟨FreeGroup.toWord g, ?_, (run_eq_some_iff_walk G).mp h⟩
    simpa [wordEval] using (FreeGroup.mk_toWord (x := g))
  · rintro ⟨w, hw, hwalk⟩
    subst g
    have hrun := (run_eq_some_iff_walk G).2 hwalk
    exact G.run_success_of_reduction G.base w hrun

/-- Executable subgroup-membership test for a finite inverse automaton. -/
def membershipTest [DecidableEq V] (G : InverseAutomaton V) (g : Free) : Bool :=
  if G.run G.base (FreeGroup.toWord g) = some G.base then true else false

@[simp]
theorem membershipTest_eq_true_iff [DecidableEq V] (G : InverseAutomaton V) (g : Free) :
    G.membershipTest g = true ↔ g ∈ G.loopSubgroup := by
  simpa [membershipTest, accepts] using G.accepts_iff_mem_loopSubgroup g

end InverseAutomaton

end Stallings
