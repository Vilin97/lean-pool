/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.SAT.Rename
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# 3-CNF formulas

The **3-CNF** refinement of the existing `CNF` type: a CNF is in 3-CNF when every
clause has exactly three literals. Following the roadmap (track N3), 3-CNF is
introduced here as a *predicate* on the existing `CNF = List Clause`, so that all
of the `CNF` semantics (`CNF.eval`, `CNF.Satisfiable`, `CNF.maxVar`, renaming)
apply unchanged and a 3-CNF is literally a CNF.

## Main definitions and results

- `CNF.Is3CNF` — every clause has length `3`; decidable
- `CNF.is3CNF_cons` — the cons characterization
- `CNF.Is3CNF.mapVar` — variable renaming preserves the 3-CNF shape

The substantive N3 milestone — a size-controlled clause-padding transformation
turning an arbitrary CNF into an equisatisfiable 3-CNF — builds on this predicate
and is tracked separately.
-/


@[expose] public section

namespace Complexity

namespace SAT

/-- A CNF is in **3-CNF** when every clause is a disjunction of exactly three
    literals. This is a predicate on the existing `CNF` type, so a 3-CNF formula
    is literally a `CNF` and inherits all of its semantics. -/
def CNF.Is3CNF (φ : CNF) : Prop := ∀ c ∈ φ, c.length = 3

instance (φ : CNF) : Decidable (CNF.Is3CNF φ) := List.decidableBAll _ _

/-- The empty CNF is trivially in 3-CNF. -/
@[simp] theorem CNF.is3CNF_nil : CNF.Is3CNF [] := by
  simp [CNF.Is3CNF]

/-- `c :: φ` is 3-CNF iff `c` has three literals and `φ` is 3-CNF. -/
@[simp] theorem CNF.is3CNF_cons {c : Clause} {φ : CNF} :
    CNF.Is3CNF (c :: φ) ↔ c.length = 3 ∧ CNF.Is3CNF φ :=
  List.forall_mem_cons

/-- Variable renaming preserves the 3-CNF shape: `Clause.mapVar` maps literals
    one-for-one, so it does not change clause lengths. -/
theorem CNF.Is3CNF.mapVar {φ : CNF} (h : CNF.Is3CNF φ) (f : ℕ → ℕ) :
    CNF.Is3CNF (CNF.mapVar f φ) := by
  intro c hc
  rw [CNF.mapVar] at hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  rw [Clause.mapVar, List.length_map]
  exact h c' hc'

/-! ### Padding short clauses to width three

A clause with one or two literals is padded to exactly three literals by
repeating its last literal. This changes neither the clause's models nor its
satisfiability (repeating a literal in a disjunction is idempotent), and turns a
CNF whose clauses all have width `1 … 3` into an equivalent 3-CNF. Splitting
*wide* clauses (width `> 3`) needs fresh Tseitin variables and is tracked
separately. -/

/-- Pad a clause of one or two literals to width three by repeating a literal;
    clauses of any other width are left unchanged. -/
def Clause.padTo3 : Clause → Clause
  | [a] => [a, a, a]
  | [a, b] => [a, b, b]
  | c => c

/-- Padding preserves the clause's value under every assignment (repeating a
    literal in a disjunction is idempotent). -/
theorem Clause.padTo3_eval (α : Assignment) (c : Clause) :
    Clause.eval α (Clause.padTo3 c) = Clause.eval α c := by
  match c with
  | [] => rfl
  | [a] => simp [Clause.padTo3, Clause.eval]
  | [a, b] => simp [Clause.padTo3, Clause.eval]
  | a :: b :: _ :: _ => rfl

/-- A clause of width `1 … 3` is padded to width exactly three. -/
theorem Clause.padTo3_length {c : Clause} (h1 : 1 ≤ c.length) (h2 : c.length ≤ 3) :
    (Clause.padTo3 c).length = 3 := by
  match c with
  | [a] => rfl
  | [a, b] => rfl
  | [a, b, d] => rfl
  | [] => simp at h1
  | a :: b :: d :: e :: t => simp only [List.length_cons] at h2; omega

/-- Pad every clause of a CNF to width three. -/
def CNF.padTo3 (φ : CNF) : CNF := φ.map Clause.padTo3

/-- Padding preserves the CNF's value under every assignment — hence
    satisfiability. -/
theorem CNF.padTo3_eval (α : Assignment) (φ : CNF) :
    CNF.eval α (CNF.padTo3 φ) = CNF.eval α φ := by
  unfold CNF.padTo3
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [List.map_cons, CNF.eval_cons, Clause.padTo3_eval, ih]

/-- Padding preserves satisfiability. -/
theorem CNF.padTo3_satisfiable_iff (φ : CNF) :
    CNF.Satisfiable (CNF.padTo3 φ) ↔ CNF.Satisfiable φ := by
  simp only [CNF.Satisfiable, CNF.padTo3_eval]

/-- If every clause of `φ` has width `1 … 3`, then `CNF.padTo3 φ` is a genuine
    3-CNF equivalent to `φ`. -/
theorem CNF.is3CNF_padTo3 {φ : CNF}
    (h : ∀ c ∈ φ, 1 ≤ c.length ∧ c.length ≤ 3) : CNF.Is3CNF (CNF.padTo3 φ) := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  obtain ⟨h1, h2⟩ := h c' hc'
  exact Clause.padTo3_length h1 h2

end SAT

end Complexity
