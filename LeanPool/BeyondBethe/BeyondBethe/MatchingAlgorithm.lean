/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.Permanent
public import Mathlib.Tactic

/-! # Matching Algorithm -/

@[expose] public section

namespace BeyondBethe

/-!
# Executable support matching

This first executable decision procedure is the finite reference
specification.  A polynomial augmenting-path implementation will be proved
extensionally equal to it below; the wrapper can therefore remain independent
of propositional decidability throughout that refinement.
-/

def supportMatchingDecision {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  decide (∃ σ : Equiv.Perm (Fin n), ∀ i, A (σ i) i ≠ 0)

theorem supportMatchingDecision_eq_true_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    supportMatchingDecision A = true ↔ Matrix.HasPerfectMatching A := by
  simp [supportMatchingDecision, Matrix.HasPerfectMatching]

theorem supportMatchingDecision_eq_false_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    supportMatchingDecision A = false ↔ ¬Matrix.HasPerfectMatching A := by
  simp [supportMatchingDecision, Matrix.HasPerfectMatching]

end BeyondBethe
