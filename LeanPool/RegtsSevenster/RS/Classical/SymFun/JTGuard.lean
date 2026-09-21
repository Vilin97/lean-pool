/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.TIdentity

/-!
# Guard and margin bridges for the double-sum identity

The staircase guard of the double-sum identity matches the signed
nonnegativity guard of the Jacobi–Trudi character, the shifted
margins match the shifted compositions, and sorted shapes have
injective staircase exponents.
-/

namespace RS

open Finset Equiv

variable {k : ℕ}

/-- The staircase-shifted exponent at a row. -/
theorem diagExp_apply (v : Fin k → ℕ) (j : Fin k) :
    diagExp v j = v j + ((k - 1) - (j : ℕ)) :=
  sum_single_apply (fun i => v i + ((k - 1) - (i : ℕ))) j

/-- The staircase guard is the signed nonnegativity guard. -/
theorem stair_guard_iff (v : Fin k → ℕ) (τ : Equiv.Perm (Fin k)) :
    stairShift τ ≤ diagExp v ↔
      ∀ i : Fin k, 0 ≤ (v i : ℤ) + ((τ i : Fin k) : ℕ) - (i : ℕ) := by
  rw [Finsupp.le_def]
  constructor
  · intro h i
    have h1 := h i
    rw [stairShift_apply, diagExp_apply] at h1
    have hi := i.isLt
    have hti := (τ i).isLt
    omega
  · intro h i
    rw [stairShift_apply, diagExp_apply]
    have h1 := h i
    have hi := i.isLt
    have hti := (τ i).isLt
    omega

/-- The shifted margin is the shifted composition. -/
theorem stair_margin_eq (v : Fin k → ℕ) (τ : Equiv.Perm (Fin k))
    (h : stairShift τ ≤ diagExp v) (j : Fin k) :
    (diagExp v - stairShift τ) j =
      ((v j : ℤ) + ((τ j : Fin k) : ℕ) - (j : ℕ)).toNat := by
  rw [Finsupp.tsub_apply, stairShift_apply, diagExp_apply]
  have h1 := (stair_guard_iff v τ).mp h j
  have hj := j.isLt
  have htj := (τ j).isLt
  omega

/-- Sorted shapes have injective staircase exponents. -/
theorem staircase_injective (v : Fin k → ℕ)
    (hsort : ∀ i j : Fin k, i ≤ j → v j ≤ v i) :
    Function.Injective
      (fun i : Fin k => v i + ((k - 1) - (i : ℕ))) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := hsort i j (le_of_lt hlt)
    have hi := i.isLt
    have hj := j.isLt
    have hij' : (i : ℕ) < (j : ℕ) := hlt
    simp only at hij
    omega
  · have h1 := hsort j i (le_of_lt hlt)
    have hi := i.isLt
    have hj := j.isLt
    have hij' : (j : ℕ) < (i : ℕ) := hlt
    simp only at hij
    omega

end RS
