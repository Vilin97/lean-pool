/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Zify

/-!
# Numerical parameters for the Bombieri--Stepanov argument

The sharp parameter choice in Tao's exposition uses a floor.  The BGS
application only needs a universal bidegree multiple of the square-root
error, so it is cleaner to use

`ell = s - 1`, `m = s + 2 * g`

when the square-root field size `s` is at least `(g + 1) * (g + 2)`.
These parameters satisfy the three inequalities needed by the one-point
Riemann-space argument, and give the same `O(g * s)` error term.
-/

namespace BGS.HasseWeil

/-- The slightly non-sharp parameters used in the formal Stepanov argument. -/
def stepanovEll (s : ℕ) : ℕ := s - 1

/-- The second tensor-factor parameter used in the formal Stepanov argument. -/
def stepanovM (g s : ℕ) : ℕ := s + 2 * g

/-- The first parameter is strictly smaller than the Frobenius scale. -/
theorem stepanovEll_lt
    {g s : ℕ} (hlarge : (g + 1) * (g + 2) ≤ s) :
    stepanovEll s < s := by
  have hs : 0 < s := by nlinarith
  simp only [stepanovEll]
  omega

/-- Both tensor factors are large enough for Riemann's inequality. -/
theorem stepanov_genus_le_parameters
    {g s : ℕ} (hlarge : (g + 1) * (g + 2) ≤ s) :
    g ≤ stepanovEll s + 1 ∧ g ≤ stepanovM g s + 1 := by
  have hgs : g ≤ s := by nlinarith
  constructor
  · simp only [stepanovEll]
    omega
  · simp only [stepanovM]
    omega

/-- The tensor-product dimension lower bound is strictly larger than the
dimension upper bound for the second Frobenius restriction map. -/
theorem stepanov_dimension_inequality
    {g s : ℕ} (hlarge : (g + 1) * (g + 2) ≤ s) :
    (stepanovEll s + 1 - g) * (stepanovM g s + 1 - g) >
      stepanovEll s * s + stepanovM g s + 1 := by
  have hs : 0 < s := by nlinarith
  have hgs : g ≤ s := by nlinarith
  have hfirst : stepanovEll s + 1 - g = s - g := by
    simp only [stepanovEll]
    omega
  have hsecond : stepanovM g s + 1 - g = s + g + 1 := by
    simp only [stepanovM]
    omega
  rw [hfirst, hsecond]
  simp only [stepanovEll, stepanovM]
  have hsOne : 1 ≤ s := by omega
  have hlargeZ :
      (((g + 1) * (g + 2) : ℕ) : ℤ) ≤ (s : ℤ) := by
    exact_mod_cast hlarge
  have hgoalZ :
      (((s - g : ℕ) : ℤ) * ((s + g + 1 : ℕ) : ℤ)) >
        (((s - 1 : ℕ) : ℤ) * (s : ℤ) + ((s + 2 * g : ℕ) : ℤ) + 1) := by
    rw [Nat.cast_sub hgs, Nat.cast_sub hsOne]
    push_cast at hlargeZ ⊢
    nlinarith
  exact_mod_cast hgoalZ

/-- The resulting zero-count bound is at most
`s^2 + (2g+1)s`; this is the weak Hasse--Weil upper bound needed later. -/
theorem stepanov_zero_bound
    {g s : ℕ} (hs : 0 < s) :
    stepanovEll s + stepanovM g s * s ≤
      s ^ 2 + (2 * g + 1) * s := by
  simp only [stepanovEll, stepanovM]
  nlinarith [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hs.ne')]

end BGS.HasseWeil
