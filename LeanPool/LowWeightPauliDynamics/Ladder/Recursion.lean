/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Ladder.Defs
public import LeanPool.LowWeightPauliDynamics.Ladder.HockeyStick
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-!
# Single-jump cumulation

This file proves the binomial cumulation bound for the abstract damped ladder `Lean4LPD.Ladder`,
formalizing part (i) of `apd:cor:norm_cumulation_jump`:

  `N_{≥m}^{(g)} ≤ C(g, m) · sin^m(dt) · ‖O‖`.

The proof follows the paper's: an induction over `m` whose inner step iterates the flow
recursion over `g` and closes with the hockey-stick identity (`sum_range_choose_real`).

The base case is the reservoir bound `N_{≥0}^{(l)} ≤ ‖O‖`. Unitary invariance of the 2-norm
gives it at **every** `l`, not only at `l = 0`, so the induction hypothesis and the
conclusion have the same shape.

## Main results

* `Ladder.step_iterate`: the flow recursion summed over the `g` steps.
* `Ladder.cumulation`: `N m g ≤ C(g, m) · a^m · M`.
-/

public section

namespace Lean4LPD.Ladder

open Finset

variable {a M : ℝ} (L : Ladder a M)

/-- Iterating the flow recursion over the `g` steps, using `N m 0 = 0` for `m ≥ 1` to kill the
boundary term. This is the display `N^{(g)}_{≥m} ≤ sin(dt) ∑_{l=0}^{g-1} N^{(l)}_{≥m-1}` in the
proof of `apd:cor:norm_cumulation_jump`.

Note this needs no sign hypothesis on the damping factor `a`: the paper states the recursion
with `a = sin(dt) ≥ 0`, but the iteration itself is monotone regardless. -/
lemma step_iterate {m : ℕ} (hm : 1 ≤ m) :
    ∀ g : ℕ, L.N m g ≤ a * ∑ l ∈ range g, L.N (m - 1) l := by
  intro g
  induction g with
  | zero => simp [L.init m hm]
  | succ g ih =>
    calc L.N m (g + 1)
        ≤ L.N m g + a * L.N (m - 1) g := L.step m g hm
      _ ≤ (a * ∑ l ∈ range g, L.N (m - 1) l) + a * L.N (m - 1) g := by linarith
      _ = a * ∑ l ∈ range (g + 1), L.N (m - 1) l := by
          rw [Finset.sum_range_succ]; ring

/-- **Single-jump cumulation.** Formalizes `apd:cor:norm_cumulation_jump` (i): after any `g`
Pauli rotations,

  `N_{≥m}^{(g)} ≤ C(g, m) · a^m · M`,

where `a = sin(dt)` is the damping factor and `M = ‖O‖_{2,normalized}`.

The total mass enters with coefficient one: the base case `m = 0` is the reservoir bound
`N 0 g ≤ M`, valid for every `g`. The only sign hypothesis is `0 ≤ a`, used to multiply the
inductive hypothesis through the recursion. -/
theorem cumulation (ha : 0 ≤ a) :
    ∀ m g : ℕ, L.N m g ≤ (g.choose m : ℝ) * a ^ m * M := by
  intro m
  induction m with
  | zero => intro g; simpa using L.reservoir g
  | succ m ih =>
    intro g
    have hm : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
    have h1 : L.N (m + 1) g ≤ a * ∑ l ∈ range g, L.N m l := by
      simpa using L.step_iterate hm g
    have h2 : ∑ l ∈ range g, L.N m l ≤ ∑ l ∈ range g, ((l.choose m : ℝ) * a ^ m * M) :=
      Finset.sum_le_sum fun l _ => ih l
    have h3 : ∑ l ∈ range g, ((l.choose m : ℝ) * a ^ m * M)
        = (g.choose (m + 1) : ℝ) * a ^ m * M := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, sum_range_choose_real]
    calc L.N (m + 1) g
        ≤ a * ∑ l ∈ range g, L.N m l := h1
      _ ≤ a * ∑ l ∈ range g, ((l.choose m : ℝ) * a ^ m * M) := by
          exact mul_le_mul_of_nonneg_left h2 ha
      _ = (g.choose (m + 1) : ℝ) * a ^ (m + 1) * M := by rw [h3]; ring

end Lean4LPD.Ladder
