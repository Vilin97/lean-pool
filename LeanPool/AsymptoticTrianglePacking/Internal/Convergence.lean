/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Bound

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — T3 convergence core : geometric decay of the
uncovered set

Standalone, Mathlib-only. The mathematical heart of the iterated nibble (T3): if each round covers a
definite fraction of the remaining vertices — so the uncovered count `a k` shrinks by a factor
`λ < 1` per round — then after `T = O(log 1/β)` rounds the uncovered count is `≤ β · a 0 = βq`.

* `geometric_decay` — `a (k+1) ≤ λ·a k` (with `a ≥ 0`, `λ ≥ 0`) ⇒ `a k ≤ λ^k · a 0`.
* `exists_round_count_below` — for `0 ≤ λ < 1` and target `β > 0`, some round count `T` reaches
  `a T ≤ β · a 0`.

This is the deterministic convergence mechanism into which the per-round covering bound
(`exists_large_round_matching` / `E[covered] ≥ …`) plugs to complete T3.

Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace LeanPool.AsymptoticTrianglePacking.Internal

/-- **T3-conv(1) — geometric decay.** If `a (k+1) ≤ λ · a k` for all `k` (with `a` nonnegative and
`λ ≥ 0`), then `a k ≤ λ^k · a 0`. -/
theorem geometric_decay {a : ℕ → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hstep : ∀ k, a (k + 1) ≤ lam * a k) : ∀ k, a k ≤ lam ^ k * a 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc a (k + 1) ≤ lam * a k := hstep k
        _ ≤ lam * (lam ^ k * a 0) := mul_le_mul_of_nonneg_left ih hlam
        _ = lam ^ (k + 1) * a 0 := by ring

/-- **T3-conv(2) — the uncovered count reaches `β · a 0`.** For a per-round shrink factor
`0 ≤ λ < 1` and any target fraction `β > 0`, some round count `T` brings the uncovered count down to
`a T ≤ β · a 0`. (Take `T` with `λ^T < β`.) -/
theorem exists_round_count_below {a : ℕ → ℝ} {lam β : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hβ : 0 < β) (ha : ∀ k, 0 ≤ a k) (hstep : ∀ k, a (k + 1) ≤ lam * a k) :
    ∃ T, a T ≤ β * a 0 := by
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one hβ hlam1
  exact ⟨T, le_trans (geometric_decay hlam0 hstep T)
    (mul_le_mul_of_nonneg_right hT.le (ha 0))⟩

/-- **Per-round decrease bridge.** If each round's uncovered count `a` drops by the covered amount
`b` (`a(k+1) ≤ a k - b k`) and each round covers at least a `(1-λ)` fraction (`(1-λ)·a k ≤ b k`),
then the uncovered sequence shrinks by factor `λ`: `a(k+1) ≤ λ·a k`. -/
theorem uncovered_step {a b : ℕ → ℝ} {lam : ℝ}
    (hstep : ∀ k, a (k + 1) ≤ a k - b k) (hcov : ∀ k, (1 - lam) * a k ≤ b k) :
    ∀ k, a (k + 1) ≤ lam * a k := by
  intro k
  have h1 := hstep k
  have h2 := hcov k
  nlinarith only [h1, h2]

/-- **T3 convergence chain.** If each round covers at least a `(1-λ)` fraction of the remaining
uncovered vertices (`0 ≤ λ < 1`), then for any target `β > 0` some round count `T` brings the
uncovered set down to `≤ β · a 0` — the nibble reaches `(1-β)`-coverage. -/
theorem exists_uncovered_below {a b : ℕ → ℝ} {lam β : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hβ : 0 < β) (ha : ∀ k, 0 ≤ a k) (hstep : ∀ k, a (k + 1) ≤ a k - b k)
    (hcov : ∀ k, (1 - lam) * a k ≤ b k) :
    ∃ T, a T ≤ β * a 0 :=
  exists_round_count_below hlam0 hlam1 hβ ha (uncovered_step hstep hcov)

/-! ### Bounded-rounds versions (only require the per-round bound for `k < T`)

The unbounded `hcov : ∀ k, (1-λ)·a k ≤ b k` is TOO STRONG for the nibble: the per-round covering
fraction degrades (`d_k → 0`), so `(1-λ) ≤ frac_k` cannot hold for all `k`. These bounded variants
require the decrease/covering only for `k < T`, and take `T` with `λ^T ≤ β` as data — matching the
real nibble, where the covering holds while the residual is still near-regular (`k < T`). -/

/-- **Bounded geometric decay.** If `a (k+1) ≤ λ·a k` for `k < T`, then `a T ≤ λ^T · a 0`. -/
theorem geometric_decay_lt {a : ℕ → ℝ} {lam : ℝ} (hlam : 0 ≤ lam) :
    ∀ (T : ℕ), (∀ k, k < T → a (k + 1) ≤ lam * a k) → a T ≤ lam ^ T * a 0 := by
  intro T
  induction T with
  | zero => intro _; simp
  | succ T ih =>
      intro hstep
      have hstep' : ∀ k, k < T → a (k + 1) ≤ lam * a k :=
        fun k hk => hstep k (Nat.lt_succ_of_lt hk)
      calc a (T + 1) ≤ lam * a T := hstep T (Nat.lt_succ_self T)
        _ ≤ lam * (lam ^ T * a 0) := mul_le_mul_of_nonneg_left (ih hstep') hlam
        _ = lam ^ (T + 1) * a 0 := by ring

/-- **Bounded per-round decrease bridge.** As `uncovered_step`, but only for `k < T`. -/
theorem uncovered_step_lt {a b : ℕ → ℝ} {lam : ℝ} (T : ℕ)
    (hstep : ∀ k, k < T → a (k + 1) ≤ a k - b k)
    (hcov : ∀ k, k < T → (1 - lam) * a k ≤ b k) :
    ∀ k, k < T → a (k + 1) ≤ lam * a k := by
  intro k hk
  have h1 := hstep k hk
  have h2 := hcov k hk
  nlinarith only [h1, h2]

/-- **Bounded convergence.** For a fixed `T` with `λ^T ≤ β`, if each round `k < T` covers at least a
`(1-λ)` fraction, then `a T ≤ β · a 0`. -/
theorem uncovered_below_lt {a b : ℕ → ℝ} {lam β : ℝ} (hlam0 : 0 ≤ lam) (ha : ∀ k, 0 ≤ a k)
    (T : ℕ) (hT : lam ^ T ≤ β)
    (hstep : ∀ k, k < T → a (k + 1) ≤ a k - b k)
    (hcov : ∀ k, k < T → (1 - lam) * a k ≤ b k) :
    a T ≤ β * a 0 :=
  le_trans (geometric_decay_lt hlam0 T (uncovered_step_lt T hstep hcov))
    (mul_le_mul_of_nonneg_right hT (ha 0))

end LeanPool.AsymptoticTrianglePacking.Internal

