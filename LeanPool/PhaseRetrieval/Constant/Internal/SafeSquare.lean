/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # SafeSquare.lean
  Safe-square inequalities — pure real-number estimates.
  Scaffolding notes: ElementaryLemmas/safe_square.md

  Dependencies: Mathlib only (no project imports)

  Public API:
  - `safe_square`         (Theorem 2.1)
  - `nonneg_safe_square`  (Theorem 2.2)
-/
import Mathlib.Tactic.Common
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # SafeSquare -/


open Real

namespace FockSPR

/-! ## Theorem 2.1: Safe-square inequality

For all `a, b : ℝ`: `(a + b)² ≥ (1/2) a² − b²`.

**Proof**: `(a + b)² − (1/2)a² + b² = (1/2)(a + 2b)² ≥ 0`.
-/
theorem safe_square (a b : ℝ) : (a + b) ^ 2 ≥ (1 / 2) * a ^ 2 - b ^ 2 := by
  nlinarith [sq_nonneg (a + 2 * b)]

/-! ## Theorem 2.2: Nonneg safe-square inequality

For `a, b, c : ℝ` with `a ≥ 0`, `b ≥ 0`, `c ≥ 0`, and `a ≥ b − c`:
  `a² ≥ (1/2) b² − c²`.

**Proof**: Two cases.
- If `b ≤ c`: `(1/2)b² − c² ≤ (1/2)c² − c² = −(1/2)c² ≤ 0 ≤ a²`.
- If `b > c`: `a ≥ b − c > 0`, so `a² ≥ (b−c)²`.
  Then `(b−c)² − (1/2)b² + c² = (1/2)(b − 2c)² ≥ 0`, giving `(b−c)² ≥ (1/2)b² − c²`.

**Lean notes**: Use `nlinarith` or `ring_nf` + `nlinarith`. Case split via `by_cases h : b ≤ c`.
-/
theorem nonneg_safe_square (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : a ≥ b - c) : a ^ 2 ≥ (1 / 2) * b ^ 2 - c ^ 2 := by
  by_cases h : b ≤ c
  · nlinarith [sq_nonneg a, sq_nonneg c]
  · nlinarith [sq_nonneg (b - 2 * c)]

end FockSPR
