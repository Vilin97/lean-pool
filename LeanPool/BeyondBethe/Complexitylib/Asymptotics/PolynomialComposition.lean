/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Asymptotics

/-!
# Polynomial composition bounds

This module packages natural-polynomial composition as power-form big-O
bounds. The second theorem records the coarse time expression used when two
deterministic function computations are connected sequentially.

## Main results

- `BigO.polynomial_eval_comp` — nested polynomial evaluation is polynomially bounded
- `BigO.polynomial_composition_time` — the coarse sequential runtime is polynomially bounded
-/


@[expose] public section

namespace Complexity

/-- Composing evaluations of natural-coefficient polynomials gives a function
bounded by a power whose exponent is the degree of the composed polynomial. -/
theorem BigO.polynomial_eval_comp (p q : Polynomial ℕ) :
    (fun n => q.eval (p.eval n)) =O (· ^ (q.comp p).natDegree) := by
  apply BigO.of_polynomial_bound (q.comp p)
  intro n
  simp [Polynomial.eval_comp]

/-- The coarse runtime for sequentially composing computations with polynomial
bounds `p` and `q` is itself bounded by a power. -/
theorem BigO.polynomial_composition_time (p q : Polynomial ℕ) :
    (fun n => 4 * p.eval n + 11 + q.eval (p.eval n)) =O
      (· ^ (Polynomial.C 4 * p + Polynomial.C 11 + q.comp p).natDegree) := by
  apply BigO.of_polynomial_bound
    (Polynomial.C 4 * p + Polynomial.C 11 + q.comp p)
  intro n
  simp [Polynomial.eval_comp]

end Complexity
