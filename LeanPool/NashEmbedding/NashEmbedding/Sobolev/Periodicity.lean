/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Periodicity on ℝⁿ

The `2πℤⁿ`-periodicity predicate and the shift `2πk : ℝⁿ` for
`k : ℤⁿ`. Position-space primitives, used both by the NashEmbedding.Sobolev
position-space analytic toolkit (mollifier theory, Riemann-sum
position form) and by the NashEmbedding smooth-metric structures.
-/

open scoped BigOperators
open Real

noncomputable section

namespace NashEmbedding.Sobolev

/-- The periodic shift `2πk : ℝⁿ` for `k : Fin n → ℤ`. -/
def periodicShift (n : ℕ) (k : Fin n → ℤ) : Fin n → ℝ :=
  fun i => 2 * Real.pi * (k i : ℝ)

/-- A function `f : ℝⁿ → V` is `2πℤⁿ`-periodic if
    `f(x + 2πk) = f(x)` for all `x` and integer vectors `k`. -/
def IsPeriodic2Pi {n : ℕ} {V : Type*} (f : (Fin n → ℝ) → V) : Prop :=
  ∀ (x : Fin n → ℝ) (k : Fin n → ℤ), f (x + periodicShift n k) = f x

end NashEmbedding.Sobolev

end
