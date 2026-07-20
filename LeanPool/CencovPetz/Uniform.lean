/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic


/-!
# `CencovPetz.Uniform`

Minimal facts about the uniform distribution on a finite type.

Mathlib already provides uniform distributions as probability measures / `PMF`s. This file keeps a
lightweight `α → ℝ` “density” version that is sometimes convenient in finite-dimensional
calculations.

## Main definitions

- `uniformDistribution`: the constant function `1 / |α|`.
- `IsUniform`: predicate asserting a function is uniform.
-/

namespace LeanPool.CencovPetz

open scoped BigOperators

universe u

/-- Uniform distribution over a finite type `α`, defined as `1 / |α|` for all elements. -/
noncomputable abbrev uniformDistribution {α : Type u} [Fintype α] : α → ℝ :=
  Function.const α (1 / (Fintype.card α : ℝ))

/-- Predicate asserting that a function agrees with `uniformDistribution`. -/
def IsUniform {α : Type u} [Fintype α] (p : α → ℝ) : Prop :=
  ∀ a : α, p a = uniformDistribution (α := α) a

/-- The uniform distribution sums to `1`. -/
lemma uniformDistribution_sum_one {α : Type u} [Fintype α] [Nonempty α] :
    (∑ a : α, uniformDistribution (α := α) a) = 1 := by
  simp_all

end LeanPool.CencovPetz
