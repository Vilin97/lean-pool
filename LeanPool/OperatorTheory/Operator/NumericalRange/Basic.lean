/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Numerical range — definition and membership API (L1.1)

The numerical range of a continuous linear operator `A` on a complex inner
product space `E` is the set of values `⟪x, A x⟫_ℂ` over unit vectors `x`.

Mathlib's inner product is conjugate-linear in the first argument and linear
in the second, so the operator sits in the *second* (linear) slot: `⟪x, A x⟫_ℂ`.
With the operator in the first slot, `A = i • 1` would give `W(A) = {-i}`
while `σ(A) = {i}`, breaking the spectrum inclusion that later layers need.

## Main declarations

* `numericalRange A` — the numerical range `W(A) = { ⟪x, A x⟫_ℂ | ‖x‖ = 1 }`
  as a `Set ℂ`.
* `mem_numericalRange` — the `@[simp]` membership characterisation.

No completeness assumption on `E` is needed.
-/
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The numerical range of a continuous linear operator `A` on a complex inner
product space: the set of `⟪x, A x⟫_ℂ` as `x` ranges over the unit sphere. -/
noncomputable def numericalRange (A : E →L[ℂ] E) : Set ℂ :=
  { z | ∃ x : E, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z }

/-- `z` lies in the numerical range of `A` iff `z = ⟪x, A x⟫_ℂ` for some unit
vector `x`. -/
@[simp]
theorem mem_numericalRange (A : E →L[ℂ] E) (z : ℂ) :
    z ∈ numericalRange A ↔ ∃ x : E, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z :=
  Iff.rfl
/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
