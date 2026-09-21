/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

/-
Zero sets and canonical products used in the Hadamard factorization development.

This is factored out so downstream files can talk about “a chosen enumeration of zeros”
without importing the (WIP) factorization proof in `FullTheorem.lean`.
-/

import LeanPool.LiCriterion.Hadamard.Basic

/-!
# Zero sets of entire functions

The `ZeroSet` structure packaging the zeros of an entire function together with the data the
Hadamard factorization needs, and the associated canonical product.
-/

open scoped BigOperators

namespace Hadamard

/-- A choice of zeros for a function `f`, with explicit enumeration. -/
structure ZeroSet (f : ℂ → ℂ) where
  /-- Index type for the chosen zeros. -/
  Zero : Type
  /-- The underlying complex value of a zero. -/
  z : Zero → ℂ
  /-- Each indexed value is a genuine zero of `f`. -/
  isZero : ∀ ρ : Zero, f (z ρ) = 0

/-- The canonical genus‑1 Weierstrass product over a countable zero set. -/
noncomputable def canonicalProductZeroSet
    {f : ℂ → ℂ} (Z : ZeroSet f) (s : ℂ) : ℂ :=
  ∏' ρ : Z.Zero, weierstrassE 1 (s / Z.z ρ)

end Hadamard
