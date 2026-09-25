/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
module


/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Nicholas Bulka
-/
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
This module defines the vocabulary of the two proved statements in
`LeanPool.LiCriterion.Comparator.Solution`, using Mathlib alone. Mathlib's `RiemannHypothesis`
supplies the RH side; the xi function and its analytic coefficients are defined below.

The definitions have the same bodies as their counterparts in `Lc/LiCriterion/Basic.lean`,
so the solution can delegate to the library by definitional unfolding. Their separate
`LiChallenge` namespace lets the solution import both copies without name clashes.

For the local statements and proofs, read `Comparator/Solution.lean` together with these
definitions. The independent upstream statement and its comparator procedure are preserved at
the pinned [Challenge](https://github.com/nicholasbulka/li-criterion-rh-equivalence-lean/blob/35df682f3b709ffe5fbcfdd452dfa964bd622b87/comparator/Challenge.lean)
and [audit guide](https://github.com/nicholasbulka/li-criterion-rh-equivalence-lean/blob/35df682f3b709ffe5fbcfdd452dfa964bd622b87/comparator/README.md).
Those upstream audit assets are separate from this Lean Pool import.
-/

@[expose] public section

noncomputable section

open Complex

namespace LiChallenge

/-- The Riemann ξ function in entire form: `ξ(s) = ½ · s · (s-1) · Λ₀(s) + ½`, where
`Λ₀ = completedRiemannZeta₀` is Mathlib's entire completed zeta. This is an entire function whose
zeros in the critical strip are exactly the nontrivial zeros of ζ. (Character-for-character
`LiCriterion.riemannXi`.) -/
def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ)

/-- The Cayley-type change of variable `z ↦ 1/(1-z)`, which carries the open unit disk onto the
half-plane `Re s > 1/2`. Precomposing with it turns "all zeros on the critical line" into a
statement about the unit disk, which is what makes the Li coefficients a positivity condition.
(Character-for-character `LiCriterion.phi`.) -/
def phi (f : ℂ → ℂ) (z : ℂ) : ℂ := f (1 / (1 - z))

/-- The logarithmic derivative `f' / f`. (Character-for-character `LiCriterion.logDeriv`.) -/
def logDeriv (φ : ℂ → ℂ) (z : ℂ) : ℂ := deriv φ z / φ z

/-- The zero-indexed analytic coefficient corresponding, for `f = riemannXi`, to Li's classical
`λ_{n+1}`: the `n`-th Taylor coefficient at `0` of the logarithmic derivative of `f` precomposed
with the Cayley map. These are the coefficients whose nonnegativity is Li's criterion for RH.
(Character-for-character `LiCriterion.taylorCoeff`.) -/
def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (deriv^[n] (logDeriv (phi f))) 0 / n.factorial

/-- The nontrivial zeros of `ζ`: the zeros in the open critical strip `0 < re s < 1`.
(Character-for-character `LiCriterion.NontrivialZero`.) -/
def NontrivialZero : Type := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

end LiChallenge
