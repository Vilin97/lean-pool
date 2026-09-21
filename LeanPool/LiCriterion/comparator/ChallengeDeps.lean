/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Nicholas Bulka
-/
import Mathlib

/-!
ChallengeDeps.lean — the solution-side mirror of the Li-criterion definitions
(see comparator/README.md).

Everything the challenge statement in `Challenge.lean` mentions that is not already in Mathlib is
defined directly in that file. This module repeats those definitions from Mathlib alone so that
`Solution.lean` can import them without importing the sorried Challenge module. Mathlib's
`RiemannHypothesis` supplies the RH side. This module imports nothing from the LiCriterion
development.

Every `def` below is character-for-character the one in the LiCriterion development
(`Lc/LiCriterion/Basic.lean`: `riemannXi` §1371, `phi` §463, `logDeriv` §474, `taylorCoeff`
§603), so that `Solution.lean` can delegate to the library by definitional unfolding in the
kernel. The copies live in the `LiChallenge` namespace so that `Solution.lean` can import both
this module and the LiCriterion development without name clashes (the library's live in
`LiCriterion`).

A reader auditing what is claimed needs to read only `Challenge.lean`, which imports Mathlib
directly. The proof lives in the LiCriterion library and is checked against the independently
stated Challenge declarations by the comparator (statement equality + axiom audit + kernel
replay), via `Solution.lean`.
-/

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
