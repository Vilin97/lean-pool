/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.OneRowExample
public import Mathlib.Algebra.Prime.Defs

/-!
# Conway's one-row prime in `Oz`

Let

`x = 1 + Σ n : ℕ, ω ^ (1 / (n + 1))`,

with every coefficient in the Conway normal form equal to one. The positive exponents decrease
to zero, so the support is a single row of order type `ω` followed by the constant term.

This omnific integer has exact support order type `ω + 1` and is prime, the concrete form of
LM24, Example 9.2.8.

## References

* S. L'Innocente, V. Mantova, *A factorisation theory for generalised power series and omnific
  integers*, Adv. Math. 442 (2024) 109513, cited as [LM24].
-/

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Oz.OneRowExample

open Ordinal

/-- The exponents displayed in the normal form: zero and `1/(n+1)` for `n ≥ 0`. -/
def IsDisplayedExponent (i : Surreal) : Prop :=
  i = 0 ∨ ∃ n : ℕ, i = ((1 / (n + 1 : ℝ) : ℝ) : Surreal)

/-- The named omnific integer is exactly the normal form displayed above: its coefficients are
one at zero and at the exponents `1/(n+1)`, and zero everywhere else. -/
def HasDisplayedCoefficients : Prop :=
  (∀ i : Surreal, IsDisplayedExponent i → oneRowOz.1.coeff i = 1) ∧
    ∀ i : Surreal, ¬ IsDisplayedExponent i → oneRowOz.1.coeff i = 0

/-- The displayed normal form has exact support order type `ω + 1`. -/
def HasExactSupportOrderType : Prop :=
  oneRowOz.1.length = omega0 + 1

/-- Conway's displayed one-row omnific integer is prime. -/
def IsPrime : Prop :=
  Prime oneRowOz

end ConwayRefinement.Standalone.Oz.OneRowExample

/-!
## Formal proof

Proof module: `OneRowPrimeProof`.

* `HasExactSupportOrderType` → `HasExactSupportOrderType.proof`
* `HasDisplayedCoefficients` → `HasDisplayedCoefficients.proof`
* `IsPrime` → `IsPrime.proof`
-/
