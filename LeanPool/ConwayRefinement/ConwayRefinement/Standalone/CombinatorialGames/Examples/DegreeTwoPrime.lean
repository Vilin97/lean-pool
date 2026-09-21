/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.DegreeTwoExample
public import Mathlib.Algebra.Prime.Defs

/-!
# An explicit degree-two prime in `Oz`

Let

`x = 1 + ∑ m n, ω ^ (1 / (m + 1) + 1 / ((m + 1) * (m + 2) * (n + 1)))`,

where every coefficient in the Conway normal form is one. For each `m`, the `n`-th row decreases
to `1 / (m + 1)`, and the rows decrease to zero. Thus its support has exact order type
`ω ^ 2 + 1`, and hence it has degree two.

This literal omnific integer is prime. The mathematical inputs are the PS06 three-germ
irreducibility criterion and the LM24 transfer from one Archimedean class. Every claim is stated
in the surreal numbers of an arbitrary universe `u`.

For comparison, `degreeTwoFoil = 2 * x` has exactly the same support and merely replaces every
displayed coefficient by two. Both factors are nonunits, so the foil is reducible. The pair shows
that the two-dimensional support geometry alone does not force primeness: the coefficient germs
distinguished by PS06 carry essential information.

## References

* J. Pommersheim, S. Shahriari, *Unique factorization in generalized power series rings*,
Proc. Amer. Math. Soc. 134 (2006), 1277–1287, cited as [PS06].
* S. L'Innocente, V. Mantova, *A factorisation theory for generalised power series and omnific
  integers*, Adv. Math. 442 (2024) 109513, cited as [LM24].
-/

universe u

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Oz.DegreeTwoExample

open Ordinal

/-- The exponents displayed in the normal form: zero and the row-column exponents above. -/
def IsDisplayedExponent (i : Surreal.{u}) : Prop :=
  i = 0 ∨ ∃ m n : ℕ,
    i = ((1 / (m + 1 : ℝ) +
      1 / ((m + 1 : ℝ) * (m + 2 : ℝ) * (n + 1 : ℝ)) : ℝ) : Surreal)

/-- The named omnific integer is exactly the normal form displayed above: its coefficients are
one at zero and at the row-column exponents, and zero everywhere else. -/
def HasDisplayedCoefficients : Prop :=
  (∀ i : Surreal.{u}, IsDisplayedExponent i → degreeTwoOz.{u}.1.coeff i = 1) ∧
    ∀ i : Surreal.{u}, ¬ IsDisplayedExponent i → degreeTwoOz.{u}.1.coeff i = 0

/-- The displayed normal form has exact support order type `ω ^ 2 + 1`. -/
def HasExactSupportOrderType : Prop :=
  degreeTwoOz.{u}.1.length = ω ^ (2 : Ordinal) + 1

/-- The displayed omnific integer is prime. -/
def IsPrime : Prop :=
  Prime degreeTwoOz.{u}

/-- The coefficient-doubled foil still has exact support order type `ω ^ 2 + 1`. -/
def FoilHasExactSupportOrderType : Prop :=
  degreeTwoFoil.{u}.1.length = ω ^ (2 : Ordinal) + 1

/-- The comparison element is literally twice the displayed prime. -/
def FoilIsCoefficientDouble : Prop :=
  degreeTwoFoil.{u} = 2 * degreeTwoOz.{u}

/-- The coefficient-doubled foil admits a factorisation into two nonunits. -/
def FoilHasNontrivialFactorization : Prop :=
  ∃ a b : Oz.OmnificInteger.{u},
    degreeTwoFoil = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b

end ConwayRefinement.Standalone.Oz.DegreeTwoExample

/-!
## Formal proof

Proof module: `DegreeTwoPrimeProof`.

* `HasExactSupportOrderType` → `HasExactSupportOrderType.proof`
* `HasDisplayedCoefficients` → `HasDisplayedCoefficients.proof`
* `IsPrime` → `IsPrime.proof`
* `FoilHasExactSupportOrderType` → `FoilHasExactSupportOrderType.proof`
* `FoilIsCoefficientDouble` → `FoilIsCoefficientDouble.proof`
* `FoilHasNontrivialFactorization` → `FoilHasNontrivialFactorization.proof`
-/
