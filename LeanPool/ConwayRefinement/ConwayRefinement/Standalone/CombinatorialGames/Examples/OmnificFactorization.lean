/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.OmnificIntegers
public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.ConwayRefinement
public import Mathlib.Algebra.Prime.Defs

/-!
# Factorisation in the omnific integers

CombinatorialGames provides the types `Surreal` and `SurrealHahnSeries`, but not the normal-form
ring equivalence between them or the subring `Oz`.

**Identification.** Conway defines `Oz` by `x = {x - 1 | x + 1}`. The normal-form ring
equivalence sends precisely these surreals to the series with nonnegative exponents and an integer
constant coefficient.

**Primality.** Every omnific integer is primal: whenever it divides a product, it splits as a
product of one divisor of each factor. This is the pre-Schreier form of Conway's refinement
conjecture.

**Factorisation.** Every irreducible omnific integer is prime, and two factorisations of an
omnific integer into irreducibles agree up to order and units.

## References

* S. L'Innocente, V. Mantova, *A factorisation theory for generalised power series and omnific
  integers*, Adv. Math. 442 (2024) 109513, <https://doi.org/10.1016/j.aim.2024.109513>, cited
  as [LM24].
-/

universe u

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Oz

/-- Membership in the normal-form ring `Oz`: nonnegative support and an integer coefficient at
exponent zero. -/
theorem mem_normalFormOmnificIntegers_iff (x : SurrealHahnSeries.{u}) :
    x ∈ omnificIntegers ↔
      x.support ⊆ Set.Ici 0 ∧ ∃ z : ℤ, (z : ℝ) = x.coeff 0 := by
  rw [mem_omnificIntegers, Set.mem_range]

/-- A ring equivalence from surreal numbers to surreal Hahn series identifies Conway's
cut-defined omnific integers with the normal-form subring `omnificIntegers`. -/
def NormalFormIdentifiesOmnificIntegers : Prop :=
  ∃ e : Surreal.{u} ≃+* SurrealHahnSeries.{u},
    ∀ x : Surreal.{u}, IsConwayOmnificInteger x ↔ e x ∈ omnificIntegers

/-- Every omnific integer is primal. Equivalently, `Oz` is a pre-Schreier ring. -/
def EveryOmnificIntegerIsPrimal : Prop :=
  ∀ x : (omnificIntegers : Subring SurrealHahnSeries.{u}), IsPrimal x

/-- Every irreducible omnific integer is prime. -/
def IrreducibleIsPrime : Prop :=
  ∀ x : (omnificIntegers : Subring SurrealHahnSeries.{u}), Irreducible x → Prime x

/-- Unique factorisation: two products of irreducible omnific integers that agree up to a unit
have the same factors up to order and association. -/
def IrreducibleFactorizationsAreUnique : Prop :=
  ∀ f g : Multiset (omnificIntegers : Subring SurrealHahnSeries.{u}),
    (∀ x ∈ f, Irreducible x) → (∀ x ∈ g, Irreducible x) →
      Associated f.prod g.prod → Multiset.Rel Associated f g

end ConwayRefinement.Standalone.Oz

/-!
## Formal proof

Proof module: `OmnificFactorizationProof`.

* `NormalFormIdentifiesOmnificIntegers` → `NormalFormIdentifiesOmnificIntegers.proof`
* `EveryOmnificIntegerIsPrimal` → `EveryOmnificIntegerIsPrimal.proof`
* `IrreducibleIsPrime` → `IrreducibleIsPrime.proof`
* `IrreducibleFactorizationsAreUnique` → `IrreducibleFactorizationsAreUnique.proof`
-/
