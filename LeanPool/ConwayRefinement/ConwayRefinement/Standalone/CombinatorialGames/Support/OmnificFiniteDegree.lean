/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Examples.OmnificFactorization
public import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Pow

/-!
# Finite-degree predicates for omnific integers

These predicates state the finite-degree examples in `Examples/`.
-/

universe u

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Oz

open Ordinal

/-- An omnific integer is ordinary when its Conway normal form is an integer constant. -/
def IsOrdinaryInteger (x : OmnificInteger.{u}) : Prop :=
  ∃ z : ℤ, x.1 = (z : SurrealHahnSeries)

/-- LM24 reducedness: `x` is nonzero, and the exponents occurring in both `x` and `x - 1` lie in
one Archimedean class. -/
def IsReduced (x : OmnificInteger.{u}) : Prop :=
  x ≠ 0 ∧ ∃ c : ArchimedeanClass Surreal,
    x.1.support ∩ (x.1 - 1).support ⊆ {i | ArchimedeanClass.mk i = c}

/-- Every nonordinary reduced omnific integer is primal. -/
def ReducedIsPrimal : Prop :=
  ∀ x : OmnificInteger.{u}, ¬ IsOrdinaryInteger x → IsReduced x → IsPrimal x

/-- The Conway normal form has finite degree when its support order type is below `ω ^ ω`. -/
def HasFiniteDegree (x : OmnificInteger.{u}) : Prop :=
  Ordinal.lift.{u + 1, u} x.1.length <
    (ω : Ordinal.{u + 1}) ^ (ω : Ordinal.{u + 1})

/-- Every irreducible, nonordinary, reduced omnific integer is prime. -/
def ReducedIrreducibleIsPrime : Prop :=
  ∀ x : OmnificInteger.{u}, ¬ IsOrdinaryInteger x → IsReduced x → Irreducible x → Prime x

/-- Every nonordinary reduced omnific integer of finite degree is primal. -/
def FiniteDegreeIsPrimal : Prop :=
  ∀ x : OmnificInteger.{u}, ¬ IsOrdinaryInteger x →
    IsReduced x → HasFiniteDegree x → IsPrimal x

/-- Every irreducible, nonordinary, reduced omnific integer of finite degree is prime. -/
def FiniteDegreeIrreducibleIsPrime : Prop :=
  ∀ x : OmnificInteger.{u}, ¬ IsOrdinaryInteger x →
    IsReduced x → HasFiniteDegree x → Irreducible x → Prime x

/-- Every irreducible, nonordinary, reduced omnific integer of support order type `ω ^ 2` is
prime. -/
def DegreeTwoIrreducibleIsPrime : Prop :=
  ∀ x : OmnificInteger.{u}, ¬ IsOrdinaryInteger x →
    IsReduced x → Ordinal.lift.{u + 1, u} x.1.length =
      (ω : Ordinal.{u + 1}) ^ (2 : Ordinal.{u + 1}) →
        Irreducible x → Prime x

end ConwayRefinement.Standalone.Oz
