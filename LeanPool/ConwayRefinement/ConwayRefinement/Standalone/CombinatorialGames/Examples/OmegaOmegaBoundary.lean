/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.OmegaOmegaBoundary

/-!
# The boundary at Conway length `ω ^ ω`

There is a reduced, nonordinary omnific integer whose Conway normal form has support order type
exactly `ω ^ ω`. It therefore lies exactly at the first limit excluded by the strict
finite-degree hypothesis. This statement makes no primality or nonprimality claim about it.
-/

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Oz.OmegaOmegaBoundaryExample

open Ordinal

/-- An omnific integer is ordinary when its normal form is an integer constant. -/
def IsOrdinary (x : Oz.OmnificInteger.{0}) : Prop :=
  ∃ z : ℤ, x.1 = (z : SurrealHahnSeries)

/-- Reducedness means that `x` is nonzero and the exponents shared by `x` and `x - 1` lie in one
Archimedean class. -/
def IsReduced (x : Oz.OmnificInteger.{0}) : Prop :=
  x ≠ 0 ∧ ∃ c : ArchimedeanClass Surreal,
    x.1.support ∩ (x.1 - 1).support ⊆ {i | ArchimedeanClass.mk i = c}

/-- Finite degree is the strict Conway-length bound below `ω ^ ω`. -/
def HasFiniteDegree (x : Oz.OmnificInteger.{0}) : Prop :=
  Ordinal.lift.{1, 0} x.1.length < (omega0 : Ordinal.{1}) ^ (omega0 : Ordinal.{1})

/-- A reduced nonordinary omnific integer exists exactly at the `ω ^ ω` boundary. -/
def ExistsAtBoundary : Prop :=
  ∃ x : Oz.OmnificInteger.{0},
    ¬ IsOrdinary x ∧ IsReduced x ∧
      x.1.length = (omega0 : Ordinal.{0}) ^ (omega0 : Ordinal.{0}) ∧
      ¬ HasFiniteDegree x

end ConwayRefinement.Standalone.Oz.OmegaOmegaBoundaryExample

/-!
## Formal proof

Proof module: `OmegaOmegaBoundaryProof`.

* `ExistsAtBoundary` → `ExistsAtBoundary.proof`
-/
