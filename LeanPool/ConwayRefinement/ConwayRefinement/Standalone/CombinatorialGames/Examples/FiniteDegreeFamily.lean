/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.FinitePowerFamily

/-!
# Omnific integers at every finite power of omega

For every natural number `n`, there is an omnific integer whose Conway normal form has support
order type exactly `ω ^ n + 1` and which is primal. Thus primality occurs at every finite degree;
the statement does not assert that these examples are irreducible.
-/

@[expose] public noncomputable section

namespace ConwayRefinement.Standalone.Oz.FiniteDegreeExamples

open Ordinal

/-- Every finite power `ω ^ n + 1` occurs as the exact Conway length of a primal omnific
integer. -/
def EveryFinitePowerOccurs : Prop :=
  ∀ n : ℕ, ∃ x : Oz.OmnificInteger.{0},
    x.1.length = (omega0 : Ordinal.{0}) ^ (n : Ordinal.{0}) + 1 ∧ IsPrimal x

end ConwayRefinement.Standalone.Oz.FiniteDegreeExamples

/-!
## Formal proof

Proof module: `FiniteDegreeFamilyProof`.

* `EveryFinitePowerOccurs` → `EveryFinitePowerOccurs.proof`
-/
