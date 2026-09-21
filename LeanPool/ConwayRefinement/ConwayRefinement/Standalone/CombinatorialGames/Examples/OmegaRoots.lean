/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.OmnificIntegers

/-!
# Roots of omega in the omnific integers

In Conway normal form, `ω` is the monomial with exponent `1`. For every positive integer `n`,
the monomial with exponent `1/n` is a nonunit omnific integer whose `n`th power is `ω`.
Thus one element admits factorisations into arbitrarily many nonunits.
-/

public noncomputable section

namespace ConwayRefinement.Standalone.Oz.OmegaRoots

universe u

/-- The coefficient-one Conway monomial `ω^x`, as an omnific integer. -/
def monomial (x : Surreal.{u}) (hx : 0 ≤ x) : Oz.OmnificInteger.{u} :=
  ⟨SurrealHahnSeries.single x 1, Oz.single_one_mem_omnificIntegers x hx⟩

/-- The Conway monomial `ω`. -/
def omega : Oz.OmnificInteger.{u} := monomial 1 zero_le_one

/-- The normal form of `omega` is the coefficient-one monomial at exponent `1`. -/
theorem coe_omega : omega.1 = SurrealHahnSeries.single 1 1 := (rfl)

/-- The Conway monomial `ω^(1/n)`. -/
def nthRoot (n : ℕ) : Oz.OmnificInteger.{u} :=
  monomial (n : Surreal)⁻¹ (inv_nonneg.mpr (Nat.cast_nonneg n))

/-- The normal form of `nthRoot n` is the coefficient-one monomial at exponent `1/n`. -/
theorem coe_nthRoot (n : ℕ) :
    (nthRoot.{u} n).1 = SurrealHahnSeries.single (n : Surreal)⁻¹ 1 := (rfl)

/-- The omnific integer `ω` has a nonunit `n`th root for every positive integer `n`. -/
abbrev OmegaHasRootsOfEveryPositiveOrder : Prop :=
  ∀ (n : ℕ), 0 < n →
    ¬IsUnit (nthRoot.{u} n) ∧ nthRoot.{u} n ^ n = omega.{u}

end ConwayRefinement.Standalone.Oz.OmegaRoots

/-!
## Formal proof

Proof module: `OmegaRootsProof`.

* `OmegaHasRootsOfEveryPositiveOrder` → `OmegaHasRootsOfEveryPositiveOrder.proof`
-/
