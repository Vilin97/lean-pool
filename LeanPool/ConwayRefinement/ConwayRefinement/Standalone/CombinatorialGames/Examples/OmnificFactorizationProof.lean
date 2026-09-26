/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Examples.OmnificFactorization
import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.OmnificFactorizationProof

/-! # Omnific Factorization Proof -/

public noncomputable section

universe u

namespace ConwayRefinement.Standalone.Oz

namespace NormalFormIdentifiesOmnificIntegers

/-- Conway's cut definition and the normal-form definition determine the same subring. -/
theorem proof : Oz.NormalFormIdentifiesOmnificIntegers.{u} :=
  of_normalForm

end NormalFormIdentifiesOmnificIntegers

namespace EveryOmnificIntegerIsPrimal

/-- Every omnific integer is primal. -/
theorem proof : Oz.EveryOmnificIntegerIsPrimal.{u} :=
  of_refinement

end EveryOmnificIntegerIsPrimal

namespace IrreducibleIsPrime

/-- Every irreducible omnific integer is prime. -/
theorem proof : Oz.IrreducibleIsPrime.{u} :=
  of_primality

end IrreducibleIsPrime

namespace IrreducibleFactorizationsAreUnique

/-- Irreducible factorisations in `Oz` are unique up to order and units. -/
theorem proof : Oz.IrreducibleFactorizationsAreUnique.{u} :=
  of_primality

end IrreducibleFactorizationsAreUnique

end ConwayRefinement.Standalone.Oz
