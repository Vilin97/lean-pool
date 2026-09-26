/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.FinitePowerFamily
public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Examples.OmnificFactorizationProof

/-!
# Primality of the finite-power family

Every `finitePowerOz n` is nonordinary, reduced, and has Conway length below `ω ^ ω`.
Finite-degree primality for omnific integers therefore applies to every natural number `n`.
-/

public noncomputable section

namespace ConwayRefinement.Standalone.Oz.FinitePowerFamily.PrimalFamily

/-- Every coefficient-one omnific integer `finitePowerOz n` is primal. -/
theorem proof : FinitePowerFamily.PrimalFamily := by
  rw [FinitePowerFamily.PrimalFamily]
  intro n
  exact Oz.EveryOmnificIntegerIsPrimal.proof (FinitePowerFamily.finitePowerOz n)

end ConwayRefinement.Standalone.Oz.FinitePowerFamily.PrimalFamily
