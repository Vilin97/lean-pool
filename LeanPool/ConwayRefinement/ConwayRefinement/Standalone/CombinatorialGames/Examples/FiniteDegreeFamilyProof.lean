/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Examples.FiniteDegreeFamily
import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.FinitePowerFamilyProof

/-! # Finite Degree Family Proof -/

public noncomputable section

namespace ConwayRefinement.Standalone.Oz.FiniteDegreeExamples.EveryFinitePowerOccurs

/-- The coefficient-one finite-power family supplies the examples. -/
theorem proof : FiniteDegreeExamples.EveryFinitePowerOccurs := by
  rw [FiniteDegreeExamples.EveryFinitePowerOccurs]
  intro n
  refine ⟨FinitePowerFamily.finitePowerOz n, ?_, FinitePowerFamily.PrimalFamily.proof n⟩
  rw [FinitePowerFamily.finitePowerOz_val,
    FinitePowerFamily.finitePowerNormalForm_length]

end ConwayRefinement.Standalone.Oz.FiniteDegreeExamples.EveryFinitePowerOccurs
