/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage7StrictRandomizedExpected.Transfer

/-!
The strict-oracle scale-identification impossibility theorem and its deterministic and
randomized forms.
-/

namespace V7

/-- The exact frozen four-part scale-identification impossibility carrier. -/
theorem scaleIdentificationImpossibility :
    ScaleIdentificationImpossibilityStatement := by
  exact ⟨deterministicFiniteHorizonImpossibility,
    randomizedFiniteHorizonImpossibility,
    infiniteWorstCaseExpectedHittingTime,
    oneDimensionalInteriorLpTransfer⟩


end V7
