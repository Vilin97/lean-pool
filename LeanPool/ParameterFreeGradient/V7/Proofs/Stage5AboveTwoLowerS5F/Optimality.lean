/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5F.UpperTheorem

/-!
The matching known-parameter upper and lower bounds establish above-two optimality.
-/

@[expose] public section

namespace V7

theorem knownParameterAboveTwoOptimality :
    KnownParameterAboveTwoOptimalityStatement :=
  ⟨knownParameterAboveTwoUpper, knownParameterAboveTwoLower⟩

end V7
