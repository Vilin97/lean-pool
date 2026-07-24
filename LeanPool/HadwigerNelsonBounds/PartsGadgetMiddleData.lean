/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.HadwigerNelsonBounds.PartsGadgetMiddleData0

/-! Aggregation of the generated `Middle` certificate. -/

namespace HadwigerNelsonBounds

/-- The checked `Middle` contradiction tree. -/
def partsGadgetMiddleCertificate : PartsGadgetCertificate := {
  roots := [⟨5, 0⟩, ⟨31, 3⟩, ⟨18, 1⟩]
  nodeCount := 17
  nodes := #[
    partsGadgetMiddleChunk0,
  ]
}

end HadwigerNelsonBounds
