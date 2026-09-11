/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.HadwigerNelsonBounds.PartsGadgetHardVerification
public import LeanPool.HadwigerNelsonBounds.PartsGadgetMiddleData

/-! Kernel verification of the two normalized second-stage coloring trees. -/

@[expose] public section

namespace HadwigerNelsonBounds

/-- The middle-color normalized second-stage certificate checks by reduction. -/
theorem partsGadgetMiddleCertificate_verifies :
    partsGadgetMiddleCertificate.Verifies := by
  decide

end HadwigerNelsonBounds
