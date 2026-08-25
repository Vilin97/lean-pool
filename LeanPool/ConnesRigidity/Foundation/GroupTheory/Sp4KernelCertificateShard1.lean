/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelDetector

/-!
Kernel-checked shard 2 of 8 for the exhaustive Sp₄(𝔽₂) detector.
-/

namespace Connes
namespace Sp4

/-- The detector succeeds on 16-bit matrix block 4 (with indices 0 through 31). -/
theorem kernelDetectorBlock4 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 4 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

/-- The detector succeeds on 16-bit matrix block 5 (with indices 0 through 31). -/
theorem kernelDetectorBlock5 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 5 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

/-- The detector succeeds on 16-bit matrix block 6 (with indices 0 through 31). -/
theorem kernelDetectorBlock6 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 6 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

/-- The detector succeeds on 16-bit matrix block 7 (with indices 0 through 31). -/
theorem kernelDetectorBlock7 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 7 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

end Sp4
end Connes
