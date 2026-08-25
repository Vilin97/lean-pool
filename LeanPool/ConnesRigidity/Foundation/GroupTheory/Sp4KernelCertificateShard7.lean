/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelDetector

/-!
Kernel-checked shard 8 of 8 for the exhaustive Sp₄(𝔽₂) detector.
-/

namespace Connes
namespace Sp4

/-- The detector succeeds on 16-bit matrix block 28 (with indices 0 through 31). -/
theorem kernelDetectorBlock28 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 28 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

/-- The detector succeeds on 16-bit matrix block 29 (with indices 0 through 31). -/
theorem kernelDetectorBlock29 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 29 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

/-- The detector succeeds on 16-bit matrix block 30 (with indices 0 through 31). -/
theorem kernelDetectorBlock30 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 30 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

/-- The detector succeeds on 16-bit matrix block 31 (with indices 0 through 31). -/
theorem kernelDetectorBlock31 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 31 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

end Sp4
end Connes
