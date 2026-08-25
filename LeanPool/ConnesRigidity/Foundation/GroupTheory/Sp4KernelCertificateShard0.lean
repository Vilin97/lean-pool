/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelDetector

/-!
Kernel-checked shard 1 of 8 for the exhaustive Sp₄(𝔽₂) detector.
-/

namespace Connes
namespace Sp4

/-- The detector succeeds on 16-bit matrix block 0 (with indices 0 through 31). -/
theorem kernelDetectorBlock0 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 0 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

/-- The detector succeeds on 16-bit matrix block 1 (with indices 0 through 31). -/
theorem kernelDetectorBlock1 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 1 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

/-- The detector succeeds on 16-bit matrix block 2 (with indices 0 through 31). -/
theorem kernelDetectorBlock2 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 2 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

/-- The detector succeeds on 16-bit matrix block 3 (with indices 0 through 31). -/
theorem kernelDetectorBlock3 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 3 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

end Sp4
end Connes
