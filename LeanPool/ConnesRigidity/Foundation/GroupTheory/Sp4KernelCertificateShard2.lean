/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelDetector

/-!
Kernel-checked shard 3 of 8 for the exhaustive Sp₄(𝔽₂) detector.
-/

namespace Connes
namespace Sp4

/-- The detector succeeds on 16-bit matrix block 8 (with indices 0 through 31). -/
theorem kernelDetectorBlock8 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 8 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

/-- The detector succeeds on 16-bit matrix block 9 (with indices 0 through 31). -/
theorem kernelDetectorBlock9 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 9 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

/-- The detector succeeds on 16-bit matrix block 10 (with indices 0 through 31). -/
theorem kernelDetectorBlock10 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 10 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

/-- The detector succeeds on 16-bit matrix block 11 (with indices 0 through 31). -/
theorem kernelDetectorBlock11 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 11 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide

end Sp4
end Connes
