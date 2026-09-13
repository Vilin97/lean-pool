/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
module

public import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelDetector
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
Kernel-checked shard 7 of 8 for the exhaustive Sp₄(𝔽₂) detector.
-/

@[expose] public section

namespace Connes
namespace Sp4

/-- The detector succeeds on 16-bit matrix block 24 (with indices 0 through 31). -/
theorem kernelDetectorBlock24 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 24 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 25 (with indices 0 through 31). -/
theorem kernelDetectorBlock25 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 25 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 26 (with indices 0 through 31). -/
theorem kernelDetectorBlock26 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 26 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

/-- The detector succeeds on 16-bit matrix block 27 (with indices 0 through 31). -/
theorem kernelDetectorBlock27 : ∀ high : Fin 8, ∀ middle low : Fin 16,
    kernelDetectorCheck (BitVec.ofNat 16
      (2048 * 27 + 256 * high.val + 16 * middle.val + low.val)) = true := by
  decide +kernel

end Sp4
end Connes
