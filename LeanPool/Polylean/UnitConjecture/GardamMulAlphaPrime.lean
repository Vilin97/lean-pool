/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import LeanPool.Polylean.UnitConjecture.GardamDefs

namespace LeanPool.Polylean

/-!
## Gardam: `α' · α = 1`

The kernel-level verification that `α'` times the non-trivial unit `α`
equals one in `𝔽₂[P]`. Companion to `GardamMulAlpha`; the two checks live
in separate modules so the heavy `decide +kernel` reductions can run in
parallel.
-/

namespace Gardam

/-- Local alias for the group-ring multiplication, matching the form used in
`GardamDefs` so the theorem statement uses the same surface notation. -/
private abbrev ringMul (u v : 𝔽₂[P]) : 𝔽₂[P] :=
  GroupRing.mul u v

/-- The product of Gardam's inverse and its unit is one. -/
theorem α'_mul_α : ringMul α' α = (1 : 𝔽₂[P]) := by
  decide +kernel

end Gardam

end LeanPool.Polylean
