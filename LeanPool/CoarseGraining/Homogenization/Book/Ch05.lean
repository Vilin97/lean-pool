/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Definitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems

/-! # Ch05 -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05

/-!
# Chapter 5 reboot scaffold

The previous Chapter 5 implementation has been archived under
`Archive/Ch05_legacy_2026_05_16`.  Active Chapter 5 is intentionally rebuilt
from a small theorem surface and a quarantined Ch4 boundary.

Active Ch5 code must not import legacy Ch5 modules, Ch5 measurability or
identification wrapper files, or unapproved Ch4 compatibility lanes.  Run
`scripts/audit_ch5_boundary.sh` before committing Ch5 work.
-/

end Ch05
end Book
end Homogenization
