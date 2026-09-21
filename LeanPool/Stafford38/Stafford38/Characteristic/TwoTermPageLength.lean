/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.TwoTermPageLength

/-!
Compatibility exports for length comparison for filtered two-term pages
from the shared algebraic-analysis library.
-/

namespace Stafford38.Characteristic.TwoTermPageLength

export AlgebraicAnalysis.TwoTermPageLength (
  exists_boundary_eq_top_of_iSup_eq_top
  twoTermPage_length_target_le_source)

end Stafford38.Characteristic.TwoTermPageLength
