/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermTotalPages
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermPageEquivalences
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermPageActions

/-!
Compatibility exports for total filtered two-term pages
from the shared algebraic-analysis library.
-/

namespace Stafford38.Characteristic.FilteredTwoTermPages

export AlgebraicAnalysis.FilteredTwoTermPages (
  FilteredTwoTerm.SourceTotal
  FilteredTwoTerm.TargetTotal
  FilteredTwoTerm.totalDrop
  FilteredTwoTerm.totalDrop_lof
  FilteredTwoTerm.totalDrop_lof_mk
  FilteredTwoTerm.sourceTotalSuccMap
  FilteredTwoTerm.totalSourceSuccMap_injective
  FilteredTwoTerm.range_totalSourceSuccMap
  FilteredTwoTerm.sourceTotalSuccEquivKerDrop
  FilteredTwoTerm.targetTotalSuccMap
  FilteredTwoTerm.ker_totalTargetSuccMap
  FilteredTwoTerm.targetTotalSuccEquivCokerDrop)

end Stafford38.Characteristic.FilteredTwoTermPages
