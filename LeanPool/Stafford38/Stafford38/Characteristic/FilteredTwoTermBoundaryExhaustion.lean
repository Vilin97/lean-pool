/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermBoundaryExhaustion
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermTotalPages

/-!
Compatibility exports for exhaustion of filtered two-term boundaries
from the shared algebraic-analysis library.
-/

namespace Stafford38.Characteristic.FilteredTwoTermPages

export AlgebraicAnalysis.FilteredTwoTermPages (
  FilteredTwoTerm.targetBoundaryMap
  FilteredTwoTerm.targetBoundaryMap_mk
  FilteredTwoTerm.targetBoundaryMap_surjective
  FilteredTwoTerm.targetBoundaryMap_ker_mono
  FilteredTwoTerm.totalBoundaryMap
  FilteredTwoTerm.totalBoundaryMap_lof
  FilteredTwoTerm.totalBoundaryMap_surjective
  FilteredTwoTerm.totalBoundaryMap_ker_mono
  FilteredTwoTerm.totalBoundaryMap_eventually_zero)

end Stafford38.Characteristic.FilteredTwoTermPages
