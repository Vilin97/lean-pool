/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermBoundaryNaturality
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermTotalActions
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermBoundaryExhaustion

/- Compatibility exports for the neutral AlgebraicAnalysis API. -/

namespace Stafford38.Characteristic.FilteredTwoTermPages

export AlgebraicAnalysis.FilteredTwoTermPages (FilteredTwoTerm.PageOperator.targetBoundaryMap_naturality FilteredTwoTerm.PageOperator.totalBoundaryMap_naturality)

end Stafford38.Characteristic.FilteredTwoTermPages
