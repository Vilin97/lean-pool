/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermPageEquivalences
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermPages

/- Compatibility exports for the neutral AlgebraicAnalysis API. -/

namespace Stafford38.Characteristic.FilteredTwoTermPages

export AlgebraicAnalysis.FilteredTwoTermPages (FilteredTwoTerm.sourceSuccMap FilteredTwoTerm.sourceSuccMap_mk FilteredTwoTerm.sourceSuccKernelMap FilteredTwoTerm.sourceSuccEquivKerDrop FilteredTwoTerm.targetSuccMap FilteredTwoTerm.targetSuccMap_surjective FilteredTwoTerm.ker_targetSuccMap_eq_range_drop FilteredTwoTerm.targetCokernelMap FilteredTwoTerm.targetSuccEquivCokerDrop)

end Stafford38.Characteristic.FilteredTwoTermPages
