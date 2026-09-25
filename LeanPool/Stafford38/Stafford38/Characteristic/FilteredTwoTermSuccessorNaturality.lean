/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermSuccessorNaturality
public import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermTotalActions


/-!
Compatibility exports for naturality of successor-page operators
from the shared algebraic-analysis library.
-/

@[expose] public section

namespace Stafford38.Characteristic.FilteredTwoTermPages

export AlgebraicAnalysis.FilteredTwoTermPages (
  FilteredTwoTerm.PageOperator.sourceTotalSuccMap_naturality
  FilteredTwoTerm.PageOperator.targetTotalSuccMap_naturality)

end Stafford38.Characteristic.FilteredTwoTermPages
