/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermTotalActions
public import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermTotalPages


/-!
Compatibility exports for operator actions on total filtered two-term pages
from the shared algebraic-analysis library.
-/

@[expose] public section

namespace Stafford38.Characteristic.FilteredTwoTermPages

export AlgebraicAnalysis.FilteredTwoTermPages (
  FilteredTwoTerm.PageOperator.sourceTotalMap
  FilteredTwoTerm.PageOperator.targetTotalMap
  FilteredTwoTerm.PageOperator.sourceTotalMap_lof
  FilteredTwoTerm.PageOperator.targetTotalMap_lof
  FilteredTwoTerm.PageOperator.totalDrop_intertwines
  FilteredTwoTerm.PageOperator.sourceTotalMap_commute_of_commutator_lowers
  FilteredTwoTerm.PageOperator.targetTotalMap_commute_of_commutator_lowers)

end Stafford38.Characteristic.FilteredTwoTermPages
