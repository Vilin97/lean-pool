/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermPageActions
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermPages

/-!
Compatibility exports for operator actions on filtered two-term pages
from the shared algebraic-analysis library.
-/

namespace Stafford38.Characteristic.FilteredTwoTermPages

export AlgebraicAnalysis.FilteredTwoTermPages (
  FilteredTwoTerm.PageOperator
  FilteredTwoTerm.PageOperator.comp
  FilteredTwoTerm.PageOperator.reverseComp
  FilteredTwoTerm.PageOperator.commute_apply
  FilteredTwoTerm.PageOperator.sourceRestricted
  FilteredTwoTerm.PageOperator.sourceMap
  FilteredTwoTerm.PageOperator.sourceMap_mk
  FilteredTwoTerm.PageOperator.sourcePageCast
  FilteredTwoTerm.PageOperator.sourcePageCast_mk
  FilteredTwoTerm.PageOperator.targetRestricted
  FilteredTwoTerm.PageOperator.targetMap
  FilteredTwoTerm.PageOperator.targetMap_mk
  FilteredTwoTerm.PageOperator.targetPageCast
  FilteredTwoTerm.PageOperator.targetPageCast_mk
  FilteredTwoTerm.PageOperator.targetMapAtDrop
  FilteredTwoTerm.PageOperator.targetMapAtDrop_mk
  FilteredTwoTerm.PageOperator.targetMapAtDrop_eq_cast_targetMap
  FilteredTwoTerm.PageOperator.targetMapAtDrop_drop
  FilteredTwoTerm.PageOperator.targetMap_drop
  FilteredTwoTerm.PageOperator.SameSymbol
  FilteredTwoTerm.PageOperator.sourceMap_eq_of_sameSymbol
  FilteredTwoTerm.PageOperator.targetMap_eq_of_sameSymbol
  FilteredTwoTerm.PageOperator.targetMapAtDrop_eq_of_sameSymbol)

end Stafford38.Characteristic.FilteredTwoTermPages
