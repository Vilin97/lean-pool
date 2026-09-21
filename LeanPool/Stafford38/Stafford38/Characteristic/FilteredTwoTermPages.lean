/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.FilteredTwoTermPages

/-!
Compatibility exports for filtered two-term cycles, boundaries, and pages
from the shared algebraic-analysis library.
-/

namespace Stafford38.Characteristic.FilteredTwoTermPages

export AlgebraicAnalysis.FilteredTwoTermPages (
  FilteredTwoTerm
  FilteredTwoTerm.cycles
  FilteredTwoTerm.boundaries
  FilteredTwoTerm.next_le
  FilteredTwoTerm.boundaries_le
  FilteredTwoTerm.SourcePage
  FilteredTwoTerm.TargetPage
  FilteredTwoTerm.drop
  FilteredTwoTerm.drop_mk
  FilteredTwoTerm.cycles_succ_le
  FilteredTwoTerm.boundaries_le_succ
  FilteredTwoTerm.drop_mk_eq_zero_of_mem_cycles_succ
  FilteredTwoTerm.exists_cycles_succ_rep_of_drop_mk_eq_zero
  FilteredTwoTerm.mem_boundaries_succ_rep
  FilteredTwoTerm.exists_mem_boundaries_of_surjective)

end Stafford38.Characteristic.FilteredTwoTermPages
