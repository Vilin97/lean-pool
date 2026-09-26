/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.SplitLatticePresentation


/-! Compatibility exports for the neutral split-lattice presentation. -/

@[expose] public section

namespace Stafford38.Geometry.GeneralTangentLatticePresentation

export AlgebraicAnalysis.SplitLatticePresentation
  (SplitMatrixPresentation exists_splitMatrixPresentation
    exists_splitMatrixPresentation_of_isComplemented)

end Stafford38.Geometry.GeneralTangentLatticePresentation
