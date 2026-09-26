/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.CommutingPolynomialAction


/-!
Compatibility exports for polynomial actions from commuting endomorphisms
from the shared algebraic-analysis library.
-/

@[expose] public section

namespace Stafford38.Characteristic

export AlgebraicAnalysis.CommutingPolynomialAction (
  commutingPolynomialAction
  commutingPolynomialAction_apply_X
  commutingPolynomialAction_apply_C
  commutingPolynomialAction_intertwines
  commutingPolynomialModule)

end Stafford38.Characteristic
