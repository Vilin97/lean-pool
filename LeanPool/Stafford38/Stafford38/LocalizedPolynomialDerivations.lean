/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations

/-! Compatibility exports for reusable localized polynomial derivations. -/
namespace Stafford38.LocalizedPolynomialDerivations

export AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialDerivations
  (extendDerivation extendDerivation_compAlgebraMap derivation_ext_of_compAlgebraMap_eq
   PolynomialRing localizedPderiv localizedPderiv_compAlgebraMap
   localizedPderiv_apply_algebraMap_X localizedPderiv_comm)

end Stafford38.LocalizedPolynomialDerivations
