/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialCommutant


/-! Compatibility export for the reusable localized polynomial commutant. -/

@[expose] public section
namespace Stafford38.LocalizedPolynomialCommutant

export AlgebraicAnalysis.DifferentialOperators.LocalizedPolynomialCommutant
  (eq_multiplication_of_commute_coordinate)

end Stafford38.LocalizedPolynomialCommutant
