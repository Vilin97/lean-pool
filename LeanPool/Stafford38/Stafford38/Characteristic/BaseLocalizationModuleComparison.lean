/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.BaseLocalizationModuleComparison


/-!
Compatibility exports for comparison of base and coefficient localizations
from the shared algebraic-analysis library.
-/

@[expose] public section

namespace Stafford38.Characteristic.BaseLocalizationModuleComparison

export AlgebraicAnalysis.BaseLocalizationModuleComparison (
  coefficientDenominator
  localizedModule_isLocalizedOverBase
  localizedModule_isLocalizedOverCoefficient
  localizedModuleComparison
  localizedModuleComparison_mkLinearMap
  localizedModuleComparison_mk
  localizedModuleComparison_natural)

end Stafford38.Characteristic.BaseLocalizationModuleComparison
