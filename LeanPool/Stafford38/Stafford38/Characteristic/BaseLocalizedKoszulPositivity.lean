/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.BaseLocalizedKoszulPositivity
import LeanPool.Stafford38.Stafford38.Characteristic.BaseLocalizationModuleComparison
import LeanPool.Stafford38.Stafford38.Characteristic.LocalizedKernelCokernelEquivalences
import LeanPool.Stafford38.Stafford38.Characteristic.MinimalSupportKernelCokernelLengths
import LeanPool.Stafford38.Stafford38.Characteristic.LocalizedMinimalSupportAvoidance
import LeanPool.Stafford38.Stafford38.Characteristic.PrincipalKoszulMinimalSupportPositivity

/-!
Compatibility exports for Koszul positivity after base localization
from the shared algebraic-analysis library.
-/

namespace Stafford38.Characteristic.BaseLocalizedKoszulPositivity

export AlgebraicAnalysis.BaseLocalizedKoszulPositivity (localized_length_cokernel_gt_kernel)

end Stafford38.Characteristic.BaseLocalizedKoszulPositivity
