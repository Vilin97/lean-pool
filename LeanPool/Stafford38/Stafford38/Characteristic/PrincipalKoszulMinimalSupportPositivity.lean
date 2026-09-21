/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.PrincipalKoszulMinimalSupportPositivity
import LeanPool.Stafford38.Stafford38.Characteristic.PrincipalKoszulSupportOverBase

/-!
Compatibility exports for principal Koszul positivity at minimal support
from the shared algebraic-analysis library.
-/

namespace Stafford38.Characteristic.PrincipalKoszulMinimalSupportPositivity

export AlgebraicAnalysis.PrincipalKoszulMinimalSupportPositivity (
  length_cokernel_gt_kernel_of_minimal_support)

end Stafford38.Characteristic.PrincipalKoszulMinimalSupportPositivity
