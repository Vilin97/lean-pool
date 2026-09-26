/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.PrincipalKoszulSupportOverBase
public import LeanPool.Stafford38.Stafford38.Characteristic.StableTorsionResidualSupport
public import LeanPool.Stafford38.Stafford38.Characteristic.PrincipalKoszulFiniteTorsion


/-!
Compatibility exports for principal Koszul support over the base ring
from the shared algebraic-analysis library.
-/

@[expose] public section

namespace Stafford38.Characteristic.PrincipalKoszulSupportOverBase

export AlgebraicAnalysis.PrincipalKoszulSupportOverBase (
  length_cokernel_gt_kernel_of_support_over_base)

end Stafford38.Characteristic.PrincipalKoszulSupportOverBase
