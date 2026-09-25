/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.EndomorphismKernelSupportOverBase
public import LeanPool.Stafford38.Stafford38.Characteristic.EndomorphismKernelSupport


/-!
Compatibility exports for kernel and cokernel support over the base ring
from the shared algebraic-analysis library.
-/

@[expose] public section

namespace Stafford38.Characteristic

export AlgebraicAnalysis (endomorphism_kernel_support_subset_cokernel_support_over_base)

end Stafford38.Characteristic
