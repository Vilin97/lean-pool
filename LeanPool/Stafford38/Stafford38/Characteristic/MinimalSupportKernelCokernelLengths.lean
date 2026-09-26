/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.MinimalSupportKernelCokernelLengths
public import LeanPool.Stafford38.Stafford38.Characteristic.EndomorphismKernelSupportOverBase
public import LeanPool.Stafford38.Stafford38.Characteristic.MinimalPrimeFiniteLengthLocalization


/-!
Compatibility exports for localized kernel and cokernel lengths
from the shared algebraic-analysis library.
-/

@[expose] public section

namespace Stafford38.Characteristic

export AlgebraicAnalysis (localized_kernel_and_cokernel_isFiniteLength)

end Stafford38.Characteristic
