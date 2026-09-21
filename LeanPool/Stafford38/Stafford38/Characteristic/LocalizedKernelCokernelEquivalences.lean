/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.LocalizedKernelCokernelEquivalences

/-!
Compatibility exports for localization of kernels and cokernels
from the shared algebraic-analysis library.
-/

namespace Stafford38.Characteristic.LocalizedKernelCokernelEquivalences

export AlgebraicAnalysis.LocalizedKernelCokernelEquivalences (
  localizedMap
  localizedMap_apply
  localizedEquiv
  localizedKernelEquiv
  localizedCokernelEquiv)

end Stafford38.Characteristic.LocalizedKernelCokernelEquivalences
