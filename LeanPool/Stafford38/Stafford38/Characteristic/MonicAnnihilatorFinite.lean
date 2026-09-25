/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.MonicAnnihilatorFinite


/-!
Compatibility exports for finite modules from monic annihilators
from the shared algebraic-analysis library.
-/

@[expose] public section

namespace Stafford38.Characteristic.MonicAnnihilatorFinite

export AlgebraicAnalysis.MonicAnnihilatorFinite (
  finite_of_monic_annihilator
  finite_of_variable_annihilates
  finite_kernel_and_cokernel_variable)

end Stafford38.Characteristic.MonicAnnihilatorFinite
