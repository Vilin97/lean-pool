/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.StableTorsionResidualSupport
public import LeanPool.Stafford38.Stafford38.Characteristic.PrincipalKoszulPositivity


/-!
Compatibility exports for residual support after removing stable torsion
from the shared algebraic-analysis library.
-/

@[expose] public section

namespace Stafford38.Characteristic.StableTorsionResidualSupport

export AlgebraicAnalysis.StableTorsionResidualSupport (residual_nontrivial_of_support)

end Stafford38.Characteristic.StableTorsionResidualSupport
