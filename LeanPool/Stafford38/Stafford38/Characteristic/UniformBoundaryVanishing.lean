/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.UniformBoundaryVanishing


/-!
Compatibility exports for uniform vanishing of Noetherian boundaries
from the shared algebraic-analysis library.
-/

@[expose] public section

export AlgebraicAnalysis (exists_uniform_zero_of_noetherian
  exists_uniform_subsingleton_of_noetherian exists_uniform_zero_localized
  exists_uniform_subsingleton_localized)
