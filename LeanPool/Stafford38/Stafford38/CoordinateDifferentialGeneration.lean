/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration


/-! Compatibility exports for the reusable coordinate-generation argument. -/

@[expose] public section
namespace Stafford38.CoordinateDifferentialGeneration

export AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration
  (mem_submodule_of_coordinates mem_subalgebra_of_coordinates)

end Stafford38.CoordinateDifferentialGeneration
