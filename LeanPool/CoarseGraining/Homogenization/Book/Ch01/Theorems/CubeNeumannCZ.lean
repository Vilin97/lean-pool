/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Definitions
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.Regularity

/-!
# Legacy Chapter 1 Neumann compatibility facade

This module is deliberately quarantined in
`Homogenization.Book.Ch01.Legacy`.  Its selected constant and regularity
theorem alias a downstream positive-test estimate; they are not the literal
weak-Hessian Calderon--Zygmund statement from the manuscript.
-/

namespace Homogenization
namespace Book
namespace Ch01

noncomputable section

namespace Legacy

open scoped ENNReal

/-- Legacy selected constant for the downstream Neumann positive-test
compatibility package on cubes. -/
noncomputable abbrev cubeNeumannW22Constant (d : ℕ) [NeZero d] : ℝ :=
  Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant d

theorem cubeNeumannW22Constant_nonneg (d : ℕ) [NeZero d] :
    0 ≤ cubeNeumannW22Constant d := by
  simpa [cubeNeumannW22Constant] using
    Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d

/-- Legacy cube Neumann positive-test compatibility theorem.  This is not the
literal weak-Hessian Calderon--Zygmund theorem. -/
theorem cubeNeumannW22Regularity {d : ℕ} [NeZero d] (Q : Cube d) :
    Homogenization.Legacy.CubeNeumannW22CalderonZygmundRegularity Q
      (cubeNeumannW22Constant d) := by
  simpa [cubeNeumannW22Constant] using
    Homogenization.Legacy.cubeNeumannW22CalderonZygmundRegularity Q

/-- Dimension-uniform existence form of the legacy cube Neumann positive-test
compatibility package. -/
theorem exists_cubeNeumannW22RegularityInDimension (d : ℕ) [NeZero d] :
    ∃ C : ℝ,
      Homogenization.Legacy.CubeNeumannW22CalderonZygmundRegularityInDimension d C :=
  Homogenization.Legacy.exists_cubeNeumannW22CalderonZygmundRegularityInDimension d

end Legacy

end

end Ch01
end Book
end Homogenization
