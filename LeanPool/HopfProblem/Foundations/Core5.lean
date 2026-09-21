/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.TrianglePeriodFamilyHomologySplitting
import all LeanPool.HopfProblem.Foundations.TrianglePeriodFamilyHomologySplitting

/-!
# Hopf problem: foundations · core 5

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

/-- The linear combination of local twisting numbers used by the gluing construction. -/
public
def twistOrder (ℓ₀ ℓ₁ ℓ₂ : ℤ) : ℤ :=
  12 * ℓ₀ - 4 * ℓ₁ - 3 * ℓ₂

public
theorem main_twist_value : twistOrder 0 1 (-1) = -1 := by decide

private def twistRelators (a b d : ℤ) : Fin 5 → FreeGroup (Fin 3) :=
  let c := FreeGroup.of (0 : Fin 3)
  let x := FreeGroup.of (1 : Fin 3)
  let y := FreeGroup.of (2 : Fin 3)
  ![c * x * (x * c)⁻¹, c * y * (y * c)⁻¹, x * y * (c ^ a)⁻¹, x ^ 3 * (c ^ b)⁻¹, y ^ 4 * (c ^ d)⁻¹]

end Mathoverflow1973

end
