/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Hurewicz.HigherHurewicz2
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology1
import all LeanPool.HopfProblem.Hurewicz.HigherHurewicz2

/-!
# Hopf problem: main theorem · six sphere cube 2

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

/-- The standard unit six-sphere. -/
public
abbrev SixSphereCube.StandardSphere :=
  SphereHomology.UnitSphere 6

private def SixSphereCube.euclideanOnePointSphereHomeomorph :
    OnePoint (EuclideanSpace ℝ (Fin 6)) ≃ₜ StandardSphere :=
  onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin 6)) (ι := Fin 7) (by simp)

private def SixSphereCube.sphereBasePoint : StandardSphere :=
  euclideanOnePointSphereHomeomorph (OnePoint.infty)

end Mathoverflow1973

end
