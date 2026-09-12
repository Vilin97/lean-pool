/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.Complex
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.Foundations.Complex

/-!
# Hopf problem: torus homology · period torus higher homology 8

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

private theorem PeriodTorusHigherHomology.positiveCircleCross_pointClass :
    positiveCircleCross Unit 0 (pointClass ()) =
      homeomorphHomologyEquiv
        (Homeomorph.prodUnique (PeriodTorusHigherHomology.CircleTopology.Circle) Unit).symm 1
        (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) :=
  crossProductHomology_pointClass_right (PeriodTorusHigherHomology.CircleTopology.Circle) Unit
    (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) ()

@[simp]
private theorem PeriodTorusHigherHomology.circleHomologyOneEquiv_positiveLoop :
    circleHomologyOneEquiv (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) = 1 := by
  rw [circleHomologyOneEquiv_apply, ← positiveCircleCross_pointClass,
    circleBoundary_positiveCircleCross]
  exact connectedHomologyZeroEquiv_pointClass ()

@[simp]
private theorem PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_one :
    circleHomologyOneEquiv.symm 1 = FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop := by
  apply circleHomologyOneEquiv.injective
  rw [LinearEquiv.apply_symm_apply, circleHomologyOneEquiv_positiveLoop]

public
theorem PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_int (k : ℤ) :
    circleHomologyOneEquiv.symm k =
      k • FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop := by
  apply circleHomologyOneEquiv.injective
  rw [LinearEquiv.apply_symm_apply, map_zsmul, circleHomologyOneEquiv_positiveLoop]
  simp

end Mathoverflow1973

end
