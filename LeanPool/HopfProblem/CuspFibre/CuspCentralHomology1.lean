/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Recognition.Smale5
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Recognition.Smale5

/-!
# Hopf problem: cusp fibre · cusp central homology 1

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

private theorem
    CuspCentralHomology.singularHomologyMap_const_eq_zero {Y : Type} [TopologicalSpace Y]
    (X : Type) [TopologicalSpace X] (y : Y) (n : ℕ) (hn : n ≠ 0) :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.const X y) n = 0 := by
  let := PeriodTorusHigherHomology.point_homology_subsingleton n hn
  change
    SingularMayerVietoris.singularHomologyMap
        ((ContinuousMap.const Unit y).comp (ContinuousMap.const X ())) n =
      0
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
  ext a
  change
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.const Unit y) n
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.const X ()) n a) =
      0
  rw [Subsingleton.elim (SingularMayerVietoris.singularHomologyMap (ContinuousMap.const X ()) n a)
      (0 : SingularMayerVietoris.SingularHomology Unit n),
    map_zero]

public
theorem CuspCentralHomology.singularHomologyMap_eq_zero_of_nullhomotopic {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (hf : f.Nullhomotopic) (n : ℕ)
    (hn : n ≠ 0) : SingularMayerVietoris.singularHomologyMap f n = 0 := by
  obtain ⟨y, hy⟩ := hf
  rw [PeriodTorusHigherHomology.homotopic_homologyMap hy n]
  exact singularHomologyMap_const_eq_zero X y n hn

end Mathoverflow1973

end
