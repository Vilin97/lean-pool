/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyOfX.TrianglePeriodFamilyHomologyAlgebra
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.HomologyOfX.TrianglePeriodFamilyHomologyAlgebra

/-!
# Hopf problem: torus homology · period torus higher homology 9

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

/-- Right translation by a fixed element as a continuous map. -/
@[expose]
public
def PeriodTorusHigherHomology.rightTranslation {G : Type*} [TopologicalSpace G] [AddGroup G]
    [IsTopologicalAddGroup G] (a : G) : C(G, G) :=
  ⟨fun x => x + a, continuous_id.add continuous_const⟩

@[simp]
public
theorem PeriodTorusHigherHomology.rightTranslation_apply {G : Type*} [TopologicalSpace G]
    [AddGroup G] [IsTopologicalAddGroup G] (a x : G) : rightTranslation a x = x + a :=
  rfl

private def PeriodTorusHigherHomology.rightTranslationHomotopyAlong {G : Type*} [TopologicalSpace G]
    [AddGroup G] [IsTopologicalAddGroup G] {a : G} (p : Path (0 : G) a) :
    (ContinuousMap.id G).Homotopy (rightTranslation a)
    where
  toFun z := z.2 + p z.1
  continuous_toFun := continuous_snd.add (p.continuous.comp continuous_fst)
  map_zero_left x := by simp
  map_one_left x := by simp

private theorem PeriodTorusHigherHomology.rightTranslation_singularHomologyMap_of_path {G : Type}
    [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] {a : G} (p : Path (0 : G) a)
    (n : ℕ) : SingularMayerVietoris.singularHomologyMap (rightTranslation a) n = LinearMap.id := by
  rw [← homotopy_homologyMap (rightTranslationHomotopyAlong p) n, singularHomologyMap_id]

@[simp]
private theorem PeriodTorusHigherHomology.rightTranslation_singularHomologyMap {G : Type}
    [TopologicalSpace G] [AddGroup G] [IsTopologicalAddGroup G] [PathConnectedSpace G] (a : G)
    (n : ℕ) : SingularMayerVietoris.singularHomologyMap (rightTranslation a) n = LinearMap.id :=
  rightTranslation_singularHomologyMap_of_path (PathConnectedSpace.somePath 0 a) n

end Mathoverflow1973

end
