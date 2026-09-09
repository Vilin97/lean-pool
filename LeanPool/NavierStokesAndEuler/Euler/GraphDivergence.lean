/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GraphPressurePotential
import LeanPool.NavierStokesAndEuler.Euler.ClassicalDivergence
import LeanPool.NavierStokesAndEuler.Euler.Foundations.GraphPullback

/-! Genuine lifted divergence-free fields remain divergence-free on the oscillating graph. -/

@[expose] public section


noncomputable section

namespace EulerGraphDivergence

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerClassicalDivergence EulerGraphPullback EulerGraphPressurePotential
  EulerTransportDerivatives
open scoped ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The physical graph of an actual smooth representative of a lifted solenoidal L² field is
classically divergence-free. -/
theorem divergenceFree_graph (κ k : ℝ) (hκ : k * κ = 1) (m : Vector3)
    (u : LiftL2 period) (hu : u ∈ divergenceFreeSpace period κ m)
    (g : LiftDomain period → Vector3)
    (hrep : (u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ∀ x, (∑ i : Fin 3,
      (fderiv ℝ (fun y => g (cylinderGraph period k m y)) x (EuclideanSpace.single i 1)) i) = 0 :=
          by
  let P : LiftTangent → Vector3 := localFieldLift period g 0
  have heq : (fun y => P (graphMap k m y)) = fun y => g (cylinderGraph period k m y) := by
    funext y
    simp only [P,localFieldLift,Prod.fst_zero,Prod.snd_zero,zero_add,graphMap_apply,cylinderGraph]
  have hdir (i : Fin 3) : liftedDirection κ m (EuclideanSpace.single i 1) = coordinateDirection κ m
      i := by
    simp [liftedDirection_apply,coordinateDirection,EuclideanSpace.inner_single_right]
  intro x
  have hzero := divergenceFree_classical_divergence_zero period κ m u hu g hrep hg
    (cylinderGraph period k m x)
  have hd : fderiv ℝ P (graphMap k m x) =
      fderiv ℝ (localFieldLift period g (cylinderGraph period k m x)) 0 := by
    have h := (fderiv_localFieldLift_cover period g (graphMap k m x)).symm
    simpa only [P,coveringMap,graphMap_apply,cylinderGraph] using h
  calc
    _ = ∑ i : Fin 3, k*(fieldDerivative period (coordinateDirection κ m i) g (cylinderGraph period
        k m x)) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← heq,graph_fderiv P k κ hκ m x (EuclideanSpace.single i 1) ((hg 0).differentiable (by
          simp) _),hdir,hd]
      rfl
    _ = k*(∑ i : Fin 3, (fieldDerivative period (coordinateDirection κ m i) g (cylinderGraph period
        k m x)) i) :=
      (Finset.mul_sum ..).symm
    _ = 0 := by rw [hzero,mul_zero]

end EulerGraphDivergence
