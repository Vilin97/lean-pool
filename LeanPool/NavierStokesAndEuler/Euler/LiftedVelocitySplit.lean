/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAdvection
public import LeanPool.NavierStokesAndEuler.Euler.FunctionalVelocity
public import LeanPool.NavierStokesAndEuler.Euler.LiftedTransportComponents
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SobolevDerivativeNorm

/-! The actual four-component transport vector retains the small normal
component separately from its three scaled spatial components. -/

@[expose] public section


noncomputable section

namespace EulerLiftedVelocitySplit

open MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerMetricTransport EulerSobolevTransport
  EulerFunctionalVelocity EulerVectorCylinder EulerCylinderConstantMap
  EulerCylinderScalarPrimitive EulerPacketCylinderField

/-- Spatial velocity map, given by `velocityMap (Fin.cons 0 (fun i : Fin 3 => coordinate 3 i))`. -/
def spatialVelocityMap : Space →L[ℝ] EulerSobolev.Domain 4 :=
  velocityMap (Fin.cons 0 (fun i : Fin 3 => coordinate 3 i))

/-- Normal velocity map, given by `(toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 4) (1 :
ℝ))).comp scalarProject`. -/
def normalVelocityMap : Space →L[ℝ] EulerSobolev.Domain 4 :=
  (toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 4) (1 : ℝ))).comp scalarProject

theorem spatialVelocityMap_norm : ‖spatialVelocityMap‖ ≤ 3 := by
  apply opNorm_le_bound _ (by norm_num)
  intro z
  calc
    ‖spatialVelocityMap z‖ ≤ ∑ i : Fin 4, ‖spatialVelocityMap z i‖ :=
      EulerSobolevDerivativeNorm.norm_le_sum_coordinates 4 _
    _ = ∑ i : Fin 3, ‖coordinate 3 i z‖ := by
      rw [Fin.sum_univ_succ]
      simp only [spatialVelocityMap,velocityMap_apply,Fin.cons_zero,zero_apply,
        norm_zero,Fin.cons_succ,zero_add]
    _ ≤ ∑ _i : Fin 3, ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact ((coordinate 3 i).le_opNorm z).trans
        ((mul_le_mul_of_nonneg_right (coordinate_norm_le 3 i) (norm_nonneg z)).trans_eq
          (one_mul _))
    _ = 3*‖z‖ := by simp

theorem normalVelocityMap_norm : ‖normalVelocityMap‖ ≤ 1 := by
  calc
    ‖normalVelocityMap‖ ≤ ‖toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 4) (1 : ℝ))‖*
        ‖scalarProject‖ := opNorm_comp_le _ _
    _ = 1 := by simp [norm_toSpanSingleton,scalarProject_norm]

theorem velocityMap_split (κ : ℝ) (m : Space) :
    velocityMap (velocityComponents κ m) =
      κ • spatialVelocityMap + normalVelocityMap.comp (normalComponentMap m) := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [velocityMap_apply,velocityComponents,spatialVelocityMap,normalVelocityMap,
      toSpanSingleton_apply]
  · simp [velocityMap_apply,velocityComponents,spatialVelocityMap,normalVelocityMap,
      toSpanSingleton_apply]

variable (P : ℝ) [Fact (0 < P)]

theorem velocityMap_L2_bound (κ : ℝ) (m : Space) (u : LiftL2 P) :
    ‖(velocityMap (velocityComponents κ m)).compLpL 2 (liftMeasure P) u‖ ≤
      3 * |κ| * ‖u‖ + ‖(normalComponentMap m).compLpL 2 (liftMeasure P) u‖ := by
  rw [velocityMap_split,add_compLpL,smul_compLpL,add_apply,smul_apply]
  have he : (normalVelocityMap.comp (normalComponentMap m)).compLpL 2 (liftMeasure P) u =
      normalVelocityMap.compLpL 2 (liftMeasure P)
        ((normalComponentMap m).compLpL 2 (liftMeasure P) u) := by
    exact congrArg (fun L => L u) (map_comp P normalVelocityMap (normalComponentMap m))
  rw [he]
  calc
    _ ≤ |κ| * ‖spatialVelocityMap.compLpL 2 (liftMeasure P) u‖ +
        ‖normalVelocityMap.compLpL 2 (liftMeasure P)
          ((normalComponentMap m).compLpL 2 (liftMeasure P) u)‖ := by
      simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le
        (κ • spatialVelocityMap.compLpL 2 (liftMeasure P) u)
        (normalVelocityMap.compLpL 2 (liftMeasure P)
          ((normalComponentMap m).compLpL 2 (liftMeasure P) u))
    _ ≤ |κ| * (3*‖u‖) + 1*‖(normalComponentMap m).compLpL 2 (liftMeasure P) u‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (((spatialVelocityMap.compLpL 2 (liftMeasure P)).le_opNorm u).trans
            (mul_le_mul_of_nonneg_right
              (spatialVelocityMap.norm_compLpL_le.trans spatialVelocityMap_norm) (norm_nonneg u)))
          (abs_nonneg κ)
      · exact ((normalVelocityMap.compLpL 2 (liftMeasure P)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right
            (normalVelocityMap.norm_compLpL_le.trans normalVelocityMap_norm) (norm_nonneg _))
    _ = _ := by ring

end EulerLiftedVelocitySplit
