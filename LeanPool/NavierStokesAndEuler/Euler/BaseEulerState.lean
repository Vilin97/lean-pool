/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseEulerSobolev
public import LeanPool.NavierStokesAndEuler.Euler.BaseEulerGuards
import LeanPool.NavierStokesAndEuler.Euler.BaseEulerSign

/-! The initial induction state is completely constructed from the
compact β-family. A single positive time and a single label constant
work for the family, with actual low-order guards and pressure sign. -/

@[expose] public section


noncomputable section

namespace EulerBaseDatum

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerParentPacketFrames EulerBaseEulerGuards EulerTransverseFrameCoordinates

/-- Initial time, given by `guardTime solutionTime solutionLabelConstant`. -/
def initialTime : ℝ := guardTime solutionTime solutionLabelConstant

theorem initialTime_pos : 0 < initialTime :=
  guardTime_pos _ _ solutionTime_pos

theorem initialTime_le : initialTime ≤ solutionTime := guardTime_le _ _

theorem initialTime_le_one : initialTime ≤ 1 := guardTime_le_one _ _

/-- Initial coefficient cost, given by `coefficientCost solutionLabelConstant`. -/
def initialCoefficientCost : ℝ := coefficientCost solutionLabelConstant

theorem initialCoefficientCost_nonneg : 0 ≤ initialCoefficientCost := coefficientCost_nonneg _

theorem initialTime_small :
    initialCoefficientCost*initialTime ≤ 1/4 ∧
      EulerPacketFirstPressureSign.firstSignRate initialCoefficientCost
          initialCoefficientCost*initialTime ≤ 1/4 :=
  guardTime_small _ _

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)

/-- Initial parent, given by `(solutionParent β hβ ell hell hell1).restrictTime initialTime
initialTime_pos initialTime_le`. -/
def initialParent : Parent :=
  (solutionParent β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le

/-- Initial label data, given by `(solutionLabelData β hβ ell hell hell1).restrictTime
initialTime initialTime_pos initialTime_le`. -/
def initialLabelData : LabelData (initialParent β hβ ell hell hell1) :=
  (solutionLabelData β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le

/-- Initial inverse, given by `(solutionInverse β hβ ell hell hell1).restrictTime initialTime
initialTime_pos initialTime_le`. -/
def initialInverse : ParticleInverse (initialParent β hβ ell hell hell1) :=
  (solutionInverse β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le

/-- Initial evolution, given by `(solutionEvolution β hβ ell hell hell1).restrictTime
initialTime initialTime_pos initialTime_le`. -/
def initialEvolution : Evolution (initialParent β hβ ell hell hell1) :=
  (solutionEvolution β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le

/-- Initial sobolev data, given by `(solutionSobolevData β hβ ell hell hell1).restrictTime
initialTime initialTime_pos initialTime_le`. -/
def initialSobolevData : SobolevData (initialEvolution β hβ ell hell hell1) :=
  (solutionSobolevData β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le

theorem initialOddData : OddData (initialParent β hβ ell hell hell1) :=
  (solutionOddData β hβ ell hell hell1).restrictTime initialTime initialTime_pos initialTime_le

/-- Initial low bounds, given by `lowBounds (solutionLabelData β hβ ell hell hell1)`. -/
def initialLowBounds : LowBounds (initialParent β hβ ell hell hell1) :=
  lowBounds (solutionLabelData β hβ ell hell hell1)

theorem initialLowBounds_values :
    (initialLowBounds β hβ ell hell hell1).Be=initialCoefficientCost ∧
    (initialLowBounds β hβ ell hell hell1).Bc=0 ∧
    (initialLowBounds β hβ ell hell hell1).L=0 ∧
    (initialLowBounds β hβ ell hell hell1).r=0 ∧
    (initialLowBounds β hβ ell hell hell1).K=initialCoefficientCost :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem initialParent_time : (initialParent β hβ ell hell hell1).T=initialTime := rfl

theorem initialLabelData_constant :
    (initialLabelData β hβ ell hell hell1).K=solutionLabelConstant := rfl

theorem initial_velocity (x : Space) :
    (initialParent β hβ ell hell hell1).velocity.field ⟨0,le_rfl,initialTime_pos.le⟩ x =
      velocity (linear β) x :=
  solution_initial_velocity β hβ ell hell hell1 x

theorem initial_velocity_support :
    tsupport ((initialParent β hβ ell hell hell1).velocity.field
      ⟨0,le_rfl,initialTime_pos.le⟩ : Space → Space) ⊆ Metric.closedBall 0 2 := by
  rw [funext (initial_velocity β hβ ell hell hell1)]
  exact velocity_support _

theorem solution_initialStrain (x : Space) (hx : ‖ell • x‖ < 1) :
    (solutionParent β hβ ell hell hell1).initialStrain.field x=linear β := by
  rw [Parent.initialStrain_apply,Parent.first_apply]
  have he : ((solutionParent β hβ ell hell hell1).velocity.field
      (solutionParent β hβ ell hell hell1).zeroTime : Space → Space)=velocity (linear β) :=
    funext (solution_initial_velocity β hβ ell hell hell1)
  rw [he]
  exact velocity_fderiv_plateau _ (linear_trace β) (ell • x) hx

theorem initialStrain_plateau (x : Space) (hx : ‖ell • x‖ < 1) :
    (initialParent β hβ ell hell hell1).initialStrain.field x=linear β := by
  change ((solutionParent β hβ ell hell hell1).restrictTime initialTime initialTime_pos
    initialTime_le).initialStrain.field x=linear β
  erw [Parent.restrictTime_initialStrain]
  exact solution_initialStrain β hβ ell hell hell1 x hx

theorem initial_strain_bound (t : Icc (0 : ℝ) initialTime) (x : Space) :
    ‖(initialParent β hβ ell hell hell1).strain.field t x‖ ≤ initialCoefficientCost :=
  strain_norm (initialLabelData β hβ ell hell hell1) t x

theorem initial_curvature_bound (t : Icc (0 : ℝ) initialTime) (x : Space) :
    ‖(initialParent β hβ ell hell hell1).curvature.field t x‖ ≤ initialCoefficientCost :=
  curvature_norm (initialLabelData β hβ ell hell hell1) t x

theorem initial_origin_fixed (t : Icc (0 : ℝ) initialTime) :
    (initialParent β hβ ell hell hell1).position t 0=0 :=
  (initialOddData β hβ ell hell hell1).position_zero t

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (R : U ≃ₗᵢ[ℝ] referencePlane (EuclideanSpace.single 0 1 : Space))
  (ξ : U) (hξ : (R ξ : Space) = EuclideanSpace.single 1 1)
  (S : Set Space) (hS : IsCompact S)

include hξ in
theorem initial_pressure_numerator (t : Icc (0 : ℝ) initialTime)
    (x : Space) (hx : ‖ell • x‖ < 1) :
    1/2 ≤ ⟪((initialParent β hβ ell hell hell1).transverseData
      (EuclideanSpace.single 0 1) (by simp) R S hS).normal.field t x,
      (initialParent β hβ ell hell hell1).strain.field t x
        (EulerPacketForwardFactorization.uncutVelocity
          ((initialParent β hβ ell hell hell1).transverseData
            (EuclideanSpace.single 0 1) (by simp) R S hS) ξ t x)⟫_ℝ := by
  have hξnorm : ‖ξ‖=1 := by
    have hn : ‖(R ξ : Space)‖=1 := by rw [hξ]; simp
    exact (R.norm_map ξ).symm.trans hn
  apply source_numerator_pos (initialLabelData β hβ ell hell hell1)
    (EuclideanSpace.single 0 1) (by simp) R S hS ξ hξnorm x _ _ _ t
  · rw [initialStrain_plateau β hβ ell hell hell1 x hx,hξ,linear_q]
    simp [EuclideanSpace.inner_single_left,PiLp.add_apply,PiLp.smul_apply]
  · exact initialTime_small.1.trans (by norm_num)
  · exact initialTime_small.2.trans (by norm_num)

include hξ in
theorem initial_pressure_numerator_on_support (t : Icc (0 : ℝ) initialTime)
    (x : Space) (hx : x ∈ tsupport EulerSpatialCutoffs.innerCutoff) :
    1/2 ≤ ⟪((initialParent β hβ ell hell hell1).transverseData
      (EuclideanSpace.single 0 1) (by simp) R S hS).normal.field t x,
      (initialParent β hβ ell hell hell1).strain.field t x
        (EulerPacketForwardFactorization.uncutVelocity
          ((initialParent β hβ ell hell hell1).transverseData
            (EuclideanSpace.single 0 1) (by simp) R S hS) ξ t x)⟫_ℝ := by
  apply initial_pressure_numerator β hβ ell hell hell1 R ξ hξ S hS t x
  have hn : ‖x‖ < (1/2 : ℝ) := by
    simpa only [Metric.mem_ball,dist_zero_right] using EulerSpatialCutoffs.innerCutoff_support hx
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hell]
  have hb := mul_le_mul_of_nonneg_right hell1 (norm_nonneg x)
  nlinarith

end EulerBaseDatum
