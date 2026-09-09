/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseStaticEuler
public import LeanPool.NavierStokesAndEuler.Euler.BaseEulerUniform

@[expose] public section

/-! A single positive time and a single label bound work for every
compact base datum with |β|≤1. The parent, inverse and Euler evolution
below are the actual constructed objects. -/

noncomputable section

namespace EulerBaseDatum

open Set EulerSmoothLimit EulerParentPacketFrames

private local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def solutionTime : ℝ :=
  EulerStaticEuler.baseTime 1 uniformL2Amplitude 1024 uniformL2Amplitude_nonneg (by norm_num)

theorem solutionTime_pos : 0 < solutionTime :=
  EulerStaticEuler.baseTime_pos 1 uniformL2Amplitude 1024 uniformL2Amplitude_nonneg (by norm_num)

def solutionLabelConstant : ℝ :=
  EulerStaticEuler.baseLabelConstant 1 uniformL2Amplitude 1024 uniformL2Amplitude_nonneg (by
    norm_num)

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)

def solutionParent : Parent :=
  EulerStaticEuler.baseParent 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1

def solutionLabelData : LabelData (solutionParent β hβ ell hell hell1) :=
  EulerStaticEuler.baseLabelData 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1

def solutionInverse : ParticleInverse (solutionParent β hβ ell hell hell1) :=
  EulerStaticEuler.baseInverse 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1

def solutionEvolution : Evolution (solutionParent β hβ ell hell hell1) :=
  EulerStaticEuler.baseEvolution 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1

theorem solutionParent_time : (solutionParent β hβ ell hell hell1).T=solutionTime := rfl

theorem solutionLabelData_constant :
    (solutionLabelData β hβ ell hell hell1).K=solutionLabelConstant := rfl

theorem solutionOddData : OddData (solutionParent β hβ ell hell hell1) :=
  EulerStaticEuler.baseOddData 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1 (velocity_odd (linear β))

theorem solution_initial_velocity (x : Space) :
    (solutionParent β hβ ell hell hell1).velocity.field ⟨0,le_rfl,solutionTime_pos.le⟩ x=
      velocity (linear β) x :=
  EulerStaticEuler.baseParent_initial_velocity 1 (field (linear β)) uniformL2Amplitude 1024
    uniformL2Amplitude_nonneg (by norm_num) (field_uniform_jet β hβ)
    (velocity_divergence (linear β)) ell hell hell1 x

theorem solution_initial_gradient :
    fderiv ℝ ((solutionParent β hβ ell hell hell1).velocity.field
      ⟨0,le_rfl,solutionTime_pos.le⟩ : Space → Space) 0=linear β := by
  have he : ((solutionParent β hβ ell hell hell1).velocity.field
      ⟨0,le_rfl,solutionTime_pos.le⟩ : Space → Space)=velocity (linear β) :=
    funext (solution_initial_velocity β hβ ell hell hell1)
  rw [he]
  exact velocity_fderiv_plateau _ (linear_trace β) 0 (by simp)

theorem solution_initial_support :
    tsupport ((solutionParent β hβ ell hell hell1).velocity.field
      ⟨0,le_rfl,solutionTime_pos.le⟩ : Space → Space) ⊆ Metric.closedBall 0 2 := by
  have he : ((solutionParent β hβ ell hell hell1).velocity.field
      ⟨0,le_rfl,solutionTime_pos.le⟩ : Space → Space)=velocity (linear β) :=
    funext (solution_initial_velocity β hβ ell hell hell1)
  rw [he]
  exact velocity_support _

theorem solution_origin_fixed (t : Icc (0 : ℝ) solutionTime) :
    (solutionParent β hβ ell hell hell1).position t 0=0 :=
  (solutionOddData β hβ ell hell hell1).position_zero t

omit β hβ ell hell hell1 in
theorem solutionLabelConstant_one : 1 ≤ solutionLabelConstant :=
  (solutionLabelData 0 (by norm_num) 1 zero_lt_one le_rfl).K_one

end EulerBaseDatum
