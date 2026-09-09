/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketJets
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketParity

@[expose] public section

/-! The proved raw-field contract of the concrete admissible mean solver. -/

noncomputable section

namespace EulerMeanPacketProvider

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable (D : Data) (raw : VectorField) (h : Nonempty (Forcing D raw))

include h

theorem meanSolve_angle_independent (t : ℝ) (x : Space) (θ η : ℝ) :
    (meanSolve D raw).1 (t,(x,θ)) = (meanSolve D raw).1 (t,(x,η)) ∧
      (meanSolve D raw).2 (t,(x,θ)) = (meanSolve D raw).2 (t,(x,η)) := by
  rw [meanSolve_of_admissible D raw h]
  exact ⟨(Classical.choice h).vector_angle_independent t x θ η,
    (Classical.choice h).scalar_angle_independent t x θ η⟩

theorem meanSolve_divergence (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    divergence (fun y => D.inverseFrame (t,(y,θ)) ((meanSolve D raw).1 (t,(y,θ)))) x = 0 := by
  rw [meanSolve_of_admissible D raw h]
  exact (Classical.choice h).inverse_vector_divergence t x θ

theorem meanSolve_initial_support (θ : ℝ) :
    tsupport (fun x => (meanSolve D raw).1 (0,(x,θ))) ⊆ {x : Space | ‖D.ℓ • x‖ ≤ 2} := by
  rw [meanSolve_of_admissible D raw h]
  exact (Classical.choice h).initial_vector_support θ

theorem meanSolve_initial_compact (θ : ℝ) :
    HasCompactSupport (fun x => (meanSolve D raw).1 (0,(x,θ))) := by
  rw [meanSolve_of_admissible D raw h]
  exact (Classical.choice h).initial_vector_compact θ

theorem meanSolve_joint_continuous :
    Continuous (fun z : Icc (0 : ℝ) D.T × (Space × ℝ) => (meanSolve D raw).1 (z.1,z.2)) := by
  rw [meanSolve_of_admissible D raw h]
  exact (Classical.choice h).vector_joint_continuous

theorem meanSolve_angle_jets (t : ℝ) (x : Space) (θ : ℝ) :
    (slicedJet (Icc (0 : ℝ) D.T) (meanSolve D raw).1 (t,(x,θ))).2 angleDirection = 0 ∧
      (pressureJet (meanSolve D raw).2 (t,(x,θ))).2 angleDirection = 0 := by
  rw [meanSolve_of_admissible D raw h]
  exact ⟨(Classical.choice h).vector_angle_jet t x θ, (Classical.choice h).scalar_angle_jet t x θ⟩

end EulerMeanPacketProvider
