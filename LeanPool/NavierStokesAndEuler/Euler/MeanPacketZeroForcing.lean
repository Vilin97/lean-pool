/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketForcing
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketHomogeneity

/-! Zero forcing produces the actual zero velocity, derivative, and pressure force. -/

@[expose] public section


noncomputable section

namespace EulerMeanPacketProvider.Forcing

open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerPacketProfileRecursion

variable {D : Data} {raw : VectorField} (G : Forcing D raw)

theorem raw_zero_of_path_zero (hp : G.path = 0) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    raw (t,(x,θ)) = 0 := by
  have hpt : G.path t = 0 := congrArg (fun p : C(Icc (0 : ℝ) D.T,L2) => p t) hp
  have hz : (G.path t : Space → Space) =ᵐ[volume] (fun _ => (0 : Space)) := by
    rw [hpt]
    exact Lp.coeFn_zero Space 2 volume
  have hc : Continuous (fun y => raw (t,(y,θ))) := by
    have he : (fun y => raw (t,(y,θ))) = (G.slices t).field := funext (fun y => G.raw_eq t y θ)
    rw [he]
    exact (G.slices t).smooth.continuous
  exact congrFun (Measure.eq_of_ae_eq ((G.path_ae_raw t θ).symm.trans hz) hc continuous_const) x

theorem paths_zero_of_raw_zero
    (hz : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t, (x, θ)) = 0) :
    G.velocityPath = 0 ∧ G.derivativePath = 0 ∧ G.pressureForcePath = 0 := by
  have hs : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t,(x,θ)) = (0 : ℝ) • raw (t,(x,θ)) := by
    intro t x θ
    rw [hz t x θ, zero_smul]
  exact ⟨by simpa only [zero_smul] using velocityPath_smul G G 0 hs,
    by simpa only [zero_smul] using derivativePath_smul G G 0 hs,
    by simpa only [zero_smul] using pressureForcePath_smul G G 0 hs⟩

theorem paths_zero_of_path_zero (hp : G.path = 0) :
    G.velocityPath = 0 ∧ G.derivativePath = 0 ∧ G.pressureForcePath = 0 :=
  paths_zero_of_raw_zero G (raw_zero_of_path_zero G hp)

end EulerMeanPacketProvider.Forcing
