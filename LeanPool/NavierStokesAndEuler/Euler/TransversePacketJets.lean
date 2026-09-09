/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketProvider

@[expose] public section

/-! The constructed forward transverse provider in the literal packet jet equation. -/

noncomputable section

namespace EulerPacketPointJets

open EulerSmoothLimit EulerPacketProfileRecursion

theorem pressureJet_angle_derivative (p : ScalarField) (t : ℝ) (x : Space) (θ : ℝ)
    (hp : DifferentiableAt ℝ (fun y : Space × ℝ => p (t,y)) (x,θ)) :
    (pressureJet p (t,(x,θ))).2 angleDirection = deriv (fun s => p (t,(x,s))) θ := by
  rw [pressureJet_angle]
  have hi : HasDerivAt (fun s : ℝ => (x,s)) (0,1) θ :=
    (hasDerivAt_const θ x).prodMk (hasDerivAt_id θ)
  exact (hp.hasFDerivAt.comp_hasDerivAt θ hi).deriv.symm

theorem fastPressure_pressureJet (m : Space) (p : ScalarField) (t : ℝ) (x : Space) (θ : ℝ)
    (hp : DifferentiableAt ℝ (fun y : Space × ℝ => p (t,y)) (x,θ)) :
    fastPressure m (pressureJet p (t,(x,θ))) = deriv (fun s => p (t,(x,s))) θ • m := by
  change (pressureJet p (t,(x,θ))).2 angleDirection • m = _
  rw [pressureJet_angle_derivative p t x θ hp]

end EulerPacketPointJets

namespace EulerTransversePacketProvider

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

namespace Forcing

variable {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

theorem slicedJet_time (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    (slicedJet (Icc (0 : ℝ) D.T) (G.vector I) (t,(x,θ))).2 timeDirection =
      G.vectorDerivative I (t,(x,θ)) :=
  slicedJet_time_eq _ _ _ _ ((uniqueDiffOn_Icc D.T_pos) _ t.property)
    (G.vector_hasDerivWithinAt I t x θ)

/-- This exact high-frequency equation is the interface used in the grade recursion. -/
theorem jet_equation (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    linearPart (D.strain (t,(x,θ))) (slicedJet (Icc (0 : ℝ) D.T) (G.vector I) (t,(x,θ)))+
      fastPressure (D.normalField (t,(x,θ))) (pressureJet (G.scalar I) (t,(x,θ))) = raw (t,(x,θ))
        := by
  change (slicedJet (Icc (0 : ℝ) D.T) (G.vector I) (t,(x,θ))).2 timeDirection+
    D.strain (t,(x,θ)) (G.vector I (t,(x,θ)))+_ = _
  rw [G.slicedJet_time I,fastPressure_pressureJet _ (G.scalar I) t x θ
    ((G.scalar_spatial_smooth I t).differentiable (by simp) (x,θ))]
  exact G.equation I t x θ

end Forcing

theorem highSolve_jet_equation (D : Data U) (I : InitialData P D) (raw : VectorField)
    (h : Nonempty (Forcing P D raw)) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    linearPart (D.strain (t,(x,θ)))
        (slicedJet (Icc (0 : ℝ) D.T) (highSolve P D I raw).1 (t,(x,θ)))+
      fastPressure (D.normalField (t,(x,θ)))
        (pressureJet (highSolve P D I raw).2 (t,(x,θ))) = raw (t,(x,θ)) := by
  rw [highSolve_of_admissible D I raw h]
  exact (Classical.choice h).jet_equation I t x θ

end EulerTransversePacketProvider
