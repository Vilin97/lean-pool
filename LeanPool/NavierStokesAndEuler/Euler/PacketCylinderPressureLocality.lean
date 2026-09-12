/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetOperations

/-! Spatial support and joint parity of the literal pressure-gradient term. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace
  EulerPacketPointJets EulerPacketProfileRecursion
open scoped Topology ContDiff

theorem pressureGradient_eq_spatialDual (p : ScalarField) (z : Domain) :
    pressureGradient p z = (toDual ℝ Space).symm
      ((fderiv ℝ (fun y => p (z.1,y)) z.2).comp (inl ℝ Space ℝ)) := by
  have h : (pressureJet p z).2.comp spatialInjection =
      (fderiv ℝ (fun y => p (z.1,y)) z.2).comp (inl ℝ Space ℝ) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [comp_apply,pressureJet_space,inl_apply]
  exact congrArg (toDual ℝ Space).symm h

theorem pressureGradient_zero_outside (p : ScalarField) (t : ℝ)
    (S : Set Space) (hS : IsClosed S)
    (hp : ∀ x, x ∉ S → ∀ θ, p (t, (x, θ)) = 0) (x : Space) (hx : x ∉ S) (θ : ℝ) :
    pressureGradient p (t,(x,θ)) = 0 := by
  have hn : {y : LiftTangent | y.1 ∈ Sᶜ} ∈ 𝓝 (x,θ) :=
    (hS.isOpen_compl.preimage continuous_fst).mem_nhds hx
  have he : (fun y : LiftTangent => p (t,y)) =ᶠ[𝓝 (x,θ)] (fun _ => (0 : ℝ)) := by
    filter_upwards [hn] with y hy
    exact hp y.1 hy y.2
  have hd : fderiv ℝ (fun y : LiftTangent => p (t,y)) (x,θ) = 0 := by
    simpa only [fderiv_const_apply] using he.fderiv_eq (𝕜 := ℝ)
  rw [pressureGradient_eq_spatialDual,hd,zero_comp,map_zero]

theorem pressureGradient_odd (p : ScalarField) (t : ℝ)
    (hp : ContDiff ℝ ∞ (fun y : LiftTangent => p (t,y)))
    (heven : ∀ x θ, p (t,(-x,-θ)) = p (t,(x,θ))) (x : Space) (θ : ℝ) :
    pressureGradient p (t,(-x,-θ)) = -pressureGradient p (t,(x,θ)) := by
  have heq : (fun y : LiftTangent => p (t,-y)) = (fun y : LiftTangent => p (t,y)) :=
    funext (fun y => heven y.1 y.2)
  have hd := ((hp.differentiable (by simp) (-(x,θ))).hasFDerivAt).comp (x,θ)
    ((hasFDerivAt_id (𝕜 := ℝ) (x,θ)).neg)
  have h : fderiv ℝ (fun y : LiftTangent => p (t,y)) (x,θ) =
      -fderiv ℝ (fun y : LiftTangent => p (t,y)) (-(x,θ)) := by
    simpa only [Function.comp_def,heq,comp_neg,comp_id] using hd.fderiv
  have hneg : fderiv ℝ (fun y : LiftTangent => p (t,y)) (-(x,θ)) =
      -fderiv ℝ (fun y : LiftTangent => p (t,y)) (x,θ) := by
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  rw [pressureGradient_eq_spatialDual,pressureGradient_eq_spatialDual]
  change (toDual ℝ Space).symm
    ((fderiv ℝ (fun y : LiftTangent => p (t,y)) (-(x,θ))).comp (inl ℝ Space ℝ)) = _
  rw [hneg,neg_comp,map_neg]

end EulerPacketCylinderField
