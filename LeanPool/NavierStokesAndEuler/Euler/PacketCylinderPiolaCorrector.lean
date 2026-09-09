/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPiolaData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderField

@[expose] public section

/-! The literal raw curl-corrector equals the genuine periodic Piola corrector. -/

noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerCylinderSmoothOrbit EulerPacketProfileRecursion
  EulerPacketAngularPotential EulerPacketPeriodicPotential EulerPacketPiola

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) {raw : VectorField}
  (G : Field P D.T raw) (t : Icc (0 : ℝ) D.T)

theorem rawMean_pointField
    (hm : ∀ x, (∫ θ in (0 : ℝ)..P, raw (t,(x,θ))) = 0) (x : Space) :
    (∫ θ in (0 : ℝ)..P, pointField P G.path G.orbit t (x,(θ : AddCircle P))) = 0 := by
  convert hm x using 1
  apply intervalIntegral.integral_congr
  intro θ _
  exact (G.raw_eq t x θ).symm

theorem rawCorrector_eq_lifted
    (hm : ∀ x, (∫ θ in (0 : ℝ)..P, raw (t,(x,θ))) = 0) (x : Space) (θ : ℝ) :
    D.curlCorrector P raw (t,(x,θ)) =
      EulerPacketConstructedPiola.corrector P (D.deformationEquiv t) D.m₀
        (pointField P G.path G.orbit t) (x,(θ : AddCircle P)) := by
  let A := pointField P G.path G.orbit t
  let Q := EulerPacketPeriodicPotential.field P (D.normal.field t) A
  have hAc : Continuous A := smoothField_continuous P A (pointField_smooth P G.path G.orbit t)
  have hAm : ∀ y, (∫ s in (0 : ℝ)..P, A (y,(s : AddCircle P))) = 0 :=
    rawMean_pointField D G t hm
  have hQ : (fun y : LiftTangent => D.rawPotential P raw (t,y)) =
      fun y : LiftTangent => Q (y.1,(y.2 : AddCircle P)) := by
    funext y
    have hraw : (fun s : ℝ => raw (t,(y.1,s))) =
        fun s : ℝ => A (y.1,(s : AddCircle P)) := funext (fun s => G.raw_eq t y.1 s)
    change potential P (D.normal.field (D.clamp t) y.1)
      (fun s : ℝ => raw (t,(y.1,s))) y.2 = _
    rw [EulerTransversePacketProvider.Data.clamp_coe,hraw]
    have hc := field_cover P (D.normal.field t) A hAc hAm y
    simpa only [Q,coveringMap,coveringPotential,localFieldLift,Prod.fst_zero,
      Prod.snd_zero,zero_add] using hc.symm
  change EulerMeanBoundary.curlMatrix
    ((fderiv ℝ (fun y : LiftTangent => D.rawPotential P raw (t,y)) (x,θ)).comp
      ((ContinuousLinearMap.inl ℝ Space ℝ).comp (D.FInv.field (D.clamp t) x))) = _
  rw [EulerTransversePacketProvider.Data.clamp_coe,hQ,coverField_fderiv]
  rfl

end EulerPacketCylinderField
