/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetParity
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblyParity
public import LeanPool.NavierStokesAndEuler.Euler.SmallCorrectionBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldParityAlgebra
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteParity

/-! Odd static data give the genuine parity hypotheses of the constructed
correction. In particular the actual convection residual is odd; this is
proved from its derivative formula. -/

@[expose] public section


noncomputable section

namespace EulerSmallCorrection

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerPacketCylinderField EulerPacketProfileRecursion EulerCorrectionAssembly
  EulerConstantCorrection

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField}
  (G : Field P T raw) (hodd : JointOdd T raw)

include G hodd in
theorem residual_odd (ε : ℝ) :
    JointOdd T (fun z => fderiv ℝ (fun y => (ε • raw) (z.1,y)) z.2 ((ε • raw) z,0)) := by
  have hs := hodd.smul ε
  intro t x θ
  change (fderiv ℝ (fun y => (ε • raw) (t,y)) (-x,-θ)) ((ε • raw) (t,(-x,-θ)),0) =
    -((fderiv ℝ (fun y => (ε • raw) (t,y)) (x,θ)) ((ε • raw) (t,(x,θ)),0))
  rw [(G.smul ε).raw_fderiv_even_of_odd hs t x θ,hs t x θ]
  have he : (-(ε • raw) (t,(x,θ)),(0 : ℝ)) = -((ε • raw) (t,(x,θ)),(0 : ℝ)) := by simp
  rw [he,map_neg]

include hodd in
theorem parityData (ε : ℝ) : ParityData P (input G ε) where
  metric _ _ := rfl
  linear _ _ := rfl
  quadratic _ _ _ := by
    change (0 : Space →L[ℝ] Space)= -0
    simp only [neg_zero]
  approximation t := by
    have h := ((G.smul ε).reflectionOdd_of_raw (hodd.smul ε)) t
    change -EulerCylinderFieldReflection.reflection P ((G.smul ε).path t)=(G.smul ε).path t
    rw [h,neg_neg]
  residual t := by
    have h := ((residual G ε).reflectionOdd_of_raw (residual_odd G hodd ε)) t
    change -EulerCylinderFieldReflection.reflection P ((residual G ε).path t)=(residual G ε).path t
    rw [h,neg_neg]

end EulerSmallCorrection
