/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPressureGradient
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPressureParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPressureLocality
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldSupport

@[expose] public section

/-! Support and joint odd parity of the actual high-pressure gradient used in the recursion. -/

noncomputable section

namespace EulerTransversePacketProvider

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketCylinderField
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderFieldReflection

namespace Forcing

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)

theorem scalarGradient_zero_outside (t : ℝ) (x : Space) (hx : x ∉ D.support) (θ : ℝ) :
    pressureGradient (G.scalar I) (t,(x,θ)) = 0 :=
  pressureGradient_zero_outside (G.scalar I) t D.support D.support_compact.isClosed
    (G.scalar_zero_outside I t) x hx θ

theorem scalarGradientField_supported (t : Icc (0 : ℝ) D.T) :
    (G.scalarGradientField I).path t ∈ Supported P Space D.support D.support_measurable :=
  (G.scalarGradientField I).supported_of_raw_zero D.support D.support_measurable
    (fun t => G.scalarGradient_zero_outside I t) t

theorem scalarGradient_odd
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t,(-x,-θ)) = -raw (t,(x,θ)))
    (hinit : reflection P (I.value : CylinderL2 P U) = -(I.value : CylinderL2 P U))
    (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    pressureGradient (G.scalar I) (t,(-x,-θ)) = -pressureGradient (G.scalar I) (t,(x,θ)) :=
  pressureGradient_odd (G.scalar I) t (G.scalar_spatial_smooth I t)
    (G.scalar_even I hSym hF hM hraw hinit t) x θ

end Forcing

variable (P : ℝ) [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (I : InitialData P D) (raw : VectorField)
  (h : Nonempty (Forcing P D raw))

theorem highSolvePressureGradientField_supported (t : Icc (0 : ℝ) D.T) :
    (highSolvePressureGradientField P D I raw h).path t ∈
      Supported P Space D.support D.support_measurable :=
  (Classical.choice h).scalarGradientField_supported I t

end EulerTransversePacketProvider
