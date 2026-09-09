/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldSupport
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighMean
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing

@[expose] public section

/-! Supported, zero-mean raw cylinder witnesses feed the actual high-mode solver. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderPaths
  EulerCylinderPathProduct EulerCylinderSmoothOrbit EulerLpCylinderTranslation
  EulerPacketProfileRecursion EulerCylinderAngleAverage

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Only actual support and literal mean zero are added to the existing field witness. -/
def transverseForcing (D : EulerTransversePacketProvider.Data U) {raw : VectorField}
    (G : Field P D.T raw)
    (hs : ∀ t, G.path t ∈ Supported P Space D.support D.support_measurable)
    (hm : ∀ (t : Icc (0 : ℝ) D.T) x,
      (∫ θ in (0 : ℝ)..P, raw (t,(x,θ))) = 0) :
    EulerTransversePacketProvider.Forcing P D raw where
  path := supportedPath P D.support D.support_measurable G.path hs
  path_orbit := by simpa only [include_supportedPath] using G.orbit
  raw_eq t x θ := by simpa only [include_supportedPath] using G.raw_eq t x θ
  mean_zero t := G.average_zero_of_raw_integral hm t

/-- A literal compact-support proof may be used directly, without selecting a new representative. -/
def transverseForcingOfRaw (D : EulerTransversePacketProvider.Data U) {raw : VectorField}
    (G : Field P D.T raw)
    (hs : ∀ (t : Icc (0 : ℝ) D.T) x, x ∉ D.support → ∀ θ : ℝ, raw (t,(x,θ)) = 0)
    (hm : ∀ (t : Icc (0 : ℝ) D.T) x,
      (∫ θ in (0 : ℝ)..P, raw (t,(x,θ))) = 0) :
    EulerTransversePacketProvider.Forcing P D raw :=
  G.transverseForcing D (G.supported_of_raw_zero D.support D.support_measurable hs) hm

end EulerPacketCylinderField.Field
