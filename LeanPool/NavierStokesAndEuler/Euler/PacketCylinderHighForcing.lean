/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldSupport
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighMean
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathAdvection
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderPaths

/-! Supported, zero-mean raw cylinder witnesses feed the actual high-mode solver. -/

section

/-! Genuine nonlinear cylinder products preserve support of their multiplying factor. -/

@[expose] public section

noncomputable section

namespace EulerCylinderPathProduct

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpSupportedSubspace EulerMetricTransport EulerLiftedWeakDerivative
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (S : Set Space) (hS : MeasurableSet S)

/-- Retain the actual values of a continuous path that already has the stated support. -/
def supportedPath (p : C(K, LiftL2 P)) (h : ∀ t, p t ∈ Supported P Space S hS) :
    C(K,Supported P Space S hS) :=
  ⟨fun t => ⟨p t,h t⟩, p.continuous.subtype_mk h⟩

omit [CompactSpace K] in
@[simp] theorem include_supportedPath (p : C(K, LiftL2 P))
    (h : ∀ t, p t ∈ Supported P Space S hS) :
    includePath P S hS (supportedPath P S hS p h) = p := by
  apply ContinuousMap.ext
  intro t
  rfl

variable (p q : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))

theorem scalarProductPath_supported_left (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (hs : ∀ t, p t ∈ Supported P Space S hS) (t : K) :
    scalarProductPath P L hL p q hp hq t ∈ Supported P Space S hS := by
  apply (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) _).mpr
  have hzero := (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) (p t)).mp (hs t)
  filter_upwards [hzero,scalarProductPath_ae P L hL p q hp hq t,pointField_ae P p hp t]
    with x hz hr hrep hx
  rw [hr, ← hrep, hz hx, map_zero, zero_smul]

theorem scalarProductPath_supported_right (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (hs : ∀ t, q t ∈ Supported P Space S hS) (t : K) :
    scalarProductPath P L hL p q hp hq t ∈ Supported P Space S hS := by
  apply (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) _).mpr
  have hzero := (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) (q t)).mp (hs t)
  filter_upwards [hzero,scalarProductPath_ae P L hL p q hp hq t,pointField_ae P q hq t]
    with x hz hr hrep hx
  rw [hr, ← hrep, hz hx, smul_zero]

theorem bilinearProductPath_supported_left (B : Space →L[ℝ] Space →L[ℝ] Space)
    (hs : ∀ t, p t ∈ Supported P Space S hS) (t : K) :
    bilinearProductPath P B p q hp hq t ∈ Supported P Space S hS := by
  apply (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) _).mpr
  have hzero := (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) (p t)).mp (hs t)
  filter_upwards [hzero,bilinearProductPath_ae P B p q hp hq t,pointField_ae P p hp t]
    with x hz hr hrep hx
  rw [hr, ← hrep, hz hx, map_zero, zero_apply]

theorem scalarDerivativeProductPath_supported (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (hs : ∀ t, p t ∈ Supported P Space S hS) (i : Fin 4) (t : K) :
    scalarDerivativeProductPath P L hL p q hp hq i t ∈ Supported P Space S hS :=
  scalarProductPath_supported_left P S hS p (derivativePath P q i) hp
    (derivativePath_orbit P q hq i) L hL hs t

theorem advectionPath_supported (hs : ∀ t, p t ∈ Supported P Space S hS) (t : K) :
    advectionPath P p q hp hq t ∈ Supported P Space S hS := by
  apply (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) _).mpr
  have hzero := (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) (p t)).mp (hs t)
  filter_upwards [hzero,advectionPath_ae P p q hp hq t,pointField_ae P p hp t]
    with x hz hr hrep hx
  rw [hr, ← hrep, hz hx]
  exact map_zero _

end EulerCylinderPathProduct

end
end

end

@[expose] public section

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
      (∫ θ in (0 : ℝ)..P, raw (t, (x, θ))) = 0) :
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
