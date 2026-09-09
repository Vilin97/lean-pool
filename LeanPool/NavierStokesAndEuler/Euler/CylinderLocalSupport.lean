/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurl
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialPath
public import LeanPool.NavierStokesAndEuler.Euler.CylinderRawSupport

@[expose] public section

/-! Spatial support is preserved by the actual angular primitive, mixed derivative, and slow curl
  paths. -/

noncomputable section

namespace EulerCylinderLocalSupport

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerLiftedWeakDerivative EulerCylinderSmoothOrbit
  EulerLpSupportedSubspace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpCylinderRectangular EulerCylinderAnglePrimitive EulerCylinderPotential
open scoped ContDiff Topology BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] (S : Set Space) (hS : MeasurableSet S)

private local instance : NormedAddCommGroup (LiftL2 P) := inferInstance
private local instance : NormedSpace ℝ (LiftL2 P) := inferInstance
private local instance : NormedAddCommGroup (Supported P Space S hS) := inferInstance
private local instance : NormedSpace ℝ (Supported P Space S hS) := inferInstance

/-- Pure angular integration does not move the spatial support. -/
theorem primitive_supported (u : LiftL2 P) (hu : u ∈ Supported P Space S hS) :
    primitive P u ∈ Supported P Space S hS := by
  have hs (s : ℝ) : translate P (0,s) u ∈ Supported P Space S hS := by
    apply translate_mem P (0,s) S S hS hS _ ⟨u,hu⟩
    intro x hx
    change x+(0 : Space) ∈ S at hx
    simpa only [add_zero] using hx
  have hsk (s : ℝ) : kernelCurve P u s ∈ Supported P Space S hS :=
    (Supported P Space S hS).smul_mem s (hs s)
  let f : ℝ → Supported P Space S hS := fun s => ⟨kernelCurve P u s,hsk s⟩
  have hf : Continuous f := Continuous.subtype_mk (kernelCurve_continuous P u) _
  let v : Supported P Space S hS := P⁻¹ • (∫ s in (0 : ℝ)..P, f s)
  have he : (v : LiftL2 P) = primitive P u := by
    change (Supported P Space S hS).subtypeL (P⁻¹ • (∫ s in (0 : ℝ)..P, f s)) = _
    rw [map_smul, ← (Supported P Space S hS).subtypeL.intervalIntegral_comp_comm
      (hf.intervalIntegrable 0 P)]
    rfl
  rw [← he]
  exact v.property

omit hS [Fact (0 < P)] in
/-- Outside a closed spatial support, all local first derivatives vanish. -/
theorem fieldFDeriv_zero_outside (hSc : IsClosed S) (f : LiftDomain P → Space)
    (hf : ∀ x : LiftDomain P, x.1 ∉ S → f x = 0)
    (x : LiftDomain P) (hx : x.1 ∉ S) : fieldFDeriv P f x = 0 := by
  have hn : {a : LiftTangent | x.1+a.1 ∈ Sᶜ} ∈ 𝓝 (0 : LiftTangent) :=
    (hSc.isOpen_compl.preimage (continuous_const.add continuous_fst)).mem_nhds
      (by
        change x.1+(0 : LiftTangent).1 ∉ S
        simpa only [Prod.fst_zero, add_zero] using hx)
  have he : localFieldLift P f x =ᶠ[𝓝 (0 : LiftTangent)] (fun _ => (0 : Space)) := by
    filter_upwards [hn] with a ha
    exact hf (x.1+a.1,x.2+(a.2 : AddCircle P)) ha
  simpa only [fieldFDeriv, fderiv_const_apply] using he.fderiv_eq (𝕜 := ℝ)

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (p : C(K,LiftL2 P)) (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

include hp in
theorem pointField_zero_outside (hSc : IsClosed S)
    (hs : ∀ t, p t ∈ Supported P Space S hS) (t : K) (x : LiftDomain P) (hx : x.1 ∉ S) :
    pointField P p hp t x = 0 := by
  rw [pointField_eq_representative]
  exact representative_zero_outside P S hS hSc (p t) _ (hs t) x hx

include hp in
theorem derivativePath_supported (hSc : IsClosed S)
    (hs : ∀ t, p t ∈ Supported P Space S hS) (i : Fin 4) (t : K) :
    derivativePath P p i t ∈ Supported P Space S hS := by
  apply (mem_supportedSpace_ae (liftMeasure P) (spatialSet P S)
    (spatialSet_measurable P S hS) _).mpr
  filter_upwards [pointField_ae P (derivativePath P p i) (derivativePath_orbit P p hp i) t]
    with x hx hnot
  rw [hx, pointField_derivativePath P p hp i t x,
    fieldFDeriv_zero_outside P S hSc (pointField P p hp t)
      (pointField_zero_outside P S hS p hp hSc hs t) x hnot, zero_apply]

theorem potentialPath_supported (B : C(K,Space →ᵇ Space →L[ℝ] Space))
    (hs : ∀ t, p t ∈ Supported P Space S hS) (t : K) :
    potentialPath P B p t ∈ Supported P Space S hS :=
  EulerLpOperatorField.full_mem (liftMeasure P) (spatialSet P S) (spatialSet_measurable P S hS)
    (fieldLift P (B t)) ⟨primitive P (p t), primitive_supported P S hS (p t) (hs t)⟩

include hp in
theorem slowCurlPath_supported (G : C(K,Space →ᵇ Space →L[ℝ] Space)) (hSc : IsClosed S)
    (hs : ∀ t, p t ∈ Supported P Space S hS) (t : K) :
    EulerCylinderSlowCurl.path P G p t ∈ Supported P Space S hS := by
  change (∑ i : Fin 3, EulerCylinderSlowCurl.term P G p i) t ∈ Supported P Space S hS
  rw [ContinuousMap.sum_apply]
  apply (Supported P Space S hS).sum_mem
  intro i _
  exact EulerLpOperatorField.full_mem (liftMeasure P) (spatialSet P S) (spatialSet_measurable P S
    hS)
    (fieldLift P (EulerPacketPiola.curlCoefficientPath i G t))
    ⟨derivativePath P p i.succ t, derivativePath_supported P S hS p hp hSc hs i.succ t⟩

end EulerCylinderLocalSupport
