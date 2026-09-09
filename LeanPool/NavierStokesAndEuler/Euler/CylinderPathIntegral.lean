/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral

@[expose] public section

/-! Initial time integration commutes with the genuine mixed cylinder action. -/

noncomputable section

namespace EulerCylinderPathIntegral

open Set ContinuousLinearMap EulerLpCylinderTranslation EulerLiftedGradientSpace
  EulerVolterraConvolution EulerContinuousTimeIntegral
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  (T : ℝ) (hT : 0 ≤ T)

theorem integral_translate (p : C(Icc (0 : ℝ) T,CylinderL2 P V)) (a : LiftTangent) :
    integral T hT (pathTranslate P a p) = pathTranslate P a (integral T hT p) := by
  apply ContinuousMap.ext
  intro t
  exact (translate P a).intervalIntegral_comp_comm (extendPath T hT p)

theorem integral_orbit_contDiff (p : C(Icc (0 : ℝ) T,CylinderL2 P V))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (integral T hT p)) := by
  have hh := (integral (E := CylinderL2 P V) T hT).contDiff.comp hp
  convert hh using 1
  funext a
  exact (integral_translate P T hT p a).symm

theorem orbit_contDiff_of_derivative
    (p q : C(Icc (0 : ℝ) T,CylinderL2 P V))
    (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t)
    (hzero : p ⟨0,le_rfl,hT⟩ = 0) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p) := by
  have he : p = integral T hT q := by
    apply ContinuousMap.ext
    intro t
    have hh := eq_initial_add_integral T hT q (extendPath T hT p) hd t
    simpa only [extendPath,projIcc_of_mem hT t.property,
      projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),hzero,zero_add] using hh
  rw [he]
  exact integral_orbit_contDiff P T hT q hq

end EulerCylinderPathIntegral
