/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderBoundedCover
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousBoundedTensor
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField

/-! Actual smooth bounded real-cover coefficients obtained from a smooth
mixed translation orbit in cylinder L². Every spatial tensor jet is a
continuous path in the uniform norm. No integrability on the real cover is
asserted or used. -/

@[expose] public section


noncomputable section


namespace EulerCylinderSmoothTimeField

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSmoothOrbit
  EulerLpCylinderTranslation EulerCylinderBoundedCover EulerContinuousBoundedTensor
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {K : Type} [TopologicalSpace K] [CompactSpace K]
  (p : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSmoothTimeField1 (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ]
    Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSmoothTimeField2 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space)
    := inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))`
instance to shorten typeclass synthesis. -/
local instance instCylinderSmoothTimeField3 (n : ℕ) : NormedAddCommGroup
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))` instance
to shorten typeclass synthesis. -/
local instance instCylinderSmoothTimeField4 (n : ℕ) : NormedSpace ℝ
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance

/-- Cover jet, given by `tensorPathMap n (iteratedFDeriv ℝ n (coverOrbit P p hp) 0)`. -/
def coverJet (n : ℕ) : C(K, LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) :=
  tensorPathMap n (iteratedFDeriv ℝ n (coverOrbit P p hp) 0)

theorem coverJet_eq (n : ℕ) (t : K) (x : LiftTangent) :
    coverJet P p hp n t x = iteratedFDeriv ℝ n (coverPath P p hp t : LiftTangent → Space) x := by
  rw [coverJet, tensorPath_iteratedFDeriv _ (coverOrbit_contDiff P p hp)]
  have he : (fun a => coverOrbit P p hp a t x) =
      fun a => coverPath P p hp t (x+a) := funext (fun a => coverOrbit_apply P p hp a t x)
  rw [he, iteratedFDeriv_comp_add_left]
  simp only [add_zero]

theorem coverPath_smooth (t : K) :
    ContDiff ℝ ∞ (coverPath P p hp t : LiftTangent → Space) := by
  have hc := (BoundedContinuousFunction.evalCLM ℝ (0 : LiftTangent)).contDiff.comp
    ((ContinuousMap.evalCLM ℝ t).contDiff.comp (coverOrbit_contDiff P p hp))
  have he : (fun a => coverOrbit P p hp a t 0) =
      (coverPath P p hp t : LiftTangent → Space) := by
    funext a
    simpa only [zero_add] using coverOrbit_apply P p hp a t 0
  exact he ▸ hc

/-- Of path, bundling `field`, `smooth`, `jet`, `jet_eq`. -/
def ofPath : SmoothTimeField K LiftTangent Space where
  field := coverPath P p hp
  smooth := coverPath_smooth P p hp
  jet := coverJet P p hp
  jet_eq := coverJet_eq P p hp

@[simp] theorem ofPath_apply (t : K) (x : LiftTangent) :
    (ofPath P p hp).field t x = pointField P p hp t (coveringMap P x) := rfl

theorem ofPath_jet_norm_le (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (t : K) (x : LiftTangent),
      ‖iteratedFDeriv ℝ n (fun y => pointField P p hp t (coveringMap P y)) x‖ ≤ C) :
    ‖(ofPath P p hp).jet n‖ ≤ C := by
  apply (ContinuousMap.norm_le _ hC).2
  intro t
  apply (BoundedContinuousFunction.norm_le hC).2
  intro x
  rw [(ofPath P p hp).jet_eq]
  exact hb t x

end EulerCylinderSmoothTimeField
