/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSmoothRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.CanonicalGraphPotential
import LeanPool.NavierStokesAndEuler.Euler.MeanPressurePotential
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Classical divergence and pressure identities for the reconstructed mean fields. -/

@[expose] public section


noncomputable section

namespace EulerMeanClassical

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerVectorCalculus EulerMeanSolenoidal
  EulerMeanSmoothRepresentative EulerMeanPressure EulerCanonicalGraphPotential
open scoped ContDiff

theorem solenoidal_representative_divergence (u : L2) (hu : u ∈ solenoidalSpace)
    (f : Space → Space) (hf : ContDiff ℝ ∞ f) (hrep : u =ᵐ[volume] f) :
    ∀ x, divergence f x = 0 := by
  have he : divergence f = coordinateTrace ∘ fderiv ℝ f := by
    funext x
    exact (coordinateTrace_eq_linearTrace (fderiv ℝ f x)).symm
  have hc : Continuous (divergence f) := by
    rw [he]
    exact coordinateTrace.continuous.comp (hf.fderiv_right (m := ∞) (by simp)).continuous
  have hz : divergence f =ᵐ[volume] 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hc.locallyIntegrable (fun φ hφ hcφ => by
      have hw := weak_divergence_test hu φ hcφ hφ
      have hi := gradient_test_integration_by_parts f hf φ hcφ hφ
      have heq : (∫ x, ⟪gradient φ x, u x⟫_ℝ) = ∫ x, ⟪gradient φ x, f x⟫_ℝ := by
        apply integral_congr_ae
        filter_upwards [hrep] with x hx
        rw [hx]
      change (∫ x, φ x * divergence f x) = 0
      rw [heq, hi] at hw
      exact neg_eq_zero.mp hw)
  intro x
  exact congrFun (Measure.eq_of_ae_eq hz hc continuous_const) x

/-- The actual smooth representative inherits the weak solenoidal constraint pointwise. -/
theorem representative_divergence (u : L2) (hu : u ∈ solenoidalSpace) (hs : SmoothOrbit u) :
    ∀ x, divergence (representative u hs) x = 0 :=
  solenoidal_representative_divergence u hu (representative u hs)
    (representative_smooth u hs) (representative_ae u hs)

/-- A smooth translation orbit in the genuine gradient space has a normalized classical pressure. -/
theorem representative_pressure (p : L2) (hp : p ∈ gradientSpace) (hs : SmoothOrbit p) :
    ContDiff ℝ ∞ (radialPotential (representative p hs)) ∧
      radialPotential (representative p hs) 0 = 0 ∧
      ∀ x, gradient (radialPotential (representative p hs)) x = representative p hs x :=
  gradientSpace_radial_potential p hp (representative p hs)
    (representative_ae p hs) (representative_smooth p hs)

end EulerMeanClassical
