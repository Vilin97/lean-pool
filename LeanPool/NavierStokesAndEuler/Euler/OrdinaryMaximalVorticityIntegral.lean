/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryMaximalVorticity
public import LeanPool.NavierStokesAndEuler.Euler.NonnegativeImproperIntegral

@[expose] public section

/-! The actual nonnegative vorticity density of a maximal Euler solution
has an infinite extended integral whenever its genuine partial vorticity
integrals are unbounded. The only unboundedness input is the explicit
family statement used by the BKM continuation argument. -/

noncomputable section

namespace EulerOrdinarySobolev.FiniteLifespan

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanCutoffCurl
  EulerVolterraConvolution EulerContinuousTimeIntegral
open scoped ENNReal

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

/-- The true vorticity supremum on the lifespan, extended by zero only
to make the ambient real-time integral available. -/
def maximalVorticityDensity (r : ℝ) : ℝ := by
  classical
  exact if hr : r ∈ Ico (0 : ℝ) L.duration then L.maximalVorticityNorm ⟨r,hr⟩ else 0

theorem maximalVorticityDensity_nonneg (r : ℝ) : 0 ≤ L.maximalVorticityDensity r := by
  classical
  unfold maximalVorticityDensity
  split
  · exact L.maximalVorticityNorm_nonneg _
  · exact le_rfl

theorem maximalVorticityDensity_measurable : Measurable L.maximalVorticityDensity := by
  classical
  exact L.maximalVorticityNorm_continuous.measurable.dite measurable_const measurableSet_Ico

theorem maximalVorticityDensity_eq (t : L.Time) :
    L.maximalVorticityDensity t=L.maximalVorticityNorm t := by
  classical
  simp only [maximalVorticityDensity,dite_eq_left t.property]

theorem maximalVorticityDensity_le_iff (t : L.Time) (K : ℝ) :
    L.maximalVorticityDensity t ≤ K ↔ ∀ x, ‖vectorCurl (L.maximalVelocity t) x‖ ≤ K := by
  rw [L.maximalVorticityDensity_eq]
  exact L.maximalVorticityNorm_le_iff t K

theorem maximalVorticityDensity_eq_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalVorticityDensity t=(L.evolution S hS hSL).vorticityNormPath t := by
  classical
  have ht : (t : ℝ) ∈ Ico (0 : ℝ) L.duration := ⟨t.property.1,t.property.2.trans_lt hSL⟩
  rw [maximalVorticityDensity,dite_eq_left ht]
  exact L.maximalVorticityNorm_eq_evolution S hS hSL t

theorem maximalVorticityDensity_continuousOn (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) :
    ContinuousOn L.maximalVorticityDensity (Icc (0 : ℝ) S) := by
  have hc : Continuous (fun r : ℝ =>
      (L.evolution S hS hSL).vorticityNormPath (projIcc 0 S hS.le r)) :=
    (L.evolution S hS hSL).vorticityNormPath.continuous.comp continuous_projIcc
  apply hc.continuousOn.congr
  intro r hr
  change L.maximalVorticityDensity r=
    (L.evolution S hS hSL).vorticityNormPath (projIcc 0 S hS.le r)
  rw [projIcc_of_mem hS.le hr]
  exact L.maximalVorticityDensity_eq_evolution S hS hSL ⟨r,hr⟩

theorem maximalVorticityDensity_intervalIntegrable (S : ℝ) (hS : 0 < S)
    (hSL : S < L.duration) : IntervalIntegrable L.maximalVorticityDensity volume 0 S :=
  (L.maximalVorticityDensity_continuousOn S hS hSL).intervalIntegrable_of_Icc hS.le

theorem maximalVorticityDensity_integral_eq_evolution (S : ℝ) (hS : 0 < S)
    (hSL : S < L.duration) (t : Icc (0 : ℝ) S) :
    (∫ r in (0 : ℝ)..(t : ℝ), L.maximalVorticityDensity r)=
      (L.evolution S hS hSL).vorticityIntegral t := by
  apply intervalIntegral.integral_congr
  intro r hr
  have hrt : r ∈ Icc (0 : ℝ) (t : ℝ) := by
    simpa only [uIcc_of_le t.property.1] using hr
  have hrS : r ∈ Icc (0 : ℝ) S := ⟨hrt.1,hrt.2.trans t.property.2⟩
  change L.maximalVorticityDensity r=
    (L.evolution S hS hSL).vorticityNormPath (projIcc 0 S hS.le r)
  rw [projIcc_of_mem hS.le hrS]
  exact L.maximalVorticityDensity_eq_evolution S hS hSL ⟨r,hrS⟩

theorem maximalVorticityDensity_integral_eq (t : L.Time) :
    (∫ r in (0 : ℝ)..(t : ℝ), L.maximalVorticityDensity r)=L.maximalVorticityIntegral t :=
  L.maximalVorticityDensity_integral_eq_evolution (L.intermediateHorizon t)
    (L.intermediateHorizon_pos t) (L.intermediateHorizon_lt t) (L.intermediateTime t)

/-- This is the improper integral as an extended nonnegative integral,
not the totalized real Bochner integral at the singular endpoint. -/
theorem maximalVorticity_lintegral_eq_top
    (hunbounded : ∀ G : ℝ, ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
      (t : Icc (0 : ℝ) S), G < (L.evolution S hS hSL).vorticityIntegral t) :
    (∫⁻ r in Ico (0 : ℝ) L.duration, ENNReal.ofReal (L.maximalVorticityDensity r))=⊤ := by
  apply EulerNonnegativeImproperIntegral.lintegral_eq_top_of_unbounded_partials
    L.maximalVorticityDensity L.duration
    L.maximalVorticityDensity_intervalIntegrable
    (fun r _ => L.maximalVorticityDensity_nonneg r)
  intro K
  obtain ⟨S,hS,hSL,t,hK⟩ := hunbounded K
  refine ⟨S,hS,hSL,?_⟩
  rw [L.maximalVorticityDensity_integral_eq_evolution S hS hSL ⟨S,hS.le,le_rfl⟩]
  exact hK.trans_le ((L.evolution S hS hSL).vorticityIntegral_mono
    t ⟨S,hS.le,le_rfl⟩ t.property.2)

end EulerOrdinarySobolev.FiniteLifespan
