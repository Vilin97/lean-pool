/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryLogarithmicGradient
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryBKMReduction
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryMaximalVorticityIntegral

@[expose] public section

/-! The ordinary Euler vorticity blowup criterion, with the whole-space
logarithmic estimate proved and instantiated. No spatial estimate or
unboundedness assumption remains in these conclusions. -/

noncomputable section

namespace EulerOrdinarySobolev.FiniteLifespan

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field
open scoped ENNReal

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

/-- Genuine partial vorticity integrals exceed every finite bound. -/
theorem vorticityIntegral_unbounded (G : ℝ) :
    ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
      (t : Icc (0 : ℝ) S), G < (L.evolution S hS hSL).vorticityIntegral t :=
  vorticity_unbounded_of_logarithmic logarithmicGradientConstant
    logarithmicGradientConstant_nonneg logarithmic_gradient_bound_solenoidal L G

/-- The actual partial integrals tend to infinity as time approaches the
maximal lifespan from below. -/
theorem vorticityIntegral_tendsto_atTop :
    Tendsto L.maximalVorticityIntegral (atTop : Filter L.Time) atTop :=
  L.maximalVorticityIntegral_tendsto_atTop L.vorticityIntegral_unbounded

/-- The true nonnegative vorticity supremum has infinite integral on the
half-open maximal lifespan. This is an extended integral, so divergence
is not obscured by the convention for nonintegrable real integrals. -/
theorem vorticity_lintegral_eq_top :
    (∫⁻ r in Ico (0 : ℝ) L.duration, ENNReal.ofReal (L.maximalVorticityDensity r))=⊤ :=
  L.maximalVorticity_lintegral_eq_top L.vorticityIntegral_unbounded

end EulerOrdinarySobolev.FiniteLifespan
