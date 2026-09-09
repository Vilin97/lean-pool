/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerLogarithmicControl
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerVorticity
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerLifespan
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerContinuation

/-! Reduction of the vorticity blowup criterion to the whole-space
logarithmic gradient inequality. The geometric inequality remains an
explicit hypothesis here and is discharged by the kernel argument. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Real EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSolenoidal EulerVectorCalculus EulerContinuousTimeIntegral

variable (C : ℝ) (hC : 0 ≤ C)
  (hlog : ∀ (A : SmoothL2Field Space) (W : ℝ), A.toLp ∈ solenoidalSpace →
    (∀ x, ‖EulerMeanCutoffCurl.vectorCurl A.field x‖ ≤ W) → ∀ x,
      ‖fderiv ℝ A.field x‖ ≤ C * (1 + ‖A.toLp‖ + W * log (exp 1 + tensorNorm 3 A)))

include hC hlog

theorem Evolution.gradientIntegral_of_vorticity_bound {T : ℝ} {hT : 0 ≤ T}
    (U : Evolution T hT) (Tmax G : ℝ) (hTmax : T ≤ Tmax)
    (hG : ∀ t, U.vorticityIntegral t ≤ G) (t : Icc (0 : ℝ) T) :
    U.gradientIntegral t ≤
      exp (logarithmicGronwallConstant C (U.velocity ⟨0,le_rfl,hT⟩)*(Tmax+G)) := by
  apply U.gradientIntegral_logarithmic_uniform C hC U.vorticityNormPath
    U.vorticityNormPath_nonneg _ Tmax G hTmax hG t
  intro s
  apply (U.gradientNormPath_le_iff s _).mpr
  exact hlog (U.velocity s) (U.vorticityNormPath s) (U.solenoidal s) (U.pointwise_vorticity_le s)

theorem FiniteLifespan.vorticity_unbounded_of_logarithmic {A : SmoothL2Field Space}
    (L : FiniteLifespan A) (G : ℝ) :
    ∃ (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) (t : Icc (0 : ℝ) S),
      G < (L.evolution S hS hSL).vorticityIntegral t := by
  by_contra hn
  push Not at hn
  apply L.no_endpoint
  apply L.endpoint_of_bounded_gradient
    (exp (logarithmicGronwallConstant C A*(L.duration+G)))
  intro S hS hSL t
  have h := (L.evolution S hS hSL).gradientIntegral_of_vorticity_bound C hC hlog
    L.duration G hSL.le (hn S hS hSL) t
  simpa only [L.evolution_initial S hS hSL] using h

end EulerOrdinarySobolev
