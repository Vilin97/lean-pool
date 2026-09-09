/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionLocal
import LeanPool.NavierStokesAndEuler.Euler.BoundedMildContinuation
import LeanPool.NavierStokesAndEuler.Euler.DivergenceFreeHeat

/-! Actual divergence-free continuation of the concrete viscous correction equation. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionContinuation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCorrectionOperators
  EulerQuadraticSource EulerDivergenceFreeHeat EulerBoundedMildContinuation
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every actual partial zero-initial correction solution preserves the lifted divergence
constraint. -/
theorem correction_mild_divergenceFree {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) (hν : 0 < ν)
    {T S : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : CorrectionData period q (Icc (0 : ℝ) S))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t, e t = quadraticDuhamel period ν hν hT hTS (D.coefficients period hq) 0 e t) :
    ∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction := by
  let F := ((D.coefficients period hq).comp (timeInclusion hTS)).apply
  have hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q+1) => F p.1 p.2) :=
    ((D.coefficients period hq).comp (timeInclusion hTS)).continuous
  have hz := mild_solution_preserves_gradient_zero period D.κ D.direction ν hν T hT 0
    (map_zero _) F hF (fun t u => D.source_gradient_zero period hq (timeInclusion hTS t) u) e hsol
  intro t
  exact (gradientEvaluation_zero_iff period D.κ D.direction (e t)).mp (hz t)

/-- A genuine a-priori Sobolev bound continues the actual zero-initial viscous Euler correction
across the prescribed interval. -/
theorem exists_global_correction_of_bound {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) (hν : 0 < ν)
    (S : ℝ) (hS : 0 < S) (R : ℝ) (hR : 0 ≤ R)
    (D : CorrectionData period q (Icc (0 : ℝ) S))
    (hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
      (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))),
      (∀ t, e t = quadraticDuhamel period ν hν hT hTS (D.coefficients period hq) 0 e t) → ‖e‖ ≤ R) :
    ∃ e : C(Icc (0 : ℝ) S, SobolevSpace period (q+1)),
      ‖e‖ ≤ R ∧ e ⟨0,le_rfl,hS.le⟩ = 0 ∧
      (∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) ∧
      ∀ t, e t = quadraticDuhamel period ν hν hS.le le_rfl (D.coefficients period hq) 0 e t := by
  obtain ⟨e,he,hi,hsol⟩ := exists_global_mild_of_bound period q ν hν S hS R hR 0
    (by simpa only [norm_zero] using hR) (D.coefficients period hq) hbound
  exact ⟨e,he,hi,correction_mild_divergenceFree period hq ν hν hS.le le_rfl D e hsol,hsol⟩

end EulerCorrectionContinuation
