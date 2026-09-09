/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionContinuation
public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionEquation

@[expose] public section

/-! Every actual continued mild correction obeys the literal viscous PDE with its genuine coercive
  pressure. -/

noncomputable section

namespace EulerCorrectionContinuation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCorrectionOperators
  EulerQuadraticSource EulerMildEquationBridge EulerSobolevHeatGenerator EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The literal PDE follows at every interior time from any actual correction mild solution. -/
theorem correction_mild_hasDerivAt {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) (hν : 0 < ν)
    {T S : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : CorrectionData period q (Icc (0 : ℝ) S))
    (e : C(Icc (0 : ℝ) T,SobolevSpace period (q+1)))
    (hsol : ∀ t, e t = quadraticDuhamel period ν hν hT hTS (D.coefficients period hq) 0 e t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT e r))
      (ν • laplacianEvaluation period (q+1) (by omega) (e ⟨t,ht.1.le,ht.2.le⟩) -
        value period (D.rawSource period hq (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩) (e
          ⟨t,ht.1.le,ht.2.le⟩)) -
        (D.metric.coefficient (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩)).operator
          (value period (D.pressure period hq (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩) (e
            ⟨t,ht.1.le,ht.2.le⟩)))) t := by
  let F := ((D.coefficients period hq).comp (timeInclusion hTS)).apply
  have hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q+1) => F p.1 p.2) :=
    ((D.coefficients period hq).comp (timeInclusion hTS)).continuous
  have hp := viscous_mild_hasDerivAt period (by omega : 2 ≤ q) ν hν T hT 0 F hF e hsol t ht
  change HasDerivAt _ (ν • laplacianEvaluation period (q+1) _ (e ⟨t,ht.1.le,ht.2.le⟩) +
    value period ((D.coefficients period hq).apply (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩) (e
      ⟨t,ht.1.le,ht.2.le⟩))) t at hp
  rw [D.source_value period hq] at hp
  convert hp using 1
  abel

end EulerCorrectionContinuation
