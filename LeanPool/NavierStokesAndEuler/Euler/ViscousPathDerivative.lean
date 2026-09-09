/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ViscosityDefect
public import LeanPool.NavierStokesAndEuler.Euler.ViscosityCauchy

/-! A pointwise viscous derivative expressed as a continuous path. -/

@[expose] public section


noncomputable section

namespace EulerViscousPathDerivative

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeatGenerator
  EulerViscosityDefect EulerViscosityCauchy EulerVolterraConvolution

variable (period : ℝ) [Fact (0 < period)]

/-- The actual pointwise viscous derivative equals evaluation of its continuous source path. -/
theorem hasDerivAt_path {s q : ℕ} (hs : 2 ≤ s) (ν T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (r : ℝ) (hr : r ∈ Ioo 0 T)
    (hd : HasDerivAt (fun x => value period (extendPath T hT u x))
      (ν • laplacianEvaluation period s hs (u ⟨r, hr.1.le, hr.2.le⟩) +
        value period (f ⟨r, hr.1.le, hr.2.le⟩)) r) :
    HasDerivAt (extendPath T hT (valuePath period T u))
      (extendPath T hT (viscousDefect period hs ν T u + valuePath period T f) r) r := by
  apply hd.congr_deriv
  change _ = (viscousDefect period hs ν T u + valuePath period T f) (projIcc 0 T hT r)
  rw [projIcc_of_mem hT ⟨hr.1.le,hr.2.le⟩]
  rfl

end EulerViscousPathDerivative
