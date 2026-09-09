/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMultiplier

@[expose] public section

/-! Actual representatives of linear source, transport, and pressure combinations in Bochner time
  spaces. -/

noncomputable section

namespace EulerTimeLp

open MeasureTheory Set EulerVolterraConvolution

variable {E V W H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A genuine sum of fixed spatial and time-dependent operator actions has its literal pointwise representative. -/
theorem timeLinearForcing_ae (T : ℝ) (hT : 0 ≤ T) (D : E →L[ℝ] H) (B : V →L[ℝ] W)
    (A : C(Icc (0 : ℝ) T, W →L[ℝ] H)) (G : C(Icc (0 : ℝ) T, H →L[ℝ] H))
    (U : TimeLp T V) (F P : TimeLp T E) :
    (((D.compLpL 2 (timeMeasure T) F + timeMultiplier T hT A (B.compLpL 2 (timeMeasure T) U) +
      timeMultiplier T hT G (D.compLpL 2 (timeMeasure T) P)) : TimeLp T H) : ℝ → H) =ᵐ[timeMeasure
        T]
      fun t => D (F t) + A (projIcc 0 T hT t) (B (U t)) + G (projIcc 0 T hT t) (D (P t)) := by
  let DF := D.compLpL 2 (timeMeasure T) F
  let BU := B.compLpL 2 (timeMeasure T) U
  let DP := D.compLpL 2 (timeMeasure T) P
  let AB := timeMultiplier T hT A BU
  let GP := timeMultiplier T hT G DP
  filter_upwards [Lp.coeFn_add (DF+AB) GP, Lp.coeFn_add DF AB,
    D.coeFn_compLpL F, B.coeFn_compLpL U, D.coeFn_compLpL P,
    timeMultiplier_ae T hT A BU, timeMultiplier_ae T hT G DP] with t h1 h2 h3 h4 h5 h6 h7
  change (DF+AB+GP) t = _
  simp only [Pi.add_apply] at h1 h2
  rw [h1,h2,h3,h6,h7,h4,h5]
  rfl

end EulerTimeLp
