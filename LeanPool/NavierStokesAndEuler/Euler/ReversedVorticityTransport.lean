/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffCurlBound
public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
import LeanPool.NavierStokesAndEuler.Euler.ScalarEulerVorticity

/-! Nonzero vorticity cannot disappear on an existing reverse-time particle
trajectory of a Comparator solution. -/

@[expose] public section


noncomputable section

open Set EulerSmoothLimit EulerMeanCutoffCurl
open scoped ContDiff Topology

namespace Euler.EulerExistenceAndSmoothnessR3

variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

include h

/-- A reverse-time particle path carrying nonzero vorticity at time `T`
reaches a point with nonzero initial vorticity. -/
theorem vorticity_ne_zero_along_reverse_trajectory
    (X : ℝ → Space) (T : ℝ) (hT : 0 ≤ T)
    (hX : ContinuousOn X (Icc 0 T))
    (hXd : ∀ s ∈ Ioo 0 T, HasDerivAt X (-v (X s) (T - s)) s)
    (hne : vectorCurl (v · T) (X 0) ≠ 0) :
    vectorCurl (v · 0) (X T) ≠ 0 := by
  intro hz
  have hY : ContinuousOn (fun r => X (T - r)) (Icc 0 T) :=
    hX.comp (continuousOn_const.sub continuousOn_id)
      (fun r hr => ⟨sub_nonneg.mpr hr.2, sub_le_self T hr.1⟩)
  have hYd : ∀ r ∈ Ioo 0 T,
      HasDerivAt (fun s => X (T - s)) (v (X (T - r)) r) r := by
    intro r hr
    have hs : T - r ∈ Ioo 0 T := ⟨sub_pos.mpr hr.2, sub_lt_self T hr.1⟩
    simpa only [sub_sub_cancel, neg_neg] using
      HasDerivAt.comp_const_sub T r (hXd (T - r) hs)
  have hi : vectorCurl (v · 0) (X (T - 0)) = 0 := by simpa using hz
  have he := h.vorticity_eq_zero_along_trajectory (fun r => X (T - r)) T
    hY hYd hi T ⟨hT, le_rfl⟩
  apply hne
  simpa only [sub_self] using he

/-- A path for a modified reverse-time velocity has the same nonzero
vorticity transport whenever that velocity agrees with Euler along the path. -/
theorem vorticity_ne_zero_along_reverse_trajectory_of_agrees
    (X : ℝ → Space) (w : ℝ → Space → Space) (T : ℝ) (hT : 0 ≤ T)
    (hX : ContinuousOn X (Icc 0 T))
    (hXd : ∀ s ∈ Ioo 0 T, HasDerivAt X (-w s (X s)) s)
    (hw : ∀ s ∈ Ioo 0 T, w s (X s) = v (X s) (T - s))
    (hne : vectorCurl (v · T) (X 0) ≠ 0) :
    vectorCurl (v · 0) (X T) ≠ 0 := by
  apply h.vorticity_ne_zero_along_reverse_trajectory X T hT hX _ hne
  intro s hs
  simpa only [hw s hs] using hXd s hs

end Euler.EulerExistenceAndSmoothnessR3
