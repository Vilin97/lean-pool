/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-! # Smooth extension of a vector field near one point -/

@[expose] public noncomputable section
open Set Metric Filter
open scoped Topology ContDiff

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

/-- Finite-order local smoothness admits a globally smooth representative of
the same germ. The cutoff is constant one near the selected point. -/
theorem exists_contDiff_extension (n : ℕ) {v : E → E} {x : E}
    (hv : ContDiffAt ℝ n v x) :
    ∃ w : E → E, ContDiff ℝ n w ∧ w =ᶠ[𝓝 x] v := by
  obtain ⟨U, hU, hvU⟩ := hv.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  let b : ContDiffBump x :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨fun y => b y • v y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ ball x r
    · exact b.contDiffAt.smul
        ((hvU.mono hball y hy).contDiffAt (isOpen_ball.mem_nhds hy))
    · have hd : r ≤ dist y x := le_of_not_gt hy
      have hN : ∀ᶠ z in 𝓝 y, r / 2 < dist z x :=
        (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds
          (by change r / 2 < dist y x; linarith)
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [hN] with z hz
      rw [b.zero_of_le_dist (show b.rOut ≤ dist z x from hz.le), zero_smul]
  · filter_upwards [b.eventuallyEq_one] with y hy
    simp only [hy, Pi.one_apply, one_smul]

end LichnerowiczObata
