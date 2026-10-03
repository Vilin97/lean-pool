/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorDiffusionRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.StreamFlowPiola

/-! The selected corrector diffusion expansion with all flow-divergence
inputs derived from the stream sequence. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

/-- At a nonzero odd cutoff, the source diffusion column expands into the
corrector time derivative and its inverse-flow and Piola error divergences.
The classical divergence-free property is derived from `IsStreamSeq`. -/
theorem diffusionMatrix_selected_corrector_column_divergence_source
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (k : ℤ) (t : ℝ) (x : Vec 2) (κ : ℝ) (j : Fin 2)
    (hk : Odd k) (hxi : I.xiMK m k t ≠ 0) :
    matDiv (fun y => diffusionMatrix I hΦ m κ t y *
      (1 + gradChiTilde I hΦ m κ k t y)) x j =
      deriv (fun s => I.chiMK κ m k s
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t +
        matDiv (correctorDefectMatrix I hΦ m k t κ) x j +
        matDiv (correctorPushforwardMatrix I hΦ m k t κ) x j := by
  exact diffusionMatrix_selected_corrector_column_divergence_of_smooth
    I hΦ m hm k t x κ j hk hxi
    (streamVel_spatialDivergence_eq_zero I hΦ m)

end AVenhance.Infra.Section5
