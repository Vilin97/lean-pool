/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureFluxIdentity

/-! The actual gradient diffusion term as an ordered two-spatial contraction. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Actual classical gradients have all local smoothness orders; this is
independent of the finite quantitative source jet budget. -/
theorem amnr_classical_gradient_smooth_infty
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hu : AVenhance.IsClassicalSol b κ F u₀ u) (i : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (amnrTGradient u i) (Ioi (0 : ℝ) ×ˢ univ) := by
  exact contDiffOn_infty.mpr (fun N => amnr_classical_gradient_smooth hu i N)

/-- Gradient diffusion is precisely the ordered coordinate Laplacian of the
actual gradient field, on the full positive-time spatial slice. -/
theorem amnr_classical_gradient_diffusion
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hu : AVenhance.IsClassicalSol b κ F u₀ u) (B : AmnrSpace → Vec 2)
    (i : Fin 2) {z : AmnrSpace} (hz : 0 < z.1) :
    AVenhance.spaceGrad (AVenhance.spaceLap (u z.1)) z.2 i =
      ∑ q : Fin 2, amnrWord B [some q, some q] (amnrTGradient u i) z := by
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (z.1, x)) := by fun_prop
  have hs : ContDiff ℝ (⊤ : ℕ∞) (u z.1) :=
    hu.1.comp_contDiff hm (fun x => ⟨hz.le, mem_univ x⟩)
  rw [amnr_energy_gradient_laplacian_commute hs]
  unfold AVenhance.spaceLap
  apply Finset.sum_congr rfl
  intro q _
  have he := amnrWord_spatial_slice_on_vertical_domain
    (isOpen_Ioi.prod isOpen_univ) (amnr_classical_gradient_smooth_infty hu i)
      B [q, q] z.1 (fun x => ⟨hz, mem_univ x⟩) z.2
  exact he.symm

end AVenhance.Infra.Section4
