/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Joint regularity of a spatial derivative

This file records the elementary fixed-coordinate consequence of joint
time--space smoothness: differentiating a scalar field in its spatial
variable loses one order while preserving joint regularity in the time and
space variables.
-/

@[expose] public noncomputable section

open Filter Set

namespace PoincareCurvature

/-- A joint `C^(n+1)` scalar field has a jointly `C^n` spatial derivative,
evaluated on a `C^n` spatial vector field.  The derivative is taken within an
ambient set `r`; it agrees with the ordinary spatial derivative on the open
set `s ⊆ r`. -/
theorem contDiffOn_spatialFDerivWithin_apply_of_joint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {F : ℝ × E → ℝ} {V : E → E}
    {r s : Set E} (hs : IsOpen s) (hsr : s ⊆ r)
    (hF : ContDiffOn ℝ (n + 1) F (Set.univ ×ˢ s))
    (hV : ContDiffOn ℝ n V s) :
    ContDiffOn ℝ n
      (fun p : ℝ × E ↦
        fderivWithin ℝ (fun z : E ↦ F (p.1, z)) r p.2 (V p.2))
      (Set.univ ×ˢ s) := by
  have hprod : IsOpen ((Set.univ : Set ℝ) ×ˢ s) := isOpen_univ.prod hs
  have hderiv : ContDiffOn ℝ n (fderiv ℝ F) (Set.univ ×ˢ s) :=
    hF.fderiv_of_isOpen hprod (by simp)
  have hVprod : ContDiffOn ℝ n (fun p : ℝ × E ↦ ((0 : ℝ), V p.2))
      (Set.univ ×ˢ s) := by
    exact contDiffOn_const.prodMk
      (hV.comp contDiffOn_snd (fun p hp ↦ hp.2))
  refine (hderiv.clm_apply hVprod).congr ?_
  intro p hp
  have hr : r ∈ nhds p.2 :=
    mem_of_superset (hs.mem_nhds hp.2) hsr
  rw [fderivWithin_of_mem_nhds hr]
  have hFat : ContDiffAt ℝ (n + 1) F p :=
    (hF p hp).contDiffAt (hprod.mem_nhds hp)
  have hFdiff : DifferentiableAt ℝ F p :=
    hFat.differentiableAt (by simp)
  have hcomp := HasFDerivAt.comp p.2 hFdiff.hasFDerivAt
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
  have hslice :
      fderiv ℝ (fun z : E ↦ F (p.1, z)) p.2 =
        (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    simpa [Function.comp_def] using hcomp.fderiv
  rw [hslice]
  simp [ContinuousLinearMap.comp_apply]

end PoincareCurvature
