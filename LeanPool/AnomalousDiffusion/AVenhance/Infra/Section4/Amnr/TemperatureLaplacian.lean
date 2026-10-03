/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocitySpatial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.Seed

/-! The diffusion and forcing terms of the actual temperature equation. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Spatial diffusion in ordered coordinates, with its actual finite sum. -/
def amnrSpatialLap (f : AmnrSpace → ℝ) (z : AmnrSpace) : ℝ :=
  ∑ p : Fin 2, amnrWord (fun _ => (0 : Vec 2)) [some p, some p] f z

/-- The ordered spatial Laplacian equals the slice Laplacian for the
actual classical temperature, on the entire positive-time domain. -/
theorem amnr_classical_spatialLap {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ}
    (hu : AVenhance.IsClassicalSol b κ F θ₀ u) :
    Set.EqOn (amnrSpatialLap (fun z => u z.1 z.2))
      (fun z => AVenhance.spaceLap (u z.1) z.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hU := (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).prod
    (isOpen_univ : IsOpen (Set.univ : Set (Vec 2)))
  intro z hz
  unfold amnrSpatialLap AVenhance.spaceLap
  apply Finset.sum_congr rfl
  intro p _
  have he : Set.EqOn
      (amnrOp (fun _ => (0 : Vec 2)) (some p) (fun y => u y.1 y.2))
      (fun y => AVenhance.spaceGrad (u y.1) y.2 p) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
    intro y hy
    exact amnrOp_space
      (((amnr_classical_smooth hu).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)) p
  have hw := amnrWord_congr (b := fun _ => (0 : Vec 2)) hU he [some p] hz
  simp only [amnrWord] at hw ⊢
  rw [hw]
  exact amnrOp_space
    (((amnr_classical_gradient_smooth hu p 1).contDiffAt (hU.mem_nhds hz)).differentiableAt
      (by norm_num)) p

/-- Classical smoothness supplies every finite joint derivative of diffusion,
with exactly the two additional spatial derivatives required by the cascade. -/
theorem amnr_classical_spatialLap_contDiffOn {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ}
    (hu : AVenhance.IsClassicalSol b κ F θ₀ u) (N : ℕ) :
    ContDiffOn ℝ N (fun z : AmnrSpace => AVenhance.spaceLap (u z.1) z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hU := (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).prod
    (isOpen_univ : IsOpen (Set.univ : Set (Vec 2)))
  have hf := (amnr_classical_smooth hu).of_le
    (show (N + 2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)
  have hb : ContDiffOn ℝ (N + 2) (fun _ : AmnrSpace => (0 : Vec 2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := contDiffOn_const
  have hg : ContDiffOn ℝ N (amnrSpatialLap (fun z => u z.1 z.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
    apply ContDiffOn.sum
    intro p _
    exact amnrWord_contDiffOn hU hb hf [some p, some p] (n := N) (by simp)
  apply hg.congr
  intro z hz
  exact (amnr_classical_spatialLap hu hz).symm

/-- The forcing of a classical solution has every finite joint derivative
allowed by the velocity's smoothness. No regularity of the forcing
coefficient or the solution's material derivatives is assumed. -/
theorem amnr_classical_forcing_contDiffOn {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ}
    (hu : AVenhance.IsClassicalSol b κ F θ₀ u) (N : ℕ)
    (hb : ContDiffOn ℝ (N + 1) (fun z : AmnrSpace => b z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) :
    ContDiffOn ℝ N (fun z : AmnrSpace => F z.1 z.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hU := (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).prod
    (isOpen_univ : IsOpen (Set.univ : Set (Vec 2)))
  have hf := (amnr_classical_smooth hu).of_le
    (show (N + 1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)
  have hd := amnrWord_contDiffOn hU hb hf [none] (n := N) (by simp)
  have hl := amnr_classical_spatialLap_contDiffOn hu N
  have hh := hd.sub ((contDiffOn_const (c := κ)).mul hl)
  apply hh.congr
  intro z hz
  have he := amnr_classical_material hu hz.1
  simp only [amnrWord]
  linarith only [he]

end AVenhance.Infra.Section4
