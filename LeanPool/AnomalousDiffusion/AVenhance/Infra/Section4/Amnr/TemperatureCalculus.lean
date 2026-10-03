/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.Rates
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsTIterates

/-! The actual classical temperature equation in the ordered mixed calculus. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Filter
open scoped Topology
namespace AVenhance.Infra.Section4

/-- Smoothness on the open positive-time domain follows from the classical-solution definition,
    including every finite derivative order. -/
theorem amnr_classical_smooth {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ}
    (hu : AVenhance.IsClassicalSol b κ F θ₀ u) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => u z.1 z.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
  hu.1.mono (Set.prod_mono (fun _ ht => (show (0 : ℝ) < _ from ht).le) Set.Subset.rfl)

/-- The PDE gives the material derivative itself, without a material
regularity assumption on the temperature. -/
theorem amnr_classical_material {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ}
    (hu : AVenhance.IsClassicalSol b κ F θ₀ u) {z : AmnrSpace} (ht : 0 < z.1) :
    amnrOp (fun y => b y.1 y.2) none (fun y => u y.1 y.2) z =
      κ * AVenhance.spaceLap (u z.1) z.2 + F z.1 z.2 := by
  have hc := hu.1.contDiffAt
    (prod_mem_nhds (Ici_mem_nhds ht) (Filter.univ_mem : Set.univ ∈ nhds z.2))
  rw [amnrOp_material (hc.differentiableAt (by simp))]
  have he := hu.2.2.2 z.1 ht z.2
  unfold AVenhance.advDiffOp at he
  unfold amnrMaterial
  dsimp only
  linarith only [he]

/-- Actual temperature gradients have every finite order of joint regularity;
this is proved from classical smoothness rather than supplied to the AMNR seed. -/
theorem amnr_classical_gradient_smooth {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ}
    (hu : AVenhance.IsClassicalSol b κ F θ₀ u) (p : Fin 2) (N : ℕ) :
    ContDiffOn ℝ N (fun z : AmnrSpace => AVenhance.spaceGrad (u z.1) z.2 p)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hU := (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).prod (isOpen_univ : IsOpen (Set.univ : Set
      (Vec 2)))
  have hf := (amnr_classical_smooth hu).of_le
    (show (N + 1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)
  have hb : ContDiffOn ℝ (N + 1) (fun _ : AmnrSpace => (0 : Vec 2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := contDiffOn_const
  have hg := amnrWord_contDiffOn hU hb hf [some p]
    (n := N) (by simp)
  apply hg.congr
  intro z hz
  have hd := ((amnr_classical_smooth hu).contDiffAt (hU.mem_nhds hz)).differentiableAt
    (by simp)
  exact (amnrOp_space (b := fun _ => (0 : Vec 2)) hd p).symm

/-- Differentiating the actual PDE gives the source gradient equation. The
velocity contraction has the transpose indices required by e.Tm-1:i:evo. -/
theorem amnr_classical_gradient_evolution {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ}
    (hu : AVenhance.IsClassicalSol b κ F θ₀ u) {z : AmnrSpace} (ht : 0 < z.1)
    (hb : DifferentiableAt ℝ (fun y : AmnrSpace => b y.1 y.2) z) (i : Fin 2) :
    amnrOp (fun y => b y.1 y.2) none
      (amnrOp (fun y => b y.1 y.2) (some i) (fun y => u y.1 y.2)) z =
      amnrOp (fun y => b y.1 y.2) (some i)
        (fun y => κ * AVenhance.spaceLap (u y.1) y.2 + F y.1 y.2) z -
      ∑ p : Fin 2, amnrVelocityGradient (fun y => b y.1 y.2) p i z *
        amnrOp (fun y => b y.1 y.2) (some p) (fun y => u y.1 y.2) z := by
  have hc := hu.1.contDiffAt
    (prod_mem_nhds (Ici_mem_nhds ht) (Filter.univ_mem : Set.univ ∈ nhds z.2))
  rw [amnr_material_spatial_commutator hb (hc.of_le (by simp)) i]
  have he : Set.EqOn
      (amnrOp (fun y => b y.1 y.2) none (fun y => u y.1 y.2))
      (fun y => κ * AVenhance.spaceLap (u y.1) y.2 + F y.1 y.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
    intro y hy
    exact amnr_classical_material hu hy.1
  have hw := amnrWord_congr (b := fun y => b y.1 y.2)
    (isOpen_Ioi.prod isOpen_univ) he [some i] ⟨ht, Set.mem_univ _⟩
  simp only [amnrWord] at hw
  rw [hw]

end AVenhance.Infra.Section4
