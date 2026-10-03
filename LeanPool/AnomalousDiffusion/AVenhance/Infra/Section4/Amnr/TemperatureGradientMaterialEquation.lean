/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureGradientDiffusion

/-! The actual material gradient equation with all primitive fields identified. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- The classical PDE gives the actual gradient material equation. Neither
its material derivative nor a differentiated PDE is assumed. -/
theorem amnr_classical_gradient_material_equation
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {F u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ}
    (hu : AVenhance.IsClassicalSol b κ F u₀ u)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : AmnrSpace => b z.1 z.2))
    (i : Fin 2) {z : AmnrSpace} (hz : 0 < z.1) :
    amnrOp (fun y => b y.1 y.2) none (amnrTGradient u i) z =
      κ * (∑ q : Fin 2, amnrWord (fun y => b y.1 y.2) [some q, some q] (amnrTGradient u i) z) +
      AVenhance.spaceGrad (F z.1) z.2 i -
      ∑ p : Fin 2, amnrVelocityGradient (fun y => b y.1 y.2) p i z * amnrTGradient u p z := by
  let U : Set AmnrSpace := Ioi (0 : ℝ) ×ˢ univ
  let B : AmnrSpace → Vec 2 := fun y => b y.1 y.2
  have hU : IsOpen U := isOpen_Ioi.prod isOpen_univ
  have hzu : z ∈ U := ⟨hz, mem_univ z.2⟩
  have hgu (p : Fin 2) : EqOn (amnrOp B (some p) (fun y => u y.1 y.2)) (amnrTGradient u p) U := by
    intro y hy
    exact amnrOp_space (((amnr_classical_smooth hu).contDiffAt (hU.mem_nhds hy)).differentiableAt
      (by simp)) p
  have he := amnr_classical_gradient_evolution hu hz (hb.differentiable (by simp) z) i
  have hword := amnrWord_congr (b := B) hU (hgu i) [none] hzu
  simp only [amnrWord] at hword
  rw [hword] at he
  have hLap := amnr_classical_spatialLap_contDiffOn hu 1
  have hF := amnr_classical_forcing_contDiffOn hu 1 ((hb.of_le (by simp)).contDiffOn)
  have hd := (((contDiffOn_const (c := κ)).mul hLap).add hF).contDiffAt (hU.mem_nhds hzu)
  rw [amnrOp_space (hd.differentiableAt (by norm_num)) i] at he
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (z.1, x)) := by fun_prop
  have hus : ContDiff ℝ (⊤ : ℕ∞) (u z.1) :=
    hu.1.comp_contDiff hmap (fun x => ⟨hz.le, mem_univ x⟩)
  have hFs : ContDiff ℝ 1 (F z.1) :=
    hF.comp_contDiff (hmap.of_le (by simp)) (fun x => ⟨hz, mem_univ x⟩)
  have hlapD := (amnr_energy_laplacian_smooth hus).differentiable (by simp) z.2
  have hFD := hFs.differentiable (by norm_num) z.2
  have hlinear : AVenhance.spaceGrad (fun y => κ * AVenhance.spaceLap (u z.1) y + F z.1 y) z.2 i =
      κ * AVenhance.spaceGrad (AVenhance.spaceLap (u z.1)) z.2 i +
        AVenhance.spaceGrad (F z.1) z.2 i := by
    unfold AVenhance.spaceGrad
    rw [fderiv_fun_add (hlapD.const_mul κ) hFD, fderiv_const_mul hlapD κ]
    rfl
  rw [hlinear, amnr_classical_gradient_diffusion hu B i hz] at he
  have hsum : (∑ p : Fin 2, amnrVelocityGradient B p i z *
      amnrOp B (some p) (fun y => u y.1 y.2) z) =
      ∑ p : Fin 2, amnrVelocityGradient B p i z * amnrTGradient u p z := by
    apply Finset.sum_congr rfl
    intro p _
    rw [hgu p hzu]
  rw [hsum] at he
  exact he

end AVenhance.Infra.Section4
