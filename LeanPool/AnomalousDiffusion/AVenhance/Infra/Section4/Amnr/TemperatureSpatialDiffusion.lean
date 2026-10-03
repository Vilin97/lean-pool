/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CanonicalEnvelopeL2

/-! Spatial diffusion calculus below the public AMNR facade. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

theorem amnr_energy_gradient_smooth {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceGrad f) := by
  have hjoint : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Vec 2 × Vec 2 => fderiv ℝ f p.1 p.2) :=
    hf.contDiff_fderiv_apply (by simp)
  apply contDiff_pi.2
  intro i
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (x, basisVec i)) := by
    fun_prop
  have hcomp := hjoint.comp hmap
  simpa only [Function.comp_def, Prod.fst, Prod.snd, AVenhance.spaceGrad] using hcomp

theorem amnr_energy_coordinate_derivatives_commute {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y i) x j =
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y j) x i := by
  have hAt := hf.contDiffAt (x := x)
  have hC2 : ContDiffAt ℝ 2 f x := hAt.of_le (by norm_num)
  have hsymm := hC2.isSymmSndFDerivAt (by simp)
  have hc : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have hCderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hAt.fderiv_right (m := 1) (by simp)
    exact hCderiv.differentiableAt (by norm_num)
  have hu0 : DifferentiableAt ℝ (fun _ : Vec 2 => basisVec i) x :=
    differentiableAt_const (basisVec i)
  have hu1 : DifferentiableAt ℝ (fun _ : Vec 2 => basisVec j) x :=
    differentiableAt_const (basisVec j)
  have hderiv0 : fderiv ℝ (fun y => fderiv ℝ f y (basisVec i)) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (basisVec i) := by
    have h := fderiv_clm_apply hc hu0
    simpa using h
  have hderiv1 : fderiv ℝ (fun y => fderiv ℝ f y (basisVec j)) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (basisVec j) := by
    have h := fderiv_clm_apply hc hu1
    simpa using h
  have hleft : AVenhance.spaceGrad
      (fun y => AVenhance.spaceGrad f y i) x j =
      fderiv ℝ (fderiv ℝ f) x (basisVec j) (basisVec i) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (basisVec i)) x (basisVec j) = _
    rw [hderiv0]
    rfl
  have hright : AVenhance.spaceGrad
      (fun y => AVenhance.spaceGrad f y j) x i =
      fderiv ℝ (fderiv ℝ f) x (basisVec i) (basisVec j) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (basisVec j)) x (basisVec i) = _
    rw [hderiv1]
    rfl
  rw [hleft, hright]
  exact hsymm (basisVec j) (basisVec i)

/-- The gradient of the Laplacian is the componentwise Laplacian of the
gradient. This justifies moving current diffusion derivatives to the preceding
increment in the oscillatory material pairing. -/
theorem amnr_energy_gradient_laplacian_commute {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) (i : Fin 2) :
    spaceGrad (spaceLap f) x i = spaceLap (fun y => spaceGrad f y i) x := by
  have hg (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun y => spaceGrad f y j) :=
    contDiff_pi.mp (amnr_energy_gradient_smooth hf) j
  have hgg (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => spaceGrad (fun z => spaceGrad f z j) y j) :=
    contDiff_pi.mp (amnr_energy_gradient_smooth (hg j)) j
  change fderiv ℝ (fun y => ∑ j : Fin 2,
    spaceGrad (fun z => spaceGrad f z j) y j) x (basisVec i) = _
  rw [fderiv_fun_sum (fun j _ => (hgg j).differentiable (by simp) |>.differentiableAt)]
  simp only [sum_apply]
  unfold spaceLap
  apply Finset.sum_congr rfl
  intro j _
  change spaceGrad (fun y => spaceGrad (fun z => spaceGrad f z j) y j) x i = _
  rw [amnr_energy_coordinate_derivatives_commute (hg j) j i x]
  have hswap : (fun y => spaceGrad (fun z => spaceGrad f z j) y i) =
      (fun y => spaceGrad (fun z => spaceGrad f z i) y j) := by
    funext y
    exact amnr_energy_coordinate_derivatives_commute hf j i y
  rw [hswap]

theorem amnr_energy_laplacian_smooth {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (spaceLap f) := by
  apply ContDiff.sum
  intro j _
  exact contDiff_pi.mp (amnr_energy_gradient_smooth
    (contDiff_pi.mp (amnr_energy_gradient_smooth hf) j)) j

end AVenhance.Infra.Section4
