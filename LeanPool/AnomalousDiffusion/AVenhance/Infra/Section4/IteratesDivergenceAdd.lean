/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordFluxPairing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesForcingGradient

/-! # Iterates Divergence Add

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- Divergence is additive on the actual smooth vector carriers. -/
theorem iterate_vecDiv_add {A B : Vec 2 → Vec 2}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hB : ContDiff ℝ (⊤ : ℕ∞) B) (x : Vec 2) :
    vecDiv (fun y => A y + B y) x = vecDiv A x + vecDiv B x := by
  unfold vecDiv
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold spaceGrad
  dsimp only [Pi.add_apply]
  rw [fderiv_fun_add ((contDiff_pi.mp hA j).differentiable (by simp)).differentiableAt
    ((contDiff_pi.mp hB j).differentiable (by simp)).differentiableAt]
  rfl

/-- Divergence of a time-only matrix flux is its literal Hessian contraction. -/
theorem iterate_constant_matrix_divergence
    (A : Matrix (Fin 2) (Fin 2) ℝ) {u : Vec 2 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec 2) :
    vecDiv (fun y => A.mulVec (spaceGrad u y)) x =
      ∑ j : Fin 2, ∑ k : Fin 2, A j k * spaceGrad (fun y => spaceGrad u y k) x j := by
  have ht := iterate_matrix_forcing_formula (A := fun _ => A) contDiff_const hu x
  simpa only [spaceGrad, fderiv_fun_const, Pi.zero_apply, zero_apply, zero_mul, zero_add] using ht

end AVenhance.Infra.Section4
