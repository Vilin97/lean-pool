/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MatrixFluxProduct
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.PulledGradientTransport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.MovingFluxEnergy

/-! The divergence remainder as a weighted gradient contraction. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance Homogenization

theorem ResidualR46.frob_add_right (A B C : Matrix (Fin 2) (Fin 2) ℝ) :
    frob A (B + C) = frob A B + frob A C := by
  simp [frob, Matrix.add_apply, Finset.sum_add_distrib, mul_add]

theorem ResidualR46.frob_smul_right (A B : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) :
    frob A (c • B) = c * frob A B := by
  simp only [frob, Matrix.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem ResidualR46.frob_finite_weighted_sum {ι : Type*} (S : Finset ι)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (c : ι → ℝ)
    (B : ι → Matrix (Fin 2) (Fin 2) ℝ) :
    frob A (∑ k ∈ S, c k • B k) =
      ∑ k ∈ S, c k * frob A (B k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [frob]
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha, ResidualR46.frob_add_right, ResidualR46.frob_smul_right, ih,
        Finset.sum_insert ha]

end AVenhance.Infra.Section5

end
