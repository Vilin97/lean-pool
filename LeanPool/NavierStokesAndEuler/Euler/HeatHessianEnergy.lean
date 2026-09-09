/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.HeatGradientEnergy

@[expose] public section

/-! Exact L² Hessian coercivity from actual commuting strong derivatives. -/

noncomputable section

namespace EulerHeatGradientEnergy

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSobolevLaplacian EulerSobolevHeatGenerator

variable (period : ℝ) [Fact (0 < period)]

/-- The actual sum of all sixteen second-coordinate L² energies. -/
def hessianEnergy (u : SobolevSpace period 2) : ℝ :=
  ∑ j : Fin 4, ∑ i : Fin 4, ‖value period (derivativeOperator period 0 i
    (derivativeOperator period 1 j u))‖^2

/-- One row of the genuine Hessian energy is the corresponding gradient-Laplacian pairing. -/
theorem hessian_row_identity (u : SobolevSpace period 3) (j : Fin 4) :
    (∑ i : Fin 4, ‖value period (derivativeOperator period 1 i (derivativeOperator period 2 j
      u))‖^2) =
      -⟪value period (derivativeOperator period 2 j u),
        value period (derivativeOperator period 0 j (laplacianOperator period 1 u))⟫_ℝ := by
  have h := gradient_pairing period (derivativeOperator period 2 j u)
    (truncateOperator period 1 (derivativeOperator period 2 j u))
  have he : laplacianEvaluation period 2 (by norm_num) (derivativeOperator period 2 j u) =
      value period (derivativeOperator period 0 j (laplacianOperator period 1 u)) := by
    rw [← laplacianOperator_value, laplacian_derivative]
  rw [he, value_truncateOperator] at h
  have h' := h.trans (congrArg Neg.neg (real_inner_comm (F := LiftL2 period)
      (value period (derivativeOperator period 2 j u))
      (value period (derivativeOperator period 0 j (laplacianOperator period 1 u)))))
  convert h' using 1
  apply Finset.sum_congr rfl
  intro i _
  exact (real_inner_self_eq_norm_sq (value period (derivativeOperator period 1 i
    (derivativeOperator period 2 j u)))).symm

/-- The sum of the genuine gradient-Laplacian pairings is minus the Laplacian norm squared. -/
theorem laplacian_gradient_pairing (u : SobolevSpace period 3) :
    (∑ j : Fin 4, ⟪value period (derivativeOperator period 2 j u),
      value period (derivativeOperator period 0 j (laplacianOperator period 1 u))⟫_ℝ) =
      -‖laplacianEvaluation period 3 (by norm_num) u‖^2 := by
  have hp := gradient_pairing period (truncateOperator period 2 u) (laplacianOperator period 1 u)
  have he : laplacianEvaluation period 2 (by norm_num) (truncateOperator period 2 u) =
      laplacianEvaluation period 3 (by norm_num) u := by
    rw [laplacianEvaluation_apply, laplacianEvaluation_apply]
    rfl
  rw [he, laplacianOperator_value, real_inner_self_eq_norm_sq] at hp
  exact hp

/-- All genuine second-coordinate derivatives are controlled exactly by the Laplacian. -/
theorem hessianEnergy_eq_laplacian (u : SobolevSpace period 3) :
    hessianEnergy period (truncateOperator period 2 u) =
      ‖laplacianEvaluation period 3 (by norm_num) u‖^2 := by
  calc
    _ = ∑ j : Fin 4, -⟪value period (derivativeOperator period 2 j u),
        value period (derivativeOperator period 0 j (laplacianOperator period 1 u))⟫_ℝ :=
      Finset.sum_congr rfl (fun j _ => hessian_row_identity period u j)
    _ = -(∑ j : Fin 4, ⟪value period (derivativeOperator period 2 j u),
        value period (derivativeOperator period 0 j (laplacianOperator period 1 u))⟫_ℝ) :=
      Finset.sum_neg_distrib _
    _ = _ := by rw [laplacian_gradient_pairing, neg_neg]

end EulerHeatGradientEnergy
