/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevLaplacian

@[expose] public section

/-! Genuine gradient energy and maximal-regularity estimates for smooth Sobolev heat solutions. -/

noncomputable section

namespace EulerHeatGradientEnergy

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerSobolevLaplacian EulerSobolevHeatGenerator
  EulerLiftedWeakDerivative
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual sum of the four first-derivative L² energies. -/
def gradientEnergy (u : SobolevSpace period 1) : ℝ :=
  ∑ i : Fin 4, ‖value period (derivativeOperator period 0 i u)‖ ^ 2

/-- Gradient energy is nonnegative. -/
theorem gradientEnergy_nonneg (u : SobolevSpace period 1) : 0 ≤ gradientEnergy period u :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Gradient energy is a continuous function of the actual H¹ field. -/
theorem gradientEnergy_continuous : Continuous (gradientEnergy period) := by
  apply continuous_finsetSum
  intro i _
  exact (((valueOperator period 0).continuous.comp (derivativeOperator period 0
    i).continuous).norm).pow 2

/-- Genuine strong-derivative integration by parts identifies the full gradient pairing with the Laplacian. -/
theorem gradient_pairing (u : SobolevSpace period 2) (v : SobolevSpace period 1) :
    (∑ i : Fin 4, ⟪value period (derivativeOperator period 1 i u),
      value period (derivativeOperator period 0 i v)⟫_ℝ) =
      -⟪laplacianEvaluation period 2 (by norm_num) u, value period v⟫_ℝ := by
  have hi (i : Fin 4) : ⟪value period (derivativeOperator period 1 i u),
      value period (derivativeOperator period 0 i v)⟫_ℝ =
      -⟪value period (derivativeOperator period 0 i (derivativeOperator period 1 i u)), value
        period v⟫_ℝ := by
    have h := translation_derivative_pairing period (standardDirection i)
      (value period (derivativeOperator period 1 i u))
      (value period (derivativeOperator period 0 i (derivativeOperator period 1 i u)))
      (value period v) (value period (derivativeOperator period 0 i v))
      (derivativeOperator_hasDerivAt period i (derivativeOperator period 1 i u))
      (derivativeOperator_hasDerivAt period i v)
    linarith
  rw [← laplacianOperator_value period u, laplacianOperator_apply]
  change _ = -⟪(valueOperator period 0) (∑ i : Fin 4, _), value period v⟫_ℝ
  rw [map_sum, sum_inner]
  simp only [hi, Finset.sum_neg_distrib]
  rfl

/-- Actual L² time derivatives of the first spatial derivatives determine the gradient-energy derivative. -/
theorem gradient_energy_hasDerivAt (u : ℝ → SobolevSpace period 2) (v : SobolevSpace period 1) (t :
  ℝ)
    (hd : ∀ i : Fin 4, HasDerivAt (fun s => value period (derivativeOperator period 1 i (u s)))
      (value period (derivativeOperator period 0 i v)) t) :
    HasDerivAt (fun s => gradientEnergy period (truncateOperator period 1 (u s)))
      (-2 * ⟪laplacianEvaluation period 2 (by norm_num) (u t), value period v⟫_ℝ) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4)))
    => (hd i).norm_sq)
  have he : (∑ i : Fin 4, 2 * ⟪value period (derivativeOperator period 1 i (u t)),
      value period (derivativeOperator period 0 i v)⟫_ℝ) =
      -2 * ⟪laplacianEvaluation period 2 (by norm_num) (u t), value period v⟫_ℝ := by
    rw [← Finset.mul_sum, gradient_pairing]
    ring
  rw [he] at h
  exact h

omit [Fact (0 < period)] in
/-- The scalar Young bound with the exact viscosity scaling used by maximal regularity. -/
theorem viscosity_young (ν x y : ℝ) (hν : 0 < ν) : 2*x*y ≤ ν*x^2 + ν⁻¹*y^2 := by
  have h := div_nonneg (sq_nonneg (ν*x-y)) hν.le
  have he : (ν*x-y)^2 / ν = ν*x^2 - 2*x*y + ν⁻¹*y^2 := by
    field_simp
    ring
  rw [he] at h
  linarith

/-- The true heat gradient energy absorbs the source without differentiating the source in its bound. -/
theorem heat_gradient_energy_hasDerivAt (u : ℝ → SobolevSpace period 3)
    (f : SobolevSpace period 1) (ν t : ℝ)
    (hd : ∀ i : Fin 4, HasDerivAt (fun s => value period (derivativeOperator period 2 i (u s)))
      (value period (derivativeOperator period 0 i (ν • laplacianOperator period 1 (u t) + f))) t) :
    HasDerivAt (fun s => gradientEnergy period (restrictOperator period (by norm_num : 1 ≤ 3) (u
      s)))
      (-2 * ⟪laplacianEvaluation period 3 (by norm_num) (u t),
        ν • laplacianEvaluation period 3 (by norm_num) (u t) + value period f⟫_ℝ) t := by
  have h := gradient_energy_hasDerivAt period (fun s => truncateOperator period 2 (u s))
    (ν • laplacianOperator period 1 (u t) + f) t hd
  have he : laplacianEvaluation period 2 (by norm_num) (truncateOperator period 2 (u t)) =
      laplacianEvaluation period 3 (by norm_num) (u t) := by
    rw [laplacianEvaluation_apply, laplacianEvaluation_apply]
    rfl
  change HasDerivAt _ (-2 * ⟪laplacianEvaluation period 2 _ (truncateOperator period 2 (u t)),
    ν • value period (laplacianOperator period 1 (u t)) + value period f⟫_ℝ) t at h
  rw [he, laplacianOperator_value] at h
  exact h

/-- The actual derivative of gradient energy controls the full L² Laplacian with no source derivative loss. -/
theorem heat_gradient_energy_bound (u : ℝ → SobolevSpace period 3)
    (f : SobolevSpace period 1) (ν t : ℝ) (hν : 0 < ν)
    (hd : ∀ i : Fin 4, HasDerivAt (fun s => value period (derivativeOperator period 2 i (u s)))
      (value period (derivativeOperator period 0 i (ν • laplacianOperator period 1 (u t) + f))) t) :
    deriv (fun s => gradientEnergy period (restrictOperator period (by norm_num : 1 ≤ 3) (u s))) t ≤
      -ν * ‖laplacianEvaluation period 3 (by norm_num) (u t)‖^2 + ν⁻¹ * ‖value period f‖^2 := by
  rw [(heat_gradient_energy_hasDerivAt period u f ν t hd).deriv, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hb := norm_inner_le_norm (𝕜 := ℝ) (laplacianEvaluation period 3 (by norm_num) (u t)) (value
    period f)
  rw [Real.norm_eq_abs] at hb
  have hc := neg_le_abs ⟪laplacianEvaluation period 3 (by norm_num) (u t), value period f⟫_ℝ
  have hy := viscosity_young ν ‖laplacianEvaluation period 3 (by norm_num) (u t)‖ ‖value period f‖
    hν
  nlinarith


end EulerHeatGradientEnergy
