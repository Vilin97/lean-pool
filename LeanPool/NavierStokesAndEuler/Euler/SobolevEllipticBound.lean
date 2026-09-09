/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.HeatHessianEnergy
public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction
import Mathlib.Algebra.Order.Star.Real

/-! A genuine H² bound by H¹ and the cylinder Laplacian, used in strong maximal-regularity limits.
-/

@[expose] public section


noncomputable section

namespace EulerSobolevEllipticBound

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeatGenerator
    EulerHeatGradientEnergy

variable (period : ℝ) [Fact (0 < period)]

/-- Every actual second derivative word is bounded by the full genuine Hessian energy. -/
theorem second_word_sq_le_hessian (u : SobolevSpace period 2) (w : Fin 2 → Fin 4) :
    ‖word period u (le_refl 2) w‖^2 ≤ hessianEnergy period u := by
  have hw : Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → Fin 4) (w 0)) (w 1) = w := by
    funext i
    fin_cases i <;> rfl
  have he : word period u (le_refl 2) w =
      value period (derivativeOperator period 0 (w 0) (derivativeOperator period 1 (w 1) u)) := by
    change u.val ⟨⟨2, _⟩, w⟩ = u.val ⟨⟨2, _⟩, Fin.snoc (Fin.snoc Fin.elim0 (w 0)) (w 1)⟩
    rw [hw]
  rw [he]
  exact (Finset.single_le_sum (fun i _ => sq_nonneg
    ‖value period (derivativeOperator period 0 i (derivativeOperator period 1 (w 1) u))‖)
    (Finset.mem_univ (w 0))).trans
    (Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun i _ => sq_nonneg
      ‖value period (derivativeOperator period 0 i (derivativeOperator period 1 j u))‖))
      (Finset.mem_univ (w 1)))

/-- The complete H² norm is controlled by its H¹ restriction and the actual Hessian energy. -/
theorem H2_norm_sq_le (u : SobolevSpace period 2) :
    ‖u‖^2 ≤ ‖truncateOperator period 1 u‖^2 + hessianEnergy period u := by
  have hh : 0 ≤ hessianEnergy period u := Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hB : 0 ≤ ‖truncateOperator period 1 u‖^2 + hessianEnergy period u :=
    add_nonneg (sq_nonneg _) hh
  apply (Real.le_sqrt (norm_nonneg u) hB).mp
  change ‖u.val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  rintro ⟨⟨n, hn⟩, w⟩
  apply Real.le_sqrt_of_sq_le
  by_cases hlow : n ≤ 1
  · have hnorm : ‖u.val ⟨⟨n, hn⟩, w⟩‖ ≤ ‖truncateOperator period 1 u‖ :=
      word_norm_le period (truncateOperator period 1 u) ⟨⟨n, Nat.lt_succ_of_le hlow⟩, w⟩
    nlinarith [norm_nonneg (u.val ⟨⟨n, hn⟩, w⟩), norm_nonneg (truncateOperator period 1 u)]
  · have hn2 : n = 2 := by omega
    subst n
    exact (second_word_sq_le_hessian period u w).trans (le_add_of_nonneg_left (sq_nonneg _))

/-- The actual finite Sobolev elliptic estimate has no Fourier or inverse-operator assumption. -/
theorem H2_norm_sq_le_laplacian (u : SobolevSpace period 3) :
    ‖truncateOperator period 2 u‖^2 ≤ ‖restrictOperator period (by norm_num : 1 ≤ 3) u‖^2 +
      ‖laplacianEvaluation period 3 (by norm_num) u‖^2 := by
  have h := H2_norm_sq_le period (truncateOperator period 2 u)
  rw [hessianEnergy_eq_laplacian] at h
  exact h

end EulerSobolevEllipticBound
