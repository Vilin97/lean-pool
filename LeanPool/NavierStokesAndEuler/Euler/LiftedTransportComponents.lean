/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCylinder

/-! Exact coefficient functionals for the lifted Euler transport vector (κz,m·z). -/

@[expose] public section


noncomputable section

namespace EulerSobolevTransport

open InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport EulerVectorCylinder
  EulerCylinderSobolev EulerTransportDerivatives

/-- Coordinate functionals of the actual lifted transport vector, with the angle coordinate first.
-/
def velocityComponents (κ : ℝ) (m : Vector3) : Fin 4 → Vector3 →L[ℝ] ℝ :=
  Fin.cons (innerSL ℝ m) (fun i : Fin 3 => κ • coordinate 3 i)

/-- The scale-normalized lifted velocity coefficients have norm at most one. -/
theorem velocityComponents_norm (κ : ℝ) (m : Vector3) (hκ : |κ| ≤ 1) (hm : ‖m‖ ≤ 1) :
    ∀ i, ‖velocityComponents κ m i‖ ≤ 1 := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [velocityComponents, Fin.cons_zero, innerSL_apply_norm] using hm
  · simp only [velocityComponents, Fin.cons_succ, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hκ (coordinate_norm_le 3 j) (norm_nonneg _) (by
        norm_num)).trans_eq (one_mul 1)

/-- These functionals recover exactly the four-dimensional transport direction. -/
theorem velocityComponents_direction (κ : ℝ) (m z : Vector3) :
    ∑ i : Fin 4, velocityComponents κ m i z • standardDirection i = transportDirection κ m z := by
  rw [Fin.sum_univ_succ]
  simp only [velocityComponents, Fin.cons_zero, Fin.cons_succ, innerSL_apply_apply,
    smul_apply, smul_eq_mul]
  have hz : ∑ i : Fin 3, z i • EuclideanSpace.single i 1 = z := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr z
  apply Prod.ext
  · change (⟪m,z⟫_ℝ • standardDirection 0 + ∑ i : Fin 3, (κ * z i) • standardDirection i.succ).1 =
      κ • z
    simp only [standardDirection_zero, standardDirection_succ, Prod.fst_add, Prod.fst_sum]
    change ⟪m,z⟫_ℝ • (0 : Vector3) + (∑ i : Fin 3, (κ*z i) • EuclideanSpace.single i 1) = κ • z
    rw [smul_zero, zero_add]
    calc
      (∑ i : Fin 3, (κ*z i) • EuclideanSpace.single i 1) = κ • ∑ i : Fin 3, z i •
          EuclideanSpace.single i 1 := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_smul κ (z i) _
      _ = κ • z := by rw [hz]
  · change (⟪m,z⟫_ℝ • standardDirection 0 + ∑ i : Fin 3, (κ * z i) • standardDirection i.succ).2 =
      ⟪m,z⟫_ℝ
    rw [Prod.snd_add, Prod.snd_sum]
    simp only [standardDirection_zero, standardDirection_succ, Prod.smul_snd, smul_eq_mul, mul_one,
        mul_zero, Finset.sum_const_zero, add_zero]

end EulerSobolevTransport
