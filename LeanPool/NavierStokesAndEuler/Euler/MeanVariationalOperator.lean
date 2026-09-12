/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseVariationalOperator
import Mathlib.Algebra.Order.Star.Real

/-!
# The mean displacement form with its initial boundary operator

The operator is constructed as `I - J* H J + R* C R`, where `J` is the
actual displacement primitive and `R` its initial trace.  The boundary lower
bound is required only on the trace image, as in the source's solenoidal space.
-/

@[expose] public section


noncomputable section

namespace EulerMeanVariationalOperator

open InnerProductSpace ContinuousLinearMap EulerCoerciveProjection
  EulerTransverseVariationalInverse

variable {V W X : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- The actual bounded operator representing kinetic, potential, and boundary terms. -/
def meanOperator (J : V →L[ℝ] W) (R : V →L[ℝ] X)
    (H : W →L[ℝ] W) (C : X →L[ℝ] X) : V →L[ℝ] V :=
  dirichletOperator J H + R.adjoint.comp (C.comp R)

/-- The constructed operator has exactly the intended bilinear form. -/
theorem meanOperator_inner (J : V →L[ℝ] W) (R : V →L[ℝ] X)
    (H : W →L[ℝ] W) (C : X →L[ℝ] X) (u v : V) :
    ⟪meanOperator J R H C u, v⟫_ℝ =
      ⟪u, v⟫_ℝ-⟪H (J u), J v⟫_ℝ+⟪C (R u), R v⟫_ℝ := by
  simp only [meanOperator, add_apply, inner_add_left, comp_apply,
    adjoint_inner_left, dirichletOperator_inner]

variable (J : V →L[ℝ] W) (R : V →L[ℝ] X)
  (H : W →L[ℝ] W) (C : X →L[ℝ] X)
  (P Q K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
  (hJ : ∀ u, ‖J u‖ ^ 2 ≤ P * ‖u‖ ^ 2)
  (hR : ∀ u, ‖R u‖ ^ 2 ≤ Q * ‖u‖ ^ 2)
  (hH : ∀ w, ⟪H w, w⟫_ℝ ≤ K * ‖w‖ ^ 2)
  (hC : ∀ u, -B * ‖R u‖ ^ 2 ≤ ⟪C (R u), R u⟫_ℝ)
  (hsmall : K * P + B * Q ≤ 1 / 2)

include hK hB hJ hR hH hC hsmall in
/-- The source's two time estimates and coefficient bounds prove coercivity. -/
theorem meanOperator_coercive (u : V) :
    (1/2 : ℝ)*‖u‖^2 ≤ ⟪meanOperator J R H C u, u⟫_ℝ := by
  rw [meanOperator_inner, real_inner_self_eq_norm_sq]
  have hj := mul_le_mul_of_nonneg_left (hJ u) hK
  have hr := mul_le_mul_of_nonneg_left (hR u) hB
  have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖u‖)
  nlinarith only [hH (J u), hC u, hj, hr, hs]

/-- The forcing-to-derivative map constructed from the coercive mean form. -/
def meanSolver : W →L[ℝ] V :=
  (coerciveInverse (meanOperator J R H C) (1/2) (by norm_num)
    (meanOperator_coercive J R H C P Q K B hK hB hJ hR hH hC hsmall)).comp (-J.adjoint)

/-- The actual weak equation follows from the constructed inverse. -/
theorem meanSolver_weak (f : W) (v : V) :
    let u := meanSolver J R H C P Q K B hK hB hJ hR hH hC hsmall f
    ⟪u, v⟫_ℝ-⟪H (J u), J v⟫_ℝ+⟪C (R u), R v⟫_ℝ = -⟪f, J v⟫_ℝ := by
  dsimp only
  rw [← meanOperator_inner]
  change ⟪meanOperator J R H C
    (coerciveInverse (meanOperator J R H C) (1/2) (by norm_num)
      (meanOperator_coercive J R H C P Q K B hK hB hJ hR hH hC hsmall) (-J.adjoint f)), v⟫_ℝ = _
  rw [operator_inverse_apply, inner_neg_left, adjoint_inner_left]

/-- Uniqueness holds in the same actual Hilbert displacement space. -/
theorem meanSolver_unique (f : W) (u : V)
    (hu : ∀ v, ⟪u, v⟫_ℝ - ⟪H (J u), J v⟫_ℝ + ⟪C (R u), R v⟫_ℝ = -⟪f, J v⟫_ℝ) :
    u = meanSolver J R H C P Q K B hK hB hJ hR hH hC hsmall f := by
  apply (coerciveEquiv (meanOperator J R H C) (1/2) (by norm_num)
    (meanOperator_coercive J R H C P Q K B hK hB hJ hR hH hC hsmall)).injective
  simp only [coerciveEquiv_apply]
  apply ext_inner_right ℝ
  intro v
  rw [meanOperator_inner, hu, meanOperator_inner,
    meanSolver_weak J R H C P Q K B hK hB hJ hR hH hC hsmall]

/-- The derivative bound is polynomial in the primitive norm. -/
theorem meanSolver_norm (f : W) :
    ‖meanSolver J R H C P Q K B hK hB hJ hR hH hC hsmall f‖ ≤ 2*‖J‖*‖f‖ := by
  have hi := coerciveInverse_apply_norm_le (meanOperator J R H C) (1/2) (by norm_num)
    (meanOperator_coercive J R H C P Q K B hK hB hJ hR hH hC hsmall) (-J.adjoint f)
  change ‖meanSolver J R H C P Q K B hK hB hJ hR hH hC hsmall f‖ ≤ _ at hi
  have ha := J.adjoint.le_opNorm f
  simp only [norm_neg, inv_div, div_one, LinearIsometryEquiv.norm_map] at hi ha
  calc
    _ ≤ 2*‖J.adjoint f‖ := hi
    _ ≤ 2*(‖J‖*‖f‖) := mul_le_mul_of_nonneg_left ha (by norm_num)
    _ = 2*‖J‖*‖f‖ := by ring

include hK hB hJ hR hH hC hsmall in
/-- Existence and uniqueness are conclusions, with no solution or inverse hypothesis. -/
theorem existsUnique_mean_solution (f : W) :
    ∃! u : V, ∀ v,
      ⟪u, v⟫_ℝ-⟪H (J u), J v⟫_ℝ+⟪C (R u), R v⟫_ℝ = -⟪f, J v⟫_ℝ :=
  ⟨meanSolver J R H C P Q K B hK hB hJ hR hH hC hsmall f,
    meanSolver_weak J R H C P Q K B hK hB hJ hR hH hC hsmall f,
    fun u hu => meanSolver_unique J R H C P Q K B hK hB hJ hR hH hC hsmall f u hu⟩

end EulerMeanVariationalOperator
