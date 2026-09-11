/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMultiplier
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CoerciveProjection
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.Star.Real

/-!
# The constructed Hilbert operator for the transverse displacement form

The time primitive will be substituted for `J` in `TransverseVariationalInverse`.
This file constructs, rather than assumes, the inverse of the actual operator
`I - J* H J`.  Its coercivity follows from the potential upper bound and the
primitive estimate.  No inverse, solution, or weak equation is an input.
-/

@[expose] public section


noncomputable section

namespace EulerTransverseVariationalInverse

open InnerProductSpace ContinuousLinearMap EulerCoerciveProjection

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- The operator representing the kinetic form minus the actual potential form. -/
def dirichletOperator (J : V →L[ℝ] W) (H : W →L[ℝ] W) : V →L[ℝ] V :=
  ContinuousLinearMap.id ℝ V - J.adjoint.comp (H.comp J)

/-- This is precisely the displacement variational form. -/
theorem dirichletOperator_inner (J : V →L[ℝ] W) (H : W →L[ℝ] W) (u v : V) :
    ⟪dirichletOperator J H u, v⟫_ℝ = ⟪u, v⟫_ℝ - ⟪H (J u), J v⟫_ℝ := by
  simp only [dirichletOperator, sub_apply, id_apply, comp_apply,
    inner_sub_left, adjoint_inner_left]

/-- The primitive estimate and the one-sided potential bound prove coercivity. -/
theorem dirichletOperator_coercive (J : V →L[ℝ] W) (H : W →L[ℝ] W)
    (L K : ℝ) (hK : 0 ≤ K)
    (hJ : ∀ u, ‖J u‖ ^ 2 ≤ L * ‖u‖ ^ 2)
    (hH : ∀ w, ⟪H w, w⟫_ℝ ≤ K * ‖w‖ ^ 2)
    (hsmall : K * L ≤ 1 / 2) (u : V) :
    (1 / 2 : ℝ) * ‖u‖ ^ 2 ≤ ⟪dirichletOperator J H u, u⟫_ℝ := by
  rw [dirichletOperator_inner, real_inner_self_eq_norm_sq]
  have hj := mul_le_mul_of_nonneg_left (hJ u) hK
  have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖u‖)
  nlinarith only [hH (J u), hj, hs]

/-- The actual forcing-to-derivative solution map constructed by Lax--Milgram. -/
def dirichletSolver (J : V →L[ℝ] W) (H : W →L[ℝ] W)
    (L K : ℝ) (hK : 0 ≤ K)
    (hJ : ∀ u, ‖J u‖ ^ 2 ≤ L * ‖u‖ ^ 2)
    (hH : ∀ w, ⟪H w, w⟫_ℝ ≤ K * ‖w‖ ^ 2)
    (hsmall : K * L ≤ 1 / 2) : W →L[ℝ] V :=
  (coerciveInverse (dirichletOperator J H) (1 / 2) (by norm_num)
    (dirichletOperator_coercive J H L K hK hJ hH hsmall)).comp (-J.adjoint)

/-- The constructed solution obeys the actual weak displacement equation. -/
theorem dirichletSolver_weak (J : V →L[ℝ] W) (H : W →L[ℝ] W)
    (L K : ℝ) (hK : 0 ≤ K)
    (hJ : ∀ u, ‖J u‖ ^ 2 ≤ L * ‖u‖ ^ 2)
    (hH : ∀ w, ⟪H w, w⟫_ℝ ≤ K * ‖w‖ ^ 2)
    (hsmall : K * L ≤ 1 / 2) (f : W) (v : V) :
    let u := dirichletSolver J H L K hK hJ hH hsmall f
    ⟪u, v⟫_ℝ - ⟪H (J u), J v⟫_ℝ = -⟪f, J v⟫_ℝ := by
  dsimp only
  rw [← dirichletOperator_inner]
  change ⟪dirichletOperator J H
    (coerciveInverse (dirichletOperator J H) (1 / 2) (by norm_num)
      (dirichletOperator_coercive J H L K hK hJ hH hsmall) (-J.adjoint f)), v⟫_ℝ = _
  rw [operator_inverse_apply, inner_neg_left, adjoint_inner_left]

/-- No other derivative in the same Hilbert displacement space solves this form. -/
theorem dirichletSolver_unique (J : V →L[ℝ] W) (H : W →L[ℝ] W)
    (L K : ℝ) (hK : 0 ≤ K)
    (hJ : ∀ u, ‖J u‖ ^ 2 ≤ L * ‖u‖ ^ 2)
    (hH : ∀ w, ⟪H w, w⟫_ℝ ≤ K * ‖w‖ ^ 2)
    (hsmall : K * L ≤ 1 / 2) (f : W) (u : V)
    (hu : ∀ v, ⟪u, v⟫_ℝ - ⟪H (J u), J v⟫_ℝ = -⟪f, J v⟫_ℝ) :
    u = dirichletSolver J H L K hK hJ hH hsmall f := by
  apply (coerciveEquiv (dirichletOperator J H) (1 / 2) (by norm_num)
    (dirichletOperator_coercive J H L K hK hJ hH hsmall)).injective
  simp only [coerciveEquiv_apply]
  apply ext_inner_right ℝ
  intro v
  rw [dirichletOperator_inner, hu, dirichletOperator_inner,
    dirichletSolver_weak]

/-- Quantitative boundedness of the genuinely constructed solution map. -/
theorem dirichletSolver_norm (J : V →L[ℝ] W) (H : W →L[ℝ] W)
    (L K : ℝ) (hK : 0 ≤ K)
    (hJ : ∀ u, ‖J u‖ ^ 2 ≤ L * ‖u‖ ^ 2)
    (hH : ∀ w, ⟪H w, w⟫_ℝ ≤ K * ‖w‖ ^ 2)
    (hsmall : K * L ≤ 1 / 2) (f : W) :
    ‖dirichletSolver J H L K hK hJ hH hsmall f‖ ≤ 2 * ‖J‖ * ‖f‖ := by
  have hi := coerciveInverse_apply_norm_le (dirichletOperator J H) (1 / 2)
    (by norm_num) (dirichletOperator_coercive J H L K hK hJ hH hsmall)
    (-J.adjoint f)
  change ‖dirichletSolver J H L K hK hJ hH hsmall f‖ ≤ _ at hi
  have ha := J.adjoint.le_opNorm f
  simp only [norm_neg, inv_div, div_one, LinearIsometryEquiv.norm_map] at hi ha
  calc
    ‖dirichletSolver J H L K hK hJ hH hsmall f‖ ≤ 2 * ‖J.adjoint f‖ := hi
    _ ≤ 2 * (‖J‖ * ‖f‖) := mul_le_mul_of_nonneg_left ha (by norm_num)
    _ = 2 * ‖J‖ * ‖f‖ := by ring

/-- Existence and uniqueness, as conclusions from coefficient and primitive bounds. -/
theorem existsUnique_dirichlet_solution (J : V →L[ℝ] W) (H : W →L[ℝ] W)
    (L K : ℝ) (hK : 0 ≤ K)
    (hJ : ∀ u, ‖J u‖ ^ 2 ≤ L * ‖u‖ ^ 2)
    (hH : ∀ w, ⟪H w, w⟫_ℝ ≤ K * ‖w‖ ^ 2)
    (hsmall : K * L ≤ 1 / 2) (f : W) :
    ∃! u : V, ∀ v, ⟪u, v⟫_ℝ - ⟪H (J u), J v⟫_ℝ = -⟪f, J v⟫_ℝ := by
  exact ⟨dirichletSolver J H L K hK hJ hH hsmall f,
    dirichletSolver_weak J H L K hK hJ hH hsmall f,
    fun u hu => dirichletSolver_unique J H L K hK hJ hH hsmall f u hu⟩

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution

omit [CompleteSpace W] in
/-- A pointwise upper bound on the given time-dependent Hessian gives the actual
Bochner-space quadratic-form upper bound. -/
theorem timeMultiplier_quadratic_upper (T : ℝ) (hT : 0 ≤ T)
    (H : C(Icc (0 : ℝ) T, W →L[ℝ] W)) (K : ℝ)
    (hH : ∀ t w, ⟪H t w, w⟫_ℝ ≤ K * ‖w‖ ^ 2) (u : TimeLp T W) :
    ⟪timeMultiplier T hT H u, u⟫_ℝ ≤ K * ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_mono_ae (L2.integrable_inner (timeMultiplier T hT H u) u)
    ((L2.integrable_inner u u).const_mul K)
  filter_upwards [timeMultiplier_ae T hT H u] with t ht
  rw [ht, real_inner_self_eq_norm_sq]
  exact hH (projIcc 0 T hT t) (u t)

end EulerTransverseVariationalInverse
