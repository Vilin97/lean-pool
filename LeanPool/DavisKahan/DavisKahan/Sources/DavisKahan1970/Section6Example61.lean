/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.TwoDimensionalSingularValues

/-!
# Davis--Kahan 1970, Example 6.1

The example immediately before the generalized tangent theorem, and like Examples
4.1 and 4.2 it is a counterexample rather than exposition: it shows that the
one-sided placement of `Lambda_1` in Theorem 6.3 cannot be dropped.

Theorem 6.3 concludes `delta * ‖tan Theta_0‖ <= ‖R‖` under two spectral
hypotheses, `spec(A_0) ⊆ [beta, alpha]` and `spec(Lambda_1) ⊆ [alpha + delta, ∞)`.
The source exhibits a finite matrix with `delta = 1` and tangent quantity `1` while
the residual is only `1 / sqrt 2`, when spectral mass is allowed on the wrong side
of `alpha`.  Since `1 * 1 > 1 / sqrt 2`, the conclusion fails, so the second
hypothesis is doing real work.

The witness is two-dimensional.  Take the symmetric `T` swapping the two
coordinate directions with weight `c = 1 / sqrt 2`, and take the first coordinate
vector `u` as the trial vector, so that the trial space is `span {u}`:

* the Rayleigh quotient `A_0 = ⟪T u, u⟫` is `0`, so `spec(A_0) = {0}` and
  `alpha = 0`;
* the residual `R = T u - A_0 u` is `c v`, of norm `1 / sqrt 2`;
* `T` has eigenvalues `± c`, with unit eigenvectors `(u ± v) / sqrt 2` sitting at
  `pi / 4` to the trial vector, so the tangent quantity is `1`;
* with `delta = 1` the second hypothesis would demand `spec(Lambda_1) ⊆ [1, ∞)`,
  and both eigenvalues `± 1 / sqrt 2` lie below `1` -- spectral mass on the wrong
  side, which is exactly what the source allows here and forbids in the theorem.

The tangent quantity is recorded as the equality of the trial and orthogonal
components of the eigenvector rather than through an arctangent: they are both
`1 / sqrt 2`, so the ratio defining `tan Theta_0` is `1`.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970
namespace Section6Example61

open scoped InnerProductSpace BigOperators

noncomputable section

/-- The two-dimensional real model space of Example 6.1. -/
abbrev RealPlane := EuclideanSpace ℝ (Fin 2)

/-- The example's weight, `1 / sqrt 2`. -/
noncomputable def c : ℝ := (Real.sqrt 2)⁻¹

/-- The trial vector: the first coordinate direction. -/
noncomputable def u : RealPlane := EuclideanSpace.basisFun (Fin 2) ℝ 0

/-- The orthogonal direction. -/
noncomputable def v : RealPlane := EuclideanSpace.basisFun (Fin 2) ℝ 1

/-- The example's operator: the weighted coordinate swap, which is symmetric. -/
noncomputable def T : RealPlane →ₗ[ℝ] RealPlane :=
  Matrix.toEuclideanLin (!![0, c; c, 0] : Matrix (Fin 2) (Fin 2) ℝ)

private theorem entry (M : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    (Matrix.toEuclideanLin M) (EuclideanSpace.basisFun (Fin 2) ℝ i) j = M j i := by
  simp [Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply, Matrix.mulVec_single]

private theorem real_inner (x y : RealPlane) : ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

private theorem real_norm_sq (x : RealPlane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- The example's weight is positive. -/
theorem c_pos : 0 < c := by
  rw [c]; positivity

/-- The trial vector is a unit vector. -/
theorem norm_u : ‖u‖ = 1 := by
  have : ‖u‖ ^ 2 = 1 := by
    rw [real_norm_sq]; simp [u, EuclideanSpace.basisFun_apply]
  nlinarith [norm_nonneg u, this]

/-- `T u = c • v`: the operator moves the trial vector entirely out of the trial space. -/
theorem T_u : T u = c • v := by
  ext i
  fin_cases i <;> simp [T, u, v, EuclideanSpace.basisFun_apply]

/-- **The Rayleigh quotient vanishes**, so `spec(A_0) = {0}` and `alpha = 0`. -/
theorem rayleigh_zero : ⟪T u, u⟫_ℝ = 0 := by
  rw [T_u, real_inner]
  simp [u, v, EuclideanSpace.basisFun_apply]

/-- **The residual has norm `1 / sqrt 2`.**  `R = T u - A_0 u` with `A_0 = 0`. -/
theorem residual_norm : ‖T u - (⟪T u, u⟫_ℝ) • u‖ = (Real.sqrt 2)⁻¹ := by
  rw [rayleigh_zero, zero_smul, sub_zero, T_u, norm_smul, Real.norm_eq_abs,
    abs_of_pos c_pos]
  have hv : ‖v‖ = 1 := by
    have : ‖v‖ ^ 2 = 1 := by
      rw [real_norm_sq]; simp [v, EuclideanSpace.basisFun_apply]
    nlinarith [norm_nonneg v, this]
  rw [hv, mul_one, c]

/-- The upper eigenvector of `T`, at `pi / 4` to the trial vector. -/
noncomputable def w : RealPlane := (Real.sqrt 2)⁻¹ • (u + v)

/-- `w` is an eigenvector of `T` for the eigenvalue `c`. -/
theorem T_w : T w = c • w := by
  ext i
  fin_cases i <;>
    simp [w, T, u, v, EuclideanSpace.basisFun_apply, map_smul, map_add,
      PiLp.smul_apply, PiLp.add_apply] <;> ring

/-- **The tangent quantity is `1`.**  The trial and orthogonal components of the
eigenvector are equal, both `1 / sqrt 2`, so their ratio -- which is `tan Theta_0`
-- is `1`. -/
theorem tangent_components_equal :
    ⟪w, u⟫_ℝ = (Real.sqrt 2)⁻¹ ∧ ⟪w, v⟫_ℝ = (Real.sqrt 2)⁻¹ := by
  constructor <;>
    · rw [real_inner]
      simp [w, u, v, EuclideanSpace.basisFun_apply, PiLp.smul_apply, PiLp.add_apply]

/-- **Example 6.1.**  With `delta = 1` and tangent quantity `1`, the Theorem 6.3
conclusion `delta * ‖tan Theta_0‖ <= ‖R‖` fails: the left side is `1` and the
residual is `1 / sqrt 2 < 1`.

This is why Theorem 6.3 needs `spec(Lambda_1) ⊆ [alpha + delta, ∞)`.  Here
`alpha = 0` and `delta = 1`, so that hypothesis would demand the complementary
spectrum lie in `[1, ∞)`; both eigenvalues of `T` are `± 1 / sqrt 2`, below `1`,
which is the spectral mass on the wrong side that the source allows in the
example. -/
theorem tangent_bound_fails :
    ‖T u - (⟪T u, u⟫_ℝ) • u‖ < (1 : ℝ) * 1 := by
  rw [residual_norm, mul_one]
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  rw [inv_lt_one_iff₀]
  right; exact h1

end

end Section6Example61
end DavisKahan1970
end TauCeti
