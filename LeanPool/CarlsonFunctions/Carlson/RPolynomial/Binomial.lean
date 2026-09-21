/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.RPolynomial.Coefficients
public import LeanPool.CarlsonFunctions.Carlson.RPolynomial.Basic
public import LeanPool.CarlsonFunctions.Dirichlet.Average.Continuation

/-! # The binomial theorem for Carlson's R-polynomials

Home for Carlson's Section 6.4 and its differential-difference consequences.

The underlying Chu–Vandermonde identity for `ascPochhammer` is `ascPochhammer_eval_add` in
`Pochhammer.Vandermonde`.
-/

open Complex
open scoped Classical
@[expose] public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Carlson's binomial translation formula for R-polynomials on the native convergence
domain; this is the polynomial identity in [Carl77, Section 6.4]. -/
theorem regCarlsonR_add_const_of_mem_mvBetaConvergent (n : ℕ) (a : ℂ) (z : ι → ℂ)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonR n (fun i => z i + a) b =
      ∑ m ∈ Finset.range (n + 1),
        (Nat.choose n m : ℂ) * a ^ (n - m) * regCarlsonR m z b := by
  rw [← regCarlsonDirichletAverage_pow n _ hb]
  calc
    regCarlsonDirichletAverage b (fun i => z i + a) (fun w => w ^ n) =
        regCarlsonDirichletAverage b z (fun w => (w + a) ^ n) := by
      simpa using (regCarlsonDirichletAverage_comp_affine b z
        (fun w : ℂ => w ^ n) 1 a).symm
    _ = regCarlsonDirichletAverage b z (fun w =>
          ∑ m ∈ Finset.range (n + 1),
            ((Nat.choose n m : ℂ) * a ^ (n - m)) * w ^ m) := by
      congr 1
      funext w
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = ∑ m ∈ Finset.range (n + 1),
          regCarlsonDirichletAverage b z
            (fun w => ((Nat.choose n m : ℂ) * a ^ (n - m)) * w ^ m) := by
      apply regCarlsonDirichletAverage_finsetSum hb
      intro m hm
      exact (continuous_const.mul
        ((continuous_carlsonAffineForm z).pow m)).continuousOn
    _ = ∑ m ∈ Finset.range (n + 1),
          (Nat.choose n m : ℂ) * a ^ (n - m) * regCarlsonR m z b := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [regCarlsonDirichletAverage_const_mul,
        regCarlsonDirichletAverage_pow m z hb]

/-- Carlson's binomial translation identity on the full parameter space. Gamma
regularization removes every exclusion on the total parameter. -/
theorem regCarlsonR_add_const (n : ℕ) (a : ℂ) (z b : ι → ℂ) :
    regCarlsonR n (fun i => z i + a) b =
      ∑ m ∈ Finset.range (n + 1),
        (Nat.choose n m : ℂ) * a ^ (n - m) * regCarlsonR m z b := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    (analyticOnNhd_regCarlsonR n _) ?_ ?_) b
  · intro c _
    exact Finset.analyticAt_fun_sum _ fun m _ =>
      analyticAt_const.mul (analyticOnNhd_regCarlsonR m z c (Set.mem_univ c))
  · intro c hc
    exact regCarlsonR_add_const_of_mem_mvBetaConvergent n a z hc

end DirichletTransform
end CarlsonRPolynomial
