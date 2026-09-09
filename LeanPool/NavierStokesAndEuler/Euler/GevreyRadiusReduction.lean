/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyRestriction

@[expose] public section

/-! Radius reduction for actual finite weighted Sobolev norms. -/

noncomputable section

namespace EulerGevreyRadiusReduction

open Finset EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerJetProductBounds EulerPacketWeights
  EulerSobolevGevreyOperators

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
theorem weight_mono_radius {r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R) (n : ℕ) :
    weight r n ≤ weight R n := by
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hr hR n) (sq_nonneg _)

theorem weightedNorm_mono_radius {s : ℕ} (q N : ℕ) {r R : ℝ}
    (hr : 0 ≤ r) (hR : r ≤ R) (u : SobolevSpace period s) :
    weightedNorm period q N r u ≤ weightedNorm period q N R u := by
  exact sum_le_sum fun n _ => mul_le_mul_of_nonneg_right
    (weight_mono_radius hr hR n) (blockNorm_nonneg _)

omit [Fact (0 < period)] in
theorem weightedCoefficient_mono_radius {s : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection s A) (q N : ℕ) {r R : ℝ}
    (hr : 0 ≤ r) (hR : r ≤ R) :
    weightedCoefficient period K q N r ≤ weightedCoefficient period K q N R := by
  exact sum_le_sum fun n _ => mul_le_mul_of_nonneg_right
    (weight_mono_radius hr hR n) (coefficientBlock_nonneg _)

theorem weightedNorm_mono_cutoff {s : ℕ} (q : ℕ) {N M : ℕ} (hNM : N ≤ M)
    (r : ℝ) (hr : 0 < r) (u : SobolevSpace period s) :
    weightedNorm period q N r u ≤ weightedNorm period q M r u := by
  exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
    (fun n _ _ => mul_nonneg (weight_pos hr n).le (blockNorm_nonneg _))

omit [Fact (0 < period)] in
theorem weightedCoefficient_mono_cutoff {s : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period standardDirection s A) (q : ℕ) {N M : ℕ} (hNM : N ≤ M)
    (r : ℝ) (hr : 0 < r) :
    weightedCoefficient period K q N r ≤ weightedCoefficient period K q M r := by
  exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
    (fun n _ _ => mul_nonneg (weight_pos hr n).le (coefficientBlock_nonneg _))

/-- A retained weighted norm depends only on the genuine underlying field. -/
theorem weightedNorm_unique {s t : ℕ} (q N : ℕ) (r : ℝ)
    (u : SobolevSpace period s) (v : SobolevSpace period t)
    (huv : value period u = value period v) (hs : N+q ≤ s) (ht : N+q ≤ t) :
    weightedNorm period q N r u = weightedNorm period q N r v := by
  apply sum_congr rfl
  intro n hn
  congr 1
  exact blockNorm_unique period (toJet period u) (toJet period v) huv
    (by have := mem_range.mp hn; omega) (by have := mem_range.mp hn; omega)

/-- The four actual coordinate derivatives form exactly the next external block. -/
theorem derivative_block_sum {s : ℕ} (q n : ℕ) (hn : n+q ≤ s)
    (u : SobolevSpace period (s+1)) :
    (∑ i : Fin 4, blockNorm period (toJet period (derivativeOperator period s i u)) q n) =
      blockNorm period (toJet period u) q (n+1) := by
  let J : SpatialJet period standardDirection (s+1) (value period u) :=
    .succ (fun i => value period (derivativeOperator period s i u))
      (fun i => toJet period (derivativeOperator period s i u))
      (fun i => derivativeOperator_hasDerivAt period i u)
  rw [blockNorm_unique period (toJet period u) J rfl (by omega) (by omega), blockNorm_succ]
  rfl

omit [Fact (0 < period)] in
/-- A fixed exponential absorbs the square introduced by one factorial shift. -/
theorem successor_square_le_four_two_pow (n : ℕ) :
    ((n+1 : ℕ) : ℝ)^2 ≤ 4*(2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    by_cases h0 : n = 0
    · subst n; norm_num
    by_cases h1 : n = 1
    · subst n; norm_num
    have hn : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have hs : ((n+1+1 : ℕ) : ℝ)^2 ≤ 2*((n+1 : ℕ) : ℝ)^2 := by
      push_cast
      nlinarith [sq_nonneg ((n : ℝ)-2)]
    calc
      _ ≤ 2*((n+1 : ℕ) : ℝ)^2 := hs
      _ ≤ 2*(4*(2 : ℝ)^n) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

omit [Fact (0 < period)] in
theorem weight_half_le_shift (R : ℝ) (hR : 0 < R) (n : ℕ) :
    weight (R/2) n ≤ (4/R)*weight R (n+1) := by
  have hn := successor_square_le_four_two_pow n
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hp : (0 : ℝ) < (2 : ℝ)^n := by positivity
  unfold weight
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ R, div_pow]
  have he : (4/R)*(R^n*R/(((n+1 : ℕ) : ℝ)*(n.factorial : ℝ))^2) =
      4*R^n/(((n+1 : ℕ) : ℝ)^2*(n.factorial : ℝ)^2) := by
    field_simp
  rw [he, div_div]
  apply (div_le_div_iff₀ (mul_pos hp (sq_pos_of_pos hf)) (by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_left hn (mul_nonneg (pow_nonneg hR.le n) (sq_nonneg (n.factorial
    : ℝ)))
  nlinarith only [hm]

/-- Halving the positive radius pays for one full spatial/angular derivative,
with no dependence on the external cutoff. -/
theorem weightedNorm_derivative_half {s : ℕ} (q N : ℕ) (hN : N+q ≤ s)
    (R : ℝ) (hR : 0 < R) (u : SobolevSpace period (s+1)) :
    (∑ i : Fin 4, weightedNorm period q N (R/2) (derivativeOperator period s i u)) ≤
      (4/R)*weightedNorm period q (N+1) R u := by
  calc
    _ = ∑ n ∈ range (N+1), weight (R/2) n * blockNorm period (toJet period u) q (n+1) := by
      unfold weightedNorm
      rw [sum_comm]
      apply sum_congr rfl
      intro n hn
      rw [← mul_sum, derivative_block_sum period q n (by have := mem_range.mp hn; omega)]
    _ ≤ ∑ n ∈ range (N+1), (4/R)*weight R (n+1)*blockNorm period (toJet period u) q (n+1) := by
      exact sum_le_sum fun n _ => mul_le_mul_of_nonneg_right
        (weight_half_le_shift R hR n) (blockNorm_nonneg _)
    _ = (4/R)*(∑ n ∈ range (N+1), weight R (n+1)*blockNorm period (toJet period u) q (n+1)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold weightedNorm
      conv_rhs => rw [sum_range_succ']
      exact le_add_of_nonneg_right
        (mul_nonneg (weight_pos hR 0).le (blockNorm_nonneg (q := q) (n := 0) (toJet period u)))

end EulerGevreyRadiusReduction
