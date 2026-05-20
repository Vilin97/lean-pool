/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import LeanPool.SelbergSieve4.AuxResults
import LeanPool.SelbergSieve4.Tactic.AesopDiv
import LeanPool.SelbergSieve4.UpperBoundSieve

noncomputable section

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat Aux

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-- Data for a finite weighted sieve problem. -/
structure Sieve where mk ::
  /-- Finite support of integers being sifted. -/
  support : Finset ℕ
  /-- Product of the primes used by the sieve. -/
  prodPrimes : ℕ
  prodPrimes_squarefree : Squarefree prodPrimes
  /-- Nonnegative weights on the support. -/
  weights : ℕ → ℝ
  weights_nonneg : ∀ n : ℕ, 0 ≤ weights n
  /-- Main term for the weighted support. -/
  totalMass : ℝ
  /-- Local density arithmetic function. -/
  nu : ArithmeticFunction ℝ
  nu_mult : nu.IsMultiplicative
  nu_pos_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → 0 < nu p
  nu_lt_one_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → nu p < 1

attribute [aesop safe (rule_sets := [Divisibility])] Sieve.prodPrimes_squarefree
attribute [arith_mult] Sieve.nu_mult

namespace Sieve

variable (s : Sieve)
local notation3 "ν" => Sieve.nu s
local notation3 "P" => Sieve.prodPrimes s
local notation3 "a" => Sieve.weights s
local notation3 "X" => Sieve.totalMass s
local notation3 "A" => Sieve.support s

/-- Weighted count of support elements divisible by `d`. -/
@[simp]
def multSum (d : ℕ) : ℝ :=
  ∑ n ∈ A, if d ∣ n then a n else 0

local notation3 "𝒜" => Sieve.multSum s

-- A_d = ν (d)/d X + R_d
/-- Remainder term after subtracting the expected main term from `multSum`. -/
@[simp]
def rem (d : ℕ) : ℝ :=
  𝒜 d - ν d * X

local notation3 "R" => Sieve.rem s

/-- Weighted count of support elements coprime to the sieve modulus. -/
def siftedSum : ℝ :=
  ∑ d ∈ A, if Coprime P d then a d else 0

open scoped ArithmeticFunction
/-- Selberg local factor product used in the simple upper-bound sieve. -/
def selbergTerms : ArithmeticFunction ℝ :=
  s.nu.pmul (.prodPrimeFactors fun p =>  1 / (1 - ν p))

local notation3 "g" => Sieve.selbergTerms s

/-- Expands `selbergTerms` as a product over the prime factors of `d`. -/
theorem selbergTerms_apply (d : ℕ) :
    g d = ν d * ∏ p ∈ d.primeFactors, 1/(1 - ν p) := by
  unfold selbergTerms
  by_cases h : d=0
  · rw [h]; simp
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply h]


/-- Main contribution of an upper-bound sieve weight. -/
def mainSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ divisors P, μPlus d * ν d

/-- Error contribution of an upper-bound sieve weight. -/
def errSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ divisors P, |μPlus d| * |R d|

section SieveLemmas

@[aesop forward safe (rule_sets := [Divisibility])]
theorem prodPrimes_ne_zero : P ≠ 0 :=
  Squarefree.ne_zero s.prodPrimes_squarefree

theorem squarefree_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree

theorem squarefree_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : Squarefree d := by
  simp only [Nat.mem_divisors] at hd
  exact Squarefree.squarefree_of_dvd hd.left s.prodPrimes_squarefree

theorem nu_pos_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : 0 < ν d := by
  calc
    0 < ∏ p ∈ d.primeFactors, ν p := by
      apply prod_pos
      intro p hpd
      have hp_prime : p.Prime := by exact prime_of_mem_primeFactors hpd
      have hp_dvd : p ∣ P := (dvd_of_mem_primeFactors hpd).trans hd
      exact s.nu_pos_of_prime p hp_prime hp_dvd
    _ = ν d := prod_factors_of_mult ν s.nu_mult
      (Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree)

theorem nu_ne_zero {d : ℕ} (hd : d ∣ P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  exact nu_pos_of_dvd_prodPrimes s hd

theorem nu_ne_zero_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  rw [mem_divisors] at hd
  apply s.nu_pos_of_dvd_prodPrimes hd.left

theorem multSum_eq_main_err (d : ℕ) : s.multSum d = ν d * X + R d := by
  dsimp [rem]
  ring

/-- Kronecker delta at `1`, valued in the reals. -/
def delta (n : ℕ) : ℝ := if n=1 then 1 else 0

local notation "δ" => delta

theorem siftedSum_as_delta : s.siftedSum = ∑ d ∈ s.support, a d * δ (Nat.gcd P d) :=
  by
  dsimp only [siftedSum]
  apply sum_congr rfl
  intro d _
  dsimp only [Nat.Coprime, delta] at *
  rw [mul_ite_zero]
  exact if_congr Iff.rfl (symm <| mul_one _) rfl

-- Unused ?
theorem nu_lt_self_of_dvd_prodPrimes : ∀ d : ℕ, d ∣ P → d ≠ 1 → ν d < 1 := by
  intro d hdP hd_ne_one
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
  calc
    ν d = ∏ p ∈ d.primeFactors, ν p :=
      eq_comm.mp (prod_factors_of_mult ν s.nu_mult hd_sq)
    _ < ∏ p ∈ d.primeFactors, 1 := by
      have hd_ne_zero : d ≠ 0 := by aesop_div
      apply prod_lt_prod_of_nonempty
      · intro p hp
        simp only [mem_primeFactors] at hp
        apply s.nu_pos_of_prime p (by aesop) (by aesop_div)
      · intro p hpd; rw [mem_primeFactors_of_ne_zero hd_ne_zero] at hpd
        apply s.nu_lt_one_of_prime p hpd.left (by aesop_div)
      · apply primeDivisors_nonempty _ <| (two_le_iff d).mpr ⟨hd_ne_zero, hd_ne_one⟩
    _ = 1 := by
      simp

-- Facts about g
@[aesop safe]
theorem selbergTerms_pos (l : ℕ) (hl : l ∣ P) : 0 < g l := by
  rw [selbergTerms_apply]
  apply mul_pos
  · exact s.nu_pos_of_dvd_prodPrimes hl
  · apply prod_pos
    intro p hp
    rw [one_div_pos]
    have hp_prime : p.Prime := prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ P := (Nat.dvd_of_mem_primeFactors hp).trans hl
    linarith only [s.nu_lt_one_of_prime p hp_prime hp_dvd]

theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative g := by
  unfold selbergTerms
  arith_mult

theorem one_div_selbergTerms_eq_conv_moebius_nu (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : ν l ≠ 0) : 1 / g l = ∑ d ∈ l.divisors, (μ <| l / d) * (ν d)⁻¹ :=
  by
  rw [selbergTerms_apply]
  simp only [one_div, mul_inv, inv_inv, Finset.prod_inv_distrib]
  rw [(s.nu_mult).prodPrimeFactors_one_sub_of_squarefree _ hl]
  rw [mul_sum]
  apply symm
  rw [← Nat.sum_divisorsAntidiagonal' fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  rw [Nat.sum_divisorsAntidiagonal fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  apply sum_congr rfl; intro d hd
  have hd_dvd : d ∣ l := dvd_of_mem_divisors hd
  rw [←div_mult_of_dvd_squarefree ν s.nu_mult l d (dvd_of_mem_divisors hd) hl, inv_div]
  · ring
  · revert hnu_nonzero; contrapose!
    exact multiplicative_zero_of_zero_dvd ν s.nu_mult hl hd_dvd

theorem nu_eq_conv_one_div_selbergTerms (d : ℕ) (hdP : d ∣ P) :
    (ν d)⁻¹ = ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
  apply symm
  rw [←sum_filter, Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d :=
    Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).mpr
  intro l _ hlP
  rw [sum_divisorsAntidiagonal' (f:=fun x y => (μ <| x) * (ν y)⁻¹) (n:=l)]
  apply symm
  exact s.one_div_selbergTerms_eq_conv_moebius_nu l
    (Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree)
    (_root_.ne_of_gt <| s.nu_pos_of_dvd_prodPrimes hlP)

theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ P) :
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) = g d * (ν d)⁻¹ := by
  calc
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) =
        ∑ l ∈ divisors P, if l ∣ d then g (d / l) else 0 := by
      rw [← sum_over_dvd_ite s.prodPrimes_ne_zero hd]
      rw [← Nat.sum_divisorsAntidiagonal fun x _ => g x]
      rw [Nat.sum_divisorsAntidiagonal' fun x _ => g x]
      rw [sum_over_dvd_ite s.prodPrimes_ne_zero hd]
    _ = g d * ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
      intro h
      rw [← div_mult_of_dvd_squarefree g s.selbergTerms_mult d l]
      · ring
      · exact h
      · apply Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
      · apply _root_.ne_of_gt
        rw [mem_divisors] at hl
        apply selbergTerms_pos
        exact hl.left
    _ = g d * (ν d)⁻¹ := by rw [← s.nu_eq_conv_one_div_selbergTerms d hd]

theorem upper_bound_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    s.siftedSum ≤ ∑ d ∈ divisors P, μPlus d * s.multSum d := by
  have hμ : ∀ n, δ n ≤ ∑ d ∈ n.divisors, μPlus d := μPlus.hμPlus
  rw [siftedSum_as_delta]
  trans (∑ n ∈ s.support, a n * ∑ d ∈ (Nat.gcd P n).divisors, μPlus d)
  · apply Finset.sum_le_sum; intro n _
    exact mul_le_mul_of_nonneg_left (hμ (Nat.gcd P n)) (s.weights_nonneg n)
  apply le_of_eq
  trans (∑ n ∈ s.support, ∑ d ∈ divisors P, if d ∣ n then a n * μPlus d else 0)
  · apply sum_congr rfl; intro n _
    rw [mul_sum, sum_over_dvd_ite s.prodPrimes_ne_zero (Nat.gcd_dvd_left _ _),
      sum_congr rfl]; intro d hd
    apply if_congr _ rfl rfl
    rw [Nat.dvd_gcd_iff, and_iff_right (dvd_of_mem_divisors hd)]
  rw [sum_comm, sum_congr rfl]; intro d _
  dsimp only [multSum]
  rw [mul_sum, sum_congr rfl]; intro n _
  rw [←ite_zero_mul, mul_comm]

theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    s.siftedSum ≤ X * s.mainSum μPlus + s.errSum μPlus := by
  dsimp only [mainSum, errSum]
  trans (∑ d ∈ divisors P, μPlus d * s.multSum d)
  · apply upper_bound_of_UpperBoundSieve
  trans ( X * ∑ d ∈ divisors P, μPlus d * ν d + ∑ d ∈ divisors P, μPlus d * R d )
  · apply le_of_eq
    rw [mul_sum, ←sum_add_distrib]
    apply sum_congr rfl; intro d _
    dsimp only [rem]; ring
  apply _root_.add_le_add (le_rfl)
  apply sum_le_sum; intro d _
  rw [←abs_mul]
  exact le_abs_self (UpperBoundSieve.μPlus μPlus d * rem s d)

end SieveLemmas

section LambdaSquared

/-- Lambda-squared upper-bound weights generated from a function on divisors. -/
def _root_.Sieve.lambdaSquared (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬↑(d ^ 2) ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2)
    (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2]
  · ring
  by_contra hyp
  apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr
theorem _root_.Sieve.lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [ite_self, MulZeroClass.mul_zero]
  apply sum_eq_zero; intro d1 _; apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw[mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1 (Nat.lcm_comm d1 d2 ▸ h) hle

theorem _root_.Sieve.upperMoebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    UpperMoebius <| lambdaSquared weights := by
  dsimp [UpperMoebius, lambdaSquared]
  intro n
  have h_sq :
    (∑ d ∈ n.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0) =
      (∑ d ∈ n.divisors, weights d) ^ 2 := by
    rw [sq, mul_sum, conv_lambda_sq_larger_sum _ n, sum_comm]
    apply sum_congr rfl; intro d1 hd1
    rw [sum_mul, sum_comm]
    apply sum_congr rfl; intro d2 hd2
    rw [←Aux.sum_intro]
    · ring
    · rw [mem_divisors, Nat.lcm_dvd_iff]
      exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩
  rw [h_sq]
  split_ifs with hn
  · rw [hn]; simp [hw]
  · apply sq_nonneg

-- local notation3 "ν" => Sieve.nu s
-- local notation3 "P" => Sieve.prodPrimes s
-- local notation3 "a" => Sieve.weights s
-- local notation3 "X" => Sieve.totalMass s
-- local notation3 "R" => Sieve.rem s
-- local notation3 "g" => Sieve.selbergTerms s

theorem _root_.Sieve.lambdaSquared_mainSum_eq_quad_form (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w) =
      ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        ν d1 * w d1 * ν d2 * w d2 * (ν (d1.gcd d2))⁻¹ := by
  dsimp only [mainSum, lambdaSquared]
  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors d, ∑ d2 ∈ divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · rw [sum_congr rfl]; intro d _
    rw [sum_mul, sum_congr rfl]; intro d1 _
    rw [sum_mul, sum_congr rfl]; intro d2 _
    rw [ite_zero_mul]
  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · apply conv_lambda_sq_larger_sum
  rw [sum_comm, sum_congr rfl]; intro d1 hd1
  rw [sum_comm, sum_congr rfl]; intro d2 hd2
  have h : d1.lcm d2 ∣ P := Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
  rw [←sum_intro (divisors P) (d1.lcm d2) (mem_divisors.mpr ⟨h, s.prodPrimes_ne_zero⟩ )]
  rw [mult_lcm_eq_of_ne_zero ν s.nu_mult _ _ _]
  · ring
  · refine _root_.ne_of_gt (s.nu_pos_of_dvd_prodPrimes ?_)
    trans d1
    · exact Nat.gcd_dvd_left d1 d2
    · exact dvd_of_mem_divisors hd1

theorem _root_.Sieve.lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w) =
      ∑ l ∈ divisors P,
        1 / g l * (∑ d ∈ divisors P, if l ∣ d then ν d * w d else 0) ^ 2 :=
  by
  rw [s.lambdaSquared_mainSum_eq_quad_form w]
  trans (∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P, (∑ l ∈ divisors P,
          if l ∣ d1.gcd d2 then 1 / g l * (ν d1 * w d1) * (ν d2 * w d2) else 0))
  · apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 _
    have hgcd_dvd: d1.gcd d2 ∣ P := Trans.trans (Nat.gcd_dvd_left d1 d2) (dvd_of_mem_divisors hd1)
    rw [s.nu_eq_conv_one_div_selbergTerms _ hgcd_dvd, mul_sum]
    apply sum_congr rfl; intro l _
    rw [mul_ite_zero]; apply if_congr Iff.rfl _ rfl
    ring
  trans (∑ l ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        if l ∣ Nat.gcd d1 d2 then 1 / selbergTerms s l * (ν d1 * w d1) * (ν d2 * w d2) else 0)
  · apply symm; rw [sum_comm, sum_congr rfl]; intro d1 _; rw[sum_comm];
  apply sum_congr rfl; intro l _
  rw [sq, sum_mul, mul_sum, sum_congr rfl]; intro d1 _
  rw [mul_sum, mul_sum, sum_congr rfl]; intro d2 _
  rw [ite_zero_mul_ite_zero, mul_ite_zero]
  apply if_congr (Nat.dvd_gcd_iff) _ rfl;
  ring

end LambdaSquared

end Sieve
