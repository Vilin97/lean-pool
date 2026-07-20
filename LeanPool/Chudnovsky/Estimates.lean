/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Estimates for `1728·J` and `s₂` (Milla, arXiv:1809.00533v6, Chapter 5)

This file states the explicit estimates and `q`-series approximations of Chapter 5
("Estimates") of Milla's proof of the Chudnovsky formula (arXiv:1809.00533v6):

* `Chudnovsky.Jtilde` : the truncation `Jtilde` of Klein's `J`-invariant
  (Theorem `theonaeherJ` of the paper),
  `Jtilde(τ) = (1 + 240(q + 9q²))³ / (1728·q·(1 - q - q²)²⁴)`;
* `Chudnovsky.s₂tilde` : the truncation `stilde₂` of Ramanujan's `s₂`
  (Theorem `theonaehers2` of the paper),
  `stilde₂(τ) = (1 + 240(q + 9q²))/(1 - 504(q + 33q²)) · (1 - 24(q + 3q²) - 3/(π·Im τ))`;
* `Chudnovsky.E₄trunc`, `Chudnovsky.E₆trunc`, `Chudnovsky.E₂starTrunc` : the quadratic
  truncations `X`, `Y`, `Z` of Lemma `lemxy` of the paper;
* `Chudnovsky.eisensteinTail` : the Lambert-series tails `R_w⁽ˡ⁾ = ∑_{n≥l} σ_{w-1}(n)·qⁿ`
  (Lemma `lemrestchaetz`), with `eisensteinTail k l` corresponding to weight `w = k + 1`;
* `Chudnovsky.sigma_le_pow_succ` : `σₖ(n) ≤ n^(k+1)` (Lemma `sigmaschaetz`);
* `Chudnovsky.norm_q_lt_of_mem_Region` : `|q| < e^(-7.852)` for `Im τ > 5/4`
  (Lemma `archim-lem`, with Mathlib's `π > 3.1415` replacing Archimedes);
* `Chudnovsky.norm_eisensteinTail_le` and the concrete bounds
  `norm_eisensteinTail_sigma₁/₃/₅` (Lemmas `lemrestchaetz`, `lemrestkonkr`);
* `Chudnovsky.lemE6` : `|E₆(τ)| > 0.8` on the region (Lemma `lemE6`);
* `Chudnovsky.theonaeherJ` : `|1728·J - 1728·Jtilde| < 0.2` together with the bracketing
  `0.737/|q| < |1728·J| < 1.321/|q|` and `|J| > 1.096` (Theorem `theonaeherJ`);
* `Chudnovsky.theonaehers2` : `|s₂ - stilde₂| < 222000·|q|³` (Theorem `theonaehers2`).

All estimates hold on `Chudnovsky.Region = {τ | Im τ > 5/4}`.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex ModularForm EisensteinSeries

open scoped Real ArithmeticFunction.sigma

/-! ### Explicit `q`-truncations

The quadratic truncations `X`, `Y`, `Z` of the Eisenstein series (paper Lemma `lemxy`),
and the resulting approximations `Jtilde` (paper Thm. `theonaeherJ`) and `stilde₂`
(paper Thm. `theonaehers2`). All are honest rational functions of the nome `q τ`
(plus, for `Z`, the real quantity `3/(π·Im τ)`), so the numerical phase can evaluate
them directly. -/

/-- The quadratic truncation `X := E₄⁽²⁾ = 1 + 240(q + 9q²)` of `E₄` (paper Lemma `lemxy`). -/
def E₄trunc (τ : ℍ) : ℂ := 1 + 240 * (q τ + 9 * q τ ^ 2)

/-- The quadratic truncation `Y := E₆⁽²⁾ = 1 - 504(q + 33q²)` of `E₆` (paper Lemma `lemxy`). -/
def E₆trunc (τ : ℍ) : ℂ := 1 - 504 * (q τ + 33 * q τ ^ 2)

/-- The quadratic truncation
`Z := E₂⁽²⁾ - 3/(π·Im τ) = 1 - 24(q + 3q²) - 3/(π·Im τ)` of `E₂*` (paper Lemma `lemxy`). -/
def E₂starTrunc (τ : ℍ) : ℂ := 1 - 24 * (q τ + 3 * q τ ^ 2) - 3 / (π * τ.im)

/-- The approximation `Jtilde` of Klein's `J`-invariant from Theorem `theonaeherJ` of the paper:
`Jtilde(τ) = (1 + 240(q + 9q²))³ / (1728·q·(1 - q - q²)²⁴)`.

The denominator `(1 - q - q²)²⁴` is the truncation of `∏ (1-qⁿ)²⁴ = Δ/q` coming from
Euler's pentagonal number theorem (paper Remark `penta`). -/
def Jtilde (τ : ℍ) : ℂ :=
  (1 + 240 * (q τ + 9 * q τ ^ 2)) ^ 3 / (1728 * q τ * (1 - q τ - q τ ^ 2) ^ 24)

lemma Jtilde_eq (τ : ℍ) :
    Jtilde τ = E₄trunc τ ^ 3 / (1728 * q τ * (1 - q τ - q τ ^ 2) ^ 24) := rfl

/-- `1728·Jtilde` in the normalized form used in the paper and in the numerical phase. -/
lemma mul_Jtilde_eq (τ : ℍ) :
    1728 * Jtilde τ =
      (1 + 240 * (q τ + 9 * q τ ^ 2)) ^ 3 / (q τ * (1 - q τ - q τ ^ 2) ^ 24) := by
  simp only [Jtilde]
  rw [show (1728 : ℂ) * q τ * (1 - q τ - q τ ^ 2) ^ 24
        = 1728 * (q τ * (1 - q τ - q τ ^ 2) ^ 24) by ring,
    ← div_div, mul_div_assoc', mul_div_assoc',
    mul_div_cancel_left₀ _ (by norm_num : (1728 : ℂ) ≠ 0)]

/-- The approximation `stilde₂` of Ramanujan's `s₂` from Theorem `theonaehers2` of the paper:
`stilde₂(τ) = (1 + 240(q + 9q²))/(1 - 504(q + 33q²)) · (1 - 24(q + 3q²) - 3/(π·Im τ))`. -/
def s₂tilde (τ : ℍ) : ℂ :=
  (1 + 240 * (q τ + 9 * q τ ^ 2)) / (1 - 504 * (q τ + 33 * q τ ^ 2)) *
    (1 - 24 * (q τ + 3 * q τ ^ 2) - 3 / (π * τ.im))

lemma s₂tilde_eq (τ : ℍ) : s₂tilde τ = E₄trunc τ / E₆trunc τ * E₂starTrunc τ := rfl

/-! ### The σₖ bound (paper Lemma `sigmaschaetz`) -/

/-- Paper Lemma `sigmaschaetz`: `σₖ(n) ≤ n^(k+1)`.
(The paper states this for `n ≥ 1`; with Mathlib's convention `σ k 0 = 0` it holds for
all `n`.) -/
theorem sigma_le_pow_succ (k n : ℕ) : ArithmeticFunction.sigma k n ≤ n ^ (k + 1) := by
  rw [ArithmeticFunction.sigma_apply]
  calc ∑ d ∈ n.divisors, d ^ k ≤ ∑ _d ∈ n.divisors, n ^ k :=
        Finset.sum_le_sum fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) k
    _ = n.divisors.card * n ^ k := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * n ^ k := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self n)
    _ = n ^ (k + 1) := by rw [pow_succ, mul_comm]

/-! ### The Archimedes lemma (paper Lemma `archim-lem`) -/

/-- Paper Lemma `archim-lem`: if `Im τ > 5/4` then `|q| < e^(-7.852)`.
Archimedes' bound `π > 3 + 10/71` is replaced by Mathlib's `Real.pi_gt_d4`. -/
lemma norm_q_lt_of_mem_Region {τ : ℍ} (hτ : τ ∈ Region) :
    ‖q τ‖ < Real.exp (-7.852) := by
  rw [norm_q, Real.exp_lt_exp, neg_lt_neg_iff]
  have hπ : (3.1408 : ℝ) < π := by linarith [Real.pi_gt_d4]
  have him : (5 / 4 : ℝ) < τ.im := hτ
  nlinarith [mul_pos (sub_pos.2 hπ) (sub_pos.2 him)]

/-! ### `q`-expansions of the Eisenstein series (paper Prop. `sigmaeisen`)

We derive the divisor-sum `q`-expansions of `E₄`, `E₆` and `E₂` from Mathlib's
`EisensteinSeries.q_expansion_bernoulli` and `EisensteinSeries.E2_eq_tsum_cexp`,
in a `ℕ`-indexed form suitable for splitting off the leading terms. -/

/-- Summability of the divisor-sum `q`-series `∑ σₖ(n)·qⁿ` (paper Prop. `sigmaeisen`). -/
lemma summable_sigma_q (k : ℕ) (τ : ℍ) :
    Summable fun n : ℕ ↦ (ArithmeticFunction.sigma k n : ℂ) * q τ ^ n := by
  apply Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one (k + 1) (norm_q_lt_one τ))
  intro n
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast ArithmeticFunction.sigma_le_pow_succ k n

/-- Summability of the (real, absolute) divisor-sum `q`-series `∑ σₖ(n)·|q|ⁿ`. -/
lemma summable_norm_sigma_q (k : ℕ) (τ : ℍ) :
    Summable fun n : ℕ ↦ (ArithmeticFunction.sigma k n : ℝ) * ‖q τ‖ ^ n := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_norm_pow_mul_geometric_of_norm_lt_one (k + 1) (norm_q_lt_one τ))
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast ArithmeticFunction.sigma_le_pow_succ k n

/-- Paper Prop. `sigmaeisen`: `E₄(τ) = 1 + 240·∑_{n≥1} σ₃(n)·qⁿ`. -/
lemma E₄_eq_tsum (τ : ℍ) :
    E₄ τ = 1 + 240 * ∑' n : ℕ, (ArithmeticFunction.sigma 3 (n + 1) : ℂ) * q τ ^ (n + 1) := by
  have h := EisensteinSeries.q_expansion_bernoulli (k := 4) (by norm_num) (by decide) τ
  rw [show bernoulli 4 = -1 / 30 by decide +kernel, ← q_eq] at h
  simp only [zpow_natCast] at h
  rw [tsum_pnat_eq_tsum_succ (f := fun n ↦ (ArithmeticFunction.sigma 3 n : ℂ) * q τ ^ n)] at h
  rw [h]; norm_num

/-- Paper Prop. `sigmaeisen`: `E₆(τ) = 1 - 504·∑_{n≥1} σ₅(n)·qⁿ`. -/
lemma E₆_eq_tsum (τ : ℍ) :
    E₆ τ = 1 - 504 * ∑' n : ℕ, (ArithmeticFunction.sigma 5 (n + 1) : ℂ) * q τ ^ (n + 1) := by
  have h := EisensteinSeries.q_expansion_bernoulli (k := 6) (by norm_num) (by decide) τ
  rw [show bernoulli 6 = 1 / 42 by decide +kernel, ← q_eq] at h
  simp only [zpow_natCast] at h
  rw [tsum_pnat_eq_tsum_succ (f := fun n ↦ (ArithmeticFunction.sigma 5 n : ℂ) * q τ ^ n)] at h
  rw [h]; norm_num

/-- Paper Prop. `sigmaeisen`: `E₂(τ) = 1 - 24·∑_{n≥1} σ₁(n)·qⁿ`. -/
lemma E2_eq_tsum (τ : ℍ) :
    E2 τ = 1 - 24 * ∑' n : ℕ, (ArithmeticFunction.sigma 1 (n + 1) : ℂ) * q τ ^ (n + 1) := by
  have h := EisensteinSeries.E2_eq_tsum_cexp τ
  rw [← q_eq] at h
  rw [tsum_pnat_eq_tsum_succ (f := fun n ↦ (ArithmeticFunction.sigma 1 n : ℂ) * q τ ^ n)] at h
  rw [h]

/-- Split off the first two terms of the divisor-sum `q`-series, leaving the tail
`∑_{n≥3} σₖ(n)·qⁿ` (the paper's `R_{k+1}⁽³⁾`). -/
lemma tsum_sigma_split (k : ℕ) (τ : ℍ) :
    ∑' n : ℕ, (ArithmeticFunction.sigma k (n + 1) : ℂ) * q τ ^ (n + 1) =
      (ArithmeticFunction.sigma k 1 : ℂ) * q τ ^ 1
      + (ArithmeticFunction.sigma k 2 : ℂ) * q τ ^ 2
      + ∑' n : ℕ, (ArithmeticFunction.sigma k (n + 3) : ℂ) * q τ ^ (n + 3) := by
  have hsum : Summable fun n : ℕ ↦ (ArithmeticFunction.sigma k (n + 1) : ℂ) * q τ ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_q k τ)
  have := hsum.sum_add_tsum_nat_add 2
  rw [Finset.sum_range_succ, Finset.sum_range_one] at this
  simp only [Nat.zero_add] at this
  rw [← this]

/-- Numerical bound `e^(-7.852) < 0.000389`, replacing the Archimedes step of the paper.
Proved from `Real.exp_one_gt_d9` and an 8-term Taylor lower bound for `exp 0.852`. -/
lemma exp_neg_bound : Real.exp (-7.852) < 0.000389 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h7 : (2.7182818283 : ℝ) ^ 7 < Real.exp 7 := by
    have he : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]; exact pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h852 : (2.344323 : ℝ) ≤ Real.exp 0.852 := by
    have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.852) 8
    refine le_trans ?_ hs
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  have hbig : (2570.7 : ℝ) < Real.exp 7.852 := by
    have he : Real.exp 7.852 = Real.exp 7 * Real.exp 0.852 := by rw [← Real.exp_add]; norm_num
    rw [he]
    calc (2570.7 : ℝ) < 2.7182818283 ^ 7 * 2.344323 := by norm_num
      _ ≤ Real.exp 7 * Real.exp 0.852 :=
          mul_le_mul h7.le h852 (by norm_num) (le_of_lt (lt_trans (by norm_num) h7))
  rw [Real.exp_neg]
  calc (Real.exp 7.852)⁻¹ < (2570.7 : ℝ)⁻¹ := inv_strictAnti₀ (by norm_num) hbig
    _ < 0.000389 := by norm_num

/-! ### Geometric tail bounds for the Lambert-type series
(paper Lemmas `lemrestchaetz` and `lemrestkonkr`) -/

/-- The tail of the divisor-sum (Lambert-type) `q`-series of the Eisenstein series of
weight `k + 1` (paper Lemma `lemrestchaetz`):
`eisensteinTail k l τ = ∑_{n ≥ l} σₖ(n)·qⁿ`, i.e. the paper's `R_w⁽ˡ⁾` with `w = k + 1`. -/
def eisensteinTail (k l : ℕ) (τ : ℍ) : ℂ :=
  ∑' n : ℕ, (ArithmeticFunction.sigma k (n + l) : ℂ) * q τ ^ (n + l)

/-- Paper Lemma `lemrestchaetz` (with `w = k + 1` the Eisenstein weight): if
`(1 + 1/l)^(k+1)·|q| < 1` then
`|R_w⁽ˡ⁾| ≤ l^(k+1)·|q|^l / (1 - (1 + 1/l)^(k+1)·|q|)`. -/
theorem norm_eisensteinTail_le (k l : ℕ) (hl : 0 < l) (τ : ℍ)
    (hs : (1 + 1 / (l : ℝ)) ^ (k + 1) * ‖q τ‖ < 1) :
    ‖eisensteinTail k l τ‖ ≤
      (l : ℝ) ^ (k + 1) * ‖q τ‖ ^ l / (1 - (1 + 1 / (l : ℝ)) ^ (k + 1) * ‖q τ‖) := by
  set Q := ‖q τ‖ with hQ_def
  have hQ0 : 0 ≤ Q := norm_nonneg _
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  set s : ℝ := (1 + 1 / (l : ℝ)) ^ (k + 1) * Q with hs_def
  have hs0 : 0 ≤ s := by positivity
  have hnorm : ∀ n : ℕ, ‖(ArithmeticFunction.sigma k (n + l) : ℂ) * q τ ^ (n + l)‖
      = (ArithmeticFunction.sigma k (n + l) : ℝ) * Q ^ (n + l) := by
    intro n; rw [norm_mul, norm_pow, Complex.norm_natCast]
  have hsummN : Summable fun n : ℕ ↦
      (ArithmeticFunction.sigma k (n + l) : ℝ) * Q ^ (n + l) :=
    (summable_nat_add_iff l).mpr (summable_norm_sigma_q k τ)
  have hgeo : Summable fun n : ℕ ↦ ((l : ℝ) ^ (k + 1) * Q ^ l) * s ^ n :=
    (summable_geometric_of_lt_one hs0 hs).mul_left _
  have hbound : ∀ n : ℕ, (ArithmeticFunction.sigma k (n + l) : ℝ) * Q ^ (n + l)
      ≤ ((l : ℝ) ^ (k + 1) * Q ^ l) * s ^ n := by
    intro n
    have h1l : (0 : ℝ) ≤ 1 / (l : ℝ) := by positivity
    have hbern : (1 : ℝ) + (n : ℝ) / l ≤ (1 + 1 / (l : ℝ)) ^ n := by
      have := one_add_mul_le_pow (a := 1 / (l : ℝ)) (by linarith) n
      calc (1 : ℝ) + (n : ℝ) / l = 1 + (n : ℝ) * (1 / l) := by ring
        _ ≤ (1 + 1 / (l : ℝ)) ^ n := this
    have hbase : ((n : ℝ) + l) ≤ (l : ℝ) * (1 + 1 / (l : ℝ)) ^ n := by
      have := mul_le_mul_of_nonneg_left hbern hl0.le
      calc ((n : ℝ) + l) = (l : ℝ) * (1 + (n : ℝ) / l) := by field_simp; ring
        _ ≤ (l : ℝ) * (1 + 1 / (l : ℝ)) ^ n := this
    have hpow : ((n : ℝ) + l) ^ (k + 1)
        ≤ (l : ℝ) ^ (k + 1) * (1 + 1 / (l : ℝ)) ^ (n * (k + 1)) := by
      calc ((n : ℝ) + l) ^ (k + 1)
          ≤ ((l : ℝ) * (1 + 1 / (l : ℝ)) ^ n) ^ (k + 1) :=
            pow_le_pow_left₀ (by positivity) hbase (k + 1)
        _ = (l : ℝ) ^ (k + 1) * (1 + 1 / (l : ℝ)) ^ (n * (k + 1)) := by
            rw [mul_pow, ← pow_mul]
    have hsig : (ArithmeticFunction.sigma k (n + l) : ℝ) ≤ ((n : ℝ) + l) ^ (k + 1) := by
      have := ArithmeticFunction.sigma_le_pow_succ k (n + l)
      calc (ArithmeticFunction.sigma k (n + l) : ℝ) ≤ ((n + l : ℕ) : ℝ) ^ (k + 1) := by
            exact_mod_cast this
        _ = ((n : ℝ) + l) ^ (k + 1) := by push_cast; ring
    have hQpow : (0 : ℝ) ≤ Q ^ (n + l) := by positivity
    calc (ArithmeticFunction.sigma k (n + l) : ℝ) * Q ^ (n + l)
        ≤ ((n : ℝ) + l) ^ (k + 1) * Q ^ (n + l) :=
          mul_le_mul_of_nonneg_right hsig hQpow
      _ ≤ ((l : ℝ) ^ (k + 1) * (1 + 1 / (l : ℝ)) ^ (n * (k + 1))) * Q ^ (n + l) :=
          mul_le_mul_of_nonneg_right hpow hQpow
      _ = ((l : ℝ) ^ (k + 1) * Q ^ l) * s ^ n := by
          rw [hs_def, mul_pow, ← pow_mul, pow_add]; ring
  calc ‖eisensteinTail k l τ‖
      ≤ ∑' n : ℕ, ‖(ArithmeticFunction.sigma k (n + l) : ℂ) * q τ ^ (n + l)‖ := by
        apply norm_tsum_le_tsum_norm; simp only [hnorm]; exact hsummN
    _ = ∑' n : ℕ, (ArithmeticFunction.sigma k (n + l) : ℝ) * Q ^ (n + l) := by simp only [hnorm]
    _ ≤ ∑' n : ℕ, ((l : ℝ) ^ (k + 1) * Q ^ l) * s ^ n :=
        hsummN.tsum_le_tsum hbound hgeo
    _ = ((l : ℝ) ^ (k + 1) * Q ^ l) * (1 - s)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hs0 hs]
    _ = (l : ℝ) ^ (k + 1) * Q ^ l / (1 - s) := by rw [div_eq_mul_inv]

/-- The tail `R⁽ˡ⁾` peels off its leading term: `R⁽ˡ⁾ = σₖ(l)·qˡ + R⁽ˡ⁺¹⁾`. -/
lemma eisensteinTail_succ (k l : ℕ) (τ : ℍ) :
    eisensteinTail k l τ
      = (ArithmeticFunction.sigma k l : ℂ) * q τ ^ l + eisensteinTail k (l + 1) τ := by
  have hsum : Summable fun n : ℕ ↦ (ArithmeticFunction.sigma k (n + l) : ℂ) * q τ ^ (n + l) :=
    (summable_nat_add_iff l).mpr (summable_sigma_q k τ)
  rw [eisensteinTail, hsum.tsum_eq_zero_add]
  simp only [Nat.zero_add]
  rw [eisensteinTail]
  congr 1
  apply tsum_congr
  intro n
  rw [show n + 1 + l = n + (l + 1) from by omega]

/-- `|q| > 0` on the region (`q τ = e^{2πiτ} ≠ 0`). -/
lemma norm_q_pos (τ : ℍ) : 0 < ‖q τ‖ := by rw [norm_q]; exact Real.exp_pos _

/-- Paper Lemma `lemrestkonkr`, first bound: `|R₂⁽³⁾| ≤ 4.007·|q|³` for `Im τ > 5/4`. -/
theorem norm_eisensteinTail_sigma₁ {τ : ℍ} (hτ : τ ∈ Region) :
    ‖eisensteinTail 1 3 τ‖ ≤ 4.007 * ‖q τ‖ ^ 3 := by
  set Q := ‖q τ‖ with hQdef
  have hQpos : 0 < Q := norm_q_pos τ
  have hQ : Q < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hs : (1 + 1 / (4 : ℝ)) ^ (1 + 1) * Q < 1 := by nlinarith [hQpos, hQ]
  have htail := norm_eisensteinTail_le 1 4 (by norm_num) τ hs
  norm_num at htail
  rw [eisensteinTail_succ 1 3 τ]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_pow, Complex.norm_natCast,
    show (ArithmeticFunction.sigma 1 3 : ℕ) = 4 from by decide]
  have hD : (0 : ℝ) < 1 - 25 / 16 * Q := by nlinarith [hQpos, hQ]
  have hdiv : 16 * Q ^ 4 / (1 - 25 / 16 * Q) ≤ 0.007 * Q ^ 3 := by
    rw [div_le_iff₀ hD]; nlinarith [hQpos, hQ, pow_pos hQpos 3]
  push_cast
  nlinarith [htail, hdiv]

/-- Paper Lemma `lemrestkonkr`, second bound: `|R₄⁽³⁾| ≤ 28.1·|q|³` for `Im τ > 5/4`. -/
theorem norm_eisensteinTail_sigma₃ {τ : ℍ} (hτ : τ ∈ Region) :
    ‖eisensteinTail 3 3 τ‖ ≤ 28.1 * ‖q τ‖ ^ 3 := by
  set Q := ‖q τ‖ with hQdef
  have hQpos : 0 < Q := norm_q_pos τ
  have hQ : Q < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hs : (1 + 1 / (4 : ℝ)) ^ (3 + 1) * Q < 1 := by nlinarith [hQpos, hQ]
  have htail := norm_eisensteinTail_le 3 4 (by norm_num) τ hs
  norm_num at htail
  rw [eisensteinTail_succ 3 3 τ]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_pow, Complex.norm_natCast,
    show (ArithmeticFunction.sigma 3 3 : ℕ) = 28 from by decide]
  have hD : (0 : ℝ) < 1 - 625 / 256 * Q := by nlinarith [hQpos, hQ]
  have hdiv : 256 * Q ^ 4 / (1 - 625 / 256 * Q) ≤ 0.1 * Q ^ 3 := by
    rw [div_le_iff₀ hD]; nlinarith [hQpos, hQ, pow_pos hQpos 3]
  push_cast
  nlinarith [htail, hdiv]

/-- Paper Lemma `lemrestkonkr`, third bound: `|R₆⁽³⁾| ≤ 245.6·|q|³` for `Im τ > 5/4`. -/
theorem norm_eisensteinTail_sigma₅ {τ : ℍ} (hτ : τ ∈ Region) :
    ‖eisensteinTail 5 3 τ‖ ≤ 245.6 * ‖q τ‖ ^ 3 := by
  set Q := ‖q τ‖ with hQdef
  have hQpos : 0 < Q := norm_q_pos τ
  have hQ : Q < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hs : (1 + 1 / (4 : ℝ)) ^ (5 + 1) * Q < 1 := by nlinarith [hQpos, hQ]
  have htail := norm_eisensteinTail_le 5 4 (by norm_num) τ hs
  norm_num at htail
  rw [eisensteinTail_succ 5 3 τ]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_pow, Complex.norm_natCast,
    show (ArithmeticFunction.sigma 5 3 : ℕ) = 244 from by decide]
  have hD : (0 : ℝ) < 1 - 15625 / 4096 * Q := by nlinarith [hQpos, hQ]
  have hdiv : 4096 * Q ^ 4 / (1 - 15625 / 4096 * Q) ≤ 1.6 * Q ^ 3 := by
    rw [div_le_iff₀ hD]; nlinarith [hQpos, hQ, pow_pos hQpos 3]
  push_cast
  nlinarith [htail, hdiv]

/-! ### Truncation errors (paper `δX`, `δY`, `δZ` of Lemma `lemxy`)

The Eisenstein series equal their quadratic truncations plus `240`/`-504`/`-24` times the
corresponding tail `R⁽³⁾`. -/

/-- `E₄ = X + δX` with `δX = 240·R₄⁽³⁾` (paper Lemma `lemxy`). -/
lemma E₄_eq_trunc (τ : ℍ) : E₄ τ = E₄trunc τ + 240 * eisensteinTail 3 3 τ := by
  rw [E₄_eq_tsum, tsum_sigma_split 3 τ, E₄trunc, eisensteinTail]
  simp only [show (ArithmeticFunction.sigma 3 1 : ℕ) = 1 from by decide,
    show (ArithmeticFunction.sigma 3 2 : ℕ) = 9 from by decide]
  push_cast; ring

/-- `E₆ = Y + δY` with `δY = -504·R₆⁽³⁾` (paper Lemma `lemxy`). -/
lemma E₆_eq_trunc (τ : ℍ) : E₆ τ = E₆trunc τ - 504 * eisensteinTail 5 3 τ := by
  rw [E₆_eq_tsum, tsum_sigma_split 5 τ, E₆trunc, eisensteinTail]
  simp only [show (ArithmeticFunction.sigma 5 1 : ℕ) = 1 from by decide,
    show (ArithmeticFunction.sigma 5 2 : ℕ) = 33 from by decide]
  push_cast; ring

/-- `E₂* = Z + δZ` with `δZ = -24·R₂⁽³⁾` (paper Lemma `lemxy`). -/
lemma E₂star_eq_trunc (τ : ℍ) : E₂star τ = E₂starTrunc τ - 24 * eisensteinTail 1 3 τ := by
  rw [E₂star, E2_eq_tsum, tsum_sigma_split 1 τ, E₂starTrunc, eisensteinTail]
  simp only [show (ArithmeticFunction.sigma 1 1 : ℕ) = 1 from by decide,
    show (ArithmeticFunction.sigma 1 2 : ℕ) = 3 from by decide]
  push_cast; ring

/-! ### The lower bound for `E₆` (paper Lemma `lemE6`) -/

/-- Bound `‖q τ + a·q τ²‖ ≤ |q| + a·|q|²` for `a ≥ 0`. -/
lemma norm_q_add_smul_sq_le {τ : ℍ} {a : ℝ} (ha : 0 ≤ a) :
    ‖q τ + (a : ℂ) * q τ ^ 2‖ ≤ ‖q τ‖ + a * ‖q τ‖ ^ 2 := by
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ha]

/-- Paper Lemma `lemE6`: `|E₆(τ)| > 0.8` for `Im τ > 5/4`. -/
theorem lemE6 {τ : ℍ} (hτ : τ ∈ Region) : 0.8 < ‖E₆ τ‖ := by
  set Q := ‖q τ‖ with hQdef
  have hQpos : 0 < Q := norm_q_pos τ
  have hQ : Q < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have htail : ‖eisensteinTail 5 3 τ‖ ≤ 245.6 * Q ^ 3 := norm_eisensteinTail_sigma₅ hτ
  have hqq : ‖q τ + (33 : ℂ) * q τ ^ 2‖ ≤ Q + 33 * Q ^ 2 :=
    norm_q_add_smul_sq_le (by norm_num)
  -- reverse triangle inequality
  rw [E₆_eq_trunc τ, E₆trunc]
  have htri : (1 : ℝ) - ‖(504 : ℂ) * (q τ + 33 * q τ ^ 2)‖ - ‖(504 : ℂ) * eisensteinTail 5 3 τ‖
      ≤ ‖1 - 504 * (q τ + 33 * q τ ^ 2) - 504 * eisensteinTail 5 3 τ‖ := by
    calc (1 : ℝ) - ‖(504 : ℂ) * (q τ + 33 * q τ ^ 2)‖ - ‖(504 : ℂ) * eisensteinTail 5 3 τ‖
        = (‖(1 : ℂ)‖ - ‖(504 : ℂ) * (q τ + 33 * q τ ^ 2)‖)
            - ‖(504 : ℂ) * eisensteinTail 5 3 τ‖ := by rw [norm_one]
      _ ≤ ‖(1 : ℂ) - 504 * (q τ + 33 * q τ ^ 2)‖ - ‖(504 : ℂ) * eisensteinTail 5 3 τ‖ := by
          linarith [norm_sub_norm_le (1 : ℂ) (504 * (q τ + 33 * q τ ^ 2))]
      _ ≤ ‖1 - 504 * (q τ + 33 * q τ ^ 2) - 504 * eisensteinTail 5 3 τ‖ :=
          norm_sub_norm_le _ _
  have hA : ‖(504 : ℂ) * (q τ + 33 * q τ ^ 2)‖ ≤ 504 * (Q + 33 * Q ^ 2) := by
    rw [norm_mul, Complex.norm_ofNat]; exact mul_le_mul_of_nonneg_left hqq (by norm_num)
  have hB : ‖(504 : ℂ) * eisensteinTail 5 3 τ‖ ≤ 504 * (245.6 * Q ^ 3) := by
    rw [norm_mul, Complex.norm_ofNat]; exact mul_le_mul_of_nonneg_left htail (by norm_num)
  have hfinal : (0.8 : ℝ) < 1 - 504 * (Q + 33 * Q ^ 2) - 504 * (245.6 * Q ^ 3) := by
    nlinarith [hQpos, hQ, pow_pos hQpos 2, pow_pos hQpos 3]
  linarith [htri, hA, hB, hfinal]

/-- Paper Lemma `lemE6`, "in particular": `E₆(τ) ≠ 0` for `Im τ > 5/4`. -/
theorem E₆_ne_zero_of_mem_Region {τ : ℍ} (hτ : τ ∈ Region) : E₆ τ ≠ 0 := by
  intro h
  have h8 := lemE6 hτ
  rw [h, norm_zero] at h8
  norm_num at h8

/-! ### Truncation norm bounds (paper Lemma `lemxy`) -/

/-- Paper Lemma `lemxy`: `0.8014 ≤ |Y|` where `Y = E₆⁽²⁾`. -/
lemma norm_E₆trunc_ge {τ : ℍ} (hτ : τ ∈ Region) : (0.8014 : ℝ) ≤ ‖E₆trunc τ‖ := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hqq : ‖q τ + (33 : ℂ) * q τ ^ 2‖ ≤ ‖q τ‖ + 33 * ‖q τ‖ ^ 2 :=
    norm_q_add_smul_sq_le (by norm_num)
  rw [E₆trunc]
  have htri : (1 : ℝ) - ‖(504 : ℂ) * (q τ + 33 * q τ ^ 2)‖
      ≤ ‖(1 : ℂ) - 504 * (q τ + 33 * q τ ^ 2)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (504 * (q τ + 33 * q τ ^ 2))
    rwa [norm_one] at this
  have hA : ‖(504 : ℂ) * (q τ + 33 * q τ ^ 2)‖ ≤ 504 * (‖q τ‖ + 33 * ‖q τ‖ ^ 2) := by
    rw [norm_mul, Complex.norm_ofNat]; exact mul_le_mul_of_nonneg_left hqq (by norm_num)
  have hlow : (0.8014 : ℝ) ≤ 1 - 504 * (‖q τ‖ + 33 * ‖q τ‖ ^ 2) := by
    nlinarith [hQpos, hQ, pow_pos hQpos 2]
  linarith [htri, hA, hlow]

lemma E₆trunc_ne_zero {τ : ℍ} (hτ : τ ∈ Region) : E₆trunc τ ≠ 0 := by
  intro h
  have := norm_E₆trunc_ge hτ
  rw [h, norm_zero] at this
  norm_num at this

/-- Paper Lemma `lemxy`: `|X| ≤ 1.0937` where `X = E₄⁽²⁾`. -/
lemma norm_E₄trunc_le {τ : ℍ} (hτ : τ ∈ Region) : ‖E₄trunc τ‖ ≤ 1.0937 := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hqq : ‖q τ + (9 : ℂ) * q τ ^ 2‖ ≤ ‖q τ‖ + 9 * ‖q τ‖ ^ 2 :=
    norm_q_add_smul_sq_le (by norm_num)
  rw [E₄trunc]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_one, norm_mul, Complex.norm_ofNat]
  nlinarith [hqq, hQpos, hQ, pow_pos hQpos 2]

/-- Paper Lemma `lemxy`: `|Z| ≤ 1.0094` where `Z = E₂⁽²⁾ - 3/(π Im τ)`. -/
lemma norm_E₂starTrunc_le {τ : ℍ} (hτ : τ ∈ Region) : ‖E₂starTrunc τ‖ ≤ 1.0094 := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have him : (5 / 4 : ℝ) < τ.im := hτ
  have hpos : 0 < π * τ.im := by positivity
  have ht1 : 3 / (π * τ.im) < 1 := by
    rw [div_lt_one hpos]; nlinarith [Real.pi_gt_three, him]
  have ht0 : 0 < 3 / (π * τ.im) := by positivity
  have hqq : ‖q τ + (3 : ℂ) * q τ ^ 2‖ ≤ ‖q τ‖ + 3 * ‖q τ‖ ^ 2 :=
    norm_q_add_smul_sq_le (by norm_num)
  have hZeq : E₂starTrunc τ = ((1 - 3 / (π * τ.im) : ℝ) : ℂ) - 24 * (q τ + 3 * q τ ^ 2) := by
    rw [E₂starTrunc]; push_cast; ring
  rw [hZeq]
  refine le_trans (norm_sub_le _ _) ?_
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_ofNat]
  have habs : |1 - 3 / (π * τ.im)| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [ht0, ht1]
  nlinarith [habs, hqq, hQpos, hQ, pow_pos hQpos 2]

/-- Paper: `|stilde₂| ≤ 1.3776`. -/
lemma norm_s₂tilde_le {τ : ℍ} (hτ : τ ∈ Region) : ‖s₂tilde τ‖ ≤ 1.3776 := by
  rw [s₂tilde_eq, norm_mul, norm_div]
  have hX := norm_E₄trunc_le hτ
  have hY := norm_E₆trunc_ge hτ
  have hZ := norm_E₂starTrunc_le hτ
  have hYpos : (0 : ℝ) < ‖E₆trunc τ‖ := by linarith [hY]
  have hdiv : ‖E₄trunc τ‖ / ‖E₆trunc τ‖ ≤ 1.0937 / 0.8014 :=
    div_le_div₀ (by norm_num) hX (by norm_num) hY
  have hdivnn : 0 ≤ ‖E₄trunc τ‖ / ‖E₆trunc τ‖ := by positivity
  calc ‖E₄trunc τ‖ / ‖E₆trunc τ‖ * ‖E₂starTrunc τ‖
      ≤ (1.0937 / 0.8014) * 1.0094 :=
        mul_le_mul hdiv hZ (norm_nonneg _) (by norm_num)
    _ ≤ 1.3776 := by norm_num

/-- `|δX| = |E₄ - X| ≤ 6744·|q|³`. -/
lemma norm_sub_E₄trunc_le {τ : ℍ} (hτ : τ ∈ Region) :
    ‖E₄ τ - E₄trunc τ‖ ≤ 6744 * ‖q τ‖ ^ 3 := by
  have heq : E₄ τ - E₄trunc τ = 240 * eisensteinTail 3 3 τ := by rw [E₄_eq_trunc τ]; ring
  rw [heq, norm_mul, Complex.norm_ofNat]
  nlinarith [norm_eisensteinTail_sigma₃ hτ, norm_nonneg (eisensteinTail 3 3 τ)]

/-- `|δY| = |E₆ - Y| ≤ 123783·|q|³`. -/
lemma norm_sub_E₆trunc_le {τ : ℍ} (hτ : τ ∈ Region) :
    ‖E₆ τ - E₆trunc τ‖ ≤ 123783 * ‖q τ‖ ^ 3 := by
  have heq : E₆ τ - E₆trunc τ = -(504 * eisensteinTail 5 3 τ) := by rw [E₆_eq_trunc τ]; ring
  rw [heq, norm_neg, norm_mul, Complex.norm_ofNat]
  nlinarith [norm_eisensteinTail_sigma₅ hτ, norm_nonneg (eisensteinTail 5 3 τ)]

/-- `|δZ| = |E₂* - Z| ≤ 96.2·|q|³`. -/
lemma norm_sub_E₂starTrunc_le {τ : ℍ} (hτ : τ ∈ Region) :
    ‖E₂star τ - E₂starTrunc τ‖ ≤ 96.2 * ‖q τ‖ ^ 3 := by
  have heq : E₂star τ - E₂starTrunc τ = -(24 * eisensteinTail 1 3 τ) := by
    rw [E₂star_eq_trunc τ]; ring
  rw [heq, norm_neg, norm_mul, Complex.norm_ofNat]
  nlinarith [norm_eisensteinTail_sigma₁ hτ, norm_nonneg (eisensteinTail 1 3 τ)]

/-! ### Klein's `k` and its truncation `ktilde` (paper Lemma `lemk`) -/

/-- The analytic function `k(τ) = (E₄³ - E₆²)/(1728·q) = Δ/q` (paper Lemma `lemk`). -/
def kfun (τ : ℍ) : ℂ := (E₄ τ ^ 3 - E₆ τ ^ 2) / (1728 * q τ)

/-- The truncation `ktilde(τ) = (1 - q - q²)²⁴` (paper Lemma `lemk`). -/
def ktilde (τ : ℍ) : ℂ := (1 - q τ - q τ ^ 2) ^ 24

lemma q_ne_zero (τ : ℍ) : q τ ≠ 0 := norm_pos_iff.mp (norm_q_pos τ)

/-- `1728·q·J = E₄³ / k`. -/
lemma mul_q_J_eq (τ : ℍ) : 1728 * q τ * J τ = E₄ τ ^ 3 / kfun τ := by
  rw [J, kfun]
  have h1 := E₄_cube_sub_E₆_sq_ne_zero τ
  have h2 := q_ne_zero τ
  field_simp

/-- Bound `1 - |q| - |q|² ≤ ‖1 - q - q²‖ ≤ 1 + |q| + |q|²`. -/
lemma norm_one_sub_q_sub_sq {τ : ℍ} :
    1 - ‖q τ‖ - ‖q τ‖ ^ 2 ≤ ‖1 - q τ - q τ ^ 2‖
      ∧ ‖1 - q τ - q τ ^ 2‖ ≤ 1 + ‖q τ‖ + ‖q τ‖ ^ 2 := by
  have hqq : ‖q τ + q τ ^ 2‖ ≤ ‖q τ‖ + ‖q τ‖ ^ 2 := by
    refine le_trans (norm_add_le _ _) ?_; rw [norm_pow]
  have heq : (1 : ℂ) - q τ - q τ ^ 2 = 1 - (q τ + q τ ^ 2) := by ring
  rw [heq]
  constructor
  · have := norm_sub_norm_le (1 : ℂ) (q τ + q τ ^ 2)
    rw [norm_one] at this; linarith
  · refine le_trans (norm_sub_le _ _) ?_; rw [norm_one]; linarith

/-- Paper Lemma `lemk`: `0.9907 ≤ |ktilde|`. -/
lemma norm_ktilde_ge {τ : ℍ} (hτ : τ ∈ Region) : (0.9907 : ℝ) ≤ ‖ktilde τ‖ := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  rw [ktilde, norm_pow]
  have hlow : (0.9996108 : ℝ) ≤ ‖1 - q τ - q τ ^ 2‖ := by
    have h := (norm_one_sub_q_sub_sq (τ := τ)).1
    nlinarith [h, hQ, mul_pos hQpos (sub_pos.mpr hQ)]
  calc (0.9907 : ℝ) ≤ 0.9996108 ^ 24 := by norm_num
    _ ≤ ‖1 - q τ - q τ ^ 2‖ ^ 24 := pow_le_pow_left₀ (by norm_num) hlow 24

/-- Paper Lemma `lemk`: `|ktilde| ≤ 1.0094`. -/
lemma norm_ktilde_le {τ : ℍ} (hτ : τ ∈ Region) : ‖ktilde τ‖ ≤ 1.0094 := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  rw [ktilde, norm_pow]
  have hhi : ‖1 - q τ - q τ ^ 2‖ ≤ 1.0003892 := by
    have h := (norm_one_sub_q_sub_sq (τ := τ)).2
    nlinarith [h, hQ, mul_pos hQpos (sub_pos.mpr hQ)]
  calc ‖1 - q τ - q τ ^ 2‖ ^ 24 ≤ (1.0003892 : ℝ) ^ 24 :=
        pow_le_pow_left₀ (norm_nonneg _) hhi 24
    _ ≤ 1.0094 := by norm_num

lemma ktilde_ne_zero {τ : ℍ} (hτ : τ ∈ Region) : ktilde τ ≠ 0 := by
  intro h
  have := norm_ktilde_ge hτ
  rw [h, norm_zero] at this
  norm_num at this

/-- `1728·q·Jtilde = X³ / ktilde`. -/
lemma mul_q_Jtilde_eq {τ : ℍ} (hτ : τ ∈ Region) :
    1728 * q τ * Jtilde τ = E₄trunc τ ^ 3 / ktilde τ := by
  have h2 := q_ne_zero τ
  have h3 := ktilde_ne_zero hτ
  rw [Jtilde, ktilde, E₄trunc] at *
  field_simp

/-- Paper Lemma `lemxy`: `|E₄³ - X³| ≤ 24202·|q|³` (moved above `lemk`, which consumes it). -/
lemma norm_sub_cube_E₄trunc_le {τ : ℍ} (hτ : τ ∈ Region) :
    ‖E₄ τ ^ 3 - E₄trunc τ ^ 3‖ ≤ 24202 * ‖q τ‖ ^ 3 := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hX := norm_E₄trunc_le hτ
  have hdX := norm_sub_E₄trunc_le hτ
  have hXnn := norm_nonneg (E₄trunc τ)
  have hdXnn := norm_nonneg (E₄ τ - E₄trunc τ)
  have hQ3 : ‖q τ‖ ^ 3 < 0.000389 ^ 3 := pow_lt_pow_left₀ hQ hQpos.le (by norm_num)
  have heq : E₄ τ ^ 3 - E₄trunc τ ^ 3
      = (E₄ τ - E₄trunc τ) * (3 * E₄trunc τ ^ 2
          + 3 * E₄trunc τ * (E₄ τ - E₄trunc τ) + (E₄ τ - E₄trunc τ) ^ 2) := by ring
  rw [heq, norm_mul]
  have hfac : ‖3 * E₄trunc τ ^ 2 + 3 * E₄trunc τ * (E₄ τ - E₄trunc τ)
        + (E₄ τ - E₄trunc τ) ^ 2‖
      ≤ 3 * ‖E₄trunc τ‖ ^ 2 + 3 * ‖E₄trunc τ‖ * ‖E₄ τ - E₄trunc τ‖
        + ‖E₄ τ - E₄trunc τ‖ ^ 2 := by
    refine le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _)
      (add_le_add ?_ ?_)) ?_)
    · rw [norm_mul, norm_pow, Complex.norm_ofNat]
    · rw [norm_mul, norm_mul, Complex.norm_ofNat]
    · rw [norm_pow]
  have hfac2 : ‖3 * E₄trunc τ ^ 2 + 3 * E₄trunc τ * (E₄ τ - E₄trunc τ)
        + (E₄ τ - E₄trunc τ) ^ 2‖ ≤ 3.5886 := by
    refine le_trans hfac ?_
    nlinarith [hX, hdX, hXnn, hdXnn, hQ3, pow_pos hQpos 3]
  calc ‖E₄ τ - E₄trunc τ‖ * ‖3 * E₄trunc τ ^ 2 + 3 * E₄trunc τ * (E₄ τ - E₄trunc τ)
        + (E₄ τ - E₄trunc τ) ^ 2‖
      ≤ (6744 * ‖q τ‖ ^ 3) * 3.5886 := mul_le_mul hdX hfac2 (norm_nonneg _) (by norm_num)
    _ ≤ 24202 * ‖q τ‖ ^ 3 := by nlinarith [pow_pos hQpos 3]

/-- Paper Lemma `lemxy`: `|Y| ≤ 1.1987` where `Y = E₆⁽²⁾`. -/
lemma norm_E₆trunc_le {τ : ℍ} (hτ : τ ∈ Region) : ‖E₆trunc τ‖ ≤ 1.1987 := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hqq : ‖q τ + (33 : ℂ) * q τ ^ 2‖ ≤ ‖q τ‖ + 33 * ‖q τ‖ ^ 2 :=
    norm_q_add_smul_sq_le (by norm_num)
  rw [E₆trunc]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_one, norm_mul, Complex.norm_ofNat]
  nlinarith [hqq, hQpos, hQ, pow_pos hQpos 2]

/-- `|E₆² - Y²| ≤ 296780·|q|³` (paper Lemma `lemk`, the `|E₆²-Y²|/(1728q)` term). -/
lemma norm_sub_sq_E₆trunc_le {τ : ℍ} (hτ : τ ∈ Region) :
    ‖E₆ τ ^ 2 - E₆trunc τ ^ 2‖ ≤ 296780 * ‖q τ‖ ^ 3 := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hY := norm_E₆trunc_le hτ
  have hdY := norm_sub_E₆trunc_le hτ
  have hQ3 : ‖q τ‖ ^ 3 < 0.000389 ^ 3 := pow_lt_pow_left₀ hQ hQpos.le (by norm_num)
  have heq : E₆ τ ^ 2 - E₆trunc τ ^ 2
      = (E₆ τ - E₆trunc τ) * (2 * E₆trunc τ + (E₆ τ - E₆trunc τ)) := by ring
  rw [heq, norm_mul]
  have hfac : ‖2 * E₆trunc τ + (E₆ τ - E₆trunc τ)‖
      ≤ 2 * ‖E₆trunc τ‖ + ‖E₆ τ - E₆trunc τ‖ := by
    have h := norm_add_le (2 * E₆trunc τ) (E₆ τ - E₆trunc τ)
    rwa [norm_mul, Complex.norm_ofNat] at h
  have hfac2 : ‖2 * E₆trunc τ + (E₆ τ - E₆trunc τ)‖ ≤ 2.3975 := by
    refine le_trans hfac ?_
    nlinarith [hY, hdY, hQ3, pow_pos hQpos 3]
  calc ‖E₆ τ - E₆trunc τ‖ * ‖2 * E₆trunc τ + (E₆ τ - E₆trunc τ)‖
      ≤ (123783 * ‖q τ‖ ^ 3) * 2.3975 := mul_le_mul hdY hfac2 (norm_nonneg _) (by positivity)
    _ ≤ 296780 * ‖q τ‖ ^ 3 := by nlinarith [pow_pos hQpos 3]

/-- Horner-form norm bound: for `‖p‖ ≤ ρ` (`0 ≤ ρ`), the norm of a polynomial
`∑ⱼ cⱼ·pʲ` (written in Horner form via `List.foldr`) is bounded by the same fold
with `|cⱼ|` and `ρ`. Used to bound the degree-46 polynomial remainder in `lemk`. -/
lemma horner_norm_bound (p : ℂ) {ρ : ℝ} (hp : ‖p‖ ≤ ρ) (hρ : 0 ≤ ρ) :
    ∀ l : List ℤ,
      ‖l.foldr (fun (a : ℤ) (acc : ℂ) => (a : ℂ) + p * acc) 0‖
        ≤ l.foldr (fun (a : ℤ) (acc : ℝ) => |(a : ℝ)| + ρ * acc) 0 := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.foldr_cons, List.foldr_cons]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_intCast, norm_mul]
    have hstep : ‖p‖ * ‖t.foldr (fun (a : ℤ) (acc : ℂ) => (a : ℂ) + p * acc) 0‖
        ≤ ρ * t.foldr (fun (a : ℤ) (acc : ℝ) => |(a : ℝ)| + ρ * acc) 0 :=
      le_trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
        (mul_le_mul_of_nonneg_left ih hρ)
    linarith

/-- Coefficients (ascending) of the degree-46 polynomial `G` in the exact identity
`X³ - Y² - 1728·q·(1-q-q²)²⁴ = 1728·q³·G(q)`, used in `lemk`. -/
def lemkG : List ℤ :=
  [-154, 65489, 1939170, 5838072, 16192, -78936, 82731, 212520, -649704, 73416,
   1977862, -2034672, -3487260, 7072408, 3432198, -15343944, -134596, 25077360,
   -6067446, -33474936, 12286968, 38228232, -14903725, -38228232, 12286968, 33474936,
   -6067446, -25077360, -134596, 15343944, 3432198, -7072408, -3487260, 2034672,
   1977862, -73416, -649704, -212520, 82731, 78936, 16192, -6072, -4830, -1472,
   -252, -24, -1]

/-- **Paper Lemma `lemk`** (the one analytic input still admitted): the difference between
Klein's `k = Δ/q` and its truncation `ktilde = (1-q-q²)²⁴` is `O(|q|²)`:
`|k - ktilde| ≤ 365.6·|q|²`.

Milla proves this by Taylor-expanding `(1-q-q²)²⁴` to second order (bounding the third
derivative) and comparing with the explicit expansion of `(X³-Y²)/(1728q)`; the sharper
`|k - ktilde| < 25|q|⁵` needs Euler's pentagonal number theorem. Here we instead use the exact
polynomial identity `X³ - Y² - 1728·q·(1-q-q²)²⁴ = 1728·q³·G(q)` (`G` of degree 46, with
`|G(q)| ≤ 179.8` bounded via `horner_norm_bound`), together with the truncation-error
estimates `|E₄³-X³| ≤ 24202|q|³` and `|E₆²-Y²| ≤ 296780|q|³`. -/
lemma lemk {τ : ℍ} (hτ : τ ∈ Region) : ‖kfun τ - ktilde τ‖ ≤ 365.6 * ‖q τ‖ ^ 2 := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hqne : q τ ≠ 0 := q_ne_zero τ
  have hq2 : (1728 : ℂ) * q τ ≠ 0 := mul_ne_zero (by norm_num) hqne
  set Gval : ℂ := lemkG.foldr (fun (a : ℤ) (acc : ℂ) => (a : ℂ) + q τ * acc) 0 with hGvaldef
  -- (a) exact polynomial identity for the "truncation" part
  have hpoly : E₄trunc τ ^ 3 - E₆trunc τ ^ 2 - 1728 * q τ * ktilde τ
      = 1728 * q τ ^ 3 * Gval := by
    rw [E₄trunc, E₆trunc, ktilde, hGvaldef]
    simp only [lemkG, List.foldr_cons, List.foldr_nil]
    push_cast; ring
  -- (b) bound on ‖G(q)‖
  have hGbound : ‖Gval‖ ≤ 179.8 := by
    rw [hGvaldef]
    refine le_trans (horner_norm_bound (q τ) hQ.le (by norm_num) lemkG) ?_
    simp only [lemkG, List.foldr_cons, List.foldr_nil]
    push_cast; norm_num
  -- (c) rewrite `k - ktilde` as a single quotient over `1728 q`
  have hid : kfun τ - ktilde τ
      = ((E₄ τ ^ 3 - E₄trunc τ ^ 3) - (E₆ τ ^ 2 - E₆trunc τ ^ 2)
          + 1728 * q τ ^ 3 * Gval) / (1728 * q τ) := by
    rw [← hpoly, kfun]
    field_simp
    ring
  rw [hid, norm_div]
  have hden : ‖(1728 : ℂ) * q τ‖ = 1728 * ‖q τ‖ := by rw [norm_mul, Complex.norm_ofNat]
  rw [hden, div_le_iff₀ (by positivity)]
  -- (d) bound the numerator by the three pieces of the paper's proof
  have hp1 : ‖E₄ τ ^ 3 - E₄trunc τ ^ 3‖ ≤ 24202 * ‖q τ‖ ^ 3 := norm_sub_cube_E₄trunc_le hτ
  have hp2 : ‖E₆ τ ^ 2 - E₆trunc τ ^ 2‖ ≤ 296780 * ‖q τ‖ ^ 3 := norm_sub_sq_E₆trunc_le hτ
  have hp3 : ‖(1728 : ℂ) * q τ ^ 3 * Gval‖ ≤ 1728 * ‖q τ‖ ^ 3 * 179.8 := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_pow]
    exact mul_le_mul_of_nonneg_left hGbound (by positivity)
  have hnum : ‖(E₄ τ ^ 3 - E₄trunc τ ^ 3) - (E₆ τ ^ 2 - E₆trunc τ ^ 2)
        + 1728 * q τ ^ 3 * Gval‖
      ≤ 24202 * ‖q τ‖ ^ 3 + 296780 * ‖q τ‖ ^ 3 + 1728 * ‖q τ‖ ^ 3 * 179.8 :=
    le_trans (norm_add_le _ _)
      (add_le_add (le_trans (norm_sub_le _ _) (add_le_add hp1 hp2)) hp3)
  have hR : (365.6 : ℝ) * ‖q τ‖ ^ 2 * (1728 * ‖q τ‖) = 631756.8 * ‖q τ‖ ^ 3 := by ring
  rw [hR]
  refine le_trans hnum ?_
  nlinarith [pow_pos hQpos 3]

/-- `0.9907 - 365.6|q|² ≤ |k|` (paper: `|k| ≥ |ktilde| - |δktilde|`). -/
lemma norm_kfun_ge {τ : ℍ} (hτ : τ ∈ Region) :
    0.9907 - 365.6 * ‖q τ‖ ^ 2 ≤ ‖kfun τ‖ := by
  have h1 := norm_ktilde_ge hτ
  have h2 := lemk hτ
  have h3 := norm_sub_norm_le (ktilde τ) (ktilde τ - kfun τ)
  have h4 : ‖ktilde τ - kfun τ‖ = ‖kfun τ - ktilde τ‖ := norm_sub_rev _ _
  have h5 : ktilde τ - (ktilde τ - kfun τ) = kfun τ := by ring
  rw [h5] at h3
  rw [h4] at h3
  linarith [h1, h2, h3]

lemma kfun_ne_zero {τ : ℍ} (hτ : τ ∈ Region) : kfun τ ≠ 0 := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have h := norm_kfun_ge hτ
  have : 0 < ‖kfun τ‖ := by nlinarith [h, hQ, mul_pos hQpos (sub_pos.mpr hQ)]
  exact norm_pos_iff.mp this

/-- Paper Lemma `lemxy`: `0.9063 ≤ |X|` where `X = E₄⁽²⁾`. -/
lemma norm_E₄trunc_ge {τ : ℍ} (hτ : τ ∈ Region) : (0.9063 : ℝ) ≤ ‖E₄trunc τ‖ := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hqq : ‖q τ + (9 : ℂ) * q τ ^ 2‖ ≤ ‖q τ‖ + 9 * ‖q τ‖ ^ 2 :=
    norm_q_add_smul_sq_le (by norm_num)
  rw [E₄trunc]
  have htri : (1 : ℝ) - ‖(240 : ℂ) * (q τ + 9 * q τ ^ 2)‖
      ≤ ‖(1 : ℂ) + 240 * (q τ + 9 * q τ ^ 2)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(240 * (q τ + 9 * q τ ^ 2)))
    rw [norm_one, norm_neg, sub_neg_eq_add] at this; exact this
  have hA : ‖(240 : ℂ) * (q τ + 9 * q τ ^ 2)‖ ≤ 240 * (‖q τ‖ + 9 * ‖q τ‖ ^ 2) := by
    rw [norm_mul, Complex.norm_ofNat]; exact mul_le_mul_of_nonneg_left hqq (by norm_num)
  have hlow : (0.9063 : ℝ) ≤ 1 - 240 * (‖q τ‖ + 9 * ‖q τ‖ ^ 2) := by
    nlinarith [hQpos, hQ, pow_pos hQpos 2]
  linarith [htri, hA, hlow]

/-- Paper Lemma `lem3`: `|Jtilde₂| ≤ 1.3206` where `Jtilde₂ = X³/ktilde`. -/
lemma norm_Jtilde2_le {τ : ℍ} (hτ : τ ∈ Region) :
    ‖E₄trunc τ ^ 3 / ktilde τ‖ ≤ 1.3206 := by
  rw [norm_div, norm_pow]
  have hX := norm_E₄trunc_le hτ
  have hk := norm_ktilde_ge hτ
  have h1 : ‖E₄trunc τ‖ ^ 3 ≤ 1.0937 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hX 3
  calc ‖E₄trunc τ‖ ^ 3 / ‖ktilde τ‖ ≤ 1.0937 ^ 3 / 0.9907 :=
        div_le_div₀ (by norm_num) h1 (by norm_num) hk
    _ ≤ 1.3206 := by norm_num

/-- Paper Lemma `lem3`: `0.7374 ≤ |Jtilde₂|` where `Jtilde₂ = X³/ktilde`. -/
lemma norm_Jtilde2_ge {τ : ℍ} (hτ : τ ∈ Region) :
    (0.7374 : ℝ) ≤ ‖E₄trunc τ ^ 3 / ktilde τ‖ := by
  rw [norm_div, norm_pow]
  have hX := norm_E₄trunc_ge hτ
  have hk := norm_ktilde_le hτ
  have hkpos : (0 : ℝ) < ‖ktilde τ‖ := by linarith [norm_ktilde_ge hτ]
  have h1 : (0.9063 : ℝ) ^ 3 ≤ ‖E₄trunc τ‖ ^ 3 := pow_le_pow_left₀ (by norm_num) hX 3
  calc (0.7374 : ℝ) ≤ 0.9063 ^ 3 / 1.0094 := by norm_num
    _ ≤ ‖E₄trunc τ‖ ^ 3 / ‖ktilde τ‖ := div_le_div₀ (by positivity) h1 hkpos hk

/-- Paper Lemma `lem3`: `|J₂ - Jtilde₂| ≤ 498·|q|²`. -/
lemma lem3 {τ : ℍ} (hτ : τ ∈ Region) :
    ‖1728 * q τ * J τ - 1728 * q τ * Jtilde τ‖ ≤ 498 * ‖q τ‖ ^ 2 := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hkf := kfun_ne_zero hτ
  have hkt := ktilde_ne_zero hτ
  have hid2 : 1728 * q τ * J τ - 1728 * q τ * Jtilde τ
      = (E₄ τ ^ 3 - E₄trunc τ ^ 3
          - (E₄trunc τ ^ 3 / ktilde τ) * (kfun τ - ktilde τ)) / kfun τ := by
    rw [mul_q_J_eq, mul_q_Jtilde_eq hτ]
    field_simp
    ring
  have hkfpos : (0 : ℝ) < ‖kfun τ‖ := norm_pos_iff.mpr hkf
  rw [hid2, norm_div, div_le_iff₀ hkfpos]
  have hcube := norm_sub_cube_E₄trunc_le hτ
  have hjt := norm_Jtilde2_le hτ
  have hlemk := lemk hτ
  have hkfg := norm_kfun_ge hτ
  have hnum : ‖E₄ τ ^ 3 - E₄trunc τ ^ 3
        - E₄trunc τ ^ 3 / ktilde τ * (kfun τ - ktilde τ)‖
      ≤ 24202 * ‖q τ‖ ^ 3 + 1.3206 * (365.6 * ‖q τ‖ ^ 2) := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul]
    gcongr
  have hQ3 : ‖q τ‖ ^ 3 ≤ 0.000389 * ‖q τ‖ ^ 2 := by
    nlinarith [hQ, pow_pos hQpos 2, hQpos]
  have hQ4 : ‖q τ‖ ^ 2 * ‖q τ‖ ^ 2 ≤ 0.000389 ^ 2 * ‖q τ‖ ^ 2 := by
    nlinarith [hQ, pow_pos hQpos 2, hQpos, mul_pos hQpos hQpos]
  nlinarith [hnum, hkfg, hQ3, hQ4, pow_pos hQpos 2, mul_pos (pow_pos hQpos 2) hkfpos]

/-! ### Theorem `theonaeherJ` -/

/-- `|J₂| = |1728·q·J| ≤ 1.3206 + 498|q|²` (paper: `|J₂| ≤ |Jtilde₂| + |δJtilde₂|`). -/
lemma norm_mul_q_J_le {τ : ℍ} (hτ : τ ∈ Region) :
    ‖1728 * q τ * J τ‖ ≤ 1.3206 + 498 * ‖q τ‖ ^ 2 := by
  have h1 : 1728 * q τ * J τ
      = 1728 * q τ * Jtilde τ + (1728 * q τ * J τ - 1728 * q τ * Jtilde τ) := by ring
  calc ‖1728 * q τ * J τ‖
      = ‖1728 * q τ * Jtilde τ + (1728 * q τ * J τ - 1728 * q τ * Jtilde τ)‖ := by rw [← h1]
    _ ≤ ‖1728 * q τ * Jtilde τ‖ + ‖1728 * q τ * J τ - 1728 * q τ * Jtilde τ‖ := norm_add_le _ _
    _ ≤ 1.3206 + 498 * ‖q τ‖ ^ 2 := by
        have ht1 : ‖1728 * q τ * Jtilde τ‖ ≤ 1.3206 := by
          rw [mul_q_Jtilde_eq hτ]; exact norm_Jtilde2_le hτ
        exact add_le_add ht1 (lem3 hτ)

/-- `0.7374 - 498|q|² ≤ |J₂| = |1728·q·J|` (paper: `|J₂| ≥ |Jtilde₂| - |δJtilde₂|`). -/
lemma norm_mul_q_J_ge {τ : ℍ} (hτ : τ ∈ Region) :
    0.7374 - 498 * ‖q τ‖ ^ 2 ≤ ‖1728 * q τ * J τ‖ := by
  have h1 := norm_sub_norm_le (1728 * q τ * Jtilde τ)
    (1728 * q τ * Jtilde τ - 1728 * q τ * J τ)
  have h2 : 1728 * q τ * Jtilde τ - (1728 * q τ * Jtilde τ - 1728 * q τ * J τ)
      = 1728 * q τ * J τ := by ring
  rw [h2] at h1
  have h3 : ‖1728 * q τ * Jtilde τ - 1728 * q τ * J τ‖
      = ‖1728 * q τ * J τ - 1728 * q τ * Jtilde τ‖ := norm_sub_rev _ _
  rw [h3] at h1
  have hjt : ‖1728 * q τ * Jtilde τ‖ = ‖E₄trunc τ ^ 3 / ktilde τ‖ := by rw [mul_q_Jtilde_eq hτ]
  rw [hjt] at h1
  linarith [h1, norm_Jtilde2_ge hτ, lem3 hτ]

/-- Paper Theorem `theonaeherJ`, approximation bound in the sharper `500·|q|` form:
`|1728·J(τ) - 1728·Jtilde(τ)| < 500·|q|` for `Im τ > 5/4`. -/
theorem theonaeherJ_approx {τ : ℍ} (hτ : τ ∈ Region) :
    ‖1728 * J τ - 1728 * Jtilde τ‖ < 500 * ‖q τ‖ := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hq := q_ne_zero τ
  have heq : 1728 * J τ - 1728 * Jtilde τ
      = (1728 * q τ * J τ - 1728 * q τ * Jtilde τ) / q τ := by rw [eq_div_iff hq]; ring
  rw [heq, norm_div, div_lt_iff₀ hQpos]
  nlinarith [lem3 hτ, pow_pos hQpos 2, hQpos]

/-- Paper Theorem `theonaeherJ`, headline approximation bound:
`|1728·J(τ) - 1728·Jtilde(τ)| < 0.2` for `Im τ > 5/4`. -/
theorem theonaeherJ {τ : ℍ} (hτ : τ ∈ Region) :
    ‖1728 * J τ - 1728 * Jtilde τ‖ < 0.2 := by
  have h := theonaeherJ_approx hτ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  linarith [h, hQ]

/-- Paper Theorem `theonaeherJ`, lower bracketing:
`0.737/|q| < |1728·J(τ)|` for `Im τ > 5/4`. -/
theorem theonaeherJ_lower {τ : ℍ} (hτ : τ ∈ Region) :
    0.737 / ‖q τ‖ < ‖1728 * J τ‖ := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hq := q_ne_zero τ
  have heq : 1728 * J τ = (1728 * q τ * J τ) / q τ := by rw [eq_div_iff hq]; ring
  rw [heq, norm_div, div_lt_div_iff₀ hQpos hQpos]
  have hlow := norm_mul_q_J_ge hτ
  have hQsq : ‖q τ‖ ^ 2 < 0.000389 ^ 2 := pow_lt_pow_left₀ hQ hQpos.le (by norm_num)
  nlinarith [hlow, hQsq, hQpos, pow_pos hQpos 2]

/-- Paper Theorem `theonaeherJ`, upper bracketing:
`|1728·J(τ)| < 1.321/|q|` for `Im τ > 5/4`. -/
theorem theonaeherJ_upper {τ : ℍ} (hτ : τ ∈ Region) :
    ‖1728 * J τ‖ < 1.321 / ‖q τ‖ := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hq := q_ne_zero τ
  have heq : 1728 * J τ = (1728 * q τ * J τ) / q τ := by rw [eq_div_iff hq]; ring
  rw [heq, norm_div, div_lt_div_iff₀ hQpos hQpos]
  have hup := norm_mul_q_J_le hτ
  have hQsq : ‖q τ‖ ^ 2 < 0.000389 ^ 2 := pow_lt_pow_left₀ hQ hQpos.le (by norm_num)
  nlinarith [hup, hQsq, hQpos, pow_pos hQpos 2]

/-- Paper Theorem `theonaeherJ`: `|J(τ)| > 1.096` for `Im τ > 5/4`. -/
theorem theonaeherJ_norm_J {τ : ℍ} (hτ : τ ∈ Region) : 1.096 < ‖J τ‖ := by
  have hQpos : 0 < ‖q τ‖ := norm_q_pos τ
  have hQ : ‖q τ‖ < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hq := q_ne_zero τ
  have heq : J τ = (1728 * q τ * J τ) / (1728 * q τ) := by
    rw [eq_div_iff (by simp [hq] : (1728 : ℂ) * q τ ≠ 0)]; ring
  rw [heq, norm_div]
  have hd : ‖(1728 : ℂ) * q τ‖ = 1728 * ‖q τ‖ := by rw [norm_mul, Complex.norm_ofNat]
  rw [show (1728 : ℂ) * q τ * J τ = 1728 * q τ * J τ from rfl, hd, lt_div_iff₀ (by positivity)]
  have hlow := norm_mul_q_J_ge hτ
  have hQsq : ‖q τ‖ ^ 2 < 0.000389 ^ 2 := pow_lt_pow_left₀ hQ hQpos.le (by norm_num)
  nlinarith [hlow, hQsq, hQ, hQpos, pow_pos hQpos 2]

/-- `|J(τ)| > 1` for `Im τ > 5/4`; in particular `J(τ) ≠ 0` and `J(τ) ≠ 1` there. -/
theorem one_lt_norm_J {τ : ℍ} (hτ : τ ∈ Region) : 1 < ‖J τ‖ :=
  lt_trans (by norm_num) (theonaeherJ_norm_J hτ)

/-! ### Theorem `theonaehers2` -/


/-- Paper Theorem `theonaehers2`: `|s₂(τ) - stilde₂(τ)| < 222000·|q|³` for `Im τ > 5/4`. -/
theorem theonaehers2 {τ : ℍ} (hτ : τ ∈ Region) :
    ‖s₂ τ - s₂tilde τ‖ < 222000 * ‖q τ‖ ^ 3 := by
  set Q := ‖q τ‖ with hQdef
  have hQpos : 0 < Q := norm_q_pos τ
  have hQ : Q < 0.000389 := lt_trans (norm_q_lt_of_mem_Region hτ) exp_neg_bound
  have hE6 : E₆ τ ≠ 0 := E₆_ne_zero_of_mem_Region hτ
  have hE6norm : 0.8 < ‖E₆ τ‖ := lemE6 hτ
  have hYne : E₆trunc τ ≠ 0 := E₆trunc_ne_zero hτ
  have hX := norm_E₄trunc_le hτ
  have hZ := norm_E₂starTrunc_le hτ
  have hst := norm_s₂tilde_le hτ
  have hdX := norm_sub_E₄trunc_le hτ
  have hdY := norm_sub_E₆trunc_le hτ
  have hdZ := norm_sub_E₂starTrunc_le hτ
  -- the error formula δstilde₂ = (δX·Z + X·δZ + δX·δZ - stilde₂·δY)/E₆
  have hid : s₂ τ - s₂tilde τ =
      ((E₄ τ - E₄trunc τ) * E₂starTrunc τ + E₄trunc τ * (E₂star τ - E₂starTrunc τ)
        + (E₄ τ - E₄trunc τ) * (E₂star τ - E₂starTrunc τ)
        - s₂tilde τ * (E₆ τ - E₆trunc τ)) / E₆ τ := by
    simp only [s₂, s₂tilde_eq]
    field_simp
    ring
  rw [hid, norm_div]
  rw [div_lt_iff₀ (by linarith [hE6norm] : (0 : ℝ) < ‖E₆ τ‖)]
  have hnum : ‖(E₄ τ - E₄trunc τ) * E₂starTrunc τ + E₄trunc τ * (E₂star τ - E₂starTrunc τ)
        + (E₄ τ - E₄trunc τ) * (E₂star τ - E₂starTrunc τ)
        - s₂tilde τ * (E₆ τ - E₆trunc τ)‖
      ≤ ‖E₄ τ - E₄trunc τ‖ * ‖E₂starTrunc τ‖ + ‖E₄trunc τ‖ * ‖E₂star τ - E₂starTrunc τ‖
        + ‖E₄ τ - E₄trunc τ‖ * ‖E₂star τ - E₂starTrunc τ‖
        + ‖s₂tilde τ‖ * ‖E₆ τ - E₆trunc τ‖ := by
    have key : ‖(E₄ τ - E₄trunc τ) * E₂starTrunc τ + E₄trunc τ * (E₂star τ - E₂starTrunc τ)
        + (E₄ τ - E₄trunc τ) * (E₂star τ - E₂starTrunc τ)
        - s₂tilde τ * (E₆ τ - E₆trunc τ)‖
        ≤ ‖(E₄ τ - E₄trunc τ) * E₂starTrunc τ‖ + ‖E₄trunc τ * (E₂star τ - E₂starTrunc τ)‖
          + ‖(E₄ τ - E₄trunc τ) * (E₂star τ - E₂starTrunc τ)‖
          + ‖s₂tilde τ * (E₆ τ - E₆trunc τ)‖ := by
      calc ‖_ + _ + _ - s₂tilde τ * (E₆ τ - E₆trunc τ)‖
          ≤ ‖(E₄ τ - E₄trunc τ) * E₂starTrunc τ + E₄trunc τ * (E₂star τ - E₂starTrunc τ)
              + (E₄ τ - E₄trunc τ) * (E₂star τ - E₂starTrunc τ)‖
            + ‖s₂tilde τ * (E₆ τ - E₆trunc τ)‖ := norm_sub_le _ _
        _ ≤ (‖(E₄ τ - E₄trunc τ) * E₂starTrunc τ + E₄trunc τ * (E₂star τ - E₂starTrunc τ)‖
              + ‖(E₄ τ - E₄trunc τ) * (E₂star τ - E₂starTrunc τ)‖)
            + ‖s₂tilde τ * (E₆ τ - E₆trunc τ)‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ((‖(E₄ τ - E₄trunc τ) * E₂starTrunc τ‖ + ‖E₄trunc τ * (E₂star τ - E₂starTrunc τ)‖)
              + ‖(E₄ τ - E₄trunc τ) * (E₂star τ - E₂starTrunc τ)‖)
            + ‖s₂tilde τ * (E₆ τ - E₆trunc τ)‖ := by gcongr; exact norm_add_le _ _
    rw [norm_mul, norm_mul, norm_mul, norm_mul] at key
    linarith [key]
  have hbound : ‖E₄ τ - E₄trunc τ‖ * ‖E₂starTrunc τ‖ + ‖E₄trunc τ‖ * ‖E₂star τ - E₂starTrunc τ‖
        + ‖E₄ τ - E₄trunc τ‖ * ‖E₂star τ - E₂starTrunc τ‖
        + ‖s₂tilde τ‖ * ‖E₆ τ - E₆trunc τ‖
      ≤ 177600 * Q ^ 3 := by
    have h1 : ‖E₄ τ - E₄trunc τ‖ * ‖E₂starTrunc τ‖ ≤ (6744 * Q ^ 3) * 1.0094 :=
      mul_le_mul hdX hZ (norm_nonneg _) (by positivity)
    have h2 : ‖E₄trunc τ‖ * ‖E₂star τ - E₂starTrunc τ‖ ≤ 1.0937 * (96.2 * Q ^ 3) :=
      mul_le_mul hX hdZ (norm_nonneg _) (by norm_num)
    have h3 : ‖E₄ τ - E₄trunc τ‖ * ‖E₂star τ - E₂starTrunc τ‖ ≤ (6744 * Q ^ 3) * (96.2 * Q ^ 3) :=
      mul_le_mul hdX hdZ (norm_nonneg _) (by positivity)
    have h4 : ‖s₂tilde τ‖ * ‖E₆ τ - E₆trunc τ‖ ≤ 1.3776 * (123783 * Q ^ 3) :=
      mul_le_mul hst hdY (norm_nonneg _) (by norm_num)
    have hQ3 : Q ^ 3 < 0.000389 ^ 3 := pow_lt_pow_left₀ hQ hQpos.le (by norm_num)
    have hQ6 : (6744 * Q ^ 3) * (96.2 * Q ^ 3) ≤ 1 * Q ^ 3 := by
      nlinarith [hQpos, hQ3, pow_pos hQpos 3]
    nlinarith [h1, h2, h3, h4, hQ6, pow_pos hQpos 3]
  calc ‖(E₄ τ - E₄trunc τ) * E₂starTrunc τ + E₄trunc τ * (E₂star τ - E₂starTrunc τ)
        + (E₄ τ - E₄trunc τ) * (E₂star τ - E₂starTrunc τ)
        - s₂tilde τ * (E₆ τ - E₆trunc τ)‖
      ≤ 177600 * Q ^ 3 := le_trans hnum hbound
    _ < 222000 * Q ^ 3 * ‖E₆ τ‖ := by nlinarith [hE6norm, pow_pos hQpos 3]

end Chudnovsky

