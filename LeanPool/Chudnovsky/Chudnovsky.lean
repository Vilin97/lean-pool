/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.Coefficients
import Mathlib.Analysis.Real.Pi.Chudnovsky

/-!
# Glue: from Milla's `theohud` to Mathlib's `chudnovskySum = π⁻¹`

Phase D3 of the PLAN: convert Milla's normalization
`√(640320³)/(12π) = ∑ n, (6n)!/((3n)!(n!)³)·(13591409 + 545140134·n)/(−640320³)ⁿ`
into Mathlib's statement `chudnovskySum = π⁻¹`, where
`chudnovskySum = 12/640320^(3/2) · ∑' n, chudnovskyTerm n`. This involves
`640320^(3/2 : ℝ) = √(640320³)` (rpow lemmas), the `ℚ → ℝ` coercion of
`chudnovskyTerm`, and inverting both (positive) sides.

The intermediate milestone `chudnovsky_of_singular_moduli` states the full theorem with
the Phase C inputs (`SingularModuli.lean`) as explicit hypotheses: the paper's proof
minus the literature citations (Silverman II.6.1, II.4.3(b), Buell, Masser Thm. A1).
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex Nat

open scoped Real

/-- Key factorial bound: `(6n)! ≤ 1728ⁿ·(3n)!·(n!)³`, the exponential growth rate of
`(6n)!/((3n)!(n!)³)` (Stirling gives exactly `1728 = 6⁶/3³`). Proved by induction: the
single-step ratio is `(6n+1)⋯(6n+6) ≤ 1728·(3n+1)(3n+2)(3n+3)(n+1)³`, whose difference
factors as `72·(n+1)(3n+1)(3n+2)(108n²+170n+67) ≥ 0`. -/
private theorem factorial_six_bound (n : ℕ) :
    (6 * n)! ≤ 1728 ^ n * ((3 * n)! * (n ! ) ^ 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e6 : 6 * (n + 1) = 6 * n + 6 := by ring
    have e3 : 3 * (n + 1) = 3 * n + 3 := by ring
    have exp6 : (6 * n + 6)! =
        (6*n+6)*(6*n+5)*(6*n+4)*(6*n+3)*(6*n+2)*(6*n+1) * (6*n)! := by
      simp only [Nat.factorial_succ]; ring
    have exp3 : (3 * n + 3)! = (3*n+3)*(3*n+2)*(3*n+1) * (3*n)! := by
      simp only [Nat.factorial_succ]; ring
    have expn : ((n+1) ! ) ^ 3 = (n+1)^3 * (n ! )^3 := by
      rw [Nat.factorial_succ]; ring
    rw [e6, e3, exp6, exp3, expn]
    have hstep : (6*n+6)*(6*n+5)*(6*n+4)*(6*n+3)*(6*n+2)*(6*n+1)
        ≤ 1728 * ((3*n+3)*(3*n+2)*(3*n+1)*(n+1)^3) := by
      calc (6*n+6)*(6*n+5)*(6*n+4)*(6*n+3)*(6*n+2)*(6*n+1)
          ≤ (6*n+6)*(6*n+5)*(6*n+4)*(6*n+3)*(6*n+2)*(6*n+1)
            + (69984*n^5+250128*n^4+349272*n^3+237024*n^2+77544*n+9648) :=
            Nat.le_add_right _ _
        _ = 1728 * ((3*n+3)*(3*n+2)*(3*n+1)*(n+1)^3) := by ring
    calc (6*n+6)*(6*n+5)*(6*n+4)*(6*n+3)*(6*n+2)*(6*n+1) * (6*n)!
        ≤ (6*n+6)*(6*n+5)*(6*n+4)*(6*n+3)*(6*n+2)*(6*n+1)
            * (1728^n * ((3*n)! * (n ! )^3)) := Nat.mul_le_mul_left _ ih
      _ = ((6*n+6)*(6*n+5)*(6*n+4)*(6*n+3)*(6*n+2)*(6*n+1)) * 1728^n
            * ((3*n)! * (n ! )^3) := by ring
      _ ≤ (1728 * ((3*n+3)*(3*n+2)*(3*n+1)*(n+1)^3)) * 1728^n * ((3*n)! * (n ! )^3) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hstep)
      _ = 1728 ^ (n+1) * ((3*n+3)*(3*n+2)*(3*n+1) * (3*n)! * ((n+1)^3 * (n ! )^3)) := by ring

/-- The Chudnovsky series is (absolutely) summable — needed for `hauptformel`
substitution, the series rearrangement, and the final inversion. -/
theorem summable_chudnovskyTerm : Summable fun n : ℕ ↦ (chudnovskyTerm n : ℝ) := by
  -- Comparison against `(545140134·n + 13591409)·rⁿ` with `r = 1728/640320³ < 1`.
  set r : ℝ := 1728 / 640320 ^ 3 with hr_def
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; rw [hr_def]; norm_num
  have hg1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hg0 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hr
  have hg : Summable (fun n : ℕ => (545140134 * (n : ℝ) + 13591409) * r ^ n) := by
    have hrw : (fun n : ℕ => (545140134 * (n : ℝ) + 13591409) * r ^ n)
        = (fun n : ℕ => 545140134 * ((n : ℝ) * r ^ n) + 13591409 * r ^ n) := by
      funext n; ring
    rw [hrw]
    exact (hg1.mul_left 545140134).add (hg0.mul_left 13591409)
  refine hg.of_norm_bounded (fun n => ?_)
  -- `|chudnovskyTerm n| = (6n)!·(545140134n+13591409)/((3n)!(n!)³·640320^{3n})`.
  have hval : (chudnovskyTerm n : ℝ)
      = (-1:ℝ)^n * ((((6*n)! : ℝ) * (545140134*n+13591409))
          / (((3*n)! : ℝ) * (n ! )^3 * 640320^(3*n))) := by
    simp only [chudnovskyTerm, chudnovskyNum, chudnovskyDenom]
    push_cast
    ring
  rw [Real.norm_eq_abs, hval, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (by positivity)]
  -- Reduce to `(6n)! ≤ 1728ⁿ·(3n)!·(n!)³`.
  rw [div_le_iff₀ (by positivity : (0:ℝ) < ((3*n)! : ℝ) * (n ! )^3 * 640320^(3*n))]
  have key : ((6*n)! : ℝ) ≤ 1728^n * (((3*n)! : ℝ) * (n ! )^3) := by
    have h := factorial_six_bound n
    calc ((6*n)! : ℝ) ≤ ((1728^n * ((3*n)! * (n ! )^3) : ℕ) : ℝ) := by exact_mod_cast h
      _ = 1728^n * (((3*n)! : ℝ) * (n ! )^3) := by push_cast; ring
  have hApos : (0:ℝ) ≤ 545140134*(n:ℝ)+13591409 := by positivity
  have hrpow : r^n * (640320:ℝ)^(3*n) = 1728^n := by
    rw [hr_def, div_pow, ← pow_mul,
      div_mul_cancel₀ _ (by positivity : (640320:ℝ)^(3*n) ≠ 0)]
  rw [show (545140134 * (n:ℝ) + 13591409) * r ^ n
        * (((3*n)! : ℝ) * (n ! )^3 * 640320^(3*n))
      = (545140134 * (n:ℝ) + 13591409) * (r ^ n * 640320^(3*n))
          * (((3*n)! : ℝ) * (n ! )^3) from by ring, hrpow]
  nlinarith [mul_le_mul_of_nonneg_left key hApos]

/-- The glue lemma: Milla's normalization `√(640320³)/(12π) = ∑ …` implies Mathlib's
`chudnovskySum = π⁻¹`. Shared by both `chudnovsky_of_singular_moduli` and the
unconditional `chudnovskySum_eq_pi_inv`. -/
private theorem chudnovsky_glue
    (H : (Real.sqrt (640320 ^ 3) / (12 * π) : ℂ) =
      ∑' n : ℕ, (((6 * n)! : ℂ) / (((3 * n)! : ℂ) * ((n ! : ℕ) : ℂ) ^ 3)) *
        ((13591409 + 545140134 * n) / (-640320 ^ 3 : ℂ) ^ n)) :
    chudnovskySum = π⁻¹ := by
  -- Each summand equals the `ℝ→ℂ` coercion of `chudnovskyTerm n`.
  have term_eq : ∀ n : ℕ,
      (((6 * n)! : ℂ) / (((3 * n)! : ℂ) * ((n ! : ℕ) : ℂ) ^ 3)) *
        ((13591409 + 545140134 * n) / (-640320 ^ 3 : ℂ) ^ n)
      = ((chudnovskyTerm n : ℝ) : ℂ) := by
    intro n
    have hpow : ((-640320 ^ 3 : ℂ)) ^ n = (-1 : ℂ) ^ n * (640320 : ℂ) ^ (3 * n) := by
      rw [neg_pow, ← pow_mul]
    have h1 : ((3 * n)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h3 : (640320 : ℂ) ^ (3 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h4 : ((-1 : ℂ)) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    simp only [chudnovskyTerm, chudnovskyNum, chudnovskyDenom]
    rw [hpow]
    push_cast
    field_simp
    ring_nf
    rw [show ((-1:ℂ))^(n*2) = 1 from by rw [Nat.mul_comm n 2, pow_mul, neg_one_sq, one_pow]]
    ring
  -- Turn the ℂ identity into a real one.
  have H2 : (Real.sqrt (640320 ^ 3) / (12 * π) : ℂ) = ∑' n, ((chudnovskyTerm n : ℝ) : ℂ) :=
    H.trans (tsum_congr term_eq)
  have HR : Real.sqrt (640320 ^ 3) / (12 * π) = ∑' n, (chudnovskyTerm n : ℝ) := by
    exact_mod_cast H2
  -- `640320^(3/2) = √(640320³)`.
  have hrpow : (640320 : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt (640320 ^ 3) := by
    rw [Real.sqrt_eq_rpow, show ((640320 : ℝ) ^ 3) = (640320 : ℝ) ^ ((3 : ℕ) : ℝ) from
      (Real.rpow_natCast _ 3).symm, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hs : Real.sqrt (640320 ^ 3) ≠ 0 := by positivity
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  -- Assemble.
  simp only [chudnovskySum]
  rw [hrpow, ← HR]
  field_simp

/-- **Intermediate milestone** (PLAN, Phase C): the Chudnovsky formula assuming the
singular-moduli inputs — `1728·J(τ₁₆₃)` is a (rational) integer and `s₂(τ₁₆₃)` is
rational. Everything else (Phases A, B, D) is proved. -/
theorem chudnovsky_of_singular_moduli
    (h₁ : ∃ m : ℤ, 1728 * J τ₁₆₃ = (m : ℂ))
    (h₂ : ∃ r : ℚ, s₂ τ₁₆₃ = (r : ℂ)) :
    chudnovskySum = π⁻¹ :=
  chudnovsky_glue (theohud_of h₁ h₂)

/-- **Chudnovsky's formula** (Mathlib's `proof_wanted chudnovskySum_eq_pi_inv`). -/
theorem chudnovskySum_eq_pi_inv : chudnovskySum = π⁻¹ :=
  chudnovsky_glue theohud

end Chudnovsky
