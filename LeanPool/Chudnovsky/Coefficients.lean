/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.MainTheorem
import LeanPool.Chudnovsky.Estimates
import LeanPool.Chudnovsky.Numerics
import LeanPool.Chudnovsky.SingularModuli
import LeanPool.Chudnovsky.ComplexMult
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-!
# The coefficients at `τ₁₆₃` (Milla, ch. 10)

The arithmetic half of the proof, specialized to `τ₁₆₃ = (1 + i√163)/2`:

* `jwert_τ₁₆₃` : `1728·J(τ₁₆₃) = −640320³`;
* `s₂_τ₁₆₃`   : `s₂(τ₁₆₃) = 77265280/90856689`, equivalently
  `(1 − s₂(τ₁₆₃))/6 = 13591409/545140134`;
* `theohud`   : Milla's final form
  `√(640320³)/(12π) = ∑ n, (6n)!/((3n)!(n!)³)·(13591409 + 545140134·n)/(−640320³)ⁿ`.

The proofs (Phase D2 of the PLAN) combine the estimates of ch. 5 (`Estimates.lean`),
verified numerics (`Numerics.lean`) and the integrality/rationality inputs of Phase C
(`SingularModuli.lean`, with the auxiliary-number bookkeeping `b₁₆₃ = 10996566783048`,
`a₁₆₃ = 9351571368960` from the paper's `satzhilfszahlen`): an algebraic integer that is
rational is an integer, and an integer within distance `< 1/2` of a certified numerical
approximation is determined exactly.
-/

noncomputable section

namespace Chudnovsky

open UpperHalfPlane Complex Nat ModularForm

open scoped Real

/-- The real interval-arithmetic core of `jwert2`: evaluating the truncation
`1728·Jtilde = (1 - 240e + 2160e²)³ / (-e·(1 + e - e²)²⁴)` at `q = -e`,
`e = e^{-π√163} ∈ (L, U)` (the certified `Numerics` bounds), the positive real
`S = (1-240e+2160e²)³/(e(1+e-e²)²⁴)` is within `1/2` of `640320³`.

Proved by monotone rational enclosures of the numerator `(1-240e+2160e²)³` and the
`24`-th power `(1+e-e²)²⁴`, followed by `norm_num` on the two resulting rational
inequalities (whose `24`-th powers of the ~47-digit endpoints have ~4500 digits). -/
private lemma jwert_real_bound {e : ℝ}
    (hL : (3.80898093700765233822623151647e-18 : ℝ) < e)
    (hU : e < (3.80898093700765233822623151648e-18 : ℝ)) :
    |(1 - 240 * e + 2160 * e ^ 2) ^ 3 / (e * (1 + e - e ^ 2) ^ 24) - 640320 ^ 3| < 1 / 2 := by
  have hepos : 0 < e := lt_trans (by norm_num) hL
  -- enclosures for `g = 1 - 240e + 2160e²`
  have hGLg : (1 - 240 * 3.80898093700765233822623151648e-18 : ℝ)
      ≤ 1 - 240 * e + 2160 * e ^ 2 := by nlinarith [hU, sq_nonneg e]
  have hgGH : 1 - 240 * e + 2160 * e ^ 2 ≤
      (1 - 240 * 3.80898093700765233822623151647e-18
        + 2160 * (3.80898093700765233822623151648e-18) ^ 2 : ℝ) := by nlinarith [hL, hU]
  have hGLpos : (0 : ℝ) < 1 - 240 * 3.80898093700765233822623151648e-18 := by norm_num
  have hgpos : 0 < 1 - 240 * e + 2160 * e ^ 2 := lt_of_lt_of_le hGLpos hGLg
  -- enclosures for `h = 1 + e - e²`
  have hHLh : (1 + 3.80898093700765233822623151647e-18
      - (3.80898093700765233822623151648e-18) ^ 2 : ℝ) ≤ 1 + e - e ^ 2 := by nlinarith [hL, hU]
  have hhHH : 1 + e - e ^ 2 ≤ (1 + 3.80898093700765233822623151648e-18 : ℝ) := by
    nlinarith [hU, sq_nonneg e]
  have hHLpos : (0 : ℝ) < 1 + 3.80898093700765233822623151647e-18
      - (3.80898093700765233822623151648e-18) ^ 2 := by norm_num
  have hhpos : 0 < 1 + e - e ^ 2 := lt_of_lt_of_le hHLpos hHLh
  -- cube / 24-th power the enclosures
  have hN_hi : (1 - 240 * e + 2160 * e ^ 2) ^ 3 ≤
      (1 - 240 * 3.80898093700765233822623151647e-18
        + 2160 * (3.80898093700765233822623151648e-18) ^ 2) ^ 3 :=
    pow_le_pow_left₀ hgpos.le hgGH 3
  have hN_lo : (1 - 240 * 3.80898093700765233822623151648e-18) ^ 3
      ≤ (1 - 240 * e + 2160 * e ^ 2) ^ 3 := pow_le_pow_left₀ hGLpos.le hGLg 3
  have hW_hi : (1 + e - e ^ 2) ^ 24 ≤ (1 + 3.80898093700765233822623151648e-18) ^ 24 :=
    pow_le_pow_left₀ hhpos.le hhHH 24
  have hW_lo : (1 + 3.80898093700765233822623151647e-18
      - (3.80898093700765233822623151648e-18) ^ 2) ^ 24 ≤ (1 + e - e ^ 2) ^ 24 :=
    pow_le_pow_left₀ hHLpos.le hHLh 24
  -- the two division enclosures of `S`
  have hden_pos : 0 < e * (1 + e - e ^ 2) ^ 24 := mul_pos hepos (pow_pos hhpos 24)
  have hSupper : (1 - 240 * e + 2160 * e ^ 2) ^ 3 / (e * (1 + e - e ^ 2) ^ 24) ≤
      (1 - 240 * 3.80898093700765233822623151647e-18
        + 2160 * (3.80898093700765233822623151648e-18) ^ 2) ^ 3 /
        (3.80898093700765233822623151647e-18 *
          (1 + 3.80898093700765233822623151647e-18
            - (3.80898093700765233822623151648e-18) ^ 2) ^ 24) := by
    apply div_le_div₀ (by positivity) hN_hi
      (mul_pos (by norm_num) (pow_pos hHLpos 24))
    exact mul_le_mul hL.le hW_lo (pow_nonneg hHLpos.le 24) hepos.le
  have hSlower : (1 - 240 * 3.80898093700765233822623151648e-18) ^ 3 /
        (3.80898093700765233822623151648e-18 *
          (1 + 3.80898093700765233822623151648e-18) ^ 24) ≤
      (1 - 240 * e + 2160 * e ^ 2) ^ 3 / (e * (1 + e - e ^ 2) ^ 24) := by
    apply div_le_div₀ (by positivity) hN_lo hden_pos
    exact mul_le_mul hU.le hW_hi (pow_nonneg hhpos.le 24) (by norm_num)
  -- the two heavy rational inequalities
  have hUpNum : (1 - 240 * 3.80898093700765233822623151647e-18
        + 2160 * (3.80898093700765233822623151648e-18) ^ 2) ^ 3 /
        (3.80898093700765233822623151647e-18 *
          (1 + 3.80898093700765233822623151647e-18
            - (3.80898093700765233822623151648e-18) ^ 2) ^ 24) < (640320 : ℝ) ^ 3 + 1 / 2 := by
    norm_num
  have hLoNum : (640320 : ℝ) ^ 3 - 1 / 2 <
      (1 - 240 * 3.80898093700765233822623151648e-18) ^ 3 /
        (3.80898093700765233822623151648e-18 *
          (1 + 3.80898093700765233822623151648e-18) ^ 24) := by
    norm_num
  rw [abs_lt]
  constructor <;> [linarith [hSlower, hLoNum]; linarith [hSupper, hUpNum]]

/-- Milla's `jwert2` at `N = 163`, from the integrality input `1728·J(τ₁₆₃) ∈ ℤ` as an
explicit hypothesis: the singular value `1728·J(τ₁₆₃) = −640320³`. -/
theorem jwert_τ₁₆₃_of (hjm : ∃ m : ℤ, 1728 * J τ₁₆₃ = (m : ℂ)) :
    1728 * J τ₁₆₃ = -640320 ^ 3 := by
  have hτ := τ₁₆₃_mem_Region
  obtain ⟨m, hm⟩ := hjm
  set e : ℝ := Real.exp (-(π * Real.sqrt 163)) with he_def
  have hepos : 0 < e := Real.exp_pos _
  have hL : (3.80898093700765233822623151647e-18 : ℝ) < e := exp_neg_pi_sqrt_163_gt
  have hU : e < (3.80898093700765233822623151648e-18 : ℝ) := exp_neg_pi_sqrt_163_lt
  -- `1728·Jtilde(τ₁₆₃)` is the coercion of the real number `-S`
  have hJt_eq0 : 1728 * Jtilde τ₁₆₃ =
      (((1 + 240 * (-e + 9 * (-e) ^ 2)) ^ 3 / ((-e) * (1 - (-e) - (-e) ^ 2) ^ 24) : ℝ) : ℂ) := by
    rw [mul_Jtilde_eq, q_τ₁₆₃_eq_ofReal, ← he_def]
    push_cast
    ring
  have hRreal : (1 + 240 * (-e + 9 * (-e) ^ 2)) ^ 3 / ((-e) * (1 - (-e) - (-e) ^ 2) ^ 24)
      = -((1 - 240 * e + 2160 * e ^ 2) ^ 3 / (e * (1 + e - e ^ 2) ^ 24)) := by
    rw [show (1 + 240 * (-e + 9 * (-e) ^ 2)) ^ 3 = (1 - 240 * e + 2160 * e ^ 2) ^ 3 from by ring,
      show ((-e) * (1 - (-e) - (-e) ^ 2) ^ 24) = -(e * (1 + e - e ^ 2) ^ 24) from by ring,
      div_neg]
  have hJt_eq : 1728 * Jtilde τ₁₆₃ =
      ((-((1 - 240 * e + 2160 * e ^ 2) ^ 3 / (e * (1 + e - e ^ 2) ^ 24)) : ℝ) : ℂ) := by
    rw [hJt_eq0, hRreal]
  -- hence `‖1728·Jtilde − (−640320³)‖ < 1/2`
  have hnorm_Jt : ‖1728 * Jtilde τ₁₆₃ - (-640320 ^ 3 : ℂ)‖ < 1 / 2 := by
    rw [hJt_eq, show (-640320 ^ 3 : ℂ) = ((-(640320 : ℝ) ^ 3 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [show (-((1 - 240 * e + 2160 * e ^ 2) ^ 3 / (e * (1 + e - e ^ 2) ^ 24)) - -(640320 : ℝ) ^ 3)
          = -((1 - 240 * e + 2160 * e ^ 2) ^ 3 / (e * (1 + e - e ^ 2) ^ 24) - 640320 ^ 3) by ring,
      abs_neg]
    exact jwert_real_bound hL hU
  -- combine with `theonaeherJ` (`‖1728J − 1728Jtilde‖ < 0.2`)
  have hJJt : ‖1728 * J τ₁₆₃ - 1728 * Jtilde τ₁₆₃‖ < 0.2 := theonaeherJ hτ
  have hchain : ‖1728 * J τ₁₆₃ - (-640320 ^ 3 : ℂ)‖ < 1 := by
    calc ‖1728 * J τ₁₆₃ - (-640320 ^ 3 : ℂ)‖
        = ‖(1728 * J τ₁₆₃ - 1728 * Jtilde τ₁₆₃)
            + (1728 * Jtilde τ₁₆₃ - (-640320 ^ 3 : ℂ))‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ < 0.2 + 1 / 2 := add_lt_add hJJt hnorm_Jt
      _ < 1 := by norm_num
  -- an integer within `< 1` of `−640320³` equals it
  rw [hm] at hchain
  have hz : m + 640320 ^ 3 = 0 := by
    have hnz : ‖((m + 640320 ^ 3 : ℤ) : ℂ)‖ < 1 := by
      rw [show ((m + 640320 ^ 3 : ℤ) : ℂ) = (m : ℂ) - (-640320 ^ 3 : ℂ) by push_cast; ring]
      exact hchain
    rw [Complex.norm_intCast] at hnz
    have hk : |m + 640320 ^ 3| < 1 := by exact_mod_cast hnz
    exact Int.abs_lt_one_iff.mp hk
  have hm' : m = -640320 ^ 3 := by omega
  rw [hm, hm']; push_cast; ring

/-- Milla's `jwert2` at `N = 163`: the singular value `1728·J(τ₁₆₃) = −640320³`. -/
theorem jwert_τ₁₆₃ : 1728 * J τ₁₆₃ = -640320 ^ 3 := jwert_τ₁₆₃_of j_τ₁₆₃_integer

/-- `J(τ₁₆₃)` itself, as a rational number, from the integrality input as a hypothesis. -/
theorem J_τ₁₆₃_of (hjm : ∃ m : ℤ, 1728 * J τ₁₆₃ = (m : ℂ)) :
    J τ₁₆₃ = -(640320 ^ 3 / 1728 : ℚ) := by
  have h := jwert_τ₁₆₃_of hjm
  push_cast
  linear_combination h / 1728

/-- `J(τ₁₆₃)` itself, as a rational number. -/
theorem J_τ₁₆₃ : J τ₁₆₃ = -(640320 ^ 3 / 1728 : ℚ) := J_τ₁₆₃_of j_τ₁₆₃_integer

-- (`isInt_of_integral_of_rat` and `τ₁₆₃_sq`, formerly private duplicates here, are now
-- imported from `ModularPolynomialZ.lean` / `CMRelations.lean` via `SingularModuli`.)

/-- The certified numerical evaluation of `stilde₂·b₁₆₃` at `τ₁₆₃`: for `e ∈ (L, U)`,
`π ∈ (πL, πU)`, `√163 ∈ (sL, sU)` (the `Numerics` intervals), the real value
`stilde₂(τ₁₆₃)·b₁₆₃` (with `q = −e`, `Im τ₁₆₃ = √163/2`) is within `1/2` of `9351571368960`. -/
private lemma s2tilde_real_bound {e pv sv : ℝ}
    (heL : (3.80898093700765233822623151647e-18 : ℝ) < e)
    (heU : e < (3.80898093700765233822623151648e-18 : ℝ))
    (hpL : (3.14159265358979323846 : ℝ) < pv) (hpU : pv < (3.14159265358979323847 : ℝ))
    (hsL : (12.7671453348037046617 : ℝ) < sv) (hsU : sv < (12.7671453348037046618 : ℝ)) :
    |(1 - 240 * e + 2160 * e ^ 2) / (1 + 504 * e - 16632 * e ^ 2)
        * (1 + 24 * e - 72 * e ^ 2 - 3 / (pv * (sv / 2))) * 10996566783048
        - 9351571368960| < 1 / 2 := by
  have hepos : 0 < e := lt_trans (by norm_num) heL
  have hp_pos : 0 < pv := lt_trans (by norm_num) hpL
  have hs_pos : 0 < sv := lt_trans (by norm_num) hsL
  have hpsv : 0 < pv * (sv / 2) := by positivity
  -- num = 1 − 240e + 2160e²
  have hnumL : (1 - 240 * 3.80898093700765233822623151648e-18 : ℝ)
      ≤ 1 - 240 * e + 2160 * e ^ 2 := by nlinarith [heU, sq_nonneg e]
  have hnumH : 1 - 240 * e + 2160 * e ^ 2 ≤
      (1 - 240 * 3.80898093700765233822623151647e-18
        + 2160 * (3.80898093700765233822623151648e-18) ^ 2 : ℝ) := by nlinarith [heL, heU, hepos]
  have hnumpos : 0 < 1 - 240 * e + 2160 * e ^ 2 := lt_of_lt_of_le (by norm_num) hnumL
  -- den = 1 + 504e − 16632e²
  have hdenL : (1 + 504 * 3.80898093700765233822623151647e-18
      - 16632 * (3.80898093700765233822623151648e-18) ^ 2 : ℝ)
      ≤ 1 + 504 * e - 16632 * e ^ 2 := by nlinarith [heL, heU, hepos]
  have hdenH :
      1 + 504 * e - 16632 * e ^ 2 ≤ (1 + 504 * 3.80898093700765233822623151648e-18 : ℝ) := by
    nlinarith [heU, sq_nonneg e]
  have hdenpos : 0 < 1 + 504 * e - 16632 * e ^ 2 := lt_of_lt_of_le (by norm_num) hdenL
  -- w = 3/(pv·(sv/2)); `wH` (from `πL, sL`) is the max, `wL` (from `πU, sU`) the min
  have hwH : 3 / (pv * (sv / 2))
      ≤ (3 / (3.14159265358979323846 * (12.7671453348037046617 / 2)) : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [hpL, hsL, hp_pos, hs_pos]
  have hwL : (3 / (3.14159265358979323847 * (12.7671453348037046618 / 2)) : ℝ)
      ≤ 3 / (pv * (sv / 2)) := by
    apply div_le_div_of_nonneg_left (by norm_num) hpsv
    nlinarith [hpU, hsU, hp_pos, hs_pos]
  -- Z = 1 + 24e − 72e² − w : lower bound subtracts `wH`, upper bound subtracts `wL`
  have hZL : (1 + 24 * 3.80898093700765233822623151647e-18
      - 72 * (3.80898093700765233822623151648e-18) ^ 2
      - 3 / (3.14159265358979323846 * (12.7671453348037046617 / 2)) : ℝ)
      ≤ 1 + 24 * e - 72 * e ^ 2 - 3 / (pv * (sv / 2)) := by nlinarith [heL, heU, hepos, hwH]
  have hZH : 1 + 24 * e - 72 * e ^ 2 - 3 / (pv * (sv / 2)) ≤
      (1 + 24 * 3.80898093700765233822623151648e-18
        - 72 * (3.80898093700765233822623151647e-18) ^ 2
        - 3 / (3.14159265358979323847 * (12.7671453348037046618 / 2)) : ℝ) := by
    nlinarith [heL, heU, hepos, hwL]
  have hZpos : 0 < 1 + 24 * e - 72 * e ^ 2 - 3 / (pv * (sv / 2)) :=
    lt_of_lt_of_le (by norm_num) hZL
  -- num·Z rational enclosures
  have hNZlo : (1 - 240 * 3.80898093700765233822623151648e-18)
      * (1 + 24 * 3.80898093700765233822623151647e-18
        - 72 * (3.80898093700765233822623151648e-18) ^ 2
        - 3 / (3.14159265358979323846 * (12.7671453348037046617 / 2)))
      ≤ (1 - 240 * e + 2160 * e ^ 2) * (1 + 24 * e - 72 * e ^ 2 - 3 / (pv * (sv / 2))) :=
    mul_le_mul hnumL hZL (by norm_num) hnumpos.le
  have hNZhi : (1 - 240 * e + 2160 * e ^ 2) * (1 + 24 * e - 72 * e ^ 2 - 3 / (pv * (sv / 2)))
      ≤ (1 - 240 * 3.80898093700765233822623151647e-18
          + 2160 * (3.80898093700765233822623151648e-18) ^ 2)
        * (1 + 24 * 3.80898093700765233822623151648e-18
          - 72 * (3.80898093700765233822623151647e-18) ^ 2
          - 3 / (3.14159265358979323847 * (12.7671453348037046618 / 2))) :=
    mul_le_mul hnumH hZH hZpos.le (by norm_num)
  -- rewrite the target quantity as `(num·Z)·b / den`
  rw [show (1 - 240 * e + 2160 * e ^ 2) / (1 + 504 * e - 16632 * e ^ 2)
        * (1 + 24 * e - 72 * e ^ 2 - 3 / (pv * (sv / 2))) * 10996566783048
      = (1 - 240 * e + 2160 * e ^ 2) * (1 + 24 * e - 72 * e ^ 2 - 3 / (pv * (sv / 2)))
          * 10996566783048 / (1 + 504 * e - 16632 * e ^ 2) from by ring]
  have hlo : (9351571368960 : ℝ) - 1 / 2 <
      (1 - 240 * e + 2160 * e ^ 2) * (1 + 24 * e - 72 * e ^ 2 - 3 / (pv * (sv / 2)))
        * 10996566783048 / (1 + 504 * e - 16632 * e ^ 2) := by
    rw [lt_div_iff₀ hdenpos]
    have hb : (1 - 240 * 3.80898093700765233822623151648e-18)
        * (1 + 24 * 3.80898093700765233822623151647e-18
          - 72 * (3.80898093700765233822623151648e-18) ^ 2
          - 3 / (3.14159265358979323846 * (12.7671453348037046617 / 2))) * 10996566783048
        ≤ (1 - 240 * e + 2160 * e ^ 2) * (1 + 24 * e - 72 * e ^ 2 - 3 / (pv * (sv / 2)))
            * 10996566783048 := by nlinarith [hNZlo]
    nlinarith [hb, hdenH]
  have hhi : (1 - 240 * e + 2160 * e ^ 2) * (1 + 24 * e - 72 * e ^ 2 - 3 / (pv * (sv / 2)))
        * 10996566783048 / (1 + 504 * e - 16632 * e ^ 2) < (9351571368960 : ℝ) + 1 / 2 := by
    rw [div_lt_iff₀ hdenpos]
    have hb : (1 - 240 * e + 2160 * e ^ 2) * (1 + 24 * e - 72 * e ^ 2 - 3 / (pv * (sv / 2)))
          * 10996566783048
        ≤ (1 - 240 * 3.80898093700765233822623151647e-18
            + 2160 * (3.80898093700765233822623151648e-18) ^ 2)
          * (1 + 24 * 3.80898093700765233822623151648e-18
            - 72 * (3.80898093700765233822623151647e-18) ^ 2
            - 3 / (3.14159265358979323847 * (12.7671453348037046618 / 2))) * 10996566783048 := by
      nlinarith [hNZhi]
    nlinarith [hb, hdenL]
  rw [abs_lt]
  constructor <;> linarith [hlo, hhi]

/-- Milla's `s2nenner`/`satzhilfszahlen` at `N = 163`, from the integrality and
rationality inputs as explicit hypotheses: `s₂(τ₁₆₃) = 77265280/90856689`. -/
theorem s₂_τ₁₆₃_of (hjm : ∃ m : ℤ, 1728 * J τ₁₆₃ = (m : ℂ))
    (hsr : ∃ r : ℚ, s₂ τ₁₆₃ = (r : ℂ)) : s₂ τ₁₆₃ = (77265280 / 90856689 : ℚ) := by
  have hτ := τ₁₆₃_mem_Region
  -- non-vanishing of `η` and `E₆` at `τ₁₆₃`
  have hetane : ModularForm.eta τ₁₆₃ ≠ 0 := by
    intro h
    have hΔ := discriminant_ne_zero τ₁₆₃
    rw [show ModularForm.discriminant τ₁₆₃ = ModularForm.eta τ₁₆₃ ^ 24 from rfl, h] at hΔ
    simp at hΔ
  have hE6ne : E₆ τ₁₆₃ ≠ 0 := E₆_ne_zero_of_mem_Region hτ
  -- `1728·J(τ₁₆₃)` is an algebraic integer (it is `−640320³ ∈ ℤ`)
  have hj : IsIntegral ℤ (1728 * J τ₁₆₃) := by
    rw [jwert_τ₁₆₃_of hjm,
      show (-640320 ^ 3 : ℂ) = ((-(640320 ^ 3) : ℤ) : ℂ) from by push_cast; ring]
    exact isIntegral_algebraMap
  have hE4 := isIntegral_E₄_div_eta_pow τ₁₆₃ hj
  -- the CM data `A = 41, B = −1, C = 1` and the `√D·E₂*/η⁴·(AC)²` integrality
  have hCMint :
      ((41 : ℤ) : ℂ) + ((-1 : ℤ) : ℂ) * (τ₁₆₃ : ℂ) + ((1 : ℤ) : ℂ) * (τ₁₆₃ : ℂ) ^ 2 = 0 := by
    push_cast; linear_combination τ₁₆₃_sq
  have hrest := theoezweisternrest_of_isIntegral_j τ₁₆₃ (A := 41) (B := -1) (C := 1)
    (by decide) hCMint hj
  have hP := hE4.mul hrest
  -- the auxiliary integer `K = √D·(AC)²·(E₆/η¹²)`, with `P = s₂·K`
  set K : ℂ :=
    (2 * ((1 : ℤ) : ℂ) * (τ₁₆₃ : ℂ) + ((-1 : ℤ) : ℂ)) * (((41 : ℤ) : ℂ) * ((1 : ℤ) : ℂ)) ^ 2
      * (E₆ τ₁₆₃ / ModularForm.eta τ₁₆₃ ^ 12) with hKdef
  have hsK : s₂ τ₁₆₃ * K = E₄ τ₁₆₃ / ModularForm.eta τ₁₆₃ ^ 8 *
      ((2 * ((1 : ℤ) : ℂ) * (τ₁₆₃ : ℂ) + ((-1 : ℤ) : ℂ))
        * (E₂star τ₁₆₃ / ModularForm.eta τ₁₆₃ ^ 4) * (((41 : ℤ) : ℂ) * ((1 : ℤ) : ℂ)) ^ 2) := by
    rw [hKdef]; simp only [s₂]; field_simp
  rw [← hsK] at hP
  -- `K² = b²` with `b = 10996566783048`
  have hsq1 : (2 * ((1 : ℤ) : ℂ) * (τ₁₆₃ : ℂ) + ((-1 : ℤ) : ℂ)) ^ 2 = -163 := by
    push_cast; linear_combination 4 * τ₁₆₃_sq
  have hE6sq : (E₆ τ₁₆₃ / ModularForm.eta τ₁₆₃ ^ 12) ^ 2 = 1728 * J τ₁₆₃ - 1728 := by
    have hΔ : ModularForm.discriminant τ₁₆₃ = ModularForm.eta τ₁₆₃ ^ 24 := rfl
    have hne := discriminant_ne_zero τ₁₆₃
    have hrel := E₄_cube_sub_E₆_sq_eq_discriminant τ₁₆₃
    rw [mul_J_eq, div_pow,
      show (ModularForm.eta τ₁₆₃ ^ 12) ^ 2 = ModularForm.discriminant τ₁₆₃ from by
      rw [hΔ]; ring]
    field_simp
    linear_combination -hrel
  have hKsq : K ^ 2 = (10996566783048 : ℂ) ^ 2 := by
    rw [hKdef, mul_pow, mul_pow, hsq1, hE6sq, jwert_τ₁₆₃_of hjm]
    push_cast; norm_num
  -- hence `K = ±b`, so `s₂·b = ±P` is an algebraic integer
  have hbranch : K = (10996566783048 : ℂ) ∨ K = -(10996566783048 : ℂ) := by
    have hfac : (K - 10996566783048) * (K + 10996566783048) = 0 := by linear_combination hKsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hsbint : IsIntegral ℤ (s₂ τ₁₆₃ * 10996566783048) := by
    rcases hbranch with hb | hb
    · rw [show s₂ τ₁₆₃ * (10996566783048 : ℂ) = s₂ τ₁₆₃ * K from by rw [hb]]; exact hP
    · rw [show s₂ τ₁₆₃ * (10996566783048 : ℂ) = -(s₂ τ₁₆₃ * K) from by rw [hb]; ring]; exact hP.neg
  -- `s₂·b` is rational, hence an integer `m`
  obtain ⟨r, hr⟩ := hsr
  have hsbrat : s₂ τ₁₆₃ * 10996566783048 = ((r * 10996566783048 : ℚ) : ℂ) := by
    rw [hr]; push_cast; ring
  obtain ⟨m, hm⟩ := isInt_of_integral_of_rat hsbint hsbrat
  -- numeric pin: `‖s₂·b − 9351571368960‖ < 1`
  have hqbound : ‖q τ₁₆₃‖ < 3.80898093700765233822623151648e-18 := by
    rw [norm_q_τ₁₆₃]; exact exp_neg_pi_sqrt_163_lt
  have hqpos : 0 < ‖q τ₁₆₃‖ := norm_q_pos τ₁₆₃
  have hbnorm : ‖(10996566783048 : ℂ)‖ = 10996566783048 := by
    rw [Complex.norm_ofNat]
  have hpart1 : ‖s₂ τ₁₆₃ * 10996566783048 - s₂tilde τ₁₆₃ * 10996566783048‖ < 1 / 4 := by
    rw [show s₂ τ₁₆₃ * 10996566783048 - s₂tilde τ₁₆₃ * 10996566783048
        = (s₂ τ₁₆₃ - s₂tilde τ₁₆₃) * 10996566783048 from by ring, norm_mul, hbnorm]
    have hq3 : ‖q τ₁₆₃‖ ^ 3 < (3.80898093700765233822623151648e-18 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hqbound (norm_nonneg _) (by norm_num)
    calc ‖s₂ τ₁₆₃ - s₂tilde τ₁₆₃‖ * 10996566783048
        < 222000 * ‖q τ₁₆₃‖ ^ 3 * 10996566783048 := by nlinarith [theonaehers2 hτ, hqpos]
      _ < 222000 * (3.80898093700765233822623151648e-18 : ℝ) ^ 3 * 10996566783048 := by
          nlinarith [hq3]
      _ < 1 / 4 := by norm_num
  have hnum := s2tilde_real_bound (e := Real.exp (-(π * Real.sqrt 163))) (pv := π)
    (sv := Real.sqrt 163) exp_neg_pi_sqrt_163_gt exp_neg_pi_sqrt_163_lt
    pi_gt_high_precision pi_lt_high_precision sqrt_163_gt sqrt_163_lt
  set E : ℝ := Real.exp (-(π * Real.sqrt 163)) with hEdef
  set St : ℝ := (1 - 240 * E + 2160 * E ^ 2) / (1 + 504 * E - 16632 * E ^ 2)
      * (1 + 24 * E - 72 * E ^ 2 - 3 / (π * (Real.sqrt 163 / 2))) with hStdef
  -- `hnum : |St·b − target| < 1/2`
  have hs2t_eq : s₂tilde τ₁₆₃ = ((St : ℝ) : ℂ) := by
    rw [hStdef]
    simp only [s₂tilde]
    rw [q_τ₁₆₃_eq_ofReal, τ₁₆₃_im, ← hEdef]
    push_cast
    ring
  have hpart2 : ‖s₂tilde τ₁₆₃ * 10996566783048 - 9351571368960‖ < 1 / 2 := by
    rw [hs2t_eq,
      show ((St : ℝ) : ℂ) * 10996566783048 - 9351571368960
        = ((St * 10996566783048 - 9351571368960 : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact hnum
  have hpin : ‖s₂ τ₁₆₃ * 10996566783048 - 9351571368960‖ < 1 := by
    calc ‖s₂ τ₁₆₃ * 10996566783048 - 9351571368960‖
        = ‖(s₂ τ₁₆₃ * 10996566783048 - s₂tilde τ₁₆₃ * 10996566783048)
            + (s₂tilde τ₁₆₃ * 10996566783048 - 9351571368960)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ < 1 / 4 + 1 / 2 := add_lt_add hpart1 hpart2
      _ < 1 := by norm_num
  rw [hm] at hpin
  have hmval : m = 9351571368960 := by
    have hlt : ‖((m - 9351571368960 : ℤ) : ℂ)‖ < 1 := by
      rw [show ((m - 9351571368960 : ℤ) : ℂ) = (m : ℂ) - 9351571368960 from by push_cast; ring]
      exact hpin
    rw [Complex.norm_intCast] at hlt
    have hk : |m - 9351571368960| < 1 := by exact_mod_cast hlt
    have := Int.abs_lt_one_iff.mp hk
    omega
  -- conclude `s₂ = 9351571368960/10996566783048 = 77265280/90856689`
  have hfinal : s₂ τ₁₆₃ * 10996566783048 = ((9351571368960 : ℤ) : ℂ) := by rw [hm, hmval]
  have hval : s₂ τ₁₆₃ = 9351571368960 / 10996566783048 := by
    rw [eq_div_iff (by norm_num : (10996566783048 : ℂ) ≠ 0), hfinal]; norm_num
  rw [hval]; push_cast; norm_num

/-- Milla's `s2nenner`/`satzhilfszahlen` at `N = 163`:
`s₂(τ₁₆₃) = 77265280/90856689`. -/
theorem s₂_τ₁₆₃ : s₂ τ₁₆₃ = (77265280 / 90856689 : ℚ) :=
  s₂_τ₁₆₃_of j_τ₁₆₃_integer s₂_τ₁₆₃_rational

/-- The combination entering the Chudnovsky formula, from the integrality and
rationality inputs as hypotheses: `(1 − s₂(τ₁₆₃))/6 = 13591409/545140134`. -/
theorem one_sub_s₂_τ₁₆₃_div_six_of (hjm : ∃ m : ℤ, 1728 * J τ₁₆₃ = (m : ℂ))
    (hsr : ∃ r : ℚ, s₂ τ₁₆₃ = (r : ℂ)) :
    (1 - s₂ τ₁₆₃) / 6 = (13591409 / 545140134 : ℚ) := by
  rw [s₂_τ₁₆₃_of hjm hsr]; push_cast; norm_num

/-- The combination entering the Chudnovsky formula:
`(1 − s₂(τ₁₆₃))/6 = 13591409/545140134`. -/
theorem one_sub_s₂_τ₁₆₃_div_six :
    (1 - s₂ τ₁₆₃) / 6 = (13591409 / 545140134 : ℚ) :=
  one_sub_s₂_τ₁₆₃_div_six_of j_τ₁₆₃_integer s₂_τ₁₆₃_rational

/-- Milla's `theohud`: the Chudnovsky formula in the paper's normalization,
`√(640320³)/(12π) = ∑ n, (6n)!/((3n)!(n!)³)·(13591409 + 545140134·n)/(−640320³)ⁿ`,
obtained by substituting `τ = τ₁₆₃` into the Main Theorem; from the integrality and
rationality inputs as explicit hypotheses. -/
theorem theohud_of (hjm : ∃ m : ℤ, 1728 * J τ₁₆₃ = (m : ℂ))
    (hsr : ∃ r : ℚ, s₂ τ₁₆₃ = (r : ℂ)) :
    (Real.sqrt (640320 ^ 3) / (12 * π) : ℂ) =
      ∑' n : ℕ, (((6 * n)! : ℂ) / (((3 * n)! : ℂ) * ((n ! : ℕ) : ℂ) ^ 3)) *
        ((13591409 + 545140134 * n) / (-640320 ^ 3 : ℂ) ^ n) := by
  -- rewrite the target series as `545140134 · ∑ mainSummand τ₁₆₃`
  have hterm : ∀ n : ℕ, (((6 * n)! : ℂ) / (((3 * n)! : ℂ) * ((n ! : ℕ) : ℂ) ^ 3)) *
        ((13591409 + 545140134 * n) / (-640320 ^ 3 : ℂ) ^ n)
      = 545140134 * mainSummand τ₁₆₃ n := by
    intro n
    have hpne : ((-640320 ^ 3 : ℂ)) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have hf1 : ((3 * n)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hf2 : ((n ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h545 : (545140134 : ℂ) ≠ 0 := by norm_num
    simp only [mainSummand]
    rw [one_sub_s₂_τ₁₆₃_div_six_of hjm hsr, jwert_τ₁₆₃_of hjm]
    push_cast
    field_simp
  rw [tsum_congr hterm, tsum_mul_left, ← hauptformel τ₁₆₃_mem_Region]
  -- the singular value `J(τ₁₆₃)/(J(τ₁₆₃)−1) = 640320³/(640320³+1728)` (a positive real < 1)
  have hJratio : J τ₁₆₃ / (J τ₁₆₃ - 1) =
      ((640320 ^ 3 / (640320 ^ 3 + 1728) : ℝ) : ℂ) := by
    rw [J_τ₁₆₃_of hjm]
    push_cast
    field_simp; ring
  -- the principal square root collapses to `Real.sqrt` (positive real argument)
  have hcpow : (J τ₁₆₃ / (J τ₁₆₃ - 1)) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (640320 ^ 3 / (640320 ^ 3 + 1728)) : ℝ) : ℂ) := by
    rw [hJratio, Real.sqrt_eq_rpow,
      Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 640320 ^ 3 / (640320 ^ 3 + 1728))]
    norm_num
  -- the arithmetic identity `√163·√(640320³+1728) = 12·545140134`
  have hs163_real : Real.sqrt 163 * Real.sqrt (640320 ^ 3 + 1728) = 12 * 545140134 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 163),
      show (163 : ℝ) * (640320 ^ 3 + 1728) = (12 * 545140134) ^ 2 by norm_num,
      Real.sqrt_sq (by positivity)]
  -- the real identity behind `theohud`
  have hπ := Real.pi_ne_zero
  have hs : Real.sqrt 163 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hb : Real.sqrt (640320 ^ 3 + 1728) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have gR : Real.sqrt (640320 ^ 3) / (12 * π)
      = 545140134 * (1 / (2 * π * (Real.sqrt 163 / 2)) *
          Real.sqrt (640320 ^ 3 / (640320 ^ 3 + 1728))) := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 640320 ^ 3)]
    rw [show 545140134 * (1 / (2 * π * (Real.sqrt 163 / 2)) *
          (Real.sqrt (640320 ^ 3) / Real.sqrt (640320 ^ 3 + 1728)))
        = 545140134 * Real.sqrt (640320 ^ 3)
            / (π * (Real.sqrt 163 * Real.sqrt (640320 ^ 3 + 1728))) from by
      field_simp]
    rw [hs163_real]
    field_simp
  -- transfer to `ℂ`
  rw [τ₁₆₃_im, hcpow]
  have hgRc := congrArg (fun r : ℝ => (r : ℂ)) gR
  push_cast at hgRc ⊢
  linear_combination hgRc

/-- Milla's `theohud`: the Chudnovsky formula in the paper's normalization,
`√(640320³)/(12π) = ∑ n, (6n)!/((3n)!(n!)³)·(13591409 + 545140134·n)/(−640320³)ⁿ`,
obtained by substituting `τ = τ₁₆₃` into the Main Theorem. -/
theorem theohud :
    (Real.sqrt (640320 ^ 3) / (12 * π) : ℂ) =
      ∑' n : ℕ, (((6 * n)! : ℂ) / (((3 * n)! : ℂ) * ((n ! : ℕ) : ℂ) ^ 3)) *
        ((13591409 + 545140134 * n) / (-640320 ^ 3 : ℂ) ^ n) :=
  theohud_of j_τ₁₆₃_integer s₂_τ₁₆₃_rational

end Chudnovsky
