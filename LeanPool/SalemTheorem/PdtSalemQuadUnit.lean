/-
Copyright (c) 2026 Stephanie Alexander. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephanie Alexander
-/
import Mathlib.Tactic
import LeanPool.SalemTheorem.PdtSalemCircle
import LeanPool.SalemTheorem.PdtSalemArith
import LeanPool.SalemTheorem.PdtSalemMinus
import LeanPool.SalemTheorem.PdtSalemEndgame

/-!
# PdtSalemQuadUnit — the reciprocal-quadratic case and the pattern-form theorem

The reciprocal-quadratic case of Salem's theorem, via Salem's second
construction in its explicit form
`B = (X² − rX + 1)(X^{2m} + 1) ± X^{m+1}` (Chebyshev-free), the
reduction lemma (a Pisot-pattern polynomial vanishing at `1/alpha`
forces `alpha` reciprocal quadratic), and `salem_theorem_full` — the
pattern-form theorem, which unifies Salem's two cases in one statement
(supporting; the compared Salem's Theorem IV for Pisot numbers is
`SalemPisot.salem_theorem`).  The sign `eps = −1`
approaches from above, `eps = +1` from below.

Setting: `alpha > 1` a reciprocal quadratic Pisot unit —
`alpha² = r·alpha − 1` with `r : ℤ`, `3 ≤ r`, so `alpha + 1/alpha = r`
and the conjugate is `1/alpha`.  The excluded case of
`PdtSalemEndgame.salem_two_sided` is exactly this one (`P(1/alpha) = 0`
forces it — the reduction lemma), and the explicit family

* `Bfam r eps m = (X² − C r·X + 1)·(X^{2m} + 1) + C eps·X^{m+1}`

covers it: on the circle
`B(E t) = E((m+1)t)·((2cos t − r)·2cos(mt) + eps)` gives `2m` circle
roots by sign alternation on the grid `t_k = kπ/m` (no phase, no
argument principle); off the circle the normalized form
`B(y) = y^{m+1}·((y + 1/y − r)(y^m + y^{−m}) + eps)` plants one real
root just above `alpha` (`eps = −1`) or just below (`eps = +1`), at
distance `O(2^{−m})`; the multiset squeeze and the arithmetic
certificate (the third certificate, the second port of
`PdtSalemArith.salem_certificate`) promote
the root to a Salem number, the two integer degeneracies being excluded
DIRECTLY: the root lies in `(r − 1, r)` which contains no integer, and
its trace displacement `tau + 1/tau − r = −eps/(tau^m + tau^{−m})` is
nonzero of absolute value `< 1/2`.

Main results:

* `salem_two_sided_quad_unit`: the degenerate case closed — Salem
  numbers approach a reciprocal quadratic Pisot unit from both sides;
* `reciprocal_quadratic_of_inv_root`: a Pisot-pattern polynomial
  vanishing at `1/alpha` forces `alpha² = r·alpha − 1`, `3 ≤ r`;
* `salem_theorem_full`: the pattern-form theorem — every Pisot-pattern
  polynomial has Salem numbers approaching its large root from both
  sides; it unifies Salem's two cases in one statement (supporting; the
  compared Salem's Theorem IV for Pisot numbers is
  `SalemPisot.salem_theorem`).

The reduction lemma is proved without conjugation-closure.
-/

namespace PDT
namespace SalemQuadUnit

noncomputable section
open Polynomial Complex Set Filter
open SalemCircle

/-! ### Scalar facts about the reciprocal quadratic unit -/

/-- The trace identity: `alpha + 1/alpha = r`. -/
lemma trace_eq {r : ℤ} {alpha : ℝ} (halpha : 1 < alpha)
    (hmin : alpha ^ 2 = (r : ℝ) * alpha - 1) : alpha + alpha⁻¹ = (r : ℝ) := by
  have h0 : alpha ≠ 0 := ne_of_gt (by linarith)
  field_simp
  linear_combination hmin

/-- The unit is larger than `2` (indeed larger than `r − 1 ≥ 2`). -/
lemma alpha_gt_two {r : ℤ} {alpha : ℝ} (hr : 3 ≤ r) (halpha : 1 < alpha)
    (hmin : alpha ^ 2 = (r : ℝ) * alpha - 1) : 2 < alpha := by
  by_contra hle
  have hle2 : alpha ≤ 2 := by linarith [not_lt.mp hle]
  have hrR : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hprod : (alpha - 1) * (alpha - 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have h3a : 3 * alpha ≤ (r : ℝ) * alpha :=
    mul_le_mul_of_nonneg_right hrR (by linarith)
  nlinarith [hmin, hprod, h3a]

/-- The real quadratic factors through the two conjugates. -/
lemma quad_factor {r : ℤ} {alpha : ℝ} (halpha : 1 < alpha)
    (hmin : alpha ^ 2 = (r : ℝ) * alpha - 1) (y : ℝ) :
    y ^ 2 - (r : ℝ) * y + 1 = (y - alpha) * (y - alpha⁻¹) := by
  have h0 : alpha ≠ 0 := ne_of_gt (by linarith)
  have htr : alpha + alpha⁻¹ = (r : ℝ) := trace_eq halpha hmin
  have hprod : alpha * alpha⁻¹ = 1 := mul_inv_cancel₀ h0
  linear_combination y * htr - hprod

/-- The window `(r − 1, r)` around `alpha`: upper part. -/
lemma alpha_lt_r {r : ℤ} {alpha : ℝ} (halpha : 1 < alpha)
    (hmin : alpha ^ 2 = (r : ℝ) * alpha - 1) : alpha < (r : ℝ) := by
  have htr := trace_eq halpha hmin
  have hpos : 0 < alpha⁻¹ := inv_pos.mpr (by linarith)
  linarith

/-- The window `(r − 1, r)` around `alpha`: lower part. -/
lemma r_sub_one_lt_alpha {r : ℤ} {alpha : ℝ} (halpha : 1 < alpha)
    (hmin : alpha ^ 2 = (r : ℝ) * alpha - 1) : (r : ℝ) - 1 < alpha := by
  have htr := trace_eq halpha hmin
  have h1 : alpha⁻¹ < 1 := inv_lt_one_of_one_lt₀ halpha
  linarith

/-- No integer lies in the open interval `(r − 1, r)`. -/
lemma no_int_in_window {r : ℤ} {x : ℝ} (h1 : (r : ℝ) - 1 < x) (h2 : x < (r : ℝ)) :
    ∀ n : ℤ, x ≠ (n : ℝ) := by
  intro n hn
  rw [hn] at h1 h2
  have hn2 : n < r := by exact_mod_cast h2
  have hn1 : r - 1 < n := by exact_mod_cast h1
  omega

/-! ### The IVT helper -/

/-- A sign change of a continuous function plants a root strictly
between the endpoints. -/
lemma exists_root_between (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hsign : f a * f b < 0) :
    ∃ x : ℝ, a < x ∧ x < b ∧ f x = 0 := by
  rcases lt_trichotomy (f a) 0 with hfa | hfa | hfa
  · have hfb : 0 < f b := by nlinarith
    have h0 : (0 : ℝ) ∈ Icc (f a) (f b) := ⟨le_of_lt hfa, le_of_lt hfb⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc (le_of_lt hab) hf h0
    refine ⟨x, ?_, ?_, hfx⟩
    · rcases eq_or_lt_of_le hx.1 with h | h
      · exfalso; rw [← h] at hfx; linarith
      · exact h
    · rcases eq_or_lt_of_le hx.2 with h | h
      · exfalso; rw [h] at hfx; linarith
      · exact h
  · exfalso; rw [hfa, zero_mul] at hsign; exact lt_irrefl 0 hsign
  · have hfb : f b < 0 := by nlinarith
    have h0 : (0 : ℝ) ∈ Icc (f b) (f a) := ⟨le_of_lt hfb, le_of_lt hfa⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' (le_of_lt hab) hf h0
    refine ⟨x, ?_, ?_, hfx⟩
    · rcases eq_or_lt_of_le hx.1 with h | h
      · exfalso; rw [← h] at hfx; linarith
      · exact h
    · rcases eq_or_lt_of_le hx.2 with h | h
      · exfalso; rw [h] at hfx; linarith
      · exact h

/-! ### The family over ℤ and its basic structure -/

/-- **Salem's second construction, Chebyshev-free**: the integer family
`B = (X² − rX + 1)·(X^{2m} + 1) + eps·X^{m+1}`, `eps = ±1`. -/
def Bfam (r eps : ℤ) (m : ℕ) : Polynomial ℤ :=
  (X ^ 2 - C r * X + 1) * (X ^ (2 * m) + 1) + C eps * X ^ (m + 1)

lemma quad_monic (r : ℤ) : (X ^ 2 - C r * X + 1 : Polynomial ℤ).Monic := by
  unfold Polynomial.Monic
  monicity!

lemma quad_natDegree (r : ℤ) : (X ^ 2 - C r * X + 1 : Polynomial ℤ).natDegree = 2 := by
  compute_degree!

lemma cyc_monic (m : ℕ) (hm : 1 ≤ m) : (X ^ (2 * m) + 1 : Polynomial ℤ).Monic := by
  rw [show (1 : Polynomial ℤ) = C 1 from (Polynomial.C_1).symm]
  exact monic_X_pow_add_C _ (by omega)

lemma cyc_natDegree (m : ℕ) : (X ^ (2 * m) + 1 : Polynomial ℤ).natDegree = 2 * m := by
  rw [show (1 : Polynomial ℤ) = C 1 from (Polynomial.C_1).symm]
  exact natDegree_X_pow_add_C

lemma lead_monic (r : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    ((X ^ 2 - C r * X + 1) * (X ^ (2 * m) + 1) : Polynomial ℤ).Monic :=
  (quad_monic r).mul (cyc_monic m hm)

lemma lead_natDegree (r : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    ((X ^ 2 - C r * X + 1) * (X ^ (2 * m) + 1) : Polynomial ℤ).natDegree
      = 2 * m + 2 := by
  rw [(quad_monic r).natDegree_mul (cyc_monic m hm), quad_natDegree, cyc_natDegree]
  omega

lemma pert_degree_lt (r eps : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    (C eps * X ^ (m + 1) : Polynomial ℤ).degree
      < ((X ^ 2 - C r * X + 1) * (X ^ (2 * m) + 1) : Polynomial ℤ).degree := by
  apply degree_lt_degree
  rw [lead_natDegree r m hm]
  have h1 : (C eps * X ^ (m + 1) : Polynomial ℤ).natDegree ≤ m + 1 :=
    le_trans (natDegree_C_mul_le _ _) (le_of_eq (natDegree_X_pow _))
  omega

lemma Bfam_monic (r eps : ℤ) {m : ℕ} (hm : 1 ≤ m) : (Bfam r eps m).Monic :=
  (lead_monic r m hm).add_of_left (pert_degree_lt r eps m hm)

lemma Bfam_natDegree (r eps : ℤ) {m : ℕ} (hm : 1 ≤ m) :
    (Bfam r eps m).natDegree = 2 * m + 2 := by
  unfold Bfam
  rw [natDegree_eq_of_degree_eq
    (degree_add_eq_left_of_degree_lt (pert_degree_lt r eps m hm))]
  exact lead_natDegree r m hm

/-- The real evaluation form. -/
lemma Bfam_eval_R (r eps : ℤ) (m : ℕ) (y : ℝ) :
    ((Bfam r eps m).map (Int.castRingHom ℝ)).eval y
      = (y ^ 2 - (r : ℝ) * y + 1) * (y ^ (2 * m) + 1) + (eps : ℝ) * y ^ (m + 1) := by
  simp only [Bfam, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X, Polynomial.map_C,
    eval_add, eval_mul, eval_sub, eval_pow, eval_one, eval_X, eval_C,
    Int.coe_castRingHom]

/-- The complex evaluation form. -/
lemma Bfam_eval_C (r eps : ℤ) (m : ℕ) (z : ℂ) :
    ((Bfam r eps m).map (Int.castRingHom ℂ)).eval z
      = (z ^ 2 - (r : ℂ) * z + 1) * (z ^ (2 * m) + 1) + (eps : ℂ) * z ^ (m + 1) := by
  simp only [Bfam, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X, Polynomial.map_C,
    eval_add, eval_mul, eval_sub, eval_pow, eval_one, eval_X, eval_C,
    Int.coe_castRingHom]

/-- **The key algebraic identity** (the whole "Chebyshev" content): for
`u ≠ 0`, `(u² − au + 1)(u^{2m} + 1) + b·u^{m+1}
= u^{m+1}·((u + u⁻¹ − a)(u^m + u^{−m}) + b)`. -/
lemma key_identity {K : Type*} [Field K] (a b : K) (m : ℕ) {u : K} (hu : u ≠ 0) :
    (u ^ 2 - a * u + 1) * (u ^ (2 * m) + 1) + b * u ^ (m + 1)
      = u ^ (m + 1) * ((u + u⁻¹ - a) * (u ^ m + (u⁻¹) ^ m) + b) := by
  have hc : u * u⁻¹ = 1 := mul_inv_cancel₀ hu
  have h1 : u * (u + u⁻¹ - a) = u ^ 2 - a * u + 1 := by
    calc u * (u + u⁻¹ - a) = u * u + u * u⁻¹ - a * u := by ring
      _ = u ^ 2 - a * u + 1 := by rw [hc]; ring
  have h2 : u ^ m * (u ^ m + (u⁻¹) ^ m) = u ^ (2 * m) + 1 := by
    have hcm : u ^ m * (u⁻¹) ^ m = 1 := by rw [← mul_pow, hc, one_pow]
    calc u ^ m * (u ^ m + (u⁻¹) ^ m) = u ^ m * u ^ m + u ^ m * (u⁻¹) ^ m := by ring
      _ = u ^ (2 * m) + 1 := by rw [hcm]; ring
  calc (u ^ 2 - a * u + 1) * (u ^ (2 * m) + 1) + b * u ^ (m + 1)
      = (u * (u + u⁻¹ - a)) * (u ^ m * (u ^ m + (u⁻¹) ^ m)) + b * u ^ (m + 1) := by
        rw [h1, h2]
    _ = u ^ (m + 1) * ((u + u⁻¹ - a) * (u ^ m + (u⁻¹) ^ m) + b) := by ring

/-- **Self-inversive, both signs**: `z^{2m+2}·B(1/z) = B(z)` for `z ≠ 0`
— the middle monomial `X^{m+1}` is its own reverse. -/
lemma Bfam_self_inversive (r eps : ℤ) (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    z ^ (2 * m + 2) * ((Bfam r eps m).map (Int.castRingHom ℂ)).eval z⁻¹
      = ((Bfam r eps m).map (Int.castRingHom ℂ)).eval z := by
  rw [Bfam_eval_C, Bfam_eval_C]
  have hc : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  have h1 : z ^ 2 * ((z⁻¹) ^ 2 - (r : ℂ) * z⁻¹ + 1) = 1 - (r : ℂ) * z + z ^ 2 := by
    have h2 : z ^ 2 * (z⁻¹) ^ 2 = 1 := by rw [← mul_pow, hc, one_pow]
    have h3 : z ^ 2 * z⁻¹ = z := by
      calc z ^ 2 * z⁻¹ = z * (z * z⁻¹) := by ring
        _ = z := by rw [hc]; ring
    calc z ^ 2 * ((z⁻¹) ^ 2 - (r : ℂ) * z⁻¹ + 1)
        = z ^ 2 * (z⁻¹) ^ 2 - (r : ℂ) * (z ^ 2 * z⁻¹) + z ^ 2 := by ring
      _ = 1 - (r : ℂ) * z + z ^ 2 := by rw [h2, h3]
  have h4 : z ^ (2 * m) * ((z⁻¹) ^ (2 * m) + 1) = 1 + z ^ (2 * m) := by
    have h5 : z ^ (2 * m) * (z⁻¹) ^ (2 * m) = 1 := by rw [← mul_pow, hc, one_pow]
    calc z ^ (2 * m) * ((z⁻¹) ^ (2 * m) + 1)
        = z ^ (2 * m) * (z⁻¹) ^ (2 * m) + z ^ (2 * m) := by ring
      _ = 1 + z ^ (2 * m) := by rw [h5]
  have h6 : z ^ (m + 1) * (z⁻¹) ^ (m + 1) = 1 := by rw [← mul_pow, hc, one_pow]
  calc z ^ (2 * m + 2)
        * (((z⁻¹) ^ 2 - (r : ℂ) * z⁻¹ + 1) * ((z⁻¹) ^ (2 * m) + 1)
          + (eps : ℂ) * (z⁻¹) ^ (m + 1))
      = (z ^ 2 * ((z⁻¹) ^ 2 - (r : ℂ) * z⁻¹ + 1))
          * (z ^ (2 * m) * ((z⁻¹) ^ (2 * m) + 1))
        + (eps : ℂ) * (z ^ (m + 1) * (z⁻¹) ^ (m + 1)) * z ^ (m + 1) := by ring
    _ = (1 - (r : ℂ) * z + z ^ 2) * (1 + z ^ (2 * m))
        + (eps : ℂ) * 1 * z ^ (m + 1) := by rw [h1, h4, h6]
    _ = (z ^ 2 - (r : ℂ) * z + 1) * (z ^ (2 * m) + 1) + (eps : ℂ) * z ^ (m + 1) := by
        ring

/-- The pairing: a nonzero root of `B` pairs with its inverse. -/
lemma Bfam_root_inv (r eps : ℤ) (m : ℕ) {z : ℂ} (hz : z ≠ 0)
    (hroot : ((Bfam r eps m).map (Int.castRingHom ℂ)).eval z = 0) :
    ((Bfam r eps m).map (Int.castRingHom ℂ)).eval z⁻¹ = 0 := by
  have key := Bfam_self_inversive r eps m hz
  rw [hroot] at key
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (pow_ne_zero _ hz)
  · exact h

/-! ### The circle count — `2m` distinct unimodular roots -/

/-- The real sign function on the circle:
`B(E t) = E((m+1)t)·h(t)` with `h t = (2cos t − r)·2cos(mt) + eps`. -/
def hfun (r eps : ℤ) (m : ℕ) (t : ℝ) : ℝ :=
  (2 * Real.cos t - (r : ℝ)) * (2 * Real.cos ((m : ℝ) * t)) + (eps : ℝ)

lemma continuous_hfun (r eps : ℤ) (m : ℕ) : Continuous (hfun r eps m) := by
  unfold hfun
  fun_prop

/-- **The key identity on the circle** (no phase, no `arg`):
`B(E t) = E((m+1)t)·h(t)`. -/
lemma Bfam_eval_E (r eps : ℤ) (m : ℕ) (t : ℝ) :
    ((Bfam r eps m).map (Int.castRingHom ℂ)).eval (E t)
      = E (((m : ℝ) + 1) * t) * ((hfun r eps m t : ℝ) : ℂ) := by
  have hu : E t ≠ 0 := E_ne_zero t
  have hinv : (E t)⁻¹ = E (-t) := inv_eq_of_mul_eq_one_right (E_mul_E_neg t)
  rw [Bfam_eval_C, key_identity ((r : ℂ)) ((eps : ℂ)) m hu, hinv]
  have h5 : E t ^ (m + 1) = E (((m : ℝ) + 1) * t) := by
    rw [E_pow]
    exact E_congr (by push_cast; ring)
  have h2 : E t ^ m = E ((m : ℝ) * t) := E_pow m t
  have h3 : E (-t) ^ m = E (-((m : ℝ) * t)) := by
    rw [E_pow]
    exact E_congr (by ring)
  rw [h5, h2, h3, E_add_E_neg t, E_add_E_neg ((m : ℝ) * t)]
  unfold hfun
  push_cast
  ring

/-- The zero test on the circle: `B(E t) = 0 ↔ h(t) = 0`. -/
lemma Bfam_eval_E_eq_zero_iff (r eps : ℤ) (m : ℕ) (t : ℝ) :
    ((Bfam r eps m).map (Int.castRingHom ℂ)).eval (E t) = 0 ↔ hfun r eps m t = 0 := by
  rw [Bfam_eval_E]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (E_ne_zero _)
    · exact_mod_cast h
  · intro h
    rw [h]
    simp

/-- `h` on the grid `t_k = kπ/m`: the second cosine collapses to
`(−1)^k`. -/
lemma hfun_at_grid (r eps : ℤ) {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    hfun r eps m ((k : ℝ) * Real.pi / (m : ℝ))
      = (2 * Real.cos ((k : ℝ) * Real.pi / (m : ℝ)) - (r : ℝ)) * (2 * (-1 : ℝ) ^ k)
        + (eps : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold hfun
  have harg : (m : ℝ) * ((k : ℝ) * Real.pi / (m : ℝ)) = (k : ℝ) * Real.pi := by
    field_simp
  rw [harg, Real.cos_nat_mul_pi]

/-- The alternation, even leg: `h(t_k) < 0` for `k` even — REGARDLESS
of the sign `eps = ±1` (`|eps| = 1 < 2 ≤ |product|`). -/
lemma hfun_grid_neg (r eps : ℤ) (hr : 3 ≤ r) (heps : eps = 1 ∨ eps = -1)
    {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (hk : Even k) :
    hfun r eps m ((k : ℝ) * Real.pi / (m : ℝ)) < 0 := by
  rw [hfun_at_grid r eps hm k, hk.neg_one_pow]
  have hcos : Real.cos ((k : ℝ) * Real.pi / (m : ℝ)) ≤ 1 := Real.cos_le_one _
  have hrR : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  rcases heps with h | h <;> rw [h] <;> push_cast <;> nlinarith

/-- The alternation, odd leg: `0 < h(t_k)` for `k` odd. -/
lemma hfun_grid_pos (r eps : ℤ) (hr : 3 ≤ r) (heps : eps = 1 ∨ eps = -1)
    {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (hk : Odd k) :
    0 < hfun r eps m ((k : ℝ) * Real.pi / (m : ℝ)) := by
  rw [hfun_at_grid r eps hm k, hk.neg_one_pow]
  have hcos : Real.cos ((k : ℝ) * Real.pi / (m : ℝ)) ≤ 1 := Real.cos_le_one _
  have hrR : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  rcases heps with h | h <;> rw [h] <;> push_cast <;> nlinarith

/-- **The circle count**: `B` has `2m` distinct roots
`E t`, `t ∈ (0, 2π)` — one in each open grid interval
`(kπ/m, (k+1)π/m)`, `k = 0, …, 2m − 1`, by sign alternation. -/
theorem circle_count (r eps : ℤ) (hr : 3 ≤ r) (heps : eps = 1 ∨ eps = -1)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ T : Finset ℝ, T.card = 2 * m ∧ ∀ t ∈ T, (0 < t ∧ t < 2 * Real.pi) ∧
      ((Bfam r eps m).map (Int.castRingHom ℂ)).eval (E t) = 0 := by
  classical
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  set g : ℕ → ℝ := fun k => (k : ℝ) * Real.pi / (m : ℝ) with hg
  have hgmono : ∀ j k : ℕ, j < k → g j < g k := by
    intro j k hjk
    have hjkR : (j : ℝ) < (k : ℝ) := by exact_mod_cast hjk
    simp only [hg]
    gcongr
  have hgle : ∀ j k : ℕ, j ≤ k → g j ≤ g k := by
    intro j k hjk
    rcases eq_or_lt_of_le hjk with h | h
    · rw [h]
    · exact le_of_lt (hgmono j k h)
  have hg0 : g 0 = 0 := by simp [hg]
  have hg2m : g (2 * m) = 2 * Real.pi := by
    have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmR
    simp only [hg]
    push_cast
    field_simp
  have hsign : ∀ k : ℕ, hfun r eps m (g k) * hfun r eps m (g (k + 1)) < 0 := by
    intro k
    rcases Nat.even_or_odd k with hk | hk
    · exact mul_neg_of_neg_of_pos (hfun_grid_neg r eps hr heps hm k hk)
        (hfun_grid_pos r eps hr heps hm (k + 1) hk.add_one)
    · exact mul_neg_of_pos_of_neg (hfun_grid_pos r eps hr heps hm k hk)
        (hfun_grid_neg r eps hr heps hm (k + 1) hk.add_one)
  have hex : ∀ k : ℕ, ∃ s : ℝ, g k < s ∧ s < g (k + 1) ∧ hfun r eps m s = 0 :=
    fun k => exists_root_between (hfun r eps m) (g k) (g (k + 1))
      (hgmono k (k + 1) (by omega)) (continuous_hfun r eps m).continuousOn (hsign k)
  choose sf hs1 hs2 hs3 using hex
  refine ⟨(Finset.range (2 * m)).image sf, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro j _ j' _ heq
    by_contra hne
    rcases Nat.lt_or_ge j j' with h | h
    · have h1 := hs2 j
      have h2 := hs1 j'
      have h3 : g (j + 1) ≤ g j' := hgle _ _ (by omega)
      rw [heq] at h1
      linarith
    · have hlt : j' < j := by omega
      have h1 := hs2 j'
      have h2 := hs1 j
      have h3 : g (j' + 1) ≤ g j := hgle _ _ (by omega)
      rw [← heq] at h1
      linarith
  · intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    have hkm : k < 2 * m := Finset.mem_range.mp hk
    refine ⟨⟨?_, ?_⟩, (Bfam_eval_E_eq_zero_iff r eps m (sf k)).mpr (hs3 k)⟩
    · calc (0 : ℝ) = g 0 := hg0.symm
        _ ≤ g k := hgle 0 k (by omega)
        _ < sf k := hs1 k
    · calc sf k < g (k + 1) := hs2 k
        _ ≤ g (2 * m) := hgle (k + 1) (2 * m) (by omega)
        _ = 2 * Real.pi := hg2m

/-! ### The ladder roots — direct endpoint signs -/

/-- At `alpha` the leading factor vanishes: `B(alpha) = eps·alpha^{m+1}`. -/
lemma eval_at_alpha (r eps : ℤ) {alpha : ℝ}
    (hmin : alpha ^ 2 = (r : ℝ) * alpha - 1) (m : ℕ) :
    ((Bfam r eps m).map (Int.castRingHom ℝ)).eval alpha
      = (eps : ℝ) * alpha ^ (m + 1) := by
  rw [Bfam_eval_R]
  have h : alpha ^ 2 - (r : ℝ) * alpha + 1 = 0 := by linarith
  rw [h, zero_mul, zero_add]

/-- Above sign: with `y = alpha + d`, `0 < d ≤ 1` and
`alpha + 1 < d·(alpha − 1/alpha)·2^m`, the `eps = −1` member is
positive at `y` — the second factor `y^m ≥ alpha^m > 2^m` cancels the
`2^{−m}` displacement. -/
lemma eval_above_pos (r : ℤ) {alpha : ℝ} (halpha2 : 2 < alpha)
    (hmin : alpha ^ 2 = (r : ℝ) * alpha - 1)
    (m : ℕ) {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hdm : alpha + 1 < d * (alpha - alpha⁻¹) * 2 ^ m) :
    0 < ((Bfam r (-1) m).map (Int.castRingHom ℝ)).eval (alpha + d) := by
  have halpha : 1 < alpha := by linarith
  have hfac := quad_factor halpha hmin
  have hainv1 : alpha⁻¹ < 1 := inv_lt_one_of_one_lt₀ halpha
  have hainv0 : 0 < alpha⁻¹ := inv_pos.mpr (by linarith)
  set y := alpha + d with hy
  have hy2 : (2 : ℝ) < y := by rw [hy]; linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hda : y - alpha = d := by rw [hy]; ring
  have hympos : (0 : ℝ) < y ^ m := pow_pos hy0 m
  have hym : (2 : ℝ) ^ m ≤ y ^ m := pow_le_pow_left₀ (by norm_num) (by linarith) m
  have hyle : y ≤ alpha + 1 := by rw [hy]; linarith
  have hB : alpha + 1 < d * (y - alpha⁻¹) * y ^ m := by
    calc alpha + 1 < d * (alpha - alpha⁻¹) * 2 ^ m := hdm
      _ ≤ d * (alpha - alpha⁻¹) * y ^ m :=
          mul_le_mul_of_nonneg_left hym (mul_nonneg hd0.le (by linarith))
      _ ≤ d * (y - alpha⁻¹) * y ^ m :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by rw [hy]; linarith) hd0.le) hympos.le
  have hgoal : y * y ^ m < d * (y - alpha⁻¹) * (y ^ m * y ^ m + 1) := by
    have hstep1 : y * y ^ m ≤ (alpha + 1) * y ^ m :=
      mul_le_mul_of_nonneg_right hyle hympos.le
    have hstep2 : (alpha + 1) * y ^ m < d * (y - alpha⁻¹) * y ^ m * y ^ m :=
      mul_lt_mul_of_pos_right hB hympos
    have hstep3 : d * (y - alpha⁻¹) * y ^ m * y ^ m
        ≤ d * (y - alpha⁻¹) * (y ^ m * y ^ m + 1) := by
      have hpos : (0 : ℝ) ≤ d * (y - alpha⁻¹) :=
        mul_nonneg hd0.le (by rw [hy]; linarith)
      nlinarith [hpos]
    linarith
  rw [Bfam_eval_R, hfac y]
  push_cast
  have h2m : y ^ (2 * m) = y ^ m * y ^ m := by rw [two_mul, pow_add]
  have hm1 : y ^ (m + 1) = y * y ^ m := by rw [pow_succ, mul_comm]
  rw [h2m, hm1, hda]
  nlinarith [hgoal]

/-- Below sign: with `y = alpha − d ≥ 2`, `0 < d` and `alpha < d·2^m`,
the `eps = +1` member is negative at `y`. -/
lemma eval_below_neg (r : ℤ) {alpha : ℝ} (halpha2 : 2 < alpha)
    (hmin : alpha ^ 2 = (r : ℝ) * alpha - 1)
    (m : ℕ) {d : ℝ} (hd0 : 0 < d) (hd2 : d ≤ alpha - 2)
    (hdm : alpha < d * 2 ^ m) :
    ((Bfam r 1 m).map (Int.castRingHom ℝ)).eval (alpha - d) < 0 := by
  have halpha : 1 < alpha := by linarith
  have hfac := quad_factor halpha hmin
  have hainv1 : alpha⁻¹ < 1 := inv_lt_one_of_one_lt₀ halpha
  have hainv0 : 0 < alpha⁻¹ := inv_pos.mpr (by linarith)
  set y := alpha - d with hy
  have hy2 : (2 : ℝ) ≤ y := by rw [hy]; linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hda : y - alpha = -d := by rw [hy]; ring
  have hya : y < alpha := by rw [hy]; linarith
  have hympos : (0 : ℝ) < y ^ m := pow_pos hy0 m
  have hym : (2 : ℝ) ^ m ≤ y ^ m := pow_le_pow_left₀ (by norm_num) hy2 m
  have hA1 : (1 : ℝ) ≤ y - alpha⁻¹ := by linarith
  have hgoal : y * y ^ m < d * (y - alpha⁻¹) * (y ^ m * y ^ m + 1) := by
    have hstep1 : y * y ^ m < d * 2 ^ m * y ^ m :=
      mul_lt_mul_of_pos_right (by linarith) hympos
    have hstep2 : d * 2 ^ m * y ^ m ≤ d * y ^ m * y ^ m :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hym hd0.le) hympos.le
    have hstep3 : d * y ^ m * y ^ m ≤ d * (y - alpha⁻¹) * (y ^ m * y ^ m) := by
      nlinarith [mul_nonneg (mul_nonneg hd0.le
        (by linarith : (0 : ℝ) ≤ y - alpha⁻¹ - 1)) (mul_nonneg hympos.le hympos.le)]
    have hstep4 : d * (y - alpha⁻¹) * (y ^ m * y ^ m)
        ≤ d * (y - alpha⁻¹) * (y ^ m * y ^ m + 1) := by
      have hpos : (0 : ℝ) ≤ d * (y - alpha⁻¹) := mul_nonneg hd0.le (by linarith)
      nlinarith [hpos]
    linarith
  rw [Bfam_eval_R, hfac y]
  push_cast
  have h2m : y ^ (2 * m) = y ^ m * y ^ m := by rw [two_mul, pow_add]
  have hm1 : y ^ (m + 1) = y * y ^ m := by rw [pow_succ, mul_comm]
  rw [h2m, hm1, hda]
  nlinarith [hgoal]

/-- The exact trace displacement at a root:
`(tau + 1/tau − r)·(tau^m + tau^{−m}) = −eps`. -/
lemma trace_displacement (r eps : ℤ) (m : ℕ) {tau : ℝ} (htau0 : 0 < tau)
    (hroot : ((Bfam r eps m).map (Int.castRingHom ℝ)).eval tau = 0) :
    (tau + tau⁻¹ - (r : ℝ)) * (tau ^ m + (tau⁻¹) ^ m) = -(eps : ℝ) := by
  have h0 : tau ≠ 0 := ne_of_gt htau0
  rw [Bfam_eval_R, key_identity ((r : ℝ)) ((eps : ℝ)) m h0] at hroot
  rcases mul_eq_zero.mp hroot with h | h
  · exact absurd h (pow_ne_zero _ h0)
  · linarith

/-- Direct exclusion of the trace degeneracy: at a root `tau > 2` the
trace `tau + 1/tau` differs from `r` by `0 < |·| < 1/2`, so it is not
an integer. -/
lemma trace_not_int (r eps : ℤ) (heps : eps = 1 ∨ eps = -1) {m : ℕ} (hm : 1 ≤ m)
    {tau : ℝ} (htau2 : 2 < tau)
    (hroot : ((Bfam r eps m).map (Int.castRingHom ℝ)).eval tau = 0) :
    ∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ) := by
  intro n hn
  have htau0 : (0 : ℝ) < tau := by linarith
  have hd := trace_displacement r eps m htau0 hroot
  have hinvpos : (0 : ℝ) < (tau⁻¹) ^ m := by positivity
  have htm : tau ≤ tau ^ m := le_self_pow₀ (by linarith) (by omega)
  have hS : (2 : ℝ) < tau ^ m + (tau⁻¹) ^ m := by linarith
  have hSpos : (0 : ℝ) < tau ^ m + (tau⁻¹) ^ m := by linarith
  rw [hn] at hd
  rcases eq_or_ne n r with hnr | hnr
  · rw [hnr, sub_self, zero_mul] at hd
    rcases heps with h | h <;> rw [h] at hd <;> norm_num at hd
  · have h1 : (1 : ℝ) ≤ |(n : ℝ) - (r : ℝ)| := by
      have hz : (1 : ℤ) ≤ |n - r| := Int.one_le_abs (sub_ne_zero.mpr hnr)
      have hcast : ((1 : ℤ) : ℝ) ≤ ((|n - r| : ℤ) : ℝ) := by exact_mod_cast hz
      rwa [Int.cast_one, Int.cast_abs, Int.cast_sub] at hcast
    have h2 : (2 : ℝ) < |((n : ℝ) - (r : ℝ)) * (tau ^ m + (tau⁻¹) ^ m)| := by
      rw [abs_mul, abs_of_pos hSpos]
      calc (2 : ℝ) < tau ^ m + (tau⁻¹) ^ m := hS
        _ = 1 * (tau ^ m + (tau⁻¹) ^ m) := (one_mul _).symm
        _ ≤ |(n : ℝ) - (r : ℝ)| * (tau ^ m + (tau⁻¹) ^ m) :=
            mul_le_mul_of_nonneg_right h1 hSpos.le
    rw [hd] at h2
    rcases heps with h | h <;> rw [h] at h2 <;> norm_num at h2

/-! ### The trichotomy — the third multiset squeeze -/

/-- **The trichotomy for the quadratic-unit family**: if `tau > 1` is a
root of `B`, then EVERY complex root is unimodular or lies in
`{tau, 1/tau}` — the `2m` circle points, `tau`, and `1/tau` already
exhaust the degree `2m + 2`. -/
theorem Bfam_trichotomy (r eps : ℤ) (hr : 3 ≤ r) (heps : eps = 1 ∨ eps = -1)
    {m : ℕ} (hm : 1 ≤ m) (tau : ℝ) (htau : 1 < tau)
    (hroot : ((Bfam r eps m).map (Int.castRingHom ℂ)).eval ((tau : ℂ)) = 0) :
    ∀ z : ℂ, ((Bfam r eps m).map (Int.castRingHom ℂ)).eval z = 0 →
      ‖z‖ = 1 ∨ z = ((tau : ℂ)) ∨ z = ((tau : ℂ))⁻¹ := by
  classical
  obtain ⟨T, hcard, hT⟩ := circle_count r eps hr heps hm
  have hUcard : (T.image fun t => E t).card = 2 * m := by
    rw [← hcard]
    apply Finset.card_image_of_injOn
    intro t ht s hs heq
    exact E_inj (hT t (Finset.mem_coe.mp ht)).1.1 (hT t (Finset.mem_coe.mp ht)).1.2
      (hT s (Finset.mem_coe.mp hs)).1.1 (hT s (Finset.mem_coe.mp hs)).1.2 heq
  have hUnorm : ∀ z ∈ T.image fun t => E t, ‖z‖ = 1 := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    exact norm_E t
  have htaupos : (0 : ℝ) < tau := by linarith
  have htau0 : ((tau : ℂ)) ≠ 0 := by
    intro h
    rw [Complex.ofReal_eq_zero] at h
    linarith
  have htau_norm : ‖((tau : ℂ))‖ = tau := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htaupos]
  have htauinv_norm : ‖((tau : ℂ))⁻¹‖ = tau⁻¹ := by
    rw [norm_inv, htau_norm]
  have htinv1 : tau⁻¹ < 1 := inv_lt_one_of_one_lt₀ htau
  have htau_ne : ((tau : ℂ)) ≠ ((tau : ℂ))⁻¹ := by
    intro h
    have h1 : ‖((tau : ℂ))‖ = ‖((tau : ℂ))⁻¹‖ := by rw [← h]
    rw [htau_norm, htauinv_norm] at h1
    linarith
  have hdisj : Disjoint (T.image fun t => E t)
      ({((tau : ℂ)), ((tau : ℂ))⁻¹} : Finset ℂ) := by
    rw [Finset.disjoint_left]
    intro z hzU hzV
    have h1 := hUnorm z hzU
    rcases Finset.mem_insert.mp hzV with h | h
    · rw [h, htau_norm] at h1; linarith
    · rw [Finset.mem_singleton.mp h, htauinv_norm] at h1; linarith
  have hpair : ({((tau : ℂ)), ((tau : ℂ))⁻¹} : Finset ℂ).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr htau_ne
  set S : Finset ℂ := (T.image fun t => E t) ∪ {((tau : ℂ)), ((tau : ℂ))⁻¹} with hS
  have hScard : S.card = 2 * m + 2 := by
    rw [hS, Finset.card_union_of_disjoint hdisj, hUcard, hpair]
  have hSroot : ∀ z ∈ S, ((Bfam r eps m).map (Int.castRingHom ℂ)).eval z = 0 := by
    intro z hz
    rw [hS, Finset.mem_union] at hz
    rcases hz with h | h
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      exact (hT t ht).2
    · rcases Finset.mem_insert.mp h with h1 | h1
      · rw [h1]; exact hroot
      · rw [Finset.mem_singleton.mp h1]
        exact Bfam_root_inv r eps m htau0 hroot
  have hBCmonic : ((Bfam r eps m).map (Int.castRingHom ℂ)).Monic :=
    (Bfam_monic r eps hm).map _
  have hBCdeg : ((Bfam r eps m).map (Int.castRingHom ℂ)).natDegree = 2 * m + 2 := by
    rw [(Bfam_monic r eps hm).natDegree_map]
    exact Bfam_natDegree r eps hm
  have hBne : (Bfam r eps m).map (Int.castRingHom ℂ) ≠ 0 := hBCmonic.ne_zero
  have hle : S.val ≤ ((Bfam r eps m).map (Int.castRingHom ℂ)).roots := by
    rw [Multiset.le_iff_count]
    intro z
    by_cases hz : z ∈ S
    · rw [Multiset.count_eq_one_of_mem S.nodup (Finset.mem_def.mp hz),
        Polynomial.count_roots]
      have hpos := (Polynomial.rootMultiplicity_pos hBne).mpr (hSroot z hz)
      omega
    · rw [Multiset.count_eq_zero.mpr (fun hv => hz (Finset.mem_def.mpr hv))]
      exact Nat.zero_le _
  have hcards : Multiset.card (((Bfam r eps m).map (Int.castRingHom ℂ)).roots)
      ≤ Multiset.card S.val := by
    have h1 := Polynomial.card_roots' ((Bfam r eps m).map (Int.castRingHom ℂ))
    rw [hBCdeg] at h1
    have h2 : Multiset.card S.val = S.card := rfl
    omega
  have heq : S.val = ((Bfam r eps m).map (Int.castRingHom ℂ)).roots :=
    Multiset.eq_of_le_of_card_le hle hcards
  intro z hz
  have hzmem : z ∈ ((Bfam r eps m).map (Int.castRingHom ℂ)).roots :=
    Polynomial.mem_roots'.mpr ⟨hBne, hz⟩
  rw [← heq] at hzmem
  have hzS : z ∈ S := Finset.mem_def.mpr hzmem
  rw [hS, Finset.mem_union] at hzS
  rcases hzS with h | h
  · exact Or.inl (hUnorm z h)
  · rcases Finset.mem_insert.mp h with h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Finset.mem_singleton.mp h1))

/-! ### The arithmetic Salem-ness certificate — the second port -/

/-- **The arithmetic certificate for the quadratic-unit family** — the
third certificate, the second verbatim port of
`PdtSalemArith.salem_certificate`: a real root
`tau > 1` of `B`, excluded from the two integer degeneracies, is an
algebraic integer whose conjugates fill the closed unit disk, one ON
the circle, with `1/tau` among them. -/
theorem salem_certificate_quad (r eps : ℤ) (hr : 3 ≤ r) (heps : eps = 1 ∨ eps = -1)
    {m : ℕ} (hm : 1 ≤ m) (tau : ℝ) (htau : 1 < tau)
    (hroot : ((Bfam r eps m).map (Int.castRingHom ℝ)).eval tau = 0)
    (hτZ : ∀ n : ℤ, tau ≠ (n : ℝ))
    (hτtr : ∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ)) :
    IsIntegral ℤ tau ∧
    (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 → z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
    (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
    (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0 := by
  classical
  -- bridge plumbing
  have hBzMonic : (Bfam r eps m).Monic := Bfam_monic r eps hm
  have haevalB : Polynomial.aeval tau (Bfam r eps m) = 0 := by
    rw [SalemArith.aeval_eq_eval_map, algebraMap_int_eq]
    exact hroot
  -- integrality
  have hint : IsIntegral ℤ tau := by
    refine ⟨Bfam r eps m, hBzMonic, ?_⟩
    rw [← Polynomial.aeval_def]
    exact haevalB
  have hQint : IsIntegral ℚ tau := hint.tower_top
  -- the family root over ℂ, and the trichotomy
  have hBC : ((Bfam r eps m).map (Int.castRingHom ℂ)).eval ((tau : ℂ)) = 0 := by
    rw [SalemEndgame.eval_int_transfer, hroot]
    exact Complex.ofReal_zero
  have htri : ∀ z : ℂ, ((Bfam r eps m).map (Int.castRingHom ℂ)).eval z = 0 →
      ‖z‖ = 1 ∨ z = ((tau : ℂ)) ∨ z = ((tau : ℂ))⁻¹ :=
    Bfam_trichotomy r eps hr heps hm tau htau hBC
  -- the minimal polynomial divides, so conjugates are roots of `B`
  have hmpdvd : minpoly ℚ tau ∣ (Bfam r eps m).map (Int.castRingHom ℚ) := by
    apply minpoly.dvd ℚ tau
    rw [← algebraMap_int_eq, Polynomial.aeval_map_algebraMap]
    exact haevalB
  have hdvdC : (minpoly ℚ tau).map (algebraMap ℚ ℂ)
      ∣ (Bfam r eps m).map (Int.castRingHom ℂ) := by
    have h1 : (minpoly ℚ tau).map (algebraMap ℚ ℂ) ∣
        ((Bfam r eps m).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) :=
      Polynomial.map_dvd _ hmpdvd
    rwa [Polynomial.map_map, SalemArith.castQC_triangle] at h1
  have hcontain : ∀ z : ℂ, ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval z = 0 →
      ((Bfam r eps m).map (Int.castRingHom ℂ)).eval z = 0 := by
    intro z hz
    obtain ⟨c, hc⟩ := hdvdC
    rw [hc, Polynomial.eval_mul, hz, zero_mul]
  have haevalC : ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ tau)
      = ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval z := fun z =>
    SalemArith.aeval_eq_eval_map _ z
  have htauCroot : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval ((tau : ℂ)) = 0 := by
    rw [← haevalC, SalemArith.aeval_ofReal, minpoly.aeval, Complex.ofReal_zero]
  -- scalar facts about `tau`
  have htaupos : (0 : ℝ) < tau := by linarith
  have htau_norm : ‖((tau : ℂ))‖ = tau := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htaupos]
  have htauinv_norm : ‖((tau : ℂ))⁻¹‖ = tau⁻¹ := by rw [norm_inv, htau_norm]
  have htinv1 : tau⁻¹ < 1 := inv_lt_one_of_one_lt₀ htau
  -- the closed disk
  have hdisk : ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ tau) = 0 →
      z ≠ ((tau : ℂ)) → ‖z‖ ≤ 1 := by
    intro z hz hzne
    have hz0 : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval z = 0 := by
      rw [← haevalC]; exact hz
    rcases htri z (hcontain z hz0) with h | h | h
    · exact le_of_eq h
    · exact absurd h hzne
    · rw [h, htauinv_norm]; linarith
  -- the Gauss step — every coefficient of the minimal polynomial
  -- over ℚ is the cast of an integer
  have hmz : minpoly ℚ tau = (minpoly ℤ tau).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hcoeff : ∀ i : ℕ,
      (minpoly ℚ tau).coeff i = (((minpoly ℤ tau).coeff i : ℤ) : ℚ) := by
    intro i
    rw [hmz, Polynomial.coeff_map, eq_intCast]
  -- splitting data for the complex minimal polynomial
  have hmpmonic : (minpoly ℚ tau).Monic := minpoly.monic hQint
  have hmpirr : Irreducible (minpoly ℚ tau) := minpoly.irreducible hQint
  have hmpsep : (minpoly ℚ tau).Separable := hmpirr.separable
  have hsepC : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).Separable := hmpsep.map
  have hnodup : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.Nodup :=
    Polynomial.nodup_roots hsepC
  have hmonicC : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).Monic := hmpmonic.map _
  have hCne : (minpoly ℚ tau).map (algebraMap ℚ ℂ) ≠ 0 := hmonicC.ne_zero
  have hsplits : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).Splits :=
    IsAlgClosed.splits _
  have hdegC : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).natDegree
      = (minpoly ℚ tau).natDegree := hmpmonic.natDegree_map _
  have hcard : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.card
      = (minpoly ℚ tau).natDegree := by
    rw [← hdegC]
    exact hsplits.natDegree_eq_card_roots.symm
  have hdegpos : 0 < (minpoly ℚ tau).natDegree := minpoly.natDegree_pos hQint
  have hmem : ∀ z : ℂ, z ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots ↔
      ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval z = 0 := by
    intro z
    rw [Polynomial.mem_roots']
    exact ⟨fun h => h.2, fun h => ⟨hCne, h⟩⟩
  have htauC_mem : ((tau : ℂ)) ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots :=
    (hmem _).mpr htauCroot
  -- a conjugate ON the circle
  have hcircle : ∃ z : ℂ, Polynomial.aeval z (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1 := by
    by_contra hno
    simp only [not_exists, not_and] at hno
    have hpair : ∀ z ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots,
        z = ((tau : ℂ)) ∨ z = ((tau : ℂ))⁻¹ := by
      intro z hz
      have hz0 := (hmem z).mp hz
      have hz1 : Polynomial.aeval z (minpoly ℚ tau) = 0 := by
        rw [haevalC]; exact hz0
      rcases htri z (hcontain z hz0) with h | h | h
      · exact absurd h (hno z hz1)
      · exact Or.inl h
      · exact Or.inr h
    have hsub : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.toFinset ⊆
        ({((tau : ℂ)), ((tau : ℂ))⁻¹} : Finset ℂ) := by
      intro z hz
      rcases hpair z (Multiset.mem_toFinset.mp hz) with h | h
      · exact Finset.mem_insert.mpr (Or.inl h)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
    have hdeg2 : (minpoly ℚ tau).natDegree ≤ 2 := by
      have h1 := Finset.card_le_card hsub
      have h2 : ({((tau : ℂ)), ((tau : ℂ))⁻¹} : Finset ℂ).card ≤ 2 := by
        apply le_trans (Finset.card_insert_le _ _)
        simp
      have h3 : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.toFinset.card
          = ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.card :=
        Multiset.toFinset_card_eq_card_iff_nodup.mpr hnodup
      omega
    rcases (by omega :
        (minpoly ℚ tau).natDegree = 1 ∨ (minpoly ℚ tau).natDegree = 2) with h1 | h2
    · -- degree 1: `tau` would be a rational integer
      have heq : minpoly ℚ tau = X + Polynomial.C ((minpoly ℚ tau).coeff 0) :=
        hmpmonic.eq_X_add_C h1
      have haev := minpoly.aeval ℚ tau
      rw [heq, map_add, Polynomial.aeval_X, Polynomial.aeval_C, hcoeff 0,
        map_intCast] at haev
      exact hτZ (-(minpoly ℤ tau).coeff 0) (by push_cast; linarith)
    · -- degree 2: the root multiset is exactly {tau, 1/tau}, and Vieta on
      -- the X-coefficient makes `tau + 1/tau` a rational integer
      obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem htauC_mem
      have hcards := hcard
      rw [hrest, Multiset.card_cons] at hcards
      have hcard_rest : rest.card = 1 := by omega
      obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp hcard_rest
      have hnodup' := hnodup
      rw [hrest, Multiset.nodup_cons] at hnodup'
      have hbmem : b ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots := by
        rw [hrest, hb]
        exact Multiset.mem_cons_of_mem (Multiset.mem_singleton_self b)
      have hbval : b = ((tau : ℂ))⁻¹ := by
        rcases hpair b hbmem with h | h
        · exfalso
          apply hnodup'.1
          rw [hb, h]
          exact Multiset.mem_singleton_self _
        · exact h
      have hnext := hsplits.nextCoeff_eq_neg_sum_roots_of_monic hmonicC
      rw [Polynomial.nextCoeff_of_natDegree_pos (by rw [hdegC]; omega),
        hdegC, h2, hrest, hb, hbval, Multiset.sum_cons,
        Multiset.sum_singleton] at hnext
      rw [show (2 : ℕ) - 1 = 1 by norm_num] at hnext
      rw [Polynomial.coeff_map, hcoeff 1, map_intCast] at hnext
      have hreal : (((minpoly ℤ tau).coeff 1 : ℤ) : ℝ) = -(tau + tau⁻¹) := by
        exact_mod_cast hnext
      exact hτtr (-(minpoly ℤ tau).coeff 1) (by push_cast; linarith)
  -- `1/tau` is a conjugate
  have hinvroot : Polynomial.aeval (((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0 := by
    by_contra hne
    have hroots1 : ∀ z ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots,
        z ≠ ((tau : ℂ)) → ‖z‖ = 1 := by
      intro z hz hzne
      have hz0 := (hmem z).mp hz
      rcases htri z (hcontain z hz0) with h | h | h
      · exact h
      · exact absurd h hzne
      · exfalso
        apply hne
        rw [← h, haevalC z]
        exact hz0
    obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem htauC_mem
    have hnodup' := hnodup
    rw [hrest, Multiset.nodup_cons] at hnodup'
    have hrest1 : ∀ w ∈ rest, ‖w‖ = 1 := by
      intro w hw
      apply hroots1 w (by rw [hrest]; exact Multiset.mem_cons_of_mem hw)
      intro hwz
      exact hnodup'.1 (hwz ▸ hw)
    have hc0 := hsplits.coeff_zero_eq_prod_roots_of_monic hmonicC
    rw [hrest, Multiset.prod_cons] at hc0
    have hnorm : ‖((minpoly ℚ tau).map (algebraMap ℚ ℂ)).coeff 0‖ = tau := by
      rw [hc0, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        one_mul, htau_norm, SalemArith.norm_multiset_prod_eq_one rest hrest1,
        mul_one]
    rw [Polynomial.coeff_map, hcoeff 0, map_intCast,
      show ((((minpoly ℤ tau).coeff 0 : ℤ)) : ℂ)
        = (((((minpoly ℤ tau).coeff 0 : ℤ) : ℝ)) : ℂ) by norm_cast,
      Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs] at hnorm
    exact hτZ |(minpoly ℤ tau).coeff 0| hnorm.symm
  exact ⟨hint, hdisk, hcircle, hinvroot⟩

/-- The packaged certificate: a nondegenerate root `tau > 1` of the
quadratic-unit family is a Salem number. -/
lemma isSalem_of_quad_root (r eps : ℤ) (hr : 3 ≤ r) (heps : eps = 1 ∨ eps = -1)
    {m : ℕ} (hm : 1 ≤ m) (tau : ℝ) (htau : 1 < tau)
    (hroot : ((Bfam r eps m).map (Int.castRingHom ℝ)).eval tau = 0)
    (hτZ : ∀ n : ℤ, tau ≠ (n : ℝ))
    (hτtr : ∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ)) :
    SalemEndgame.IsSalem tau := by
  obtain ⟨hint, hdisk, hcirc, hinv⟩ :=
    salem_certificate_quad r eps hr heps hm tau htau hroot hτZ hτtr
  exact ⟨htau, hint, hdisk, hcirc, hinv⟩

/-! ### The degenerate case closed -/

/-- **The degenerate case closed**: Salem numbers approach a
reciprocal quadratic Pisot unit `alpha` (`alpha² = r·alpha − 1`,
`3 ≤ r`) from BOTH sides — the `eps = +1` member of the family plants a
root in `(alpha − δ, alpha)`, the `eps = −1` member in
`(alpha, alpha + δ)`, both inside the integer-free window `(r − 1, r)`,
and the certificate promotes them to Salem numbers. -/
theorem salem_two_sided_quad_unit (r : ℤ) (hr : 3 ≤ r)
    (alpha : ℝ) (halpha : 1 < alpha) (hmin : alpha ^ 2 = (r : ℝ) * alpha - 1)
    (eps : ℝ) (heps : 0 < eps) :
    (∃ tau : ℝ, SalemEndgame.IsSalem tau ∧ alpha - eps < tau ∧ tau < alpha) ∧
    (∃ tau : ℝ, SalemEndgame.IsSalem tau ∧ alpha < tau ∧ tau < alpha + eps) := by
  have halpha2 : 2 < alpha := alpha_gt_two hr halpha hmin
  have htr : alpha + alpha⁻¹ = (r : ℝ) := trace_eq halpha hmin
  have hainv1 : alpha⁻¹ < 1 := inv_lt_one_of_one_lt₀ halpha
  have hainv0 : 0 < alpha⁻¹ := inv_pos.mpr (by linarith)
  have hral : (r : ℝ) - 1 < alpha := r_sub_one_lt_alpha halpha hmin
  have haltr : alpha < (r : ℝ) := alpha_lt_r halpha hmin
  have h2pow : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  constructor
  · -- BELOW `alpha`: the `eps = +1` member
    obtain ⟨δ, hδ0, hδeps, hδa2, hδinv⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ eps ∧
        δ ≤ alpha - 2 ∧ δ ≤ (1 - alpha⁻¹) / 2 :=
      ⟨min eps (min (alpha - 2) ((1 - alpha⁻¹) / 2)),
        lt_min heps (lt_min (by linarith) (by linarith)),
        min_le_left _ _,
        le_trans (min_le_right _ _) (min_le_left _ _),
        le_trans (min_le_right _ _) (min_le_right _ _)⟩
    have hev : ∀ᶠ k : ℕ in atTop, alpha / δ < 2 ^ k := h2pow.eventually_gt_atTop _
    obtain ⟨m, hm1, hm2⟩ := (hev.and (eventually_ge_atTop 1)).exists
    have hdm : alpha < δ * 2 ^ m := by
      rw [div_lt_iff₀ hδ0] at hm1
      linarith
    have hsignA : 0 < ((Bfam r 1 m).map (Int.castRingHom ℝ)).eval alpha := by
      rw [eval_at_alpha r 1 hmin m]
      push_cast
      have hp : (0 : ℝ) < alpha ^ (m + 1) := pow_pos (by linarith) _
      linarith
    have hsignB := eval_below_neg r halpha2 hmin m hδ0 hδa2 hdm
    obtain ⟨tau, htau1, htau2, htauroot⟩ := exists_root_between
      (fun y => ((Bfam r 1 m).map (Int.castRingHom ℝ)).eval y)
      (alpha - δ) alpha (by linarith)
      (Polynomial.continuous _).continuousOn
      (mul_neg_of_neg_of_pos hsignB hsignA)
    have htaugt2 : 2 < tau := by linarith
    have htauwin1 : (r : ℝ) - 1 < tau := by
      have hkey : alpha - (1 - alpha⁻¹) = (r : ℝ) - 1 := by linarith
      linarith
    have htauwin2 : tau < (r : ℝ) := by linarith
    exact ⟨tau, isSalem_of_quad_root r 1 hr (Or.inl rfl) hm2 tau (by linarith)
      htauroot (no_int_in_window htauwin1 htauwin2)
      (trace_not_int r 1 (Or.inl rfl) hm2 htaugt2 htauroot),
      by linarith, htau2⟩
  · -- ABOVE `alpha`: the `eps = −1` member
    obtain ⟨δ, hδ0, hδeps, hδinv⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ eps ∧ δ ≤ alpha⁻¹ :=
      ⟨min eps alpha⁻¹, lt_min heps hainv0, min_le_left _ _, min_le_right _ _⟩
    have hδ1 : δ ≤ 1 := by linarith
    have hcpos : 0 < δ * (alpha - alpha⁻¹) := mul_pos hδ0 (by linarith)
    have hev : ∀ᶠ k : ℕ in atTop, (alpha + 1) / (δ * (alpha - alpha⁻¹)) < 2 ^ k :=
      h2pow.eventually_gt_atTop _
    obtain ⟨m, hm1, hm2⟩ := (hev.and (eventually_ge_atTop 1)).exists
    have hdm : alpha + 1 < δ * (alpha - alpha⁻¹) * 2 ^ m := by
      rw [div_lt_iff₀ hcpos] at hm1
      linarith
    have hsignA : ((Bfam r (-1) m).map (Int.castRingHom ℝ)).eval alpha < 0 := by
      rw [eval_at_alpha r (-1) hmin m]
      push_cast
      have hp : (0 : ℝ) < alpha ^ (m + 1) := pow_pos (by linarith) _
      linarith
    have hsignB := eval_above_pos r halpha2 hmin m hδ0 hδ1 hdm
    obtain ⟨tau, htau1, htau2, htauroot⟩ := exists_root_between
      (fun y => ((Bfam r (-1) m).map (Int.castRingHom ℝ)).eval y)
      alpha (alpha + δ) (by linarith)
      (Polynomial.continuous _).continuousOn
      (mul_neg_of_neg_of_pos hsignA hsignB)
    have htaugt2 : 2 < tau := by linarith
    have htauwin1 : (r : ℝ) - 1 < tau := by linarith
    have htauwin2 : tau < (r : ℝ) := by linarith
    exact ⟨tau, isSalem_of_quad_root r (-1) hr (Or.inr rfl) hm2 tau (by linarith)
      htauroot (no_int_in_window htauwin1 htauwin2)
      (trace_not_int r (-1) (Or.inr rfl) hm2 htaugt2 htauroot),
      htau1, by linarith⟩

/-! ### The reduction and the full theorem -/

/-- The reflect-evaluation identity over ℂ (the verbatim complex twin
of `SalemEndgame.reflect_eval_eq`): `(reflect p W)(z) = z^p·W(1/z)` for
`z ≠ 0`. -/
lemma reflect_eval_eq_C (W : Polynomial ℂ) {z : ℂ} (hz : z ≠ 0) (p : ℕ)
    (hdeg : W.natDegree ≤ p) :
    (W.reflect p).eval z = z ^ p * W.eval z⁻¹ := by
  have hzinv : (z⁻¹ : ℂ) ≠ 0 := inv_ne_zero hz
  let : Invertible (z⁻¹ : ℂ) := invertibleOfNonzero hzinv
  have key := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) z⁻¹ p W hdeg
  rw [Polynomial.eval₂_id, Polynomial.eval₂_id, invOf_eq_inv, inv_inv] at key
  have hp1 : (z⁻¹ : ℂ) ^ p * z ^ p = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hz, one_pow]
  calc (W.reflect p).eval z
      = (W.reflect p).eval z * ((z⁻¹ : ℂ) ^ p * z ^ p) := by rw [hp1, mul_one]
    _ = ((W.reflect p).eval z * (z⁻¹ : ℂ) ^ p) * z ^ p := by ring
    _ = W.eval z⁻¹ * z ^ p := by rw [key]
    _ = z ^ p * W.eval z⁻¹ := by ring

private lemma roots_of_pisot_pattern (Pz : Polynomial ℤ) (alpha : ℝ) (inside : Multiset ℂ)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside) :
    ∀ z : ℂ, (Pz.map (Int.castRingHom ℂ)).eval z = 0 →
    z = ((alpha : ℂ)) ∨ z ∈ inside := by
  intro z hz
  rw [hfacC, SalemCircle.eval_P] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · rw [Multiset.prod_eq_zero_iff] at h
    obtain ⟨w, hw, hw0⟩ := Multiset.mem_map.mp h
    have hzw : z = w := sub_eq_zero.mp hw0
    rw [hzw]
    exact Or.inr hw

private lemma roots_of_divisor_in_pattern (Pz : Polynomial ℤ) (alpha : ℝ) (inside : Multiset ℂ)
    (hPzRoots : ∀ z : ℂ, (Pz.map (Int.castRingHom ℂ)).eval z = 0 →
      z = (alpha : ℂ) ∨ z ∈ inside) : ∀ W : Polynomial ℚ, W ∣ Pz.map (Int.castRingHom ℚ) →
    ∀ z : ℂ, (W.map (algebraMap ℚ ℂ)).eval z = 0 →
      z = ((alpha : ℂ)) ∨ z ∈ inside := by
  intro W hW z hz
  apply hPzRoots
  have h1 : W.map (algebraMap ℚ ℂ)
      ∣ (Pz.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) :=
    Polynomial.map_dvd _ hW
  rw [Polynomial.map_map, SalemArith.castQC_triangle] at h1
  obtain ⟨c, hc⟩ := h1
  rw [hc, Polynomial.eval_mul, hz, zero_mul]

private lemma eval_reciprocal_reflect_zero :
    ∀ x : ℝ, x ≠ 0 → ∀ W : Polynomial ℚ, Polynomial.aeval x W = 0 →
    Polynomial.aeval x⁻¹ (W.reflect W.natDegree) = 0 := by
  intro x hx W hW
  rw [SalemArith.aeval_eq_eval_map] at hW ⊢
  rw [← Polynomial.reflect_map]
  have hdeg : (W.map (algebraMap ℚ ℝ)).natDegree ≤ W.natDegree :=
    Polynomial.natDegree_map_le
  rw [SalemEndgame.reflect_eval_eq (W.map (algebraMap ℚ ℝ)) (inv_ne_zero hx)
    W.natDegree hdeg, inv_inv, hW, mul_zero]

private lemma monic_reflect_ne_zero : ∀ W : Polynomial ℚ, W.Monic → W.reflect W.natDegree ≠ 0 := by
  intro W hW h
  have h1 : (W.reflect W.natDegree).coeff 0 = 1 := by
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero]
    exact hW.coeff_natDegree
  rw [h, Polynomial.coeff_zero] at h1
  exact one_ne_zero h1.symm

private lemma minpoly_map_eval_zero_ne : ∀ x : ℝ, IsIntegral ℚ x → x ≠ 0 →
    ((minpoly ℚ x).map (algebraMap ℚ ℂ)).eval 0 ≠ 0 := by
  intro x hx hx0 h
  have h1 : (algebraMap ℚ ℂ) ((minpoly ℚ x).coeff 0) = 0 := by
    rw [← Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero]
    exact h
  have h2 : (minpoly ℚ x).coeff 0 = 0 :=
    (algebraMap ℚ ℂ).injective (h1.trans (map_zero _).symm)
  exact minpoly.coeff_zero_ne_zero hx hx0 h2

/-- **The reduction**: a Pisot-pattern polynomial vanishing at
`1/alpha` forces `alpha` to be a reciprocal quadratic Pisot unit —
`alpha² = r·alpha − 1` with `3 ≤ r : ℤ`.  (No conjugation-closure is
needed.) -/
theorem reciprocal_quadratic_of_inv_root
    (Pz : Polynomial ℤ) (hmonic : Pz.Monic) (alpha : ℝ) (halpha : 1 < alpha)
    (inside : Multiset ℂ) (hin : ∀ z ∈ inside, ‖z‖ < 1)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside)
    (h0 : (Pz.map (Int.castRingHom ℝ)).eval alpha⁻¹ = 0) :
    ∃ r : ℤ, 3 ≤ r ∧ alpha ^ 2 = (r : ℝ) * alpha - 1 := by
  classical
  have hapos : (0 : ℝ) < alpha := by linarith
  have ha0 : alpha ≠ 0 := ne_of_gt hapos
  have hainv0 : (alpha⁻¹ : ℝ) ≠ 0 := inv_ne_zero ha0
  have hainvpos : (0 : ℝ) < alpha⁻¹ := inv_pos.mpr hapos
  have hainv1 : alpha⁻¹ < 1 := inv_lt_one_of_one_lt₀ halpha
  -- (a) both `alpha` and `1/alpha` are integral
  have hPrAlpha : (Pz.map (Int.castRingHom ℝ)).eval alpha = 0 := by
    have h1 : ((((Pz.map (Int.castRingHom ℝ)).eval alpha : ℝ)) : ℂ)
        = (Pz.map (Int.castRingHom ℂ)).eval ((alpha : ℂ)) :=
      (SalemEndgame.eval_int_transfer Pz alpha).symm
    rw [hfacC, SalemCircle.eval_P, sub_self, zero_mul] at h1
    exact_mod_cast h1
  have hint_a : IsIntegral ℤ alpha := by
    refine ⟨Pz, hmonic, ?_⟩
    rw [← Polynomial.aeval_def, SalemArith.aeval_eq_eval_map, algebraMap_int_eq]
    exact hPrAlpha
  have hint_b : IsIntegral ℤ (alpha⁻¹ : ℝ) := by
    refine ⟨Pz, hmonic, ?_⟩
    rw [← Polynomial.aeval_def, SalemArith.aeval_eq_eval_map, algebraMap_int_eq]
    exact h0
  have hQa : IsIntegral ℚ alpha := hint_a.tower_top
  have hQb : IsIntegral ℚ (alpha⁻¹ : ℝ) := hint_b.tower_top
  have hmonic_a : (minpoly ℚ alpha).Monic := minpoly.monic hQa
  have hmonic_b : (minpoly ℚ (alpha⁻¹ : ℝ)).Monic := minpoly.monic hQb
  have hdega_pos : 0 < (minpoly ℚ alpha).natDegree := minpoly.natDegree_pos hQa
  have hdegb_pos : 0 < (minpoly ℚ (alpha⁻¹ : ℝ)).natDegree := minpoly.natDegree_pos hQb
  -- (b) roots of any divisor of `Pz` lie in `{alpha} ∪ inside`
  have hPzRoots := roots_of_pisot_pattern Pz alpha inside hfacC
  have hdvd_roots := roots_of_divisor_in_pattern Pz alpha inside hPzRoots
  have hdvd_a : minpoly ℚ alpha ∣ Pz.map (Int.castRingHom ℚ) := by
    apply minpoly.dvd ℚ alpha
    rw [← algebraMap_int_eq, Polynomial.aeval_map_algebraMap,
      SalemArith.aeval_eq_eval_map, algebraMap_int_eq]
    exact hPrAlpha
  have hdvd_b : minpoly ℚ (alpha⁻¹ : ℝ) ∣ Pz.map (Int.castRingHom ℚ) := by
    apply minpoly.dvd ℚ (alpha⁻¹ : ℝ)
    rw [← algebraMap_int_eq, Polynomial.aeval_map_algebraMap,
      SalemArith.aeval_eq_eval_map, algebraMap_int_eq]
    exact h0
  -- (c) the two minimal polynomials divide each other's reverse, so
  -- their degrees agree
  have hrev_root := eval_reciprocal_reflect_zero
  have hdvd_b_reva : minpoly ℚ (alpha⁻¹ : ℝ)
      ∣ (minpoly ℚ alpha).reflect (minpoly ℚ alpha).natDegree :=
    minpoly.dvd ℚ (alpha⁻¹ : ℝ) (hrev_root alpha ha0 _ (minpoly.aeval ℚ alpha))
  have hdvd_a_revb : minpoly ℚ alpha
      ∣ (minpoly ℚ (alpha⁻¹ : ℝ)).reflect (minpoly ℚ (alpha⁻¹ : ℝ)).natDegree := by
    have h1 := hrev_root (alpha⁻¹ : ℝ) hainv0 _ (minpoly.aeval ℚ (alpha⁻¹ : ℝ))
    rw [inv_inv] at h1
    exact minpoly.dvd ℚ alpha h1
  have hrefl_ne := monic_reflect_ne_zero
  have hrefl_deg : ∀ W : Polynomial ℚ, (W.reflect W.natDegree).natDegree ≤ W.natDegree :=
    fun W => Polynomial.reverse_natDegree_le W
  have hdeq : (minpoly ℚ alpha).natDegree = (minpoly ℚ (alpha⁻¹ : ℝ)).natDegree :=
    le_antisymm
      (le_trans (Polynomial.natDegree_le_of_dvd hdvd_a_revb (hrefl_ne _ hmonic_b))
        (hrefl_deg _))
      (le_trans (Polynomial.natDegree_le_of_dvd hdvd_b_reva (hrefl_ne _ hmonic_a))
        (hrefl_deg _))
  -- zero is a root of neither complex minimal polynomial
  have hcoeff0_ne := minpoly_map_eval_zero_ne
  -- (d) every complex root of `minpoly ℚ alpha` is `alpha` or `1/alpha`
  have hpair_a : ∀ z : ℂ, ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).eval z = 0 →
      z = ((alpha : ℂ)) ∨ z = ((alpha : ℂ))⁻¹ := by
    intro z hz
    by_cases hza : z = ((alpha : ℂ))
    · exact Or.inl hza
    right
    have hzin : z ∈ inside := by
      rcases hdvd_roots _ hdvd_a z hz with h | h
      · exact absurd h hza
      · exact h
    have hznorm : ‖z‖ < 1 := hin z hzin
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      exact hcoeff0_ne alpha hQa ha0 hz
    have hz_rev : (((minpoly ℚ (alpha⁻¹ : ℝ)).reflect
        (minpoly ℚ (alpha⁻¹ : ℝ)).natDegree).map (algebraMap ℚ ℂ)).eval z = 0 := by
      obtain ⟨c, hc⟩ := hdvd_a_revb
      rw [hc, Polynomial.map_mul, Polynomial.eval_mul, hz, zero_mul]
    rw [← Polynomial.reflect_map] at hz_rev
    have hdegz : ((minpoly ℚ (alpha⁻¹ : ℝ)).map (algebraMap ℚ ℂ)).natDegree
        ≤ (minpoly ℚ (alpha⁻¹ : ℝ)).natDegree := Polynomial.natDegree_map_le
    rw [reflect_eval_eq_C _ hz0 _ hdegz] at hz_rev
    have hz_inv_root : ((minpoly ℚ (alpha⁻¹ : ℝ)).map (algebraMap ℚ ℂ)).eval z⁻¹ = 0 := by
      rcases mul_eq_zero.mp hz_rev with h | h
      · exact absurd h (pow_ne_zero _ hz0)
      · exact h
    rcases hdvd_roots _ hdvd_b z⁻¹ hz_inv_root with h | h
    · rw [← h, inv_inv]
    · exfalso
      have h1 : ‖z⁻¹‖ < 1 := hin _ h
      have h2 : ‖z‖ * ‖z⁻¹‖ = 1 := by
        rw [← norm_mul, mul_inv_cancel₀ hz0, norm_one]
      nlinarith [norm_nonneg z, norm_nonneg (z⁻¹)]
  -- (e) splitting data: the degree is at most 2
  have hQirr : Irreducible (minpoly ℚ alpha) := minpoly.irreducible hQa
  have hsep : (minpoly ℚ alpha).Separable := hQirr.separable
  have hsepC : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).Separable := hsep.map
  have hnodup : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).roots.Nodup :=
    Polynomial.nodup_roots hsepC
  have hmonicC : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).Monic := hmonic_a.map _
  have hCne : (minpoly ℚ alpha).map (algebraMap ℚ ℂ) ≠ 0 := hmonicC.ne_zero
  have hsplits : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).Splits :=
    IsAlgClosed.splits _
  have hdegC : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).natDegree
      = (minpoly ℚ alpha).natDegree := hmonic_a.natDegree_map _
  have hcard : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).roots.card
      = (minpoly ℚ alpha).natDegree := by
    rw [← hdegC]
    exact hsplits.natDegree_eq_card_roots.symm
  have hmem : ∀ z : ℂ, z ∈ ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).roots ↔
      ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).eval z = 0 := by
    intro z
    rw [Polynomial.mem_roots']
    exact ⟨fun h => h.2, fun h => ⟨hCne, h⟩⟩
  have halphaCroot : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).eval ((alpha : ℂ)) = 0 := by
    rw [← SalemArith.aeval_eq_eval_map, SalemArith.aeval_ofReal, minpoly.aeval,
      Complex.ofReal_zero]
  have halphaC_mem : ((alpha : ℂ)) ∈ ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).roots :=
    (hmem _).mpr halphaCroot
  have hsub : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).roots.toFinset ⊆
      ({((alpha : ℂ)), ((alpha : ℂ))⁻¹} : Finset ℂ) := by
    intro z hz
    rcases hpair_a z ((hmem z).mp (Multiset.mem_toFinset.mp hz)) with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
  have hdeg2 : (minpoly ℚ alpha).natDegree ≤ 2 := by
    have h1 := Finset.card_le_card hsub
    have h2 : ({((alpha : ℂ)), ((alpha : ℂ))⁻¹} : Finset ℂ).card ≤ 2 := by
      apply le_trans (Finset.card_insert_le _ _)
      simp
    have h3 : ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).roots.toFinset.card
        = ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).roots.card :=
      Multiset.toFinset_card_eq_card_iff_nodup.mpr hnodup
    omega
  -- Gauss steps for both minimal polynomials
  have hmza : minpoly ℚ alpha = (minpoly ℤ alpha).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint_a
  have hcoeffa : ∀ i : ℕ,
      (minpoly ℚ alpha).coeff i = (((minpoly ℤ alpha).coeff i : ℤ) : ℚ) := by
    intro i
    rw [hmza, Polynomial.coeff_map, eq_intCast]
  have hmzb : minpoly ℚ (alpha⁻¹ : ℝ)
      = (minpoly ℤ (alpha⁻¹ : ℝ)).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint_b
  have hcoeffb : ∀ i : ℕ, (minpoly ℚ (alpha⁻¹ : ℝ)).coeff i
      = (((minpoly ℤ (alpha⁻¹ : ℝ)).coeff i : ℤ) : ℚ) := by
    intro i
    rw [hmzb, Polynomial.coeff_map, eq_intCast]
  rcases (by omega :
      (minpoly ℚ alpha).natDegree = 1 ∨ (minpoly ℚ alpha).natDegree = 2) with h1 | h2
  · -- (f) degree 1 is impossible: `1/alpha` would be an integer in `(0, 1)`
    exfalso
    have h1b : (minpoly ℚ (alpha⁻¹ : ℝ)).natDegree = 1 := by omega
    have heqb : minpoly ℚ (alpha⁻¹ : ℝ)
        = X + Polynomial.C ((minpoly ℚ (alpha⁻¹ : ℝ)).coeff 0) :=
      hmonic_b.eq_X_add_C h1b
    have haev := minpoly.aeval ℚ (alpha⁻¹ : ℝ)
    rw [heqb, map_add, Polynomial.aeval_X, Polynomial.aeval_C, hcoeffb 0,
      map_intCast] at haev
    have h3 : (-1 : ℝ) < (((minpoly ℤ (alpha⁻¹ : ℝ)).coeff 0 : ℤ) : ℝ) := by linarith
    have h4 : (((minpoly ℤ (alpha⁻¹ : ℝ)).coeff 0 : ℤ) : ℝ) < 0 := by linarith
    have h5 : (-1 : ℤ) < (minpoly ℤ (alpha⁻¹ : ℝ)).coeff 0 := by exact_mod_cast h3
    have h6 : (minpoly ℤ (alpha⁻¹ : ℝ)).coeff 0 < 0 := by exact_mod_cast h4
    omega
  · -- (g) degree 2: Vieta on the X-coefficient delivers `r`
    obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem halphaC_mem
    have hcards := hcard
    rw [hrest, Multiset.card_cons] at hcards
    have hcard_rest : rest.card = 1 := by omega
    obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp hcard_rest
    have hnodup' := hnodup
    rw [hrest, Multiset.nodup_cons] at hnodup'
    have hbmem : b ∈ ((minpoly ℚ alpha).map (algebraMap ℚ ℂ)).roots := by
      rw [hrest, hb]
      exact Multiset.mem_cons_of_mem (Multiset.mem_singleton_self b)
    have hbval : b = ((alpha : ℂ))⁻¹ := by
      rcases hpair_a b ((hmem b).mp hbmem) with h | h
      · exfalso
        apply hnodup'.1
        rw [hb, h]
        exact Multiset.mem_singleton_self _
      · exact h
    have hnext := hsplits.nextCoeff_eq_neg_sum_roots_of_monic hmonicC
    rw [Polynomial.nextCoeff_of_natDegree_pos (by rw [hdegC]; omega),
      hdegC, h2, hrest, hb, hbval, Multiset.sum_cons, Multiset.sum_singleton] at hnext
    rw [show (2 : ℕ) - 1 = 1 by norm_num] at hnext
    rw [Polynomial.coeff_map, hcoeffa 1, map_intCast] at hnext
    have hreal : (((minpoly ℤ alpha).coeff 1 : ℤ) : ℝ) = -(alpha + alpha⁻¹) := by
      exact_mod_cast hnext
    refine ⟨-(minpoly ℤ alpha).coeff 1, ?_, ?_⟩
    · have hx : alpha * alpha⁻¹ = 1 := mul_inv_cancel₀ ha0
      have h2lt : (2 : ℝ) < alpha + alpha⁻¹ := by
        nlinarith [mul_pos (sub_pos.mpr halpha) (sub_pos.mpr halpha), hx, hapos]
      have hgt : (2 : ℝ) < ((-(minpoly ℤ alpha).coeff 1 : ℤ) : ℝ) := by
        push_cast
        linarith
      have hZ : (2 : ℤ) < -(minpoly ℤ alpha).coeff 1 := by exact_mod_cast hgt
      omega
    · have htr2 : alpha + alpha⁻¹ = ((-(minpoly ℤ alpha).coeff 1 : ℤ) : ℝ) := by
        push_cast
        linarith
      have hx : alpha * alpha⁻¹ = 1 := mul_inv_cancel₀ ha0
      linear_combination alpha * htr2 - hx

/-- **The pattern-form theorem** (supporting; the compared Salem's
Theorem IV for Pisot numbers is `SalemPisot.salem_theorem`): every
Pisot-pattern polynomial (monic over ℤ, one real root `alpha > 1`, all
other roots strictly inside the unit circle, conjugation-closed) has
Salem numbers approaching `alpha` from both sides; the statement
unifies Salem's two cases in one.
If `P(1/alpha) ≠ 0` this is `PdtSalemEndgame.salem_two_sided`; if
`P(1/alpha) = 0` the reduction forces `alpha` reciprocal quadratic and
the explicit family closes the case. -/
theorem salem_theorem_full
    (Pz : Polynomial ℤ) (hmonic : Pz.Monic)
    (alpha : ℝ) (halpha : 1 < alpha)
    (inside : Multiset ℂ) (hin : ∀ z ∈ inside, ‖z‖ < 1)
    (hconj : inside.map (starRingEnd ℂ) = inside)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside)
    (eps : ℝ) (heps : 0 < eps) :
    (∃ tau : ℝ, SalemEndgame.IsSalem tau ∧ alpha - eps < tau ∧ tau < alpha) ∧
    (∃ tau : ℝ, SalemEndgame.IsSalem tau ∧ alpha < tau ∧ tau < alpha + eps) := by
  by_cases h : (Pz.map (Int.castRingHom ℝ)).eval alpha⁻¹ = 0
  · obtain ⟨r, hr, hmin⟩ :=
      reciprocal_quadratic_of_inv_root Pz hmonic alpha halpha inside hin hfacC h
    exact salem_two_sided_quad_unit r hr alpha halpha hmin eps heps
  · exact SalemEndgame.salem_two_sided Pz hmonic alpha halpha inside hin hconj
      hfacC h eps heps

end
end SalemQuadUnit
end PDT

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Stephanie Alexander

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
