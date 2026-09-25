/-
Copyright (c) 2026 Stephanie Alexander. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephanie Alexander
-/
module
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic

/-!
# PdtSalemCircle — the circle count

The circle count for Salem's construction: `R_m`'s roots on the unit
circle, counted by the explicit-phase route; Salem-ness / arithmetic
assembly is NOT here (that is `PdtSalemArith`); the companion `Q` is
the mirrored product, its identification with the reverse polynomial
is deferred to `PdtSalemArith`.

Fixed data: `alpha : ℝ` with `1 < alpha`, and a conjugation-closed
multiset `roots : Multiset ℂ` of "inside" conjugates (`‖r‖ < 1`; it may
be empty).  With `p := roots.card + 1`,

* `P = (X − C α)·∏ (X − C r)` — monic of degree `p`, the root `α`
  outside the circle and the rest inside;
* `Q = (1 − C α·X)·∏ (1 − C r·X)` — the mirrored product, so that
  `z^p·P(1/z) = Q(z)` pointwise (`mirror_P`);
* `R m = X^m·P + Q`.

The three theorems:

* **the self-inversive pairing** (`salem_root_inv`): for `z ≠ 0`,
  `R_m(z) = 0 → R_m(1/z) = 0` — pure product algebra, no reverse-
  polynomial API;
* **the circle count** (`salem_circle_count`): `R_m` has `m + p − 2`
  distinct roots `exp(t·I)` with `t ∈ (0, 2π)`.  The route is the
  explicit phase: on the circle
  `R_m(E t) = 2·N t·cos(ψ t)·E((m+p)·t/2)` with `N > 0` and
  `ψ t = (m+p)·t/2 + A t`, where `A` is an explicit sum of `arg`-terms
  each valued in an open half-plane, hence continuous; `ψ` climbs by
  `(m+p−2)·π` across `[0, 2π]`, and the intermediate value theorem
  plants one root per half-period grid point — no argument principle,
  no Rouché theorem;
* **the trichotomy** (`salem_root_trichotomy`): if moreover `τ > 1` is
  a root of `R_m`, then EVERY root is unimodular or lies in
  `{τ, 1/τ}` — the circle points, `τ`, and `1/τ` already exhaust the
  degree `m + p`, by the multiset squeeze `S.val ≤ (R m).roots`.

The pairing `salem_root_inv` and the count `salem_circle_count` are
stated without the hypothesis `1 ≤ m` — it is not needed (for the
count, `3 ≤ m + p` alone drives the phase climb); the trichotomy
carries both `1 ≤ m` and `3 ≤ m + p`.
-/

public section

namespace PDT
namespace SalemCircle

noncomputable section
open Polynomial Complex Set

/-! ### The fixed objects -/

/-- The circle parametrization `E t = exp(t·I)`. -/
@[expose] def E (t : ℝ) : ℂ := Complex.exp (t * Complex.I)

/-- `P = (X − C α)·∏_{r ∈ roots} (X − C r)`: monic, degree
`roots.card + 1`, roots `α` and the inside conjugates. -/
@[expose] def P (alpha : ℝ) (roots : Multiset ℂ) : Polynomial ℂ :=
  (X - C (alpha : ℂ)) * (roots.map fun r => X - C r).prod

/-- `Q = (1 − C α·X)·∏_{r ∈ roots} (1 − C r·X)`: the mirrored product,
`z^p·P(1/z) = Q(z)` for `z ≠ 0` (`mirror_P`). -/
def Q (alpha : ℝ) (roots : Multiset ℂ) : Polynomial ℂ :=
  (1 - C (alpha : ℂ) * X) * (roots.map fun r => 1 - C r * X).prod

/-- The Salem family `R_m = X^m·P + Q`. -/
@[expose] def R (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) : Polynomial ℂ :=
  X ^ m * P alpha roots + Q alpha roots

/-- The reduced product on the circle: `Q(E t) = conj (V t)` and
`P(E t) = E(p·t)·V t`. -/
def V (alpha : ℝ) (roots : Multiset ℂ) (t : ℝ) : ℂ :=
  (1 - (alpha : ℂ) * E (-t)) * (roots.map fun r => 1 - r * E (-t)).prod

/-- The modulus of `V`: strictly positive on the whole circle. -/
def N (alpha : ℝ) (roots : Multiset ℂ) (t : ℝ) : ℝ :=
  ‖(alpha : ℂ) - E t‖ * (roots.map fun r => ‖1 - r * E (-t)‖).prod

/-- The explicit phase of `V`: every `arg`-term lives in an open
half-plane, so `A` is continuous (`continuous_A`). -/
def A (alpha : ℝ) (roots : Multiset ℂ) (t : ℝ) : ℝ :=
  -t + Real.pi + Complex.arg ((alpha : ℂ) - E t)
    + (roots.map fun r => Complex.arg (1 - r * E (-t))).sum

/-- The half-angle phase of `R_m` on the circle:
`R_m(E t) = 2·N t·cos(ψ t)·E((m+p)·t/2)`. -/
@[expose] def psi (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) (t : ℝ) : ℝ :=
  ((m + roots.card + 1 : ℕ) : ℝ) * t / 2 + A alpha roots t

/-! ### Scalar evaluations and the self-inversive pairing -/

lemma eval_P (alpha : ℝ) (roots : Multiset ℂ) (z : ℂ) :
    (P alpha roots).eval z = (z - (alpha : ℂ)) * (roots.map fun r => z - r).prod := by
  simp only [P, eval_mul, eval_sub, eval_X, eval_C, eval_multiset_prod,
    Multiset.map_map, Function.comp_def]

lemma eval_Q (alpha : ℝ) (roots : Multiset ℂ) (z : ℂ) :
    (Q alpha roots).eval z
      = (1 - (alpha : ℂ) * z) * (roots.map fun r => 1 - r * z).prod := by
  simp only [Q, eval_mul, eval_sub, eval_one, eval_X, eval_C, eval_multiset_prod,
    Multiset.map_map, Function.comp_def]

lemma eval_R (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) (z : ℂ) :
    (R alpha roots m).eval z
      = z ^ m * (P alpha roots).eval z + (Q alpha roots).eval z := by
  simp only [R, eval_add, eval_mul, eval_pow, eval_X]

/-- Collecting one copy of `z` into each factor:
`z^card·∏ (1/z − r) = ∏ (1 − r·z)`. -/
lemma prod_shift (s : Multiset ℂ) {z : ℂ} (hz : z ≠ 0) :
    z ^ s.card * (s.map fun r => z⁻¹ - r).prod = (s.map fun r => 1 - r * z).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    have ha : z * (z⁻¹ - a) = 1 - a * z := by
      rw [mul_sub, mul_inv_cancel₀ hz]; ring
    calc z ^ Multiset.card s * z * ((z⁻¹ - a) * (s.map fun r => z⁻¹ - r).prod)
        = (z * (z⁻¹ - a)) * (z ^ Multiset.card s * (s.map fun r => z⁻¹ - r).prod) := by
          ring
      _ = (1 - a * z) * (s.map fun r => 1 - r * z).prod := by rw [ha, ih]

/-- The mirror of `prod_shift`: `z^card·∏ (1 − r/z) = ∏ (z − r)`. -/
lemma prod_shift' (s : Multiset ℂ) {z : ℂ} (hz : z ≠ 0) :
    z ^ s.card * (s.map fun r => 1 - r * z⁻¹).prod = (s.map fun r => z - r).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    have ha : z * (1 - a * z⁻¹) = z - a := by
      field_simp
    calc z ^ Multiset.card s * z * ((1 - a * z⁻¹) * (s.map fun r => 1 - r * z⁻¹).prod)
        = (z * (1 - a * z⁻¹)) * (z ^ Multiset.card s * (s.map fun r => 1 - r * z⁻¹).prod) := by
          ring
      _ = (z - a) * (s.map fun r => z - r).prod := by rw [ha, ih]

/-- The first mirror identity: `z^p·P(1/z) = Q(z)` for `z ≠ 0`. -/
lemma mirror_P (alpha : ℝ) (roots : Multiset ℂ) {z : ℂ} (hz : z ≠ 0) :
    z ^ (roots.card + 1) * (P alpha roots).eval z⁻¹ = (Q alpha roots).eval z := by
  rw [eval_P, eval_Q, pow_succ]
  have h1 : z * (z⁻¹ - (alpha : ℂ)) = 1 - (alpha : ℂ) * z := by
    rw [mul_sub, mul_inv_cancel₀ hz]; ring
  calc z ^ Multiset.card roots * z
        * ((z⁻¹ - (alpha : ℂ)) * (roots.map fun r => z⁻¹ - r).prod)
      = (z * (z⁻¹ - (alpha : ℂ)))
        * (z ^ Multiset.card roots * (roots.map fun r => z⁻¹ - r).prod) := by ring
    _ = (1 - (alpha : ℂ) * z) * (roots.map fun r => 1 - r * z).prod := by
        rw [h1, prod_shift roots hz]

/-- The second mirror identity: `z^p·Q(1/z) = P(z)` for `z ≠ 0`. -/
lemma mirror_Q (alpha : ℝ) (roots : Multiset ℂ) {z : ℂ} (hz : z ≠ 0) :
    z ^ (roots.card + 1) * (Q alpha roots).eval z⁻¹ = (P alpha roots).eval z := by
  rw [eval_P, eval_Q, pow_succ]
  have h1 : z * (1 - (alpha : ℂ) * z⁻¹) = z - (alpha : ℂ) := by
    field_simp
  calc z ^ Multiset.card roots * z
        * ((1 - (alpha : ℂ) * z⁻¹) * (roots.map fun r => 1 - r * z⁻¹).prod)
      = (z * (1 - (alpha : ℂ) * z⁻¹))
        * (z ^ Multiset.card roots * (roots.map fun r => 1 - r * z⁻¹).prod) := by ring
    _ = (z - (alpha : ℂ)) * (roots.map fun r => z - r).prod := by
        rw [h1, prod_shift' roots hz]

/-- The self-inversive functional equation:
`z^(m+p)·R_m(1/z) = R_m(z)` for `z ≠ 0`. -/
lemma R_eval_inv (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    z ^ (m + (roots.card + 1)) * (R alpha roots m).eval z⁻¹
      = (R alpha roots m).eval z := by
  have hzm : z ^ m * (z⁻¹) ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  rw [eval_R, eval_R, pow_add]
  calc z ^ m * z ^ (roots.card + 1)
        * ((z⁻¹) ^ m * (P alpha roots).eval z⁻¹ + (Q alpha roots).eval z⁻¹)
      = (z ^ m * (z⁻¹) ^ m) * (z ^ (roots.card + 1) * (P alpha roots).eval z⁻¹)
        + z ^ m * (z ^ (roots.card + 1) * (Q alpha roots).eval z⁻¹) := by ring
    _ = z ^ m * (P alpha roots).eval z + (Q alpha roots).eval z := by
        rw [hzm, mirror_P alpha roots hz, mirror_Q alpha roots hz]; ring

/-- **The self-inversive pairing**: a nonzero root of `R_m` pairs
with its inverse.  (Stated without the redundant `1 ≤ m`.) -/
theorem salem_root_inv (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) {z : ℂ} (hz : z ≠ 0)
    (hroot : (R alpha roots m).eval z = 0) : (R alpha roots m).eval z⁻¹ = 0 := by
  have key := R_eval_inv alpha roots m hz
  rw [hroot] at key
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (pow_ne_zero _ hz)
  · exact h

/-! ### The `E`-calculus -/

lemma E_zero : E 0 = 1 := by simp [E]

lemma E_add (s t : ℝ) : E (s + t) = E s * E t := by
  simp only [E, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma E_congr {s t : ℝ} (h : s = t) : E s = E t := by rw [h]

lemma E_mul_E_neg (t : ℝ) : E t * E (-t) = 1 := by
  rw [← E_add, add_neg_cancel, E_zero]

lemma E_ne_zero (t : ℝ) : E t ≠ 0 := by
  simp only [E]; exact Complex.exp_ne_zero _

lemma norm_E (t : ℝ) : ‖E t‖ = 1 := by
  simp only [E]; exact Complex.norm_exp_ofReal_mul_I t

lemma conj_E (t : ℝ) : (starRingEnd ℂ) (E t) = E (-t) := by
  simp only [E, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

lemma E_pow (n : ℕ) (t : ℝ) : E t ^ n = E ((n : ℝ) * t) := by
  simp only [E, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma E_pi : E Real.pi = -1 := by
  simp only [E]; exact Complex.exp_pi_mul_I

lemma E_two_pi : E (2 * Real.pi) = 1 := by
  simp only [E]
  rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma E_re (t : ℝ) : (E t).re = Real.cos t := by
  simp only [E]; exact Complex.exp_ofReal_mul_I_re t

/-- `exp(iψ) + exp(−iψ) = 2·cos ψ`, over the reals. -/
lemma E_add_E_neg (x : ℝ) : E x + E (-x) = 2 * ((Real.cos x : ℝ) : ℂ) := by
  simp only [E, Complex.exp_mul_I]
  push_cast
  simp only [Complex.cos_neg, Complex.sin_neg]
  ring

lemma norm_mul_E (w : ℂ) (t : ℝ) : ‖w * E t‖ = ‖w‖ := by
  rw [norm_mul, norm_E, mul_one]

/-! ### Nonvanishing and the half-plane locations -/

lemma one_sub_ne_zero_of_norm_ne_one {w : ℂ} (hw : ‖w‖ ≠ 1) : 1 - w ≠ 0 := by
  intro h
  have hw1 : w = 1 := (sub_eq_zero.mp h).symm
  rw [hw1, norm_one] at hw
  exact hw rfl

lemma alpha_factor_ne_zero {alpha : ℝ} (halpha : 1 < alpha) (t : ℝ) :
    1 - (alpha : ℂ) * E (-t) ≠ 0 := by
  apply one_sub_ne_zero_of_norm_ne_one
  rw [norm_mul_E, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith : (0 : ℝ) < alpha)]
  exact ne_of_gt halpha

lemma root_factor_ne_zero {r : ℂ} (hr : ‖r‖ < 1) (t : ℝ) : 1 - r * E (-t) ≠ 0 := by
  apply one_sub_ne_zero_of_norm_ne_one
  rw [norm_mul_E]
  exact ne_of_lt hr

lemma alpha_sub_E_ne_zero {alpha : ℝ} (halpha : 1 < alpha) (t : ℝ) :
    (alpha : ℂ) - E t ≠ 0 := by
  intro h
  have h1 : (alpha : ℂ) = E t := sub_eq_zero.mp h
  have hn : ‖(alpha : ℂ)‖ = 1 := by rw [h1, norm_E]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith : (0 : ℝ) < alpha)] at hn
  linarith

lemma N_pos (alpha : ℝ) (roots : Multiset ℂ) (halpha : 1 < alpha)
    (hroots : ∀ r ∈ roots, ‖r‖ < 1) (t : ℝ) : 0 < N alpha roots t := by
  unfold N
  apply mul_pos
  · exact norm_pos_iff.mpr (alpha_sub_E_ne_zero halpha t)
  · apply Multiset.prod_pos
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    exact norm_pos_iff.mpr (root_factor_ne_zero (hroots r hr) t)

lemma re_pos_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 0 < (1 - w).re := by
  have h1 : w.re ≤ |w.re| := le_abs_self _
  have h2 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma alpha_sub_E_mem_slitPlane {alpha : ℝ} (halpha : 1 < alpha) (t : ℝ) :
    (alpha : ℂ) - E t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simp only [Complex.sub_re, Complex.ofReal_re, E_re]
  have := Real.cos_le_one t
  linarith

lemma root_factor_mem_slitPlane {r : ℂ} (hr : ‖r‖ < 1) (t : ℝ) :
    1 - r * E (-t) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  apply re_pos_of_norm_lt_one
  rw [norm_mul_E]
  exact hr

/-! ### The polar form and the key identity -/

/-- The polar form, phrased through `E`. -/
lemma polar (w : ℂ) : w = (‖w‖ : ℂ) * E (Complex.arg w) := by
  simp only [E]
  exact (Complex.norm_mul_exp_arg_mul_I w).symm

/-- A multiset product of polar forms is the polar form of the product:
norms multiply, phases add. -/
lemma prod_norm_mul_E (s : Multiset ℂ) (nf af : ℂ → ℝ) :
    (s.map fun r => ((nf r : ℝ) : ℂ) * E (af r)).prod
      = (((s.map nf).prod : ℝ) : ℂ) * E ((s.map af).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp [E_zero]
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, ih, E_add]
    push_cast
    ring

/-- Pulling a constant out of every factor. -/
lemma prod_map_const_mul (c : ℂ) (s : Multiset ℂ) (f : ℂ → ℂ) :
    (s.map fun r => c * f r).prod = c ^ s.card * (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, ih]
    ring

/-- Two polar forms multiply to a polar form. -/
lemma polar_mul (a b x y : ℝ) :
    ((a : ℂ) * E x) * ((b : ℂ) * E y) = ((a * b : ℝ) : ℂ) * E (x + y) := by
  rw [E_add]
  push_cast
  ring

/-- The rotated polar form of the leading factor of `V`:
`1 − α·E(−t) = ‖α − E t‖·E(−t + π + arg(α − E t))`. -/
lemma first_factor_polar (alpha : ℝ) (t : ℝ) :
    1 - (alpha : ℂ) * E (-t)
      = (‖(alpha : ℂ) - E t‖ : ℂ)
        * E (-t + Real.pi + Complex.arg ((alpha : ℂ) - E t)) := by
  have key : ∀ w : ℂ, w = (alpha : ℂ) - E t →
      1 - (alpha : ℂ) * E (-t) = (‖w‖ : ℂ) * E (-t + Real.pi + Complex.arg w) := by
    intro w hw
    rw [E_add, E_add, E_pi]
    have hpolar : (‖w‖ : ℂ) * E (Complex.arg w) = w := (polar w).symm
    calc 1 - (alpha : ℂ) * E (-t) = E (-t) * (-1 * ((alpha : ℂ) - E t)) := by
          linear_combination -E_mul_E_neg t
      _ = E (-t) * (-1 * w) := by rw [← hw]
      _ = E (-t) * (-1 * ((‖w‖ : ℂ) * E (Complex.arg w))) := by rw [hpolar]
      _ = (‖w‖ : ℂ) * (E (-t) * -1 * E (Complex.arg w)) := by ring
  exact key _ rfl

/-- The polar decomposition of `V`: modulus `N`, phase `A`. -/
lemma V_polar (alpha : ℝ) (roots : Multiset ℂ) (t : ℝ) :
    V alpha roots t = ((N alpha roots t : ℝ) : ℂ) * E (A alpha roots t) := by
  unfold V N A
  rw [first_factor_polar alpha t]
  have hprod : (roots.map fun r => 1 - r * E (-t)).prod
      = (((roots.map fun r => ‖1 - r * E (-t)‖).prod : ℝ) : ℂ)
        * E ((roots.map fun r => Complex.arg (1 - r * E (-t))).sum) := by
    have hmap : roots.map (fun r => 1 - r * E (-t))
        = roots.map fun r =>
            ((‖1 - r * E (-t)‖ : ℝ) : ℂ) * E (Complex.arg (1 - r * E (-t))) :=
      Multiset.map_congr rfl fun r _ => polar _
    rw [hmap, prod_norm_mul_E]
  rw [hprod]
  exact polar_mul _ _ _ _

/-- `P` on the circle: `P(E t) = E(p·t)·V t`. -/
lemma eval_P_E (alpha : ℝ) (roots : Multiset ℂ) (t : ℝ) :
    (P alpha roots).eval (E t)
      = E (((roots.card + 1 : ℕ) : ℝ) * t) * V alpha roots t := by
  rw [eval_P]
  unfold V
  have hfac : ∀ w : ℂ, E t - w = E t * (1 - w * E (-t)) := by
    intro w
    rw [mul_sub, mul_one, show E t * (w * E (-t)) = w * (E t * E (-t)) by ring,
      E_mul_E_neg, mul_one]
  have hmap : roots.map (fun r => E t - r)
      = roots.map fun r => E t * (1 - r * E (-t)) :=
    Multiset.map_congr rfl fun r _ => hfac r
  rw [hmap, prod_map_const_mul, hfac ((alpha : ℂ)), ← E_pow]
  ring

/-- `Q` on the circle: `Q(E t) = conj (V t)` — this is where
conjugation-closure of the root multiset enters. -/
lemma eval_Q_E (alpha : ℝ) (roots : Multiset ℂ)
    (hconj : roots.map (starRingEnd ℂ) = roots) (t : ℝ) :
    (Q alpha roots).eval (E t) = (starRingEnd ℂ) (V alpha roots t) := by
  rw [eval_Q]
  unfold V
  rw [map_mul]
  congr 1
  · rw [map_sub, map_one, map_mul, Complex.conj_ofReal, conj_E, neg_neg]
  · rw [map_multiset_prod, Multiset.map_map]
    have hstep : roots.map ((starRingEnd ℂ) ∘ fun r => 1 - r * E (-t))
        = (roots.map (starRingEnd ℂ)).map fun r => 1 - r * E t := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun r _ => ?_
      simp only [Function.comp_apply, map_sub, map_one, map_mul, conj_E, neg_neg]
    rw [hstep, hconj]

/-- **The key identity**: on the circle,
`R_m(E t) = 2·N t·cos(ψ t)·E((m+p)·t/2)` — the explicit phase that
replaces the argument principle. -/
lemma R_eval_E (alpha : ℝ) (roots : Multiset ℂ)
    (hconj : roots.map (starRingEnd ℂ) = roots) (m : ℕ) (t : ℝ) :
    (R alpha roots m).eval (E t)
      = ((2 * N alpha roots t * Real.cos (psi alpha roots m t) : ℝ) : ℂ)
        * E (((m + roots.card + 1 : ℕ) : ℝ) * t / 2) := by
  have hV := V_polar alpha roots t
  have hQE := eval_Q_E alpha roots hconj t
  have hPE := eval_P_E alpha roots t
  have hpsi : psi alpha roots m t
      = ((m + roots.card + 1 : ℕ) : ℝ) * t / 2 + A alpha roots t := rfl
  set c2 : ℝ := ((m + roots.card + 1 : ℕ) : ℝ) * t / 2 with hc2
  set a : ℝ := A alpha roots t with ha
  set n : ℝ := N alpha roots t with hn
  set ψ : ℝ := psi alpha roots m t with hψ
  have e1 : E ((m : ℝ) * t) * E (((roots.card + 1 : ℕ) : ℝ) * t) * E a
      = E c2 * E ψ := by
    rw [← E_add, ← E_add, ← E_add]
    apply E_congr
    rw [hpsi, hc2]
    push_cast
    ring
  have e2 : E (-a) = E c2 * E (-ψ) := by
    rw [← E_add]
    apply E_congr
    rw [hpsi]
    ring
  have e3 : E ψ + E (-ψ) = 2 * ((Real.cos ψ : ℝ) : ℂ) := E_add_E_neg ψ
  calc (R alpha roots m).eval (E t)
      = E t ^ m * (P alpha roots).eval (E t) + (Q alpha roots).eval (E t) :=
        eval_R alpha roots m (E t)
    _ = E ((m : ℝ) * t) * (E (((roots.card + 1 : ℕ) : ℝ) * t) * V alpha roots t)
        + (starRingEnd ℂ) (V alpha roots t) := by rw [E_pow, hPE, hQE]
    _ = (n : ℂ) * (E ((m : ℝ) * t) * E (((roots.card + 1 : ℕ) : ℝ) * t) * E a)
        + (n : ℂ) * E (-a) := by
        rw [hV, map_mul, Complex.conj_ofReal, conj_E]; ring
    _ = (n : ℂ) * (E c2 * E ψ) + (n : ℂ) * (E c2 * E (-ψ)) := by rw [e1, e2]
    _ = (n : ℂ) * E c2 * (E ψ + E (-ψ)) := by ring
    _ = (n : ℂ) * E c2 * (2 * ((Real.cos ψ : ℝ) : ℂ)) := by rw [e3]
    _ = ((2 * n * Real.cos ψ : ℝ) : ℂ) * E c2 := by push_cast; ring

/-- The zero test on the circle: `R_m(E t) = 0 ↔ cos(ψ t) = 0`. -/
lemma R_eval_E_eq_zero_iff (alpha : ℝ) (roots : Multiset ℂ) (halpha : 1 < alpha)
    (hroots : ∀ r ∈ roots, ‖r‖ < 1)
    (hconj : roots.map (starRingEnd ℂ) = roots) (m : ℕ) (t : ℝ) :
    (R alpha roots m).eval (E t) = 0 ↔ Real.cos (psi alpha roots m t) = 0 := by
  rw [R_eval_E alpha roots hconj m t]
  have hN := N_pos alpha roots halpha hroots t
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · have h2 : (2 * N alpha roots t * Real.cos (psi alpha roots m t) : ℝ) = 0 :=
        Complex.ofReal_eq_zero.mp h
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exfalso; linarith
      · exact h3
    · exact absurd h (E_ne_zero _)
  · intro h
    rw [h]
    simp

/-! ### Continuity of the phase -/

lemma continuous_E : Continuous E := by
  change Continuous fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)
  fun_prop

lemma continuous_arg_alpha {alpha : ℝ} (halpha : 1 < alpha) :
    Continuous fun t : ℝ => Complex.arg ((alpha : ℂ) - E t) := by
  rw [continuous_iff_continuousAt]
  intro t0
  have hcont : Continuous fun t : ℝ => (alpha : ℂ) - E t :=
    continuous_const.sub continuous_E
  have hcomp : ContinuousAt (Complex.arg ∘ fun t : ℝ => (alpha : ℂ) - E t) t0 := by
    apply ContinuousAt.comp
    · exact Complex.continuousAt_arg (alpha_sub_E_mem_slitPlane halpha t0)
    · exact hcont.continuousAt
  exact hcomp

lemma continuous_arg_root {r : ℂ} (hr : ‖r‖ < 1) :
    Continuous fun t : ℝ => Complex.arg (1 - r * E (-t)) := by
  rw [continuous_iff_continuousAt]
  intro t0
  have hcont : Continuous fun t : ℝ => 1 - r * E (-t) :=
    continuous_const.sub (continuous_const.mul (continuous_E.comp continuous_neg))
  have hcomp : ContinuousAt (Complex.arg ∘ fun t : ℝ => 1 - r * E (-t)) t0 := by
    apply ContinuousAt.comp
    · exact Complex.continuousAt_arg (root_factor_mem_slitPlane hr t0)
    · exact hcont.continuousAt
  exact hcomp

lemma continuous_arg_sum (roots : Multiset ℂ) (hroots : ∀ r ∈ roots, ‖r‖ < 1) :
    Continuous fun t : ℝ =>
      (roots.map fun r => Complex.arg (1 - r * E (-t))).sum := by
  revert hroots
  induction roots using Multiset.induction_on with
  | empty =>
    intro _
    simp only [Multiset.map_zero, Multiset.sum_zero]
    exact continuous_const
  | cons a s ih =>
    intro hroots
    have ha : ‖a‖ < 1 := hroots a (Multiset.mem_cons_self a s)
    have hs := ih fun r hr => hroots r (Multiset.mem_cons_of_mem hr)
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (continuous_arg_root ha).add hs

lemma continuous_A (alpha : ℝ) (roots : Multiset ℂ) (halpha : 1 < alpha)
    (hroots : ∀ r ∈ roots, ‖r‖ < 1) :
    Continuous fun t : ℝ => A alpha roots t := by
  unfold A
  exact ((continuous_neg.add continuous_const).add
    (continuous_arg_alpha halpha)).add (continuous_arg_sum roots hroots)

lemma continuous_psi (alpha : ℝ) (roots : Multiset ℂ) (halpha : 1 < alpha)
    (hroots : ∀ r ∈ roots, ‖r‖ < 1) (m : ℕ) :
    Continuous fun t : ℝ => psi alpha roots m t := by
  unfold psi
  exact ((continuous_const.mul continuous_id).div_const 2).add
    (continuous_A alpha roots halpha hroots)

/-! ### The endpoints -/

/-- Across `[0, 2π]` every `arg`-term returns to its start; only the
linear `−t` part moves: `A(2π) = A(0) − 2π`. -/
lemma A_two_pi (alpha : ℝ) (roots : Multiset ℂ) :
    A alpha roots (2 * Real.pi) = A alpha roots 0 - 2 * Real.pi := by
  unfold A
  have h1 : E (2 * Real.pi) = 1 := E_two_pi
  have h2 : E (-(2 * Real.pi)) = 1 := by
    have h := E_mul_E_neg (2 * Real.pi)
    rw [h1, one_mul] at h
    exact h
  have h3 : E (0 : ℝ) = 1 := E_zero
  have h4 : E (-(0 : ℝ)) = 1 := by rw [neg_zero]; exact E_zero
  rw [h1, h2, h3, h4]
  ring

/-- The total climb of the phase: `ψ(2π) = ψ(0) + (m+p)·π − 2π`. -/
lemma psi_two_pi (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) :
    psi alpha roots m (2 * Real.pi)
      = psi alpha roots m 0 + ((m + roots.card + 1 : ℕ) : ℝ) * Real.pi
        - 2 * Real.pi := by
  unfold psi
  rw [A_two_pi]
  ring

/-- `R_m(1) = 2·P(1) ≠ 0`: the phase starts off the cosine grid. -/
lemma eval_R_one_ne_zero (alpha : ℝ) (roots : Multiset ℂ) (halpha : 1 < alpha)
    (hroots : ∀ r ∈ roots, ‖r‖ < 1) (m : ℕ) :
    (R alpha roots m).eval 1 ≠ 0 := by
  have hPQ : (Q alpha roots).eval 1 = (P alpha roots).eval 1 := by
    rw [eval_P, eval_Q]
    simp only [mul_one]
  have hP1 : (P alpha roots).eval 1 ≠ 0 := by
    rw [eval_P]
    apply mul_ne_zero
    · intro h
      have h1 : (1 : ℂ) = (alpha : ℂ) := sub_eq_zero.mp h
      have h2 : (1 : ℝ) = alpha := by exact_mod_cast h1
      linarith
    · rw [Ne, Multiset.prod_eq_zero_iff]
      intro h0
      obtain ⟨r, hr, hr0⟩ := Multiset.mem_map.mp h0
      have hr1 : (1 : ℂ) = r := sub_eq_zero.mp hr0
      have := hroots r hr
      rw [← hr1, norm_one] at this
      exact lt_irrefl _ this
  rw [eval_R, one_pow, one_mul, hPQ]
  intro h
  apply hP1
  have h2 : (2 : ℂ) * (P alpha roots).eval 1 = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact h3

lemma cos_psi_zero_ne_zero (alpha : ℝ) (roots : Multiset ℂ) (halpha : 1 < alpha)
    (hroots : ∀ r ∈ roots, ‖r‖ < 1)
    (hconj : roots.map (starRingEnd ℂ) = roots) (m : ℕ) :
    Real.cos (psi alpha roots m 0) ≠ 0 := by
  intro h
  have h0 := (R_eval_E_eq_zero_iff alpha roots halpha hroots hconj m 0).mpr h
  rw [E_zero] at h0
  exact eval_R_one_ne_zero alpha roots halpha hroots m h0

/-! ### The grid count -/

/-- **The grid-count workhorse.**  A continuous phase `f` on `[0, 2π]`
that climbs by exactly `L·π` and starts off the cosine grid attains `L`
distinct interior grid values, planting `L` distinct zeros of
`cos ∘ f` in `(0, 2π)`. -/
lemma exists_interior_grid (f : ℝ → ℝ) (hf : Continuous f) (L : ℕ)
    (hclimb : f (2 * Real.pi) = f 0 + (L : ℝ) * Real.pi)
    (hcos0 : Real.cos (f 0) ≠ 0) :
    ∃ T : Finset ℝ, T.card = L ∧ ∀ t ∈ T,
      (0 < t ∧ t < 2 * Real.pi) ∧ Real.cos (f t) = 0 := by
  classical
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set k0 : ℤ := ⌊(f 0 - Real.pi / 2) / Real.pi⌋ with hk0
  have hcosg : ∀ j : ℕ,
      Real.cos (Real.pi / 2 + ((k0 : ℝ) + 1 + (j : ℝ)) * Real.pi) = 0 := by
    intro j
    rw [Real.cos_eq_zero_iff]
    exact ⟨k0 + 1 + (j : ℤ), by push_cast; ring⟩
  have hlow : ∀ j : ℕ, f 0 < Real.pi / 2 + ((k0 : ℝ) + 1 + (j : ℝ)) * Real.pi := by
    intro j
    have h1 : (f 0 - Real.pi / 2) / Real.pi < (k0 : ℝ) + 1 := by
      rw [hk0]; exact Int.lt_floor_add_one _
    have h2 : f 0 - Real.pi / 2 < ((k0 : ℝ) + 1) * Real.pi := by
      rw [div_lt_iff₀ hπ] at h1
      exact h1
    have h3 : (0 : ℝ) ≤ (j : ℝ) * Real.pi := mul_nonneg (Nat.cast_nonneg j) hπ.le
    nlinarith [h2, h3]
  have hstrict : Real.pi / 2 + (k0 : ℝ) * Real.pi < f 0 := by
    have h1 : (k0 : ℝ) ≤ (f 0 - Real.pi / 2) / Real.pi := by
      rw [hk0]; exact Int.floor_le _
    have h2 : (k0 : ℝ) * Real.pi ≤ f 0 - Real.pi / 2 := (le_div_iff₀ hπ).mp h1
    rcases lt_or_eq_of_le h2 with h | h
    · linarith
    · exfalso
      apply hcos0
      rw [Real.cos_eq_zero_iff]
      exact ⟨k0, by linarith⟩
  have hhigh : ∀ j : ℕ, j < L →
      Real.pi / 2 + ((k0 : ℝ) + 1 + (j : ℝ)) * Real.pi < f (2 * Real.pi) := by
    intro j hj
    rw [hclimb]
    have hjL : (j : ℝ) + 1 ≤ (L : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hj
    nlinarith [hstrict,
      mul_nonneg (by linarith : (0 : ℝ) ≤ (L : ℝ) - (j : ℝ) - 1) hπ.le]
  have hIVT := intermediate_value_Icc
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hf.continuousOn
  have hex : ∀ j : ℕ, j < L → ∃ t : ℝ, (0 < t ∧ t < 2 * Real.pi) ∧
      f t = Real.pi / 2 + ((k0 : ℝ) + 1 + (j : ℝ)) * Real.pi := by
    intro j hj
    have hmem : Real.pi / 2 + ((k0 : ℝ) + 1 + (j : ℝ)) * Real.pi
        ∈ Icc (f 0) (f (2 * Real.pi)) :=
      ⟨le_of_lt (hlow j), le_of_lt (hhigh j hj)⟩
    obtain ⟨t, htmem, hteq⟩ := hIVT hmem
    refine ⟨t, ⟨?_, ?_⟩, hteq⟩
    · rcases eq_or_lt_of_le htmem.1 with h | h
      · exfalso
        rw [← h] at hteq
        exact absurd hteq (ne_of_lt (hlow j))
      · exact h
    · rcases eq_or_lt_of_le htmem.2 with h | h
      · exfalso
        rw [h] at hteq
        exact absurd hteq (ne_of_gt (hhigh j hj))
      · exact h
  set tf : ℕ → ℝ := fun j => if h : j < L then (hex j h).choose else 0 with htf
  have htf_spec : ∀ j : ℕ, j < L → (0 < tf j ∧ tf j < 2 * Real.pi) ∧
      f (tf j) = Real.pi / 2 + ((k0 : ℝ) + 1 + (j : ℝ)) * Real.pi := by
    intro j hj
    simp only [htf, dite_eq_left hj]
    exact (hex j hj).choose_spec
  refine ⟨(Finset.range L).image tf, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro j hj j' hj' heq
    have hj1 := (htf_spec j (Finset.mem_range.mp hj)).2
    have hj2 := (htf_spec j' (Finset.mem_range.mp hj')).2
    rw [heq] at hj1
    have h12 : Real.pi / 2 + ((k0 : ℝ) + 1 + (j : ℝ)) * Real.pi
        = Real.pi / 2 + ((k0 : ℝ) + 1 + (j' : ℝ)) * Real.pi := hj1.symm.trans hj2
    have h13 := mul_right_cancel₀ (ne_of_gt hπ) (add_left_cancel h12)
    have h14 : (j : ℝ) = (j' : ℝ) := by linarith
    exact_mod_cast h14
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    have hspec := htf_spec j (Finset.mem_range.mp hj)
    exact ⟨hspec.1, by rw [hspec.2]; exact hcosg j⟩

/-- **The circle count**: with `p = roots.card + 1` and
`3 ≤ m + p`, the polynomial `R_m` has `m + p − 2` distinct roots
`exp(t·I)`, `t ∈ (0, 2π)`, on the unit circle.
(Stated without the redundant `1 ≤ m`.) -/
theorem salem_circle_count (alpha : ℝ) (roots : Multiset ℂ) (halpha : 1 < alpha)
    (hroots : ∀ r ∈ roots, ‖r‖ < 1)
    (hconj : roots.map (starRingEnd ℂ) = roots) (m : ℕ)
    (hmp : 3 ≤ m + (roots.card + 1)) :
    ∃ T : Finset ℝ, T.card = m + (roots.card + 1) - 2 ∧
      ∀ t ∈ T, (0 < t ∧ t < 2 * Real.pi) ∧
        (R alpha roots m).eval (Complex.exp (t * Complex.I)) = 0 := by
  have hclimb : psi alpha roots m (2 * Real.pi)
      = psi alpha roots m 0 + ((m + (roots.card + 1) - 2 : ℕ) : ℝ) * Real.pi := by
    rw [psi_two_pi]
    have h2 : 2 ≤ m + roots.card + 1 := by omega
    have heq : m + (roots.card + 1) - 2 = m + roots.card + 1 - 2 := by omega
    rw [heq, Nat.cast_sub h2]
    push_cast
    ring
  obtain ⟨T, hcard, hT⟩ := exists_interior_grid (psi alpha roots m)
    (continuous_psi alpha roots halpha hroots m) (m + (roots.card + 1) - 2) hclimb
    (cos_psi_zero_ne_zero alpha roots halpha hroots hconj m)
  refine ⟨T, hcard, fun t ht => ⟨(hT t ht).1, ?_⟩⟩
  exact (R_eval_E_eq_zero_iff alpha roots halpha hroots hconj m t).mpr (hT t ht).2

/-! ### Degree bookkeeping — `R_m` is monic of degree `m + p` -/

lemma P_monic (alpha : ℝ) (roots : Multiset ℂ) : (P alpha roots).Monic :=
  (monic_X_sub_C _).mul
    (monic_multiset_prod_of_monic roots _ fun r _ => monic_X_sub_C r)

lemma prod_X_sub_C_natDegree (roots : Multiset ℂ) :
    ((roots.map fun r => X - C r).prod).natDegree = roots.card := by
  rw [natDegree_multiset_prod_of_monic]
  · rw [Multiset.map_map]
    have h : roots.map (natDegree ∘ fun r => X - C r) = roots.map fun _ => 1 :=
      Multiset.map_congr rfl fun r _ => by
        simp [Function.comp_apply]
    rw [h, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
  · intro f hf
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hf
    exact monic_X_sub_C r

lemma P_natDegree (alpha : ℝ) (roots : Multiset ℂ) :
    (P alpha roots).natDegree = roots.card + 1 := by
  unfold P
  rw [(monic_X_sub_C ((alpha : ℂ))).natDegree_mul
    (monic_multiset_prod_of_monic roots _ fun r _ => monic_X_sub_C r),
    natDegree_X_sub_C, prod_X_sub_C_natDegree]
  omega

lemma XmP_monic (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) :
    (X ^ m * P alpha roots).Monic :=
  (monic_X_pow m).mul (P_monic alpha roots)

lemma XmP_natDegree (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) :
    (X ^ m * P alpha roots).natDegree = m + (roots.card + 1) := by
  rw [(monic_X_pow m).natDegree_mul (P_monic alpha roots), natDegree_X_pow,
    P_natDegree]

lemma factor_natDegree_le (r : ℂ) : (1 - C r * X : Polynomial ℂ).natDegree ≤ 1 := by
  refine le_trans (natDegree_sub_le _ _) ?_
  rw [natDegree_one]
  simp only [max_le_iff]
  exact ⟨Nat.zero_le 1, le_trans (natDegree_C_mul_le _ _) (le_of_eq natDegree_X)⟩

lemma Q_natDegree_le (alpha : ℝ) (roots : Multiset ℂ) :
    (Q alpha roots).natDegree ≤ roots.card + 1 := by
  unfold Q
  refine le_trans natDegree_mul_le ?_
  have h1 : (1 - C ((alpha : ℂ)) * X).natDegree ≤ 1 := factor_natDegree_le _
  have h2 : ((roots.map fun r => 1 - C r * X).prod).natDegree ≤ roots.card := by
    refine le_trans (natDegree_multiset_prod_le _) ?_
    rw [Multiset.map_map]
    refine le_trans (Multiset.sum_le_card_nsmul _ 1 ?_) ?_
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
      exact factor_natDegree_le r
    · rw [Multiset.card_map, smul_eq_mul, mul_one]
  omega

lemma degree_Q_lt (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) (hm : 1 ≤ m) :
    (Q alpha roots).degree < (X ^ m * P alpha roots).degree := by
  apply degree_lt_degree
  rw [XmP_natDegree]
  have hQle := Q_natDegree_le alpha roots
  omega

lemma R_monic (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) (hm : 1 ≤ m) :
    (R alpha roots m).Monic :=
  (XmP_monic alpha roots m).add_of_left (degree_Q_lt alpha roots m hm)

lemma R_natDegree (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) (hm : 1 ≤ m) :
    (R alpha roots m).natDegree = m + (roots.card + 1) := by
  unfold R
  rw [natDegree_eq_of_degree_eq
    (degree_add_eq_left_of_degree_lt (degree_Q_lt alpha roots m hm))]
  exact XmP_natDegree alpha roots m

/-! ### Injectivity of the circle parametrization -/

lemma E_inj {t s : ℝ} (ht : 0 < t) (ht2 : t < 2 * Real.pi) (hs : 0 < s)
    (hs2 : s < 2 * Real.pi) (heq : E t = E s) : t = s := by
  simp only [E] at heq
  rw [Complex.exp_eq_exp_iff_exists_int] at heq
  obtain ⟨n, hn⟩ := heq
  have hI : ((t : ℂ)) * Complex.I = ((s + n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    rw [hn]; push_cast; ring
  have hreal : t = s + n * (2 * Real.pi) := by
    have h2 := mul_right_cancel₀ Complex.I_ne_zero hI
    exact_mod_cast h2
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with h | h | h
    · exfalso
      have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
      nlinarith [mul_le_mul_of_nonneg_right hn1
        (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    · exact h
    · exfalso
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      nlinarith [mul_le_mul_of_nonneg_right hn1
        (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rw [hn0] at hreal
  simpa using hreal

/-! ### The trichotomy -/

/-- **The trichotomy**: if `τ > 1` is a root of `R_m` (with
`1 ≤ m` and `3 ≤ m + p`), then EVERY root of `R_m` is unimodular or
lies in `{τ, 1/τ}` — the `m + p − 2` circle points of the circle count together with
`τ` and `1/τ` already exhaust the degree `m + p` of the monic `R_m`,
by the multiset squeeze `S.val ≤ (R_m).roots`. -/
theorem salem_root_trichotomy (alpha : ℝ) (roots : Multiset ℂ) (halpha : 1 < alpha)
    (hroots : ∀ r ∈ roots, ‖r‖ < 1)
    (hconj : roots.map (starRingEnd ℂ) = roots) (m : ℕ) (hm : 1 ≤ m)
    (hmp : 3 ≤ m + (roots.card + 1))
    (tau : ℝ) (htau : 1 < tau) (hroot : (R alpha roots m).eval ((tau : ℂ)) = 0) :
    ∀ z : ℂ, (R alpha roots m).eval z = 0 →
      ‖z‖ = 1 ∨ z = ((tau : ℂ)) ∨ z = ((tau : ℂ))⁻¹ := by
  classical
  obtain ⟨T, hcard, hT⟩ := salem_circle_count alpha roots halpha hroots hconj m hmp
  have hUcard : (T.image fun t => E t).card = m + (roots.card + 1) - 2 := by
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
  have hScard : S.card = m + (roots.card + 1) := by
    rw [hS, Finset.card_union_of_disjoint hdisj, hUcard, hpair]
    omega
  have hSroot : ∀ z ∈ S, (R alpha roots m).eval z = 0 := by
    intro z hz
    rw [hS, Finset.mem_union] at hz
    rcases hz with h | h
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      exact (hT t ht).2
    · rcases Finset.mem_insert.mp h with h1 | h1
      · rw [h1]; exact hroot
      · rw [Finset.mem_singleton.mp h1]
        exact salem_root_inv alpha roots m htau0 hroot
  have hRne : R alpha roots m ≠ 0 := (R_monic alpha roots m hm).ne_zero
  have hle : S.val ≤ (R alpha roots m).roots := by
    rw [Multiset.le_iff_count]
    intro z
    by_cases hz : z ∈ S
    · rw [Multiset.count_eq_one_of_mem S.nodup (Finset.mem_def.mp hz),
        Polynomial.count_roots]
      have hpos := (Polynomial.rootMultiplicity_pos hRne).mpr (hSroot z hz)
      omega
    · rw [Multiset.count_eq_zero.mpr (fun hv => hz (Finset.mem_def.mpr hv))]
      exact Nat.zero_le _
  have hcards : Multiset.card ((R alpha roots m).roots) ≤ Multiset.card S.val := by
    have h1 := Polynomial.card_roots' (R alpha roots m)
    rw [R_natDegree alpha roots m hm] at h1
    have h2 : Multiset.card S.val = S.card := rfl
    omega
  have heq : S.val = (R alpha roots m).roots :=
    Multiset.eq_of_le_of_card_le hle hcards
  intro z hz
  have hzmem : z ∈ (R alpha roots m).roots := Polynomial.mem_roots'.mpr ⟨hRne, hz⟩
  rw [← heq] at hzmem
  have hzS : z ∈ S := Finset.mem_def.mpr hzmem
  rw [hS, Finset.mem_union] at hzS
  rcases hzS with h | h
  · exact Or.inl (hUnorm z h)
  · rcases Finset.mem_insert.mp h with h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Finset.mem_singleton.mp h1))

end
end SalemCircle
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
