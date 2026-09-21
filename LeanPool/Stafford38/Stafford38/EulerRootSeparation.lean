/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib
import LeanPool.Stafford38.Stafford38.EvolutionaryCertificate

/-!
# The Euler root line and the Bézout hypothesis

The evolutionary Stafford certificate of `Stafford38.EvolutionaryCertificate`
consumes one Bézout identity: the Euler corner polynomial

    C_r = R₊ - R₋,   R₊ = (X+1)⋯(X+r),   R₋ = X(X-1)⋯(X-r+1)

must be coprime to `R₊` and to each of its own positive integer shifts
`C_r(X + n)`, `n ≥ 1`.  This file discharges that hypothesis.

The mechanism is a one-dimensional root separation.  For `i ≥ 1`,

    |z + i|² - |z - (i-1)|² = (2i - 1)(2 Re z + 1),

so on `Re z > -1/2` every rising factor strictly dominates the corresponding
falling factor and on `Re z < -1/2` every one is strictly dominated.  Hence

    C_r(z) = 0  ⟹  Re z = -1/2,

and all roots of `C_r` lie on a single vertical line.  Coprimality with `R₊`
follows because the roots of `R₊` are the negative integers, and coprimality
with every positive shift follows because the line `Re z = -1/2` is disjoint
from its own translates.

Everything is proved over `ℂ`, descended to `ℚ` by `Polynomial.isCoprime_map`,
and transported to an arbitrary characteristic-zero field by `IsCoprime.map`.
-/

namespace Stafford38.Evolution

open Polynomial

/-- Over `ℂ` regarded as a `ℂ`-algebra, `aeval` is ordinary evaluation. -/
lemma aeval_eq_eval_complex (z : ℂ) (f : ℂ[X]) : aeval z f = f.eval z := by
  rfl

/-! ## The factorwise comparison -/

/-- The exact difference of squared moduli of one rising and one falling
factor.  This single computation drives the whole file. -/
lemma normSq_sub_normSq (z : ℂ) (i : ℕ) :
    Complex.normSq (z + ((i : ℂ) + 1)) - Complex.normSq (z - (i : ℂ))
      = (2 * (i : ℝ) + 1) * (2 * z.re + 1) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im]
  ring

lemma abs_lt_of_re_pos {z : ℂ} (hz : 0 < 2 * z.re + 1) (i : ℕ) :
    ‖z - (i : ℂ)‖ < ‖z + ((i : ℂ) + 1)‖ := by
  have hpos : 0 < (2 * (i : ℝ) + 1) * (2 * z.re + 1) := by positivity
  have h := normSq_sub_normSq z i
  have hlt : Complex.normSq (z - (i : ℂ)) < Complex.normSq (z + ((i : ℂ) + 1)) := by linarith
  simpa [Complex.norm_def] using
    (Real.sqrt_lt_sqrt (Complex.normSq_nonneg _) hlt)

lemma abs_lt_of_re_neg {z : ℂ} (hz : 2 * z.re + 1 < 0) (i : ℕ) :
    ‖z + ((i : ℂ) + 1)‖ < ‖z - (i : ℂ)‖ := by
  have hpos : 0 < (2 * (i : ℝ) + 1) := by positivity
  have h := normSq_sub_normSq z i
  have hlt : Complex.normSq (z + ((i : ℂ) + 1)) < Complex.normSq (z - (i : ℂ)) := by
    nlinarith [h, hpos, hz]
  simpa [Complex.norm_def] using
    (Real.sqrt_lt_sqrt (Complex.normSq_nonneg _) hlt)

/-! ## Strict domination of the whole product -/

lemma abs_falling_lt_rising {z : ℂ} (hz : 0 < 2 * z.re + 1) :
    ∀ r : ℕ, 1 ≤ r → ‖falling z r‖ < ‖rising z r‖
  | 0, h => absurd h (by norm_num)
  | 1, _ => by
      simpa [rising_succ, falling_succ] using abs_lt_of_re_pos hz 0
  | (r + 2), _ => by
      have ih := abs_falling_lt_rising hz (r + 1) (by omega)
      have hfac := abs_lt_of_re_pos hz (r + 1)
      rw [rising_succ, falling_succ, norm_mul, norm_mul]
      exact mul_lt_mul'' ih (by simpa using hfac) (by positivity) (by positivity)

lemma abs_rising_lt_falling {z : ℂ} (hz : 2 * z.re + 1 < 0) :
    ∀ r : ℕ, 1 ≤ r → ‖rising z r‖ < ‖falling z r‖
  | 0, h => absurd h (by norm_num)
  | 1, _ => by
      simpa [rising_succ, falling_succ] using abs_lt_of_re_neg hz 0
  | (r + 2), _ => by
      have ih := abs_rising_lt_falling hz (r + 1) (by omega)
      have hfac := abs_lt_of_re_neg hz (r + 1)
      rw [rising_succ, falling_succ, norm_mul, norm_mul]
      exact mul_lt_mul'' ih (by simpa using hfac) (by positivity) (by positivity)

/-- **The Euler root line.**  Every complex root of the corner polynomial `C_r`
has real part `-1/2`. -/
theorem re_eq_neg_half_of_isRoot {r : ℕ} (hr : 1 ≤ r) {z : ℂ}
    (hz : (cornerPoly ℂ r).IsRoot z) : z.re = -(1 / 2) := by
  have heval : rising z r - falling z r = 0 := by
    rw [← aeval_cornerPoly (k := ℂ) z r, aeval_eq_eval_complex]
    exact hz
  have heq : rising z r = falling z r := sub_eq_zero.mp heval
  have habs : ‖rising z r‖ = ‖falling z r‖ := by rw [heq]
  by_contra hne
  rcases lt_trichotomy (2 * z.re + 1) 0 with h | h | h
  · exact absurd habs (ne_of_lt (abs_rising_lt_falling h r hr))
  · exact hne (by linarith)
  · exact absurd habs.symm (ne_of_lt (abs_falling_lt_rising h r hr))

/-! ## The corner polynomial is nonzero, and `R₊` has no root on the line -/

lemma falling_zero_eq_zero : ∀ r : ℕ, 1 ≤ r → falling (0 : ℂ) r = 0
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp [falling_succ]
  | (r + 2), _ => by
      rw [falling_succ, falling_zero_eq_zero (r + 1) (by omega), zero_mul]

lemma rising_ne_zero_of_re_neg_half {z : ℂ} (hz : z.re = -(1 / 2)) :
    ∀ r : ℕ, rising z r ≠ 0
  | 0 => by simp
  | (r + 1) => by
      rw [rising_succ]
      refine mul_ne_zero (rising_ne_zero_of_re_neg_half hz r) ?_
      intro hcon
      have : (z + ((r : ℂ) + 1)).re = 0 := by rw [hcon]; simp
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, hz] at this
      have : (0 : ℝ) < (r : ℝ) + 1 := by positivity
      linarith

lemma rising_zero_ne_zero : ∀ r : ℕ, rising (0 : ℂ) r ≠ 0
  | 0 => by simp
  | (r + 1) => by
      rw [rising_succ]
      refine mul_ne_zero (rising_zero_ne_zero r) ?_
      have : (0 : ℝ) < (r : ℝ) + 1 := by positivity
      intro hcon
      have hre : ((0 : ℂ) + ((r : ℂ) + 1)).re = 0 := by rw [hcon]; simp
      simp only [Complex.add_re, Complex.zero_re, Complex.natCast_re, Complex.one_re] at hre
      linarith

lemma cornerPoly_ne_zero {r : ℕ} (hr : 1 ≤ r) : cornerPoly ℂ r ≠ 0 := by
  intro hcon
  have h0 : aeval (0 : ℂ) (cornerPoly ℂ r) = 0 := by rw [hcon]; simp
  rw [aeval_cornerPoly, falling_zero_eq_zero r hr, sub_zero] at h0
  exact rising_zero_ne_zero r h0

/-! ## Coprimality over `ℂ` -/

lemma isCoprime_of_no_common_root {f g : ℂ[X]} (hf : f ≠ 0)
    (h : ∀ z : ℂ, f.IsRoot z → g.IsRoot z → False) : IsCoprime f g := by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff]
  by_contra hu
  have hg0 : EuclideanDomain.gcd f g ≠ 0 := by
    intro hcon
    exact hf (EuclideanDomain.gcd_eq_zero_iff.mp hcon).1
  have hdeg : 0 < (EuclideanDomain.gcd f g).degree := by
    have hne : (EuclideanDomain.gcd f g).degree ≠ 0 := fun hcon =>
      hu (Polynomial.isUnit_iff_degree_eq_zero.mpr hcon)
    exact lt_of_le_of_ne (Polynomial.zero_le_degree_iff.mpr hg0) (Ne.symm hne)
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  rw [Polynomial.isRoot_gcd_iff_isRoot_left_right] at hz
  exact h z hz.1 hz.2

/-- `C_r` is coprime to the rising factorial `R₊`: the roots of `R₊` are
negative integers, and none of them lies on the line `Re = -1/2`. -/
theorem isCoprime_corner_rising_complex {r : ℕ} (hr : 1 ≤ r) :
    IsCoprime (cornerPoly ℂ r) (risingPoly ℂ r) := by
  refine isCoprime_of_no_common_root (cornerPoly_ne_zero hr) ?_
  intro z hzc hzr
  have hre := re_eq_neg_half_of_isRoot hr hzc
  have hzero : rising z r = 0 := by
    rw [← aeval_risingPoly (k := ℂ) z r, aeval_eq_eval_complex]
    exact hzr
  exact rising_ne_zero_of_re_neg_half hre r hzero

/-- `C_r` is coprime to each of its own positive integer shifts: the line
`Re = -1/2` is disjoint from every translate of itself. -/
theorem isCoprime_corner_shift_complex {r : ℕ} (hr : 1 ≤ r) {n : ℕ} (hn : 1 ≤ n) :
    IsCoprime (cornerPoly ℂ r) ((cornerPoly ℂ r).comp (X + Polynomial.C (n : ℂ))) := by
  refine isCoprime_of_no_common_root (cornerPoly_ne_zero hr) ?_
  intro z hzc hzs
  have h1 := re_eq_neg_half_of_isRoot hr hzc
  have hroot : (cornerPoly ℂ r).IsRoot (z + (n : ℂ)) := by
    simpa [Polynomial.IsRoot, Polynomial.eval_comp] using hzs
  have h2 := re_eq_neg_half_of_isRoot hr hroot
  simp only [Complex.add_re, Complex.natCast_re, h1] at h2
  have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-! ## Descent to an arbitrary characteristic-zero field -/

section Transport

variable {k K : Type*} [CommRing k] [CommRing K]

lemma map_risingPoly (φ : k →+* K) : ∀ n : ℕ, (risingPoly k n).map φ = risingPoly K n
  | 0 => by simp
  | (n + 1) => by
      rw [risingPoly_succ, Polynomial.map_mul, map_risingPoly φ n, risingPoly_succ]
      simp

lemma map_fallingPoly (φ : k →+* K) : ∀ n : ℕ, (fallingPoly k n).map φ = fallingPoly K n
  | 0 => by simp
  | (n + 1) => by
      rw [fallingPoly_succ, Polynomial.map_mul, map_fallingPoly φ n, fallingPoly_succ]
      simp

lemma map_cornerPoly (φ : k →+* K) (r : ℕ) :
    (cornerPoly k r).map φ = cornerPoly K r := by
  simp [cornerPoly, Polynomial.map_sub, map_risingPoly, map_fallingPoly]

end Transport

variable {k : Type*} [Field k] [CharZero k]

/-- `C_r` and `R₊` are coprime over every characteristic-zero field. -/
theorem isCoprime_corner_rising {r : ℕ} (hr : 1 ≤ r) :
    IsCoprime (cornerPoly k r) (risingPoly k r) := by
  have hQ : IsCoprime (cornerPoly ℚ r) (risingPoly ℚ r) := by
    rw [← Polynomial.isCoprime_map (Rat.castHom ℂ), map_cornerPoly, map_risingPoly]
    exact isCoprime_corner_rising_complex hr
  have := hQ.map (Polynomial.mapRingHom (Rat.castHom k))
  simpa [Polynomial.coe_mapRingHom, map_cornerPoly, map_risingPoly] using this

/-- `C_r` is coprime to each positive integer shift of itself, over every
characteristic-zero field. -/
theorem isCoprime_corner_shift {r : ℕ} (hr : 1 ≤ r) {n : ℕ} (hn : 1 ≤ n) :
    IsCoprime (cornerPoly k r) ((cornerPoly k r).comp (X + Polynomial.C (n : k))) := by
  have hQ : IsCoprime (cornerPoly ℚ r)
      ((cornerPoly ℚ r).comp (X + Polynomial.C (n : ℚ))) := by
    rw [← Polynomial.isCoprime_map (Rat.castHom ℂ), map_cornerPoly, Polynomial.map_comp,
      map_cornerPoly]
    simpa using isCoprime_corner_shift_complex hr hn
  have := hQ.map (Polynomial.mapRingHom (Rat.castHom k))
  simpa [Polynomial.coe_mapRingHom, map_cornerPoly, Polynomial.map_comp] using this

/-! ## The Bézout hypothesis of the main theorem -/

variable {D : Type*}

/-- The full coprimality statement consumed by `evolution_stafford_certificate`:
`C_r` is coprime to `R₊ · ∏ⱼ C_r(X + r + j)`, for every potential support.  The
shifts are `r + j ≥ r ≥ 1`, so no shifted factor meets the root line. -/
theorem isCoprime_corner_hyper {r : ℕ} (hr : 1 ≤ r) (terms : List (D × ℕ)) :
    IsCoprime (cornerPoly k r)
      (risingPoly k r * shiftedProd (cornerPoly k r) (shiftSupport terms r)) := by
  refine (isCoprime_corner_rising hr).mul_right ?_
  induction terms with
  | nil => simpa [shiftSupport] using isCoprime_one_right (x := cornerPoly k r)
  | cons t ts ih =>
      have hshift : IsCoprime (cornerPoly k r)
          ((cornerPoly k r).comp (X + Polynomial.C ((t.2 + r : ℕ) : k))) :=
        isCoprime_corner_shift hr (by omega)
      simpa [shiftSupport, shiftedProd_cons] using hshift.mul_right ih

/-- **Existence of the Bézout pair.**  This is exactly the hypothesis
`hbezout` of `evolution_stafford_certificate`, so the main theorem is
unconditional for every `r ≥ 1`. -/
theorem exists_bezout {r : ℕ} (hr : 1 ≤ r) (terms : List (D × ℕ)) :
    ∃ α β : k[X], cornerPoly k r * α
      + (risingPoly k r * shiftedProd (cornerPoly k r) (shiftSupport terms r)) * β = 1 := by
  obtain ⟨α, β, hαβ⟩ := isCoprime_corner_hyper (k := k) hr terms
  exact ⟨α, β, by linear_combination hαβ⟩

end Stafford38.Evolution
