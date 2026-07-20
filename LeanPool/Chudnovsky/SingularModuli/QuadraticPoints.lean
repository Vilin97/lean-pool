/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.Modular

/-!
# Binary quadratic forms and CM points (Phase C, Track 3)

This file develops the elementary theory of integral binary quadratic forms
`f = (a, b, c)` (meaning `a X² + b XY + c Y²`) together with their action of
`GL₂(ℤ)`/`SL₂(ℤ)`, the discriminant and content, and the correspondence with
*CM points* — points `τ ∈ ℍ` satisfying `a τ² + b τ + c = 0`.

It is the arithmetic input to `FormReduction.lean` (the reduction algorithm and the
`decide`-enumeration of reduced forms of discriminant `−163`) and to the three-prime
rationality argument of `PhaseC-PLAN.md` §4.2, whose chunk (C5) consumes:

* the discriminant `disc f = b² − 4ac` and its invariance under `SL₂` (`disc_act`);
* primitivity (`IsPrimitive`) and its preservation under `GL₂(ℤ)` (`IsPrimitive.act`);
* the *fixed-point / `ℚ[Λ]`-algebra* classification: an integer matrix fixing a CM point
  `τ` of a primitive form is `p·I + k·(form matrix)`, with
  `det = p² + b p k + a c k²` (`fixes_iff`, `det_of_fixes`).

Conventions match `ComplexMult.lean`: at `τ₁₆₃` the CM relation is `41 − τ + τ² = 0`,
i.e. the form `(a, b, c) = (1, −1, 41)`, `disc = −163`.

The `GL₂` action is the classical *right* action on forms,
`(f · M)(X, Y) = f(pX + qY, rX + sY)` for `M = ![![p, q], ![r, s]]`; it is packaged as
`BQF.act f p q r s` taking the four entries directly (avoiding matrix-coercion churn).
-/

noncomputable section

namespace Chudnovsky.QF

open Complex UpperHalfPlane

/-- An integral binary quadratic form `a X² + b XY + c Y²`, recorded as its coefficient
triple `(a, b, c)`. -/
@[ext] structure BQF where
  /-- The `X²` coefficient. -/
  a : ℤ
  /-- The `XY` coefficient. -/
  b : ℤ
  /-- The `Y²` coefficient. -/
  c : ℤ
deriving DecidableEq

/-- The discriminant `b² − 4ac`. -/
def disc (f : BQF) : ℤ := f.b ^ 2 - 4 * f.a * f.c

/-- A form is positive definite when `a > 0` and `disc < 0` (then `c > 0` too). -/
def IsPosDef (f : BQF) : Prop := 0 < f.a ∧ disc f < 0

/-- A form is primitive when its coefficients have no common non-unit divisor. -/
def IsPrimitive (f : BQF) : Prop :=
  ∀ d : ℤ, d ∣ f.a → d ∣ f.b → d ∣ f.c → IsUnit d

/-- The right `GL₂`-action on forms: `(f · ![![p,q],![r,s]])`. -/
def act (f : BQF) (p q r s : ℤ) : BQF where
  a := f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2
  b := 2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s
  c := f.a * q ^ 2 + f.b * q * s + f.c * s ^ 2

@[simp] lemma act_a (f : BQF) (p q r s : ℤ) :
    (act f p q r s).a = f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2 := rfl
@[simp] lemma act_b (f : BQF) (p q r s : ℤ) :
    (act f p q r s).b = 2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s := rfl
@[simp] lemma act_c (f : BQF) (p q r s : ℤ) :
    (act f p q r s).c = f.a * q ^ 2 + f.b * q * s + f.c * s ^ 2 := rfl

/-- The identity matrix acts trivially. -/
@[simp] lemma act_one (f : BQF) : act f 1 0 0 1 = f := by
  ext <;> simp

/-- **Discriminant transforms by the square of the determinant.** In particular for
`SL₂` (`p s − q r = 1`) the discriminant is invariant. -/
theorem disc_act (f : BQF) (p q r s : ℤ) :
    disc (act f p q r s) = (p * s - q * r) ^ 2 * disc f := by
  simp only [disc, act_a, act_b, act_c]; ring

/-- Composition of two `act`s is the `act` of the matrix product. -/
theorem act_act (f : BQF) (p q r s p' q' r' s' : ℤ) :
    act (act f p q r s) p' q' r' s' =
      act f (p * p' + q * r') (p * q' + q * s') (r * p' + s * r') (r * q' + s * s') := by
  ext <;> simp only [act_a, act_b, act_c] <;> ring

/-- Acting by an `SL₂`-matrix and then by its inverse `![![s,-q],![-r,p]]` returns `f`. -/
theorem act_act_inv (f : BQF) {p q r s : ℤ} (hdet : p * s - q * r = 1) :
    act (act f p q r s) s (-q) (-r) p = f := by
  rw [act_act]
  have h1 : p * s + q * (-r) = 1 := by ring_nf; linarith [hdet]
  have h2 : r * s + s * (-r) = 0 := by ring
  have h3 : p * (-q) + q * p = 0 := by ring
  have h4 : r * (-q) + s * p = 1 := by ring_nf; linarith [hdet]
  rw [h1, h2, h3, h4, act_one]

/-- A common divisor of the coefficients divides the coefficients of any `act`. -/
lemma dvd_act_of_dvd {d : ℤ} {f : BQF} (ha : d ∣ f.a) (hb : d ∣ f.b) (hc : d ∣ f.c)
    (p q r s : ℤ) :
    d ∣ (act f p q r s).a ∧ d ∣ (act f p q r s).b ∧ d ∣ (act f p q r s).c := by
  simp only [act_a, act_b, act_c]
  refine ⟨dvd_add (dvd_add (ha.mul_right _) ((hb.mul_right p).mul_right r)) (hc.mul_right _),
    dvd_add (dvd_add (((ha.mul_left 2).mul_right p).mul_right q) (hb.mul_right _))
      (((hc.mul_left 2).mul_right r).mul_right s),
    dvd_add (dvd_add (ha.mul_right _) ((hb.mul_right q).mul_right s)) (hc.mul_right _)⟩

/-- **Primitivity is preserved by `SL₂`** (indeed `GL₂(ℤ)`). -/
theorem IsPrimitive.act {f : BQF} (hf : IsPrimitive f) {p q r s : ℤ}
    (hdet : p * s - q * r = 1) : IsPrimitive (act f p q r s) := by
  intro d hda hdb hdc
  obtain ⟨ha, hb, hc⟩ := dvd_act_of_dvd hda hdb hdc s (-q) (-r) p
  rw [act_act_inv f hdet] at ha hb hc
  exact hf d ha hb hc

/-! ## CM points: roots of a form in the upper half-plane -/

/-- `τ ∈ ℍ` is a *root* of the form `f` when `a τ² + b τ + c = 0`. -/
def IsRoot (f : BQF) (τ : ℍ) : Prop :=
  (f.a : ℂ) * (τ : ℂ) ^ 2 + (f.b : ℂ) * (τ : ℂ) + (f.c : ℂ) = 0

/-- A real linear relation `α·τ + β = 0` at a point of `ℍ` forces `α = 0` (and then
`β = 0`): the imaginary part gives `α · Im τ = 0`. -/
lemma real_lin_eq_zero (τ : ℍ) {α β : ℝ} (h : (α : ℂ) * (τ : ℂ) + (β : ℂ) = 0) :
    α = 0 ∧ β = 0 := by
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, Complex.zero_im, zero_mul, add_zero] at him
  have hα : α = 0 := by
    rcases mul_eq_zero.mp him with h' | h'
    · exact h'
    · exact absurd h' τ.im_ne_zero
  refine ⟨hα, ?_⟩
  have hre := congrArg Complex.re h
  simp only [hα, Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_re,
    Complex.zero_re] at hre
  simpa using hre

/-- An integer linear relation `α·τ + β = 0` at a point of `ℍ` forces `α = β = 0`. -/
lemma int_lin_eq_zero (τ : ℍ) {α β : ℤ} (h : (α : ℂ) * (τ : ℂ) + (β : ℂ) = 0) :
    α = 0 ∧ β = 0 := by
  have h' : ((α : ℝ) : ℂ) * (τ : ℂ) + ((β : ℝ) : ℂ) = 0 := by push_cast at h ⊢; exact h
  obtain ⟨hα, hβ⟩ := real_lin_eq_zero τ h'
  exact ⟨by exact_mod_cast hα, by exact_mod_cast hβ⟩

/-- For a positive-definite form, `c > 0` as well (`4ac = b² − disc > 0`). -/
lemma IsPosDef.c_pos {f : BQF} (hf : IsPosDef f) : 0 < f.c := by
  obtain ⟨ha, hd⟩ := hf
  simp only [disc] at hd
  nlinarith [sq_nonneg f.b, hd, ha]

/-- The square-completion identity `(2aτ + b)² = disc f` for a root `τ` of `f`. -/
lemma sq_two_a_root {f : BQF} {τ : ℍ} (h : IsRoot f τ) :
    (2 * (f.a : ℂ) * (τ : ℂ) + (f.b : ℂ)) ^ 2 = (disc f : ℂ) := by
  simp only [disc, IsRoot] at *
  push_cast
  linear_combination (4 * (f.a : ℂ)) * h

/-- **Uniqueness of the CM point of a positive-definite form.** Two roots in `ℍ` of the
same positive-definite form are equal (both are the root with positive imaginary part). -/
theorem root_unique {f : BQF} (hf : IsPosDef f) {τ τ' : ℍ}
    (h : IsRoot f τ) (h' : IsRoot f τ') : τ = τ' := by
  obtain ⟨ha, _⟩ := hf
  have haC : (f.a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hsq : (2 * (f.a : ℂ) * (τ : ℂ) + (f.b : ℂ)) ^ 2
      = (2 * (f.a : ℂ) * (τ' : ℂ) + (f.b : ℂ)) ^ 2 := by
    rw [sq_two_a_root h, sq_two_a_root h']
  have hfac : (2 * (f.a : ℂ) * (τ : ℂ) - 2 * (f.a : ℂ) * (τ' : ℂ)) *
      (2 * (f.a : ℂ) * (τ : ℂ) + (f.b : ℂ) + (2 * (f.a : ℂ) * (τ' : ℂ) + (f.b : ℂ))) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | h2
  · -- `2a(τ − τ') = 0` ⇒ `τ = τ'`
    have : (τ : ℂ) = (τ' : ℂ) := by
      have := mul_left_cancel₀ (mul_ne_zero (two_ne_zero) haC) (by linear_combination h1 :
        2 * (f.a : ℂ) * (τ : ℂ) = 2 * (f.a : ℂ) * (τ' : ℂ))
      exact this
    exact UpperHalfPlane.ext this
  · -- `a(τ + τ') = −b` contradicts positive imaginary parts
    exfalso
    have h3 : (f.a : ℂ) * ((τ : ℂ) + (τ' : ℂ)) = -(f.b : ℂ) := by linear_combination h2 / 2
    have him := congrArg Complex.im h3
    simp only [Complex.mul_im, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
      UpperHalfPlane.coe_im, Complex.neg_im, zero_mul, add_zero, mul_add, neg_zero] at him
    have hτ := τ.im_pos
    have hτ' := τ'.im_pos
    have haR : (0 : ℝ) < (f.a : ℝ) := by exact_mod_cast ha
    nlinarith [him, hτ, hτ', haR]

/-! ## The fixed-point (`ℚ[Λ]`) algebra

An integer matrix `![![p,q],![r,s]]` *fixes* `τ ∈ ℍ` (as a Möbius transformation) when
`p τ + q = τ (r τ + s)`, i.e. `r τ² + (s − p) τ − q = 0`.  For a root `τ` of a primitive
positive-definite form `f = (a,b,c)`, the fixing matrices are exactly `p·I + k·M_f` where
`M_f = ![![0,−c],![a,b]]` is the companion matrix of `f`; the determinant is the norm form
`p² + b p k + a c k²`.  This is the `ℚ[Λ]`-algebra fact consumed by `PhaseC-PLAN.md`
§4.2 (C5) and §5.1 step 4. -/

/-- The fixing relation `p τ + q = τ (r τ + s)`, division-free. -/
def Fixes (p q r s : ℤ) (τ : ℍ) : Prop :=
  (p : ℂ) * (τ : ℂ) + (q : ℂ) = (τ : ℂ) * ((r : ℂ) * (τ : ℂ) + (s : ℂ))

/-- A primitive form admits a Bézout relation among its coefficients. -/
lemma bezout_of_primitive {f : BQF} (hf : IsPrimitive f) :
    ∃ u v w : ℤ, u * f.a + v * f.b + w * f.c = 1 := by
  have hg1 : Int.gcd f.a (Int.gcd f.b f.c) = 1 := by
    have hda : ((Int.gcd f.a (Int.gcd f.b f.c) : ℤ)) ∣ f.a :=
      Int.gcd_dvd_left f.a (Int.gcd f.b f.c : ℤ)
    have hdd : ((Int.gcd f.a (Int.gcd f.b f.c) : ℤ)) ∣ (Int.gcd f.b f.c : ℤ) :=
      Int.gcd_dvd_right f.a (Int.gcd f.b f.c : ℤ)
    have hb : ((Int.gcd f.b f.c : ℤ)) ∣ f.b := Int.gcd_dvd_left f.b f.c
    have hc : ((Int.gcd f.b f.c : ℤ)) ∣ f.c := Int.gcd_dvd_right f.b f.c
    have hu := hf _ hda (hdd.trans hb) (hdd.trans hc)
    rcases Int.isUnit_iff.mp hu with h | h
    · exact_mod_cast h
    · exfalso; have : (0 : ℤ) ≤ (Int.gcd f.a (Int.gcd f.b f.c) : ℤ) := Int.natCast_nonneg _
      omega
  have hco : IsCoprime f.a (Int.gcd f.b f.c : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast hg1)
  obtain ⟨u, v, huv⟩ := hco
  have hbc := Int.gcd_eq_gcd_ab f.b f.c
  refine ⟨u, v * Int.gcdA f.b f.c, v * Int.gcdB f.b f.c, ?_⟩
  have : (u * f.a + v * (Int.gcd f.b f.c : ℤ)) = 1 := huv
  rw [hbc] at this
  linear_combination this

/-- **Fixed-matrix classification.** If an integer matrix `![![p,q],![r,s]]` fixes a root
`τ` of a primitive positive-definite form `f`, then there is `k : ℤ` with
`r = k·a`, `s − p = k·b`, `q = −k·c`. -/
theorem fixes_classification {f : BQF} (hf : IsPrimitive f) (hpd : IsPosDef f)
    {p q r s : ℤ} {τ : ℍ} (hroot : IsRoot f τ) (hfix : Fixes p q r s τ) :
    ∃ k : ℤ, r = k * f.a ∧ s - p = k * f.b ∧ q = -(k * f.c) := by
  have ha : f.a ≠ 0 := hpd.1.ne'
  -- the fixing quadratic `r τ² + (s−p) τ − q = 0`
  have hAf : (r : ℂ) * (τ : ℂ) ^ 2 + ((s : ℂ) - (p : ℂ)) * (τ : ℂ) + (-(q : ℂ)) = 0 := by
    simp only [Fixes] at hfix; linear_combination -hfix
  -- eliminate `τ²`: `(r·b − a·(s−p))τ + (r·c − a·(−q)) = 0`
  have hlin : ((r * f.b - f.a * (s - p) : ℤ) : ℂ) * (τ : ℂ)
      + ((r * f.c - f.a * (-q) : ℤ) : ℂ) = 0 := by
    simp only [IsRoot] at hroot; push_cast
    linear_combination (r : ℂ) * hroot - (f.a : ℂ) * hAf
  obtain ⟨r1, r2⟩ := int_lin_eq_zero τ hlin
  -- `r1 : r*b = a*(s-p)`, `r2 : r*c = a*(-q)`
  have hr1 : r * f.b = f.a * (s - p) := by linarith [r1]
  have hr2 : r * f.c = f.a * (-q) := by linarith [r2]
  -- primitivity ⇒ `a ∣ r`
  obtain ⟨u, v, w, huvw⟩ := bezout_of_primitive hf
  have hdvd : f.a ∣ r := by
    refine ⟨u * r + v * (s - p) + w * (-q), ?_⟩
    have hr : r * (u * f.a + v * f.b + w * f.c) = r := by rw [huvw]; ring
    linear_combination -hr + v * hr1 + w * hr2
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨k, by rw [hk]; ring, ?_, ?_⟩
  · -- `s − p = k*b` from `r*b = a*(s−p)` and `r = a*k`
    have : f.a * (k * f.b) = f.a * (s - p) := by rw [← hr1, hk]; ring
    exact (mul_left_cancel₀ ha this).symm
  · -- `q = −(k*c)` from `r*c = a*(−q)` and `r = a*k`
    have : f.a * (k * f.c) = f.a * (-q) := by rw [← hr2, hk]; ring
    have := mul_left_cancel₀ ha this
    linarith [this]

/-- **Determinant is the norm form.** For a fixing matrix as classified above,
`det = p s − q r = p² + b p k + a c k²` — the value of the norm form of the order at
`(p, k)`, with `disc = b² − 4ac`. -/
theorem det_of_fixes {f : BQF} (hf : IsPrimitive f) (hpd : IsPosDef f)
    {p q r s : ℤ} {τ : ℍ} (hroot : IsRoot f τ) (hfix : Fixes p q r s τ) :
    ∃ k : ℤ, p * s - q * r = p ^ 2 + f.b * p * k + f.a * f.c * k ^ 2 := by
  obtain ⟨k, hr, hsp, hq⟩ := fixes_classification hf hpd hroot hfix
  refine ⟨k, ?_⟩
  have hs : s = p + k * f.b := by linarith [hsp]
  rw [hr, hq, hs]; ring

end Chudnovsky.QF
