/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import LeanPool.LiCriterion.Hadamard.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
Helper results used by the Hadamard/Li development.

This file intentionally contains no global axioms: the deep factorization theorem itself is
handled elsewhere; here we only record consequences and clean lemmas that downstream files use.
-/

open Filter Topology Set Metric

namespace Hadamard

/-- For genus 0, the Weierstrass elementary factor is just (1 - w). -/
lemma weierstrass_E_zero' (w : ℂ) : weierstrass_E 0 w = 1 - w := weierstrass_E_zero w

/-! ### Exponentials of linear functions

`Basic.lean` proves that a zero‑free entire function of finite order is an exponential of a
polynomial; here we package the order‑≤1 case as an exponential of a linear function.
-/

lemma polynomial_eval_eq_linear_of_natDegree_le_one (p : Polynomial ℂ) (hp : p.natDegree ≤ 1) :
    ∃ a b : ℂ, ∀ z : ℂ, p.eval z = a * z + b := by
  obtain ⟨a, b, rfl⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one (p := p) hp
  refine ⟨a, b, ?_⟩
  intro z
  simp

/-- **Exponential constraint from symmetry**

If f satisfies f(z) = f(c - z) for some c, and f = exp(az + b) * P(z) where P
is a symmetric product (P(z) = P(c - z)), then exp(a * c) = 1.

This means a * c ∈ 2πiℤ. For real a and real c (as in the ξ function with c = 1),
this forces a * c = 0 since the only real element of 2πiℤ is 0.

For ξ, we have ξ(s) = ξ(1-s) with c = 1. If a is real, then a = 0.

Reference: This is a consequence of comparing f(z) = f(c-z) with the factored form.
-/
theorem exp_constraint_from_symmetry (f P : ℂ → ℂ) (c a b : ℂ)
    (h_symm : ∀ z, f z = f (c - z))
    (h_P_symm : ∀ z, P z = P (c - z))
    (h_factored : ∀ z, f z = Complex.exp (a * z + b) * P z)
    (h_P_nonzero_0 : P 0 ≠ 0) :
    Complex.exp (a * c) = 1 := by
  -- From f(z) = f(c-z) and the factored forms:
  --   exp(az + b) * P(z) = exp(a(c-z) + b) * P(c-z)
  -- Using P(z) = P(c-z):
  --   exp(az + b) = exp(a(c-z) + b)
  --   exp(az) = exp(ac - az)
  --   exp(2az - ac) = 1  for all z
  -- This requires 2az - ac = 2πik for all z, which forces a = 0 (coefficient of z must be 0)
  -- Hence a * c = 0.
  -- The key insight: from h_symm and h_factored with h_P_symm, for any z where P(z) ≠ 0:
  --   exp(az + b) * P(z) = exp(a(c-z) + b) * P(c-z) = exp(a(c-z) + b) * P(z)
  -- So exp(az) = exp(a(c-z)), i.e., exp(2az - ac) = 1
  -- Taking z = 0 and z = 1 (if both have P nonzero):
  --   exp(-ac) = 1  and  exp(2a - ac) = 1
  -- From these: exp(2a) = 1
  -- Combined with exp(-ac) = 1: exp(ac) = 1, exp(2a) = 1
  -- If a ≠ 0, then ac = 2πik and 2a = 2πim for some integers k, m
  -- So c = πik/a = πik / (πim) = k/m (rational multiple)
  -- But this doesn't force ac = 0 directly.
  --
  -- Better approach: use that h_symm holds for ALL z, including where P might be zero.
  -- Actually, if a ≠ 0 and c ≠ 0, pick z₁, z₂ with z₁ ≠ z₂ and P(z₁) ≠ 0, P(z₂) ≠ 0.
  -- Then exp(2a*z₁ - ac) = 1 and exp(2a*z₂ - ac) = 1
  -- So exp(2a*(z₁ - z₂)) = 1
  -- For this to hold for all pairs z₁, z₂ with P nonzero, we need 2a = 0, i.e., a = 0.
  -- Simplified proof: show the exponential identity forces a = 0, hence a*c = 0
  -- For any z, from the symmetry and factorization:
  have h_exp_eq : ∀ z, P z ≠ 0 → Complex.exp (a * z + b) = Complex.exp (a * (c - z) + b) := by
    intro z hPz
    have h1 := h_factored z
    have h2 := h_factored (c - z)
    have h3 := h_symm z
    have h4 := h_P_symm z
    have h2' : f (c - z) = Complex.exp (a * (c - z) + b) * P z := by rw [h2, h4]
    rw [h1, h2'] at h3
    exact mul_right_cancel₀ hPz h3
  -- At z = 0: exp(b) = exp(ac + b)
  have h_at_0 := h_exp_eq 0 h_P_nonzero_0
  simp only [mul_zero, zero_add, sub_zero] at h_at_0
  -- h_at_0 : exp(b) = exp(a*c + b)
  -- From h_at_0: exp(b) = exp(ac + b) = exp(ac) * exp(b)
  -- Dividing by exp(b) ≠ 0: 1 = exp(ac)
  have h_exp_ac : Complex.exp (a * c) = 1 := by
    have h := h_at_0
    -- h : exp(b) = exp(a * c + b)
    have h' : Complex.exp (a * c + b) = Complex.exp (a * c) * Complex.exp b := Complex.exp_add _ _
    rw [h'] at h
    have hb_ne : Complex.exp b ≠ 0 := Complex.exp_ne_zero b
    -- h : exp(b) = exp(a * c) * exp(b)
    -- Want: exp(a * c) = 1
    -- This is equivalent to: exp(b) = exp(a*c) * exp(b) implies exp(a*c) = 1
    have h_cancel :
        Complex.exp (a * c) * Complex.exp b = Complex.exp b → Complex.exp (a * c) = 1 := by
      intro heq
      have hmul : Complex.exp (a * c) * Complex.exp b = 1 * Complex.exp b := by
        simpa using heq
      exact mul_right_cancel₀ hb_ne hmul
    exact h_cancel h.symm
  -- This is exactly what we wanted to prove!
  exact h_exp_ac

/-- **Linear coefficient vanishes for real symmetry**

Corollary: If additionally a and c are real, then exp(ac) = 1 implies ac = 0.
The only real number w with exp(w) = 1 is w = 0.
-/
theorem linear_coeff_zero_of_real_symmetry (f P : ℂ → ℂ) (c a : ℝ) (b : ℂ)
    (h_symm : ∀ z, f z = f ((c : ℂ) - z))
    (h_P_symm : ∀ z, P z = P ((c : ℂ) - z))
    (h_factored : ∀ z, f z = Complex.exp ((a : ℂ) * z + b) * P z)
    (h_P_nonzero_0 : P 0 ≠ 0) :
    a * c = 0 := by
  have h_exp :=
    exp_constraint_from_symmetry f P (c : ℂ) (a : ℂ) b
      h_symm h_P_symm h_factored h_P_nonzero_0
  -- h_exp : exp((a : ℂ) * (c : ℂ)) = 1
  -- Since a and c are real, (a : ℂ) * (c : ℂ) = (a * c : ℂ)
  simp only [← Complex.ofReal_mul] at h_exp
  -- h_exp : exp((a * c : ℂ)) = 1
  -- For real x, Complex.exp(x : ℂ) = (Real.exp x : ℂ)
  -- We have h_exp : Complex.exp ↑(a * c) = 1
  -- Use Complex.exp_ofReal_re or explicit lemma
  have h_eq : Complex.exp (↑(a * c) : ℂ) = (Real.exp (a * c) : ℂ) := by
    rw [← Complex.ofReal_exp]
  rw [h_eq] at h_exp
  -- h_exp : (Real.exp (a * c) : ℂ) = 1
  -- Convert to real equation: Real.exp(a * c) = 1
  have h_real_exp : Real.exp (a * c) = 1 := Complex.ofReal_eq_one.mp h_exp
  -- Real.exp x = 1 iff x = 0
  exact (Real.exp_eq_one_iff (a * c)).mp h_real_exp

end Hadamard
