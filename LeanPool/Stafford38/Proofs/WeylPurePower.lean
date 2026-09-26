/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Rat.Star
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.Tactic
public import Mathlib.Tactic.NoncommRing


/-!
# Pure-power Weyl certificates

This file formalizes the all-degree part of the one-variable Weyl--Bézout
calculation. It works in an arbitrary ring containing a Weyl pair
`d * x - x * d = 1`; the only coefficient input is the ordinary polynomial
Bézout relation between the two disjoint Euler products.

The remaining universal monic problem is not hidden here: it is the passage
from a pure power to a general monic polynomial.
-/

@[expose] public section

namespace Stafford

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The Euler element associated with the coordinate and momentum. -/
def eulerElement (x d : A) : A := x * d

private def falling (x d : A) : ℕ → A
  | 0 => 1
  | n + 1 => falling x d n * (eulerElement x d - (n : A))

private def fallingShift (x d : A) : ℕ → A
  | 0 => 1
  | n + 1 => fallingShift x d n * (eulerElement x d - ((n + 1 : ℕ) : A))

private def rising (x d : A) : ℕ → A
  | 0 => 1
  | n + 1 => rising x d n * (eulerElement x d + ((n + 1 : ℕ) : A))

private def risingShift (x d : A) : ℕ → A
  | 0 => 1
  | n + 1 => risingShift x d n * (eulerElement x d + ((n + 2 : ℕ) : A))

/-- The monic polynomial with roots `0, ..., n - 1`. -/
def fallingPolynomial : ℕ → Polynomial ℚ
  | 0 => 1
  | n + 1 => fallingPolynomial n * (Polynomial.X - Polynomial.C (n : ℚ))

/-- The monic polynomial with roots `-1, ..., -n`. -/
def risingPolynomial : ℕ → Polynomial ℚ
  | 0 => 1
  | n + 1 => risingPolynomial n * (Polynomial.X + Polynomial.C ((n + 1 : ℕ) : ℚ))

private lemma fallingPoly_eq_prod (n : ℕ) :
    fallingPolynomial n = ∏ i ∈ Finset.range n,
      (Polynomial.X - Polynomial.C (i : ℚ)) := by
  induction n with
  | zero => simp [fallingPolynomial]
  | succ n ih =>
      rw [fallingPolynomial, ih, Finset.prod_range_succ]

private lemma risingPoly_eq_prod (n : ℕ) :
    risingPolynomial n = ∏ i ∈ Finset.range n,
      (Polynomial.X + Polynomial.C ((i + 1 : ℕ) : ℚ)) := by
  induction n with
  | zero => simp [risingPolynomial]
  | succ n ih =>
      rw [risingPolynomial, ih, Finset.prod_range_succ]

private lemma falling_factor_coprime_rising_factor (i j : ℕ) :
    IsCoprime (Polynomial.X - Polynomial.C (i : ℚ))
      (Polynomial.X + Polynomial.C ((j + 1 : ℕ) : ℚ)) := by
  have hunit : IsUnit ((i : ℚ) - -((j + 1 : ℕ) : ℚ)) := by
    apply isUnit_iff_ne_zero.mpr
    have hi : 0 ≤ (i : ℚ) := by positivity
    have hj : 0 < ((j + 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.succ_pos j
    have hpos : 0 < (i : ℚ) - -((j + 1 : ℕ) : ℚ) := by linarith
    exact ne_of_gt hpos
  convert Polynomial.isCoprime_X_sub_C_of_isUnit_sub hunit using 1
  · simp [sub_eq_add_neg]

private lemma fallingPoly_isCoprime_risingPoly (n : ℕ) :
    IsCoprime (fallingPolynomial n) (risingPolynomial n) := by
  rw [fallingPoly_eq_prod, risingPoly_eq_prod]
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.prod_right
  intro j hj
  exact falling_factor_coprime_rising_factor i j

private lemma x_mul_theta_sub_nat
    (x d : A) (h : d * x = x * d + 1) (n : ℕ) :
    x * (eulerElement x d - (n : A)) =
      (eulerElement x d - ((n + 1 : ℕ) : A)) * x := by
  have hxt : x * eulerElement x d = (eulerElement x d - 1) * x := by
    dsimp [eulerElement]
    have h' : x * d = d * x - 1 := by
      simp [h]
    calc
      x * (x * d) = x * (d * x - 1) := by rw [h']
      _ = x * d * x - x := by noncomm_ring
      _ = (x * d - 1) * x := by noncomm_ring
  have hn : (n : A) * x = x * (n : A) := by
    simpa using (Algebra.commutes (n : ℚ) x)
  rw [mul_sub, hxt]
  push_cast
  rw [← hn]
  noncomm_ring

private lemma d_mul_theta_add_nat
    (x d : A) (h : d * x = x * d + 1) (n : ℕ) :
    d * (eulerElement x d + ((n + 1 : ℕ) : A)) =
      (eulerElement x d + ((n + 2 : ℕ) : A)) * d := by
  have hdt : d * eulerElement x d = (eulerElement x d + 1) * d := by
    dsimp [eulerElement]
    calc
      d * (x * d) = (d * x) * d := by noncomm_ring
      _ = (x * d + 1) * d := by rw [h]
      _ = (eulerElement x d + 1) * d := rfl
  have hn : (n : A) * d = d * (n : A) := by
    simpa using (Algebra.commutes (n : ℚ) d)
  rw [mul_add, hdt]
  push_cast
  simp only [mul_add]
  rw [← hn]
  noncomm_ring

private lemma x_mul_falling
    (x d : A) (h : d * x = x * d + 1) : ∀ n : ℕ,
    x * falling x d n = fallingShift x d n * x
  | 0 => by simp [falling, fallingShift]
  | n + 1 => by
      change x * (falling x d n * (eulerElement x d - (n : A))) =
        (fallingShift x d n * (eulerElement x d - ((n + 1 : ℕ) : A))) * x
      calc
        x * (falling x d n * (eulerElement x d - (n : A))) =
            (x * falling x d n) * (eulerElement x d - (n : A)) := by
              noncomm_ring
        _ = (fallingShift x d n * x) *
            (eulerElement x d - (n : A)) := by rw [x_mul_falling x d h n]
        _ = fallingShift x d n *
            ((eulerElement x d - ((n + 1 : ℕ) : A)) * x) := by
              calc
                fallingShift x d n * x * (eulerElement x d - (n : A)) =
                    fallingShift x d n *
                      (x * (eulerElement x d - (n : A))) := by rw [mul_assoc]
                _ = fallingShift x d n *
                    ((eulerElement x d - ((n + 1 : ℕ) : A)) * x) := by
                      rw [x_mul_theta_sub_nat x d h n]
        _ = (fallingShift x d n *
            (eulerElement x d - ((n + 1 : ℕ) : A))) * x := by
              noncomm_ring

private lemma d_mul_rising
    (x d : A) (h : d * x = x * d + 1) : ∀ n : ℕ,
    d * rising x d n = risingShift x d n * d
  | 0 => by simp [rising, risingShift]
  | n + 1 => by
      change d * (rising x d n * (eulerElement x d + ((n + 1 : ℕ) : A))) =
        (risingShift x d n * (eulerElement x d + ((n + 2 : ℕ) : A))) * d
      calc
        d * (rising x d n * (eulerElement x d + ((n + 1 : ℕ) : A))) =
            (d * rising x d n) *
              (eulerElement x d + ((n + 1 : ℕ) : A)) := by noncomm_ring
        _ = (risingShift x d n * d) *
            (eulerElement x d + ((n + 1 : ℕ) : A)) := by rw [d_mul_rising x d h n]
        _ = risingShift x d n *
            ((eulerElement x d + ((n + 2 : ℕ) : A)) * d) := by
              calc
                risingShift x d n * d *
                      (eulerElement x d + ((n + 1 : ℕ) : A)) =
                    risingShift x d n *
                      (d * (eulerElement x d + ((n + 1 : ℕ) : A))) := by
                        rw [mul_assoc]
                _ = risingShift x d n *
                    ((eulerElement x d + ((n + 2 : ℕ) : A)) * d) := by
                      rw [d_mul_theta_add_nat x d h n]
        _ = (risingShift x d n *
            (eulerElement x d + ((n + 2 : ℕ) : A))) * d := by
              noncomm_ring

private lemma fallingShift_mul_theta
    (x d : A) : ∀ n : ℕ,
    fallingShift x d n * eulerElement x d = falling x d (n + 1)
  | 0 => by simp [falling, fallingShift]
  | n + 1 => by
      change (fallingShift x d n *
          (eulerElement x d - ((n + 1 : ℕ) : A))) * eulerElement x d =
        falling x d (n + 2)
      calc
        (fallingShift x d n *
            (eulerElement x d - ((n + 1 : ℕ) : A))) * eulerElement x d =
            (fallingShift x d n * eulerElement x d) *
              (eulerElement x d - ((n + 1 : ℕ) : A)) := by
                have hn : ((n + 1 : ℕ) : A) * eulerElement x d =
                    eulerElement x d * ((n + 1 : ℕ) : A) := by
                  simpa using (Algebra.commutes ((n + 1 : ℕ) : ℚ) (eulerElement x d))
                calc
                  (fallingShift x d n *
                      (eulerElement x d - ((n + 1 : ℕ) : A))) * eulerElement x d =
                      fallingShift x d n *
                        ((eulerElement x d - ((n + 1 : ℕ) : A)) * eulerElement x d) := by
                          rw [mul_assoc]
                  _ = fallingShift x d n *
                        (eulerElement x d *
                          (eulerElement x d - ((n + 1 : ℕ) : A))) := by
                          congr 1
                          rw [mul_sub, sub_mul, hn]
                  _ = (fallingShift x d n * eulerElement x d) *
                        (eulerElement x d - ((n + 1 : ℕ) : A)) := by
                          rw [mul_assoc]
        _ = falling x d (n + 1) *
              (eulerElement x d - ((n + 1 : ℕ) : A)) := by
                rw [fallingShift_mul_theta x d n]
        _ = falling x d (n + 2) := by rfl

private lemma risingShift_mul_theta_add_one
    (x d : A) : ∀ n : ℕ,
    risingShift x d n * (eulerElement x d + 1) = rising x d (n + 1)
  | 0 => by simp [rising, risingShift]
  | n + 1 => by
      change (risingShift x d n *
          (eulerElement x d + ((n + 2 : ℕ) : A))) *
            (eulerElement x d + 1) = rising x d (n + 2)
      calc
        (risingShift x d n *
            (eulerElement x d + ((n + 2 : ℕ) : A))) *
              (eulerElement x d + 1) =
            (risingShift x d n * (eulerElement x d + 1)) *
              (eulerElement x d + ((n + 2 : ℕ) : A)) := by
                have hn : ((n + 2 : ℕ) : A) * eulerElement x d =
                    eulerElement x d * ((n + 2 : ℕ) : A) := by
                  simpa only [map_natCast] using
                    (Algebra.commutes ((n + 2 : ℕ) : ℚ) (eulerElement x d))
                calc
                  (risingShift x d n *
                      (eulerElement x d + ((n + 2 : ℕ) : A))) *
                        (eulerElement x d + 1) =
                      risingShift x d n *
                        ((eulerElement x d + ((n + 2 : ℕ) : A)) *
                          (eulerElement x d + 1)) := by
                            rw [mul_assoc]
                  _ = risingShift x d n *
                        ((eulerElement x d + 1) *
                          (eulerElement x d + ((n + 2 : ℕ) : A))) := by
                            congr 1
                            simp only [add_mul, mul_add]
                            rw [hn]
                            noncomm_ring
                  _ = (risingShift x d n * (eulerElement x d + 1)) *
                        (eulerElement x d + ((n + 2 : ℕ) : A)) := by
                            rw [mul_assoc]
        _ = rising x d (n + 1) *
              (eulerElement x d + ((n + 2 : ℕ) : A)) := by
                rw [risingShift_mul_theta_add_one x d n]
        _ = rising x d (n + 2) := by rfl

private lemma x_pow_mul_d_pow
    (x d : A) (h : d * x = x * d + 1) : ∀ n : ℕ,
    x ^ n * d ^ n = falling x d n
  | 0 => by simp [falling]
  | n + 1 => by
      calc
        x ^ (n + 1) * d ^ (n + 1) = x * (x ^ n * d ^ n) * d := by
          rw [pow_succ', pow_succ]
          simp only [mul_assoc]
        _ = x * falling x d n * d := by rw [x_pow_mul_d_pow x d h n]
        _ = fallingShift x d n * (x * d) := by
          rw [x_mul_falling x d h n]
          noncomm_ring
        _ = falling x d (n + 1) := by
          simpa [eulerElement] using fallingShift_mul_theta x d n

private lemma d_pow_mul_x_pow
    (x d : A) (h : d * x = x * d + 1) : ∀ n : ℕ,
    d ^ n * x ^ n = rising x d n
  | 0 => by simp [rising]
  | n + 1 => by
      calc
        d ^ (n + 1) * x ^ (n + 1) = d * (d ^ n * x ^ n) * x := by
          rw [pow_succ', pow_succ]
          simp only [mul_assoc]
        _ = d * rising x d n * x := by rw [d_pow_mul_x_pow x d h n]
        _ = risingShift x d n * (d * x) := by
          rw [d_mul_rising x d h n]
          noncomm_ring
        _ = rising x d (n + 1) := by
          rw [h]
          simpa [eulerElement] using risingShift_mul_theta_add_one x d n

private lemma eval_fallingPoly
    (x d : A)
    (ev : Polynomial ℚ →+* A)
    (hev : ev Polynomial.X = eulerElement x d)
    (hC : ∀ q : ℚ, ev (Polynomial.C q) = (algebraMap ℚ A) q) :
    ev (fallingPolynomial n) = falling x d n := by
  induction n with
  | zero => simp [fallingPolynomial, falling]
  | succ n ih =>
      rw [fallingPolynomial, map_mul, map_sub, hev, hC]
      push_cast
      rw [ih]
      simp [falling]

private lemma eval_risingPoly
    (x d : A)
    (ev : Polynomial ℚ →+* A)
    (hev : ev Polynomial.X = eulerElement x d)
    (hC : ∀ q : ℚ, ev (Polynomial.C q) = (algebraMap ℚ A) q) :
    ev (risingPolynomial n) = rising x d n := by
  induction n with
  | zero => simp [risingPolynomial, rising]
  | succ n ih =>
      rw [risingPolynomial, map_mul, map_add, hev, hC]
      push_cast
      rw [ih]
      simp [rising]

/-- Evaluation of a rational polynomial at the Euler element `x*d`. -/
def eulerPolynomialEval (x d : A) : Polynomial ℚ →+* A :=
  Polynomial.eval₂RingHom' (algebraMap ℚ A) (eulerElement x d)
    (fun q => Algebra.commutes q (eulerElement x d))

@[simp]
theorem eulerPolynomialEval_X (x d : A) :
    eulerPolynomialEval x d Polynomial.X = x * d := by
  change Polynomial.eval₂ (algebraMap ℚ A) (eulerElement x d) Polynomial.X = x * d
  rw [Polynomial.eval₂_X (algebraMap ℚ A) (eulerElement x d)]
  rfl

@[simp]
theorem eulerPolynomialEval_C (x d : A) (q : ℚ) :
    eulerPolynomialEval x d (Polynomial.C q) = algebraMap ℚ A q := by
  change Polynomial.eval₂ (algebraMap ℚ A) (eulerElement x d) (Polynomial.C q) =
    algebraMap ℚ A q
  exact Polynomial.eval₂_C (algebraMap ℚ A) (eulerElement x d)

/-- Equal powers `x^n*d^n` are a rational polynomial in the Euler element. -/
theorem exists_eulerPolynomial_x_pow_mul_d_pow
    (x d : A) (h : d * x = x * d + 1) (n : ℕ) :
    ∃ f : Polynomial ℚ,
      eulerPolynomialEval x d f = x ^ n * d ^ n := by
  refine ⟨fallingPolynomial n, ?_⟩
  rw [eval_fallingPoly x d (eulerPolynomialEval x d)
    (by rw [eulerPolynomialEval_X]; rfl) (by intro q; simp)]
  exact (x_pow_mul_d_pow x d h n).symm

/-- Equal powers `d^n*x^n` are also a rational polynomial in `x*d`. -/
theorem exists_eulerPolynomial_d_pow_mul_x_pow
    (x d : A) (h : d * x = x * d + 1) (n : ℕ) :
    ∃ f : Polynomial ℚ,
      eulerPolynomialEval x d f = d ^ n * x ^ n := by
  refine ⟨risingPolynomial n, ?_⟩
  rw [eval_risingPoly x d (eulerPolynomialEval x d)
    (by rw [eulerPolynomialEval_X]; rfl) (by intro q; simp)]
  exact (d_pow_mul_x_pow x d h n).symm

/-- The pure-power certificate, assuming the ordinary Euler products are
coprime in the coefficient polynomial ring. -/
theorem pure_power_weyl_certificate
    (x d : A) (h : d * x = x * d + 1) (n : ℕ)
    (a b : Polynomial ℚ)
    (hab : a * fallingPolynomial n + b * risingPolynomial n = 1) :
    ∃ p q : A, 1 = p * (x ^ n) + q * (x ^ n * d ^ n) := by
  let θ : A := eulerElement x d
  let ev : Polynomial ℚ →+* A :=
    Polynomial.eval₂RingHom' (algebraMap ℚ A) θ (fun q => Algebra.commutes q θ)
  have hfall : ev (fallingPolynomial n) = x ^ n * d ^ n := by
    rw [eval_fallingPoly x d ev
      (by change Polynomial.eval₂ (algebraMap ℚ A) θ Polynomial.X = _
          exact Polynomial.eval₂_X (algebraMap ℚ A) θ)
      (by intro q
          change Polynomial.eval₂ (algebraMap ℚ A) θ (Polynomial.C q) = _
          exact Polynomial.eval₂_C (algebraMap ℚ A) θ)]
    exact (x_pow_mul_d_pow x d h n).symm
  have hrise : ev (risingPolynomial n) = d ^ n * x ^ n := by
    rw [eval_risingPoly x d ev
      (by change Polynomial.eval₂ (algebraMap ℚ A) θ Polynomial.X = _
          exact Polynomial.eval₂_X (algebraMap ℚ A) θ)
      (by intro q
          change Polynomial.eval₂ (algebraMap ℚ A) θ (Polynomial.C q) = _
          exact Polynomial.eval₂_C (algebraMap ℚ A) θ)]
    exact (d_pow_mul_x_pow x d h n).symm
  have hev := congrArg ev hab
  rw [map_add, map_mul, map_mul, hfall, hrise, map_one] at hev
  refine ⟨ev b * d ^ n, ev a, ?_⟩
  rw [mul_assoc]
  rw [add_comm] at hev
  exact hev.symm

/- The Euler products are coprime over `ℚ`, so the coefficient hypothesis in
the transfer theorem is available in every degree. -/
theorem pure_power_weyl_certificate_exists
    (x d : A) (h : d * x = x * d + 1) (n : ℕ) :
    ∃ p q : A, 1 = p * (x ^ n) + q * (x ^ n * d ^ n) := by
  rcases fallingPoly_isCoprime_risingPoly n with ⟨a, b, hab⟩
  exact pure_power_weyl_certificate x d h n a b hab

/-- The two Euler products admit a Bezout identity with right cofactors.
This is the orientation used by the canonical right quotient. -/
theorem euler_products_right_bezout_exists
    (x d : A) (h : d * x = x * d + 1) (n : ℕ) :
    ∃ u v : A,
      (d ^ n * x ^ n) * u + (x ^ n * d ^ n) * v = 1 := by
  rcases fallingPoly_isCoprime_risingPoly n with ⟨a, b, hab⟩
  let θ : A := eulerElement x d
  let ev : Polynomial ℚ →+* A :=
    Polynomial.eval₂RingHom' (algebraMap ℚ A) θ
      (fun q => Algebra.commutes q θ)
  have hfall : ev (fallingPolynomial n) = x ^ n * d ^ n := by
    rw [eval_fallingPoly x d ev
      (by change Polynomial.eval₂ (algebraMap ℚ A) θ Polynomial.X = _
          exact Polynomial.eval₂_X (algebraMap ℚ A) θ)
      (by intro q
          change Polynomial.eval₂ (algebraMap ℚ A) θ (Polynomial.C q) = _
          exact Polynomial.eval₂_C (algebraMap ℚ A) θ)]
    exact (x_pow_mul_d_pow x d h n).symm
  have hrise : ev (risingPolynomial n) = d ^ n * x ^ n := by
    rw [eval_risingPoly x d ev
      (by change Polynomial.eval₂ (algebraMap ℚ A) θ Polynomial.X = _
          exact Polynomial.eval₂_X (algebraMap ℚ A) θ)
      (by intro q
          change Polynomial.eval₂ (algebraMap ℚ A) θ (Polynomial.C q) = _
          exact Polynomial.eval₂_C (algebraMap ℚ A) θ)]
    exact (d_pow_mul_x_pow x d h n).symm
  have hpoly : risingPolynomial n * b + fallingPolynomial n * a = 1 := by
    rw [mul_comm (risingPolynomial n) b, mul_comm (fallingPolynomial n) a, add_comm]
    exact hab
  have hev := congrArg ev hpoly
  rw [map_add, map_mul, map_mul, hrise, hfall, map_one] at hev
  exact ⟨ev b, ev a, hev⟩


/-- The right Bezout cofactors may be retained as rational polynomials in the
Euler element. -/
theorem euler_products_polynomial_right_bezout_exists
    (x d : A) (h : d * x = x * d + 1) (n : ℕ) :
    ∃ u v : Polynomial ℚ,
      (d ^ n * x ^ n) * eulerPolynomialEval x d u +
        (x ^ n * d ^ n) * eulerPolynomialEval x d v = 1 := by
  rcases fallingPoly_isCoprime_risingPoly n with ⟨a, b, hab⟩
  have hfall : eulerPolynomialEval x d (fallingPolynomial n) =
      x ^ n * d ^ n := by
    rw [eval_fallingPoly x d (eulerPolynomialEval x d)
      (by rw [eulerPolynomialEval_X]; rfl) (by intro q; simp)]
    exact (x_pow_mul_d_pow x d h n).symm
  have hrise : eulerPolynomialEval x d (risingPolynomial n) =
      d ^ n * x ^ n := by
    rw [eval_risingPoly x d (eulerPolynomialEval x d)
      (by rw [eulerPolynomialEval_X]; rfl) (by intro q; simp)]
    exact (d_pow_mul_x_pow x d h n).symm
  have hpoly : risingPolynomial n * b + fallingPolynomial n * a = 1 := by
    rw [mul_comm (risingPolynomial n) b, mul_comm (fallingPolynomial n) a, add_comm]
    exact hab
  have hev := congrArg (eulerPolynomialEval x d) hpoly
  rw [map_add, map_mul, map_mul, hrise, hfall, map_one] at hev
  exact ⟨b, a, hev⟩


theorem pure_power_translate_weyl_certificate_exists
    (x d c : A) (h : d * x = x * d + 1)
    (hcd : Commute c d) (n : ℕ) :
    ∃ p q : A, 1 = p * ((x - c) ^ n) + q * ((x - c) ^ n * d ^ n) := by
  have hshift : d * (x - c) = (x - c) * d + 1 := by
    calc
      d * (x - c) = d * x - d * c := by rw [mul_sub]
      _ = x * d + 1 - c * d := by rw [h, ← hcd.eq]
      _ = (x - c) * d + 1 := by rw [sub_mul]; noncomm_ring
  exact pure_power_weyl_certificate_exists (x - c) d hshift n

/-- A nilpotent central constant can be added to a pure power without losing
the Weyl--Bézout certificate.  This is the formal constant-coefficient
instance of the nilpotent thickening step; the general nilpotent coefficient
ideal is deliberately not hidden in this statement. -/
theorem nilpotent_constant_weyl_certificate_exists
    (x d e : A) (h : d * x = x * d + 1)
    (he : IsNilpotent e) (hcentral : ∀ a : A, Commute e a) (n : ℕ) :
    ∃ p q : A,
      1 = p * (x ^ n - e) + q * ((x ^ n - e) * d ^ n) := by
  rcases fallingPoly_isCoprime_risingPoly n with ⟨a, b, hab⟩
  have hpow := pure_power_weyl_certificate x d h n a b hab
  rcases hpow with ⟨p0, q0, hpow⟩
  let H : A := x ^ n - e
  let r : A := p0 * e + q0 * (e * d ^ n)
  have hrewrite :
      1 - r = p0 * H + q0 * (H * d ^ n) := by
    dsimp [r, H]
    have hx : x ^ n = (x ^ n - e) + e := by noncomm_ring
    rw [hpow, hx]
    noncomm_ring
  have hcomm : Commute e (p0 + q0 * d ^ n) := hcentral _
  have hr : r = e * (p0 + q0 * d ^ n) := by
    dsimp [r]
    calc
      p0 * e + q0 * (e * d ^ n) = e * p0 + (q0 * e) * d ^ n := by
        rw [← hcentral p0 |>.eq]
        noncomm_ring
      _ = e * p0 + (e * q0) * d ^ n := by rw [hcentral q0 |>.eq]
      _ = e * (p0 + q0 * d ^ n) := by noncomm_ring
  have hrnil : IsNilpotent r := by
    rw [hr]
    exact hcomm.isNilpotent_mul_right he
  rcases hrnil with ⟨N, hN⟩
  let g : A := ∑ i ∈ Finset.range N, r ^ i
  have hgeom : g * (1 - r) = 1 - r ^ N := by
    dsimp [g]
    rw [show (1 : A) - r = -(r - 1) by noncomm_ring, mul_neg]
    rw [geom_sum_mul]
    noncomm_ring
  have hone : (1 : A) = g * (1 - r) := by
    rw [hgeom, hN, sub_zero]
  have hfinal :
      1 = (g * p0) * H + (g * q0) * (H * d ^ n) := by
    calc
      1 = g * (1 - r) := hone
      _ = g * (p0 * H + q0 * (H * d ^ n)) := by rw [hrewrite]
      _ = (g * p0) * H + (g * q0) * (H * d ^ n) := by noncomm_ring
  refine ⟨g * p0, g * q0, ?_⟩
  simpa [H] using hfinal

end
end Stafford
