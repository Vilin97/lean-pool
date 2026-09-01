/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic.LinearCombination

/-!
# Even polynomials as polynomials in `X² + c`

An even polynomial (one fixed by `X ↦ -X`) over a domain of characteristic `≠ 2` is a polynomial
in `X² + c`.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

open Polynomial

/-- `X² + c` is fixed by `X ↦ -X`. -/
lemma Polynomial.X_sq_add_C_comp_neg_X {R : Type*} [CommRing R] (c : R) :
    (X ^ 2 + C c).comp (-X) = X ^ 2 + C c := by
  simp only [add_comp, pow_comp, X_comp, C_comp]
  ring

/-- `X ↦ -X` preserves being associated. -/
lemma Associated.comp_neg_X {R : Type*} [CommRing R] {p q : R[X]} (h : Associated p q) :
    Associated (p.comp (-X)) (q.comp (-X)) := by
  have hσ (r : R[X]) : algEquivAevalNegX r = r.comp (-X) := by
    rw [algEquivAevalNegX_apply, ← comp_eq_aeval]
  rw [← hσ p, ← hσ q]
  exact h.map (algEquivAevalNegX (R := R)).toMulEquiv.toMonoidHom

/-- Normalizing before reflecting does not change the normalized reflection. -/
lemma Polynomial.normalize_normalize_comp_neg_X {R : Type*} [CommRing R] [IsDomain R]
    [NormalizationMonoid R[X]] (p : R[X]) :
    normalize ((normalize p).comp (-X)) = normalize (p.comp (-X)) := by
  have h := (normalize_associated p).comp_neg_X
  exact normalize_eq_normalize h.dvd h.symm.dvd

/-- Over a domain, a polynomial whose reflection is merely *associated* to it is fixed by
`X ↦ -X` up to a sign. -/
theorem Polynomial.comp_neg_X_eq_or_eq_neg_of_associated {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} (hp : p ≠ 0) (h : Associated (p.comp (-X)) p) :
    p.comp (-X) = p ∨ p.comp (-X) = -p := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨c, -, hcu⟩ := isUnit_iff.mp u.isUnit
  rw [← hcu] at hu
  have hcsq : c * c = 1 := by
    have h2 : p * C c = p.comp (-X) := by
      simpa only [mul_comp, comp_neg_X_comp_neg_X, C_comp] using
        congrArg (fun q ↦ q.comp (-X)) hu
    have h4 : p * C c * C c = p := by rwa [h2]
    rw [mul_assoc, ← C_mul] at h4
    have hc2 : C (c * c) = (1 : R[X]) := mul_left_cancel₀ hp (by rw [h4, mul_one])
    exact C_injective (by rw [hc2, C_1])
  rcases mul_self_eq_one_iff.mp hcsq with rfl | rfl
  · exact .inl (by rwa [C_1, mul_one] at hu)
  · exact .inr (by rw [C_neg, C_1, mul_neg, mul_one] at hu; linear_combination -hu)

/-- A polynomial in `X²` is fixed by `X ↦ -X`. -/
@[simp] theorem Polynomial.expand_two_comp_neg_X {R : Type*} [CommRing R] (h : R[X]) :
    (expand R 2 h).comp (-X) = expand R 2 h := by
  rw [expand_eq_comp_X_pow, comp_assoc]
  congr 1
  simp only [pow_comp, X_comp]
  ring

/-- Over a domain of characteristic `≠ 2`, a polynomial fixed by `X ↦ -X` is a polynomial
in `X²`. -/
theorem Polynomial.eq_expand_two_contract_of_comp_neg_X {R : Type*} [CommRing R]
    [NoZeroDivisors R] [NeZero (2 : R)] {b : R[X]} (hb : b.comp (-X) = b) :
    b = expand R 2 (contract 2 b) := by
  have hoddzero n (hn : ¬ 2 ∣ n) : b.coeff n = 0 := by
    have hcoeff : (b.comp (-X)).coeff n = b.coeff n * (-1) ^ n := by
      simpa using comp_C_mul_X_coeff (p := b) (r := -1) (n := n)
    rw [hb, Odd.neg_one_pow (Nat.odd_iff.mpr (show n % 2 = 1 by lia))] at hcoeff
    exact (mul_eq_zero.mp (by linear_combination hcoeff : (2 : R) * b.coeff n = 0)).resolve_left
      two_ne_zero
  ext n
  rw [coeff_expand (by norm_num)]
  by_cases hdvd : 2 ∣ n
  · rw [ite_eq_left hdvd, coeff_contract (by norm_num)]; congr 1; lia
  · rw [ite_eq_right hdvd]; exact hoddzero n hdvd

/-- An even polynomial over a domain of characteristic `≠ 2` is a polynomial in `X² + c`. -/
theorem Polynomial.even_eq_comp_X_sq_add_C {R : Type*} [CommRing R] [NoZeroDivisors R]
    [NeZero (2 : R)] (c : R) (b : R[X]) (hb : b.comp (-X) = b) :
    ∃ e : R[X], b = e.comp (X ^ 2 + C c) := by
  have hexp := eq_expand_two_contract_of_comp_neg_X hb
  refine ⟨(contract 2 b).comp (X - C c), ?_⟩
  have hXsq : (X - C c).comp (X ^ 2 + C c) = X ^ 2 := by
    simp only [sub_comp, X_comp, C_comp]; ring
  calc b = expand R 2 (contract 2 b) := hexp
    _ = (contract 2 b).comp (X ^ 2) := expand_eq_comp_X_pow 2
    _ = ((contract 2 b).comp (X - C c)).comp (X ^ 2 + C c) := by rw [comp_assoc, hXsq]
