/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Tactic.Ring
/-!
# Hilbert ramification theory: polynomial sources

This file contains the generic polynomial congruence lemma used by the
completion-free formalization of ramification-number theory.
-/

@[expose] public section

namespace RamificationTheory.HilbertRamification
namespace Higher

/-- If two evaluation points are congruent modulo an ideal, then evaluating
any polynomial at them gives congruent results modulo the same ideal. -/
theorem polynomial_eval₂_sub_mem_of_sub_mem
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal S) {x y : S} (hxy : x - y ∈ I)
    (P : Polynomial R) :
    P.eval₂ f x - P.eval₂ f y ∈ I := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [Polynomial.eval₂_add, Polynomial.eval₂_add]
      have hsum : (P.eval₂ f x - P.eval₂ f y) +
          (Q.eval₂ f x - Q.eval₂ f y) ∈ I :=
        Ideal.add_mem I hP hQ
      convert hsum using 1
      ring
  | monomial n a =>
      rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial]
      have hpow : x ^ n - y ^ n ∈ I := by
        rcases sub_dvd_pow_sub_pow x y n with ⟨c, hc⟩
        rw [hc]
        exact Ideal.mul_mem_right c I hxy
      have hrewrite : f a * x ^ n - f a * y ^ n =
          f a * (x ^ n - y ^ n) := by
        ring
      rw [hrewrite]
      exact Ideal.mul_mem_left I (f a) hpow

end Higher
end RamificationTheory.HilbertRamification
