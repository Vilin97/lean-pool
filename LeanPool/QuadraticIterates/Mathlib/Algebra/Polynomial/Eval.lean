/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomial evaluation lemmas

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

/-- A ring homomorphism intertwines iterated evaluation of `p` with iterated evaluation of the
mapped polynomial. -/
lemma Polynomial.map_iterate_eval {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : Polynomial R) (z : R) (j : ℕ) :
    f ((fun y ↦ p.eval y)^[j] z) = ((p.map f).eval)^[j] (f z) := by
  induction j generalizing z with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, Polynomial.eval_map,
      Polynomial.eval₂_at_apply]

/-- Evaluating the `L`-reduction of an integer polynomial at an integer point of an `L`-algebra
yields the cast of the integral value. -/
lemma Polynomial.aeval_intCast_map {L K : Type*} [CommRing L] [CommRing K] [Algebra L K]
    (p : Polynomial ℤ) (m : ℤ) :
    Polynomial.aeval (m : K) (p.map (Int.castRingHom L)) = ((p.eval m : ℤ) : K) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_at_intCast, Polynomial.eval_intCast_map]
  simp
