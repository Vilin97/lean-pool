/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Root-set lemmas

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

/-- For a polynomial without repeated roots in `E`, a product over the (coerced) `rootSet` equals
the corresponding multiset product over `aroots`. -/
lemma Polynomial.prod_rootSet_eq_prod_aroots {K E M : Type*} [Field K] [Field E] [Algebra K E]
    [CommMonoid M] {p : Polynomial K} (hnodup : (p.aroots E).Nodup) (f : E → M) :
    ∏ β : (p.rootSet E), f β = ((p.aroots E).map f).prod := by
  classical
  rw [Finset.prod_set_coe (f := f),
    show (p.rootSet E).toFinset = (p.aroots E).toFinset by ext x; simp [Polynomial.mem_rootSet'],
    Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
