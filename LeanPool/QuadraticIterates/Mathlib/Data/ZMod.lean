/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.ZMod.Units

/-!
# `ZMod` lemmas

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

/-- If `m ∣ a + b`, then `b ≡ -a mod m`. -/
lemma ZMod.intCast_eq_neg_intCast_of_dvd_add {a b : ℤ} {m : ℕ} (h : (m : ℤ) ∣ a + b) :
    (b : ZMod m) = -(a : ZMod m) := by
  have h0 : ((a + b : ℤ) : ZMod m) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr h
  push_cast at h0
  linear_combination h0

/-- If `m` is coprime to `a` and divides `a + b`, then `b` is a unit mod `m`. -/
lemma ZMod.isUnit_intCast_of_isCoprime_of_dvd_add {a b : ℤ} {m : ℕ}
    (hcop : IsCoprime (m : ℤ) a) (h : (m : ℤ) ∣ a + b) : IsUnit ((b : ZMod m)) := by
  have hu := (ZMod.coe_int_isUnit_iff_isCoprime a m).mpr hcop
  simpa [ZMod.intCast_eq_neg_intCast_of_dvd_add h] using hu.neg
