/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import LeanPool.GranvilleMoore.Defs.TheFermatQuotient

-- Adapted for Lean Pool: relocated imports and simplified supporting infrastructure.

/-!
# The defining identity of the Fermat quotient and the Frobenius exponent

This file proves the three basic identities that make the definitions of
`GranvilleMoore.Defs.TheFermatQuotient` usable without unfolding them.

## Main results

* `GranvilleMoore.fermatUnit_eq_one_add_natCast_mul_fermatQuotient`: the defining identity
  `t_x = 1 + p * q_p(x)`, an equation in `ℚ`.
* `GranvilleMoore.sub_one_mul_frobeniusExponent`: the closed form `(p - 1) * e_k = p ^ k - 1`
  of the Frobenius exponent, together with the subtraction-free
  `GranvilleMoore.sub_one_mul_frobeniusExponent_add_one`.
* `GranvilleMoore.pow_pow_eq_mul_pow_frobeniusExponent`: the reason `e_k` is the exponent it
  is, namely `x ^ p ^ k = x * (x ^ (p - 1)) ^ e_k`.

## Implementation notes

The defining identity is stated in `ℚ`, where `fermatQuotient` lives, and so needs only `p ≠ 0`:
the hypothesis `p ∤ x` is what makes `q_p(x)` an *integer*, which is a separate statement about the
same rational number and not part of this identity.

The closed form `(p - 1) * e_k = p ^ k - 1` is stated in `ℕ` with truncated subtraction and
needs no hypothesis at all — at `p = 0` both sides vanish. Consumers who want to move the
`- 1` across should use `sub_one_mul_frobeniusExponent_add_one`, which is where the
hypothesis `p ≠ 0` is genuinely needed.

`pow_pow_eq_mul_pow_frobeniusExponent` is stated for an arbitrary monoid, since nothing in
it is about `ℤ`. For `x : ℤ` its right-hand side is `x * fermatUnit p x ^ frobeniusExponent p k`,
`fermatUnit` being reducible.
-/

@[expose] public section

namespace GranvilleMoore

/-! ### The defining identity -/

/-- **The defining identity of the Fermat quotient**: `t_x = 1 + p * q_p(x)`.

This is the equation of `GranvilleMoore.fermatQuotient` multiplied by `p` with `1` added to
both sides, and it is the form in which consumers use the Fermat quotient. It is an identity
in `ℚ`; that both sides are integers when `p ∤ x` is the separate integrality statement. -/
theorem fermatUnit_eq_one_add_natCast_mul_fermatQuotient {p : ℕ} (hp : p ≠ 0) (x : ℤ) :
    (fermatUnit p x : ℚ) = 1 + (p : ℚ) * fermatQuotient p x := by
  rw [natCast_mul_fermatQuotient hp]
  push_cast
  ring

/-! ### The closed form of the Frobenius exponent -/

/-- The Frobenius exponent in subtraction-free form: `(p - 1) * e_k + 1 = p ^ k`.

This is the shape in which the closed form is used as an exponent identity, see
`GranvilleMoore.pow_pow_eq_mul_pow_frobeniusExponent`. -/
theorem sub_one_mul_frobeniusExponent_add_one {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    (p - 1) * frobeniusExponent p k + 1 = p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp' : 1 + (p - 1) = p := by omega
    calc (p - 1) * frobeniusExponent p (k + 1) + 1
        = (p - 1) * frobeniusExponent p k + 1 + (p - 1) * p ^ k := by
          rw [frobeniusExponent_succ]; ring
      _ = (1 + (p - 1)) * p ^ k := by rw [ih]; ring
      _ = p ^ (k + 1) := by rw [hp']; ring

/-- **The Frobenius exponent, closed form**: `(p - 1) * e_k = p ^ k - 1`.

The subtraction is truncated, which is why no hypothesis on `p` is needed; for the version
that moves the `- 1` to the other side see
`GranvilleMoore.sub_one_mul_frobeniusExponent_add_one`. -/
theorem sub_one_mul_frobeniusExponent (p k : ℕ) :
    (p - 1) * frobeniusExponent p k = p ^ k - 1 := by
  rcases eq_or_ne p 0 with rfl | hp
  · rcases k with _ | k <;> simp
  · have := sub_one_mul_frobeniusExponent_add_one hp k
    omega

/-! ### Frobenius powers in terms of the unit -/

/-- **Frobenius powers in terms of the unit**: `x ^ p ^ k = x * (x ^ (p - 1)) ^ e_k`.

For `x : ℤ` the right-hand factor is `GranvilleMoore.fermatUnit p x ^ frobeniusExponent p k`;
this is the identity that makes the Frobenius exponent the exponent of the unit `t_x`
contributed by the `p ^ k`-th power map. -/
theorem pow_pow_eq_mul_pow_frobeniusExponent {M : Type*} [Monoid M] {p : ℕ} (hp : p ≠ 0)
    (x : M) (k : ℕ) :
    x ^ p ^ k = x * (x ^ (p - 1)) ^ frobeniusExponent p k := by
  rw [← pow_mul, ← pow_succ', sub_one_mul_frobeniusExponent_add_one hp]

end GranvilleMoore
