/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Preliminaries.Arithmetic

/-!
# Frobenius periodicity

If an element of a field of characteristic two is fixed by `pi^k` and by `pi^n`,
where `pi` is the Frobenius `x -> x^2` and `gcd (k, n) = 1`, then it is fixed by `pi`, hence lies
in the prime field `F_2`.

No algebraic closedness is needed: `x^2 = x` already forces `x = 0` or `x = 1` in any field.
-/

namespace KasamiCyclicAdditive.FermatCubic

variable {K : Type*} [Field K]

/-- An element fixed by `pi^k` and `pi^n` with `gcd (k, n) = 1`
lies in `F_2`, i.e. equals `0` or `1`. -/
theorem eq_zero_or_one_of_frobenius_fixed {x : K} {k n : ℕ} (hkn : Nat.gcd k n = 1)
    (hk : x ^ 2 ^ k = x) (hn : x ^ 2 ^ n = x) : x = 0 ∨ x = 1 := by
  have h := pow_two_pow_gcd hk hn
  rw [hkn, pow_one] at h
  have : x * (x - 1) = 0 := by ring_nf; linear_combination h
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

end KasamiCyclicAdditive.FermatCubic
