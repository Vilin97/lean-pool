/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Nilpotence under zero-preserving multiplicative maps

A positive vanishing exponent transports through a multiplicative
map even when that map does not preserve the identity.
-/

@[expose] public section

namespace RS

/-- A zero-preserving multiplicative map preserves nilpotence. -/
theorem isNilpotent_map_of_mul_zero {A B : Type*}
    [MonoidWithZero A] [MonoidWithZero B] (F : A → B)
    (hzero : F 0 = 0) (hmul : ∀ a b, F (a * b) = F a * F b)
    {x : A} (hx : IsNilpotent x) : IsNilpotent (F x) := by
  obtain ⟨n, hn⟩ := hx
  have hpow : ∀ m : ℕ, F (x ^ (m + 1)) = (F x) ^ (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, hmul, ih, ← pow_succ]
  refine ⟨n + 1, ?_⟩
  rw [← hpow, pow_succ, hn, zero_mul, hzero]

end RS
