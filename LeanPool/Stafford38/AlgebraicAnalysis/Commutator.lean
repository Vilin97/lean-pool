/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib

/-!
# Ring commutators

This module contains the multiplication identities used by both the Weyl
symplectic layer and the differential-Ore escape layer.  The convention is
`[u,v] = u*v - v*u`; no Weyl relation, Ore presentation, or application
specific structure is assumed.
-/

namespace AlgebraicAnalysis

section

variable {A : Type*} [Ring A]

/-- The ring commutator, with the written multiplication order retained. -/
def ringCommutator (u v : A) : A := u * v - v * u

@[simp] theorem ringCommutator_apply (u v : A) :
    ringCommutator u v = u * v - v * u := rfl

/-- Leibniz expansion in the first argument. -/
theorem ringCommutator_mul (u v x : A) :
    ringCommutator (u * v) x =
      u * ringCommutator v x + ringCommutator u x * v := by
  simp only [ringCommutator]
  noncomm_ring

/-- Iterated commutation with a Weyl-type relation. -/
theorem ringCommutator_pow (z x : A) (h : ringCommutator z x = 1) :
    ∀ n : ℕ, ringCommutator (z ^ n) x = n • z ^ (n - 1)
  | 0 => by simp [ringCommutator]
  | n + 1 => by
      rw [pow_succ, ringCommutator_mul, h, ringCommutator_pow z x h n]
      by_cases hn : n = 0
      · subst n
        simp
      · rw [smul_mul_assoc, Nat.succ_sub_one, mul_one, add_nsmul]
        have hpow : z ^ (n - 1) * z = z ^ n := by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
        rw [hpow, one_nsmul]
        exact add_comm _ _

end

end AlgebraicAnalysis
