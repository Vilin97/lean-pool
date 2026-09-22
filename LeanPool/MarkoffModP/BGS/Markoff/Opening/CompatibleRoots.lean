/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

namespace BGS.Markoff

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

theorem exists_common_primitiveRoot_powers (n : ℕ) [NeZero n]
    (w₁ w₂ w₃ : K) (hw₁ : w₁ ^ n = 1) (hw₂ : w₂ ^ n = 1)
    (hw₃ : w₃ ^ n = 1) :
    ∃ ζ : K, ∃ a₁ a₂ a₃ : ℕ,
      IsPrimitiveRoot ζ n ∧ a₁ < n ∧ a₂ < n ∧ a₃ < n ∧
      ζ ^ a₁ = w₁ ∧ ζ ^ a₂ = w₂ ∧ ζ ^ a₃ = w₃ := by
  have : NeZero (n : K) := ⟨by exact_mod_cast (NeZero.ne n)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  obtain ⟨a₁, ha₁n, ha₁⟩ := hζ.eq_pow_of_pow_eq_one hw₁
  obtain ⟨a₂, ha₂n, ha₂⟩ := hζ.eq_pow_of_pow_eq_one hw₂
  obtain ⟨a₃, ha₃n, ha₃⟩ := hζ.eq_pow_of_pow_eq_one hw₃
  exact ⟨ζ, a₁, a₂, a₃, hζ, ha₁n, ha₂n, ha₃n, ha₁, ha₂, ha₃⟩

/-- Three units whose exact orders divide `n` are simultaneous powers of one primitive
`n`-th root.  This is the group-theoretic core of the compatible cyclotomic lift. -/
theorem exists_common_primitiveRoot_powers_of_orderOf_dvd
    (n : ℕ) [NeZero n] (w₁ w₂ w₃ : Kˣ)
    (hw₁ : orderOf w₁ ∣ n) (hw₂ : orderOf w₂ ∣ n)
    (hw₃ : orderOf w₃ ∣ n) :
    ∃ ζ : K, ∃ a₁ a₂ a₃ : ℕ,
      IsPrimitiveRoot ζ n ∧ a₁ < n ∧ a₂ < n ∧ a₃ < n ∧
      ζ ^ a₁ = (w₁ : K) ∧ ζ ^ a₂ = (w₂ : K) ∧ ζ ^ a₃ = (w₃ : K) := by
  have hpow₁ : (w₁ : K) ^ n = 1 := by
    simpa using congrArg Units.val (orderOf_dvd_iff_pow_eq_one.mp hw₁)
  have hpow₂ : (w₂ : K) ^ n = 1 := by
    simpa using congrArg Units.val (orderOf_dvd_iff_pow_eq_one.mp hw₂)
  have hpow₃ : (w₃ : K) ^ n = 1 := by
    simpa using congrArg Units.val (orderOf_dvd_iff_pow_eq_one.mp hw₃)
  exact exists_common_primitiveRoot_powers n (w₁ : K) (w₂ : K) (w₃ : K)
    hpow₁ hpow₂ hpow₃

end BGS.Markoff
