/-
Copyright (c) 2026 the authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira
-/
module

public import LeanPool.NagataFactoriality.NagataFactoriality.Basic.Divisibility


/-!
# MultSet

Supporting results for Nagata’s factoriality theorem.
-/

@[expose] public section

namespace NagataFactoriality

namespace Submonoid

variable {α : Type*} [CommRing α] [IsDomain α]

theorem zero_notMem_of_prime_or_unit {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) : (0 : α) ∉ S := by
  intro h0
  rcases hS 0 h0 with h0prime | h0unit
  · exact h0prime.ne_zero rfl
  · exact h0unit.ne_zero rfl

omit [IsDomain α] in
theorem mem_ne_zero {S : Submonoid α} [Fact ((0 : α) ∉ S)] {s : α} (hs : s ∈ S) : s ≠ 0 := by
  intro hs0
  have h0 : (0 : α) ∈ S := by simpa [hs0] using hs
  exact (Fact.out : (0 : α) ∉ S) h0

theorem le_nonZeroDivisors {S : Submonoid α} [Fact ((0 : α) ∉ S)] :
    S ≤ nonZeroDivisors α := by
  intro s hs
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact mem_ne_zero hs

end Submonoid

end NagataFactoriality
