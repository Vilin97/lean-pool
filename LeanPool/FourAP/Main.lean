/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/
module

public import LeanPool.FourAP.Construction

/-!
# The theorem of the paper

The declarations here assemble the preceding modules into the unconditional
existence theorem of the paper “A 4AP-free permutation of the positive
integers”. For the closest match to the displayed theorem in the paper, see
`exists_fourAPFree_positive_permutation`, which uses positive integers both
as positions and as values, and an arbitrary nonzero integer difference.
Each existential statement below uses the explicit, verified construction.
-/
public section

namespace FourAP

/-- The main theorem before the final shift: a permutation of `ℕ₀` with no
four-term arithmetic progression in increasing positions. -/
theorem exists_fourAPFree_permutation : ∃ f : ℕ ≃ ℕ, SequenceAPFree f :=
  ⟨explicitPermutation, explicitPermutation_apFree⟩

/-- The main theorem after adding one to every value, retaining zero-based
positions for compatibility with Lean lists and sequences. -/
theorem exists_fourAPFree_positive_sequence :
    ∃ f : ℕ ≃ ℕ+, ∀ i j k l : ℕ,
      i < j → j < k → k < l → ∀ a r : ℤ, r ≠ 0 →
      ¬ (((f i : ℕ) : ℤ) = a ∧ ((f j : ℕ) : ℤ) = a + r ∧
         ((f k : ℕ) : ℤ) = a + 2 * r ∧ ((f l : ℕ) : ℤ) = a + 3 * r) :=
  ⟨explicitPositiveSequence, explicitPositiveSequence_apFree⟩

/-- **The theorem of the paper.** There exists a permutation of the positive
integers containing no subsequence `a, a+r, a+2r, a+3r` with `r ≠ 0` in `ℤ`.

A Lean equivalence supplies both injectivity and surjectivity: no value is
repeated or omitted. The indices here are positive integers, matching the
paper's convention `a₁ a₂ …`. Negative common differences are included. -/
theorem exists_fourAPFree_positive_permutation :
    ∃ f : ℕ+ ≃ ℕ+, ∀ i j k l : ℕ+,
      i < j → j < k → k < l → ∀ a r : ℤ, r ≠ 0 →
      ¬ (((f i : ℕ) : ℤ) = a ∧ ((f j : ℕ) : ℤ) = a + r ∧
         ((f k : ℕ) : ℤ) = a + 2 * r ∧ ((f l : ℕ) : ℤ) = a + 3 * r) :=
  ⟨explicitPositivePermutation, explicitPositivePermutation_apFree⟩

end FourAP
