/-
Copyright (c) 2026 Arthur Champernowne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Champernowne
-/
module

public import LeanPool.Champernowne.Asymptotics

/-!
# Champernowne's theorem (1933)

The base-`b` Champernowne sequence is normal in base `b`.
-/

@[expose] public section

namespace Champernowne

theorem champernowne_normal (b : ℕ) (hb : 2 ≤ b) :
    IsNormalSequence b (champDigit b) := by
  intro w hwne hw
  have h := tendsto_countOccurrences_champPrefix_div (b := b) (w := w) (by omega) hw hwne
  simpa only [champPrefix_eq_map] using h

/-- The classical base-10 statement. -/
theorem champernowne_normal_ten : IsNormalSequence 10 (champDigit 10) :=
  champernowne_normal 10 (by norm_num)

end Champernowne
