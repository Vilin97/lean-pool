/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Counting.Definitions
import LeanPool.KasamiCyclicAdditive.Phase.AdditiveCharacter

/-!
# Elementary inputs

Three bookkeeping inputs the assembled theorem needs:

* a primitive additive character `K → ℂ` is supplied by Mathlib
  (`KasamiCyclicAdditive.primitiveAddChar`);
* the exponent inverse `D` is supplied by the extended Euclidean algorithm;
* the admissible-slope finset is nonempty as soon as `|K| > 2`.

-/

open Finset

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Coprimality yields a nonzero inverse exponent `D` with `m * D ≡ 1 [MOD N]`.
The modulus is abstract; the application takes `N = |Kˣ|`. -/
theorem exists_inverse_exponent {m N : ℕ} (hcop : Nat.Coprime m N) (hN : 1 < N) :
    ∃ D : ℕ, D ≠ 0 ∧ m * D ≡ 1 [MOD N] := by
  obtain ⟨D, _hDlt, hDmod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hN
  have hD0 : D ≠ 0 := by
    intro h
    subst D
    simp at hDmod
  refine ⟨D, hD0, ?_⟩
  rw [Nat.ModEq]
  simpa [Nat.mod_eq_of_lt hN] using hDmod

/-- A finite field with more than two elements has an admissible slope. -/
theorem slopes_nonempty_of_two_lt_card (hcard : 2 < Fintype.card K) :
    (slopes K).Nonempty := by
  have hex : ∃ r : K, r ≠ 0 ∧ r ≠ 1 := by
    by_contra h
    push Not at h
    let f : Bool → K := fun b => if b then 1 else 0
    have hsurj : Function.Surjective f := by
      intro r
      by_cases hr0 : r = 0
      · exact ⟨false, by simp [f, hr0]⟩
      · exact ⟨true, by simp [f, h r hr0]⟩
    have hc : Fintype.card K ≤ Fintype.card Bool :=
      Fintype.card_le_of_surjective f hsurj
    norm_num at hc
    omega
  obtain ⟨r, hr0, hr1⟩ := hex
  refine ⟨r, ?_⟩
  simp [slopes, hr0, hr1]

/-- The field-cardinality hypothesis occurring in the Kasami statement implies
nonempty slopes as soon as `2 ≤ n`. -/
theorem slopes_nonempty_of_card_two_pow {n : ℕ}
    (hn : 2 ≤ n) (hcard : Fintype.card K = 2 ^ n) :
    (slopes K).Nonempty := by
  apply slopes_nonempty_of_two_lt_card
  rw [hcard]
  calc
    2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn

end KasamiCyclicAdditive
