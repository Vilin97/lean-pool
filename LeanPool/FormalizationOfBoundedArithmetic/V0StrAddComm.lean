/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

-- This file proves:
-- ∀ {X Y : str}, X + Y = Y + X
-- However, the proof was done using leanstral and is very verbose
-- Please see V0.lean for the manually written foundations.
import LeanPool.FormalizationOfBoundedArithmetic.V0

variable {num str : Type} [M : V0ExtModel num str]
open FirstOrder Language
open HasTypes_is
open HasEmptySet
open HasLen
open HasSucc
open V0ExtModel V0Model BASICModel

lemma carry_comm : ∀ {X Y : str}, ∀ {i : num}, Carry i X Y ↔ Carry i Y X := by
  intro X Y i
  unfold Carry
  constructor
  · intro h
    obtain ⟨k, hk_lt_i, hkX, hkY, hkprop⟩ := h
    refine ⟨k, hk_lt_i, hkY, hkX, ?_⟩
    intro j hj_lt_i hk_lt_j
    rcases hkprop j hj_lt_i hk_lt_j with hjX | hjY
    · exact Or.inr hjX
    · exact Or.inl hjY
  · intro h
    obtain ⟨k, hk_lt_i, hkY, hkX, hkprop⟩ := h
    refine ⟨k, hk_lt_i, hkX, hkY, ?_⟩
    intro j hj_lt_i hk_lt_j
    rcases hkprop j hj_lt_i hk_lt_j with hjY | hjX
    · exact Or.inr hjY
    · exact Or.inl hjX

lemma mem_add_iff_xor : ∀ {X Y : str}, ∀ {i : num},
    i ∈ X + Y ↔ Xor' (Xor' (i ∈ X) (i ∈ Y)) (Carry i X Y) := by
  intro X Y i
  constructor
  · intro h
    exact (ax_add (X := X) (Y := Y) (i := i)).mp h |>.2
  · intro h_xor
    have h_lt : i < len X + len Y := by
      rw [xor3_split] at h_xor
      rcases h_xor with h | h | h | h
      · exact lt_of_lt_of_le (L1 h.1) (show len X ≤ len X + len Y from B8)
      · exact lt_of_lt_of_le (L1 h.2.1) (by
          rw [_root_.add_comm]
          exact B8)
      · exact carry_lt_add_len h.2.2
      · exact lt_of_lt_of_le (L1 h.1) (show len X ≤ len X + len Y from B8)
    exact (ax_add (X := X) (Y := Y) (i := i)).mpr ⟨h_lt, h_xor⟩

theorem str_add_comm : ∀ {X Y : str}, X + Y = Y + X := by
  intro X Y
  refine str_eq_of_mem_iff (num := num) (str := str) (X := X + Y) (Y := Y + X) ?_
  intro i
  rw [mem_add_iff_xor (X := X) (Y := Y) (i := i)]
  rw [mem_add_iff_xor (X := Y) (Y := X) (i := i)]
  rw [carry_comm (X := X) (Y := Y) (i := i)]
  unfold Xor'
  tauto

/-- Named alias emphasizing that this theorem is conditional on the strengthened V0 extension. -/
theorem str_add_comm_strengthened_v0 : ∀ {X Y : str}, X + Y = Y + X :=
  str_add_comm
