/-
Copyright (c) 2026 Wondermonger-daydreaming. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wondermonger-daydreaming
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Fin.Basic

/-!
  `finRotate` arithmetic lemmas isolated for eventual Mathlib extraction.
-/

open Equiv Equiv.Perm

/-- Powers of `finRotate` act by addition modulo `m`.

This is the arithmetic core behind the rotation normalization arguments. -/
@[simp] lemma finRotate_pow_apply' {m : ℕ} (hm : 0 < m) (k : ℕ) (x : Fin m) :
    ((finRotate m) ^ k) x = ⟨(x.val + k) % m, Nat.mod_lt _ hm⟩ := by
  cases m with
  | zero => exact absurd hm (by omega)
  | succ m' =>
    induction k generalizing x with
    | zero =>
      ext
      simp [Nat.mod_eq_of_lt x.isLt]
    | succ k ih =>
      rw [pow_succ, mul_apply, ih]
      congr 1
      simp only [coe_finRotate]
      split_ifs with h
      · have hx : x.val = m' := by
          rw [Fin.ext_iff] at h
          simpa [Fin.val_last] using h
        rw [hx, show m' + (k + 1) = k + (m' + 1) from by omega]
        simp [Nat.add_mod_right]
      · congr 1
        omega

/-- Rotating `m` times is the identity on `Fin m`. -/
lemma finRotate_pow_self' {m : ℕ} (hm : 0 < m) : (finRotate m) ^ m = 1 := by
  ext x : 1
  have h := finRotate_pow_apply' hm m x
  simp only [Equiv.Perm.coe_one, id_eq] at h ⊢
  rw [h]
  exact Fin.ext (by simp [Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt])

section RotationFacts

variable (m : ℕ) (hm : 0 < m) (i : Fin m)

/-- Rotating `i` by `m - i.val` lands on `0`. -/
lemma rotate_self_eq_zero :
    ((finRotate m) ^ (m - i.val)) i = ⟨0, hm⟩ := by
  rw [finRotate_pow_apply' hm]
  congr 1
  have : i.val + (m - i.val) = m := by omega
  rw [this, Nat.mod_self]

/-- Rotating `finRotate m i` by `m - i.val` lands on `1`, provided `m ≥ 2`. -/
lemma rotate_succ_eq_one (hm2 : 2 ≤ m) :
    ((finRotate m) ^ (m - i.val)) (finRotate m i) = ⟨1, by omega⟩ := by
  rw [finRotate_pow_apply' (by omega : 0 < m)]
  congr 1
  cases m with
  | zero => omega
  | succ m' =>
    simp only [coe_finRotate]
    split_ifs with h
    · have hx : i.val = m' := by
        simp only [Fin.ext_iff, Fin.val_last] at h
        exact h
      rw [hx, show 0 + (m' + 1 - m') = 1 from by omega]
      exact Nat.mod_eq_of_lt (by omega)
    · have hi : i.val < m' := by
        simp only [Fin.ext_iff, Fin.val_last] at h
        exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) h
      rw [show i.val + 1 + (m' + 1 - i.val) = m' + 1 + 1 from by omega,
          Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)

end RotationFacts
