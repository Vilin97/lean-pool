/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.AlgorithmicSpec
import LeanPool.BeyondBethe.BeyondBethe.RationalEllipsoid
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-! # Dyadic Rounding -/

open scoped BigOperators

namespace BeyondBethe

/-!
# Executable dyadic rounding

The exact rational ellipsoid update is mathematically convenient, but its
reduced numerators and denominators need not have polynomial length after a
polynomial number of iterations.  This file defines the rounding primitive
used by the bounded-bit implementation.  It is deliberately just integer
floor followed by division by a power of two, so its output has an explicit
dyadic presentation and its error is proved directly from the floor axioms.
-/

/-- The mesh of the dyadic grid with `p` fractional bits. -/
def dyadicMesh (p : ℕ) : ℚ := 1 / (2 : ℚ) ^ p

theorem dyadicMesh_pos (p : ℕ) : 0 < dyadicMesh p := by
  simp [dyadicMesh]

theorem dyadicMesh_nonneg (p : ℕ) : 0 ≤ dyadicMesh p :=
  (dyadicMesh_pos p).le

theorem dyadicMesh_le_one (p : ℕ) : dyadicMesh p ≤ 1 := by
  rw [dyadicMesh, one_div]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2))

/-- Finer dyadic grids have smaller mesh. -/
theorem dyadicMesh_antitone {p q : ℕ} (hpq : p ≤ q) :
    dyadicMesh q ≤ dyadicMesh p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpq
  rw [dyadicMesh, dyadicMesh]
  exact one_div_le_one_div_of_le (by positivity : (0 : ℚ) < (2 : ℚ) ^ p)
    (by
      rw [pow_add]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2))
        (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ p))

theorem dyadicMesh_mul_pow_two (p : ℕ) :
    dyadicMesh p * (2 : ℚ) ^ p = 1 := by
  simp [dyadicMesh]

/-- Round a rational down to the `2^-p` grid.  This is executable integer
division, not a choice of a nearby rational. -/
def dyadicFloor (p : ℕ) (q : ℚ) : ℚ :=
  (Int.floor (q * (2 : ℚ) ^ p) : ℚ) / (2 : ℚ) ^ p

theorem dyadicFloor_eq_floor_mul_mesh (p : ℕ) (q : ℚ) :
    dyadicFloor p q = (Int.floor (q * (2 : ℚ) ^ p) : ℚ) * dyadicMesh p := by
  simp [dyadicFloor, dyadicMesh, div_eq_mul_inv]

theorem dyadicFloor_mul_pow_two (p : ℕ) (q : ℚ) :
    dyadicFloor p q * (2 : ℚ) ^ p =
      (Int.floor (q * (2 : ℚ) ^ p) : ℚ) := by
  rw [dyadicFloor]
  field_simp

/-- Rounding down never increases the input. -/
theorem dyadicFloor_le (p : ℕ) (q : ℚ) : dyadicFloor p q ≤ q := by
  have hfloor :
      ((Int.floor (q * (2 : ℚ) ^ p) : ℤ) : ℚ) ≤
        q * (2 : ℚ) ^ p := Int.floor_le _
  rw [dyadicFloor]
  exact (div_le_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ p)).2
    (by simpa [mul_comm] using hfloor)

/-- The one-sided rounding error is strictly smaller than one mesh. -/
theorem lt_dyadicFloor_add_mesh (p : ℕ) (q : ℚ) :
    q < dyadicFloor p q + dyadicMesh p := by
  have hfloor : q * (2 : ℚ) ^ p <
      ((Int.floor (q * (2 : ℚ) ^ p) : ℤ) : ℚ) + 1 :=
    Int.lt_floor_add_one _
  rw [dyadicFloor, dyadicMesh]
  have hp : (0 : ℚ) < (2 : ℚ) ^ p := by positivity
  rw [show
      ((Int.floor (q * (2 : ℚ) ^ p) : ℤ) : ℚ) / (2 : ℚ) ^ p +
          1 / (2 : ℚ) ^ p =
        (((Int.floor (q * (2 : ℚ) ^ p) : ℤ) : ℚ) + 1) /
          (2 : ℚ) ^ p by rw [add_div]]
  exact (lt_div_iff₀ hp).2 (by simpa [mul_comm] using hfloor)

theorem dyadicFloor_error_nonneg (p : ℕ) (q : ℚ) :
    0 ≤ q - dyadicFloor p q := sub_nonneg.mpr (dyadicFloor_le p q)

theorem dyadicFloor_error_lt (p : ℕ) (q : ℚ) :
    q - dyadicFloor p q < dyadicMesh p := by
  linarith [lt_dyadicFloor_add_mesh p q]

/-- Absolute-error form used by vector and matrix estimates. -/
theorem abs_dyadicFloor_sub_lt (p : ℕ) (q : ℚ) :
    abs (dyadicFloor p q - q) < dyadicMesh p := by
  rw [abs_of_nonpos (sub_nonpos.mpr (dyadicFloor_le p q))]
  simpa only [neg_sub] using dyadicFloor_error_lt p q

theorem abs_dyadicFloor_le (p : ℕ) (q : ℚ) :
    abs (dyadicFloor p q) < abs q + dyadicMesh p := by
  calc
    abs (dyadicFloor p q) =
        abs ((dyadicFloor p q - q) + q) := by ring_nf
    _ ≤ abs (dyadicFloor p q - q) + abs q := abs_add_le _ _
    _ < dyadicMesh p + abs q := by
      gcongr
      exact abs_dyadicFloor_sub_lt p q
    _ = abs q + dyadicMesh p := by ring

/-- Coordinatewise dyadic rounding of a finite vector. -/
def dyadicFloorVector {d : ℕ} (p : ℕ) (x : Fin d → ℚ) : Fin d → ℚ :=
  fun i ↦ dyadicFloor p (x i)

/-- Coordinatewise dyadic rounding of a finite matrix. -/
def dyadicFloorMatrix {m n : ℕ} (p : ℕ)
    (A : Matrix (Fin m) (Fin n) ℚ) : Matrix (Fin m) (Fin n) ℚ :=
  fun i j ↦ dyadicFloor p (A i j)

theorem dyadicFloorVector_error_l1_lt {d : ℕ} (hd : 0 < d) (p : ℕ)
    (x : Fin d → ℚ) :
    (∑ i, abs (dyadicFloorVector p x i - x i)) < d * dyadicMesh p := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [show (d : ℚ) * dyadicMesh p =
      ∑ _i : Fin d, dyadicMesh p by simp]
  apply Finset.sum_lt_sum
  · intro i _
    exact (abs_dyadicFloor_sub_lt p (x i)).le
  · let i : Fin d := ⟨0, hd⟩
    exact ⟨i, Finset.mem_univ i, abs_dyadicFloor_sub_lt p (x i)⟩

theorem dyadicFloorVector_error_normSq_lt {d : ℕ} (hd : 0 < d)
    (p : ℕ) (x : Fin d → ℚ) :
    finiteNormSq (fun i ↦ dyadicFloorVector p x i - x i) <
      d * dyadicMesh p ^ 2 := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [finiteNormSq, finiteDot,
    show (d : ℚ) * dyadicMesh p ^ 2 =
      ∑ _i : Fin d, dyadicMesh p ^ 2 by simp]
  have hentry : ∀ i : Fin d,
      (dyadicFloorVector p x i - x i) *
          (dyadicFloorVector p x i - x i) < dyadicMesh p ^ 2 := by
    intro i
    have habs : abs (dyadicFloorVector p x i - x i) < dyadicMesh p := by
      simpa only [dyadicFloorVector] using abs_dyadicFloor_sub_lt p (x i)
    have habs0 : 0 ≤ abs (dyadicFloorVector p x i - x i) := abs_nonneg _
    have hmesh := dyadicMesh_nonneg p
    calc
      (dyadicFloorVector p x i - x i) *
          (dyadicFloorVector p x i - x i) =
        abs (dyadicFloorVector p x i - x i) ^ 2 := by
          rw [sq_abs, sq]
      _ < dyadicMesh p ^ 2 := (sq_lt_sq₀ habs0 hmesh).2 habs
  apply Finset.sum_lt_sum
  · intro i _
    exact (hentry i).le
  · let i : Fin d := ⟨0, hd⟩
    exact ⟨i, Finset.mem_univ i, hentry i⟩

theorem dyadicFloorMatrix_entry_error_lt {m n : ℕ} (p : ℕ)
    (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (j : Fin n) :
    abs (dyadicFloorMatrix p A i j - A i j) < dyadicMesh p :=
  abs_dyadicFloor_sub_lt p (A i j)

theorem cast_dyadicFloorMatrix_entry_error_lt {m n : ℕ} (p : ℕ)
    (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (j : Fin n) :
    abs (((dyadicFloorMatrix p A i j - A i j : ℚ) : ℝ)) <
      (dyadicMesh p : ℝ) := by
  exact_mod_cast dyadicFloorMatrix_entry_error_lt p A i j

theorem abs_cast_dyadicFloorMatrix_le {m n : ℕ} (p : ℕ)
    (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (j : Fin n) :
    abs ((dyadicFloorMatrix p A i j : ℚ) : ℝ) <
      abs ((A i j : ℚ) : ℝ) + (dyadicMesh p : ℝ) := by
  exact_mod_cast abs_dyadicFloor_le p (A i j)

/-- Every rounded value has a concrete integer-over-power-of-two
presentation.  Later bit-complexity proofs use this presentation rather than
the implementation-dependent reduced numerator and denominator. -/
theorem dyadicFloor_has_integer_presentation (p : ℕ) (q : ℚ) :
    ∃ z : ℤ, dyadicFloor p q = (z : ℚ) / (2 : ℚ) ^ p := by
  exact ⟨Int.floor (q * (2 : ℚ) ^ p), rfl⟩

end BeyondBethe
