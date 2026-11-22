/-
Copyright (c) 2026 Weighted Horn Cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weighted Horn Cores contributors
-/
module

public import Mathlib.Order.Monotone.Basic

/-!
# Capacity of a weighted budget

The capacity doubles over each block of `p` steps and interpolates linearly between
consecutive block boundaries.
-/

@[expose] public section

namespace WeightedHornCores

/-- Capacity at budget `t`, with doubling period `p`. -/
def capacity (p t : ℕ) : ℕ := (p + t % p) * 2 ^ (t / p)

/-- Each unit of budget increases capacity by at least one. -/
theorem succ_capacity_le {p : ℕ} (hp : 0 < p) (t : ℕ) :
    capacity p t + 1 ≤ capacity p (t + 1) := by
  change (p + t % p) * 2 ^ (t / p) < (p + (t + 1) % p) * 2 ^ ((t + 1) / p)
  by_cases h : (t + 1) % p = 0
  · rw [Nat.succ_div_of_mod_eq_zero h, h, Nat.add_zero, Nat.pow_succ]
    calc
      _ < (p + p) * 2 ^ (t / p) := Nat.mul_lt_mul_of_pos_right
        (Nat.add_lt_add_left (Nat.mod_lt t hp) p) (Nat.two_pow_pos _)
      _ = _ := by rw [Nat.add_mul, ← Nat.mul_assoc, Nat.mul_two]
  · have hd := Nat.succ_div_of_mod_ne_zero h
    have h₀ := Nat.mod_add_div t p
    have h₁ := Nat.mod_add_div (t + 1) p
    rw [hd] at h₁ ⊢
    exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)

/-- Capacity is monotone in the available budget. -/
theorem capacity_mono {p : ℕ} (hp : 0 < p) : Monotone (capacity p) :=
  (strictMono_nat_of_lt_succ (f := capacity p) (succ_capacity_le hp)).monotone

/-- Adding one period doubles the capacity exactly. -/
theorem capacity_add_period {p : ℕ} (hp : 0 < p) (t : ℕ) :
    capacity p (t + p) = 2 * capacity p t := by
  simp only [capacity, Nat.add_mod_right, Nat.add_div_right _ hp, Nat.pow_succ]
  ac_rfl

/-- A period and one additional unit pay for two copies and one extra unit. -/
theorem double_capacity_le {p : ℕ} (hp : 0 < p) (t : ℕ) :
    2 * capacity p t + 1 ≤ capacity p (t + (p + 1)) := by
  rw [← capacity_add_period hp, ← Nat.add_assoc]
  exact succ_capacity_le hp (t + p)

/-- At block boundaries the capacity is exactly exponential. -/
theorem capacity_mul {p : ℕ} (hp : 0 < p) (k : ℕ) :
    capacity p (p * k) = p * 2 ^ k := by
  simp only [capacity, Nat.mul_mod_right, Nat.add_zero, Nat.mul_div_cancel_left k hp]

end WeightedHornCores
