/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.GCD.Basic

/-!
# Arithmetic bounds for three torsion orders

Bound the least common multiple of three orders by the cube of their maximum and transfer the
resulting modulus estimate.
-/

@[expose] public section

namespace BGS.Markoff

/-- The totient exponent is no larger than the conductor exponent. -/
theorem twenty_pow_totient_le_twenty_pow (n : ℕ) :
    20 ^ n.totient ≤ 20 ^ n :=
  Nat.pow_le_pow_right (by norm_num) (Nat.totient_le n)

/-- The least common multiple of three positive orders is bounded by their product. -/
theorem lcm_three_le_product {l₁ l₂ l₃ : ℕ}
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (hl₃ : 0 < l₃) :
    Nat.lcm (Nat.lcm l₁ l₂) l₃ ≤ l₁ * l₂ * l₃ := by
  apply Nat.le_of_dvd (mul_pos (mul_pos hl₁ hl₂) hl₃)
  exact (Nat.lcm_dvd_mul (Nat.lcm l₁ l₂) l₃).trans
    (Nat.mul_dvd_mul_right (Nat.lcm_dvd_mul l₁ l₂) l₃)

/-- Three orders are bounded by the cube of their maximum. -/
theorem product_le_max_cube (l₁ l₂ l₃ : ℕ) :
    l₁ * l₂ * l₃ ≤ max (max l₁ l₂) l₃ ^ 3 := by
  have h₁ : l₁ ≤ max (max l₁ l₂) l₃ := le_trans (le_max_left _ _) (le_max_left _ _)
  have h₂ : l₂ ≤ max (max l₁ l₂) l₃ := le_trans (le_max_right _ _) (le_max_left _ _)
  have h₃ : l₃ ≤ max (max l₁ l₂) l₃ := le_max_right _ _
  calc
    l₁ * l₂ * l₃ ≤ max (max l₁ l₂) l₃ * max (max l₁ l₂) l₃ *
        max (max l₁ l₂) l₃ := Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃
    _ = max (max l₁ l₂) l₃ ^ 3 := by ring

/-- The numerical conclusion of the opening norm argument in maximum-order form. -/
theorem modulus_le_twenty_pow_max_order_cube_of_lcm_totient_bound
    {p l₁ l₂ l₃ : ℕ} (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (hl₃ : 0 < l₃)
    (hbound : p ≤ 20 ^ (Nat.lcm (Nat.lcm l₁ l₂) l₃).totient) :
    p ≤ 20 ^ (max (max l₁ l₂) l₃ ^ 3) := by
  calc
    p ≤ 20 ^ (Nat.lcm (Nat.lcm l₁ l₂) l₃).totient := hbound
    _ ≤ 20 ^ Nat.lcm (Nat.lcm l₁ l₂) l₃ :=
      twenty_pow_totient_le_twenty_pow _
    _ ≤ 20 ^ (l₁ * l₂ * l₃) :=
      Nat.pow_le_pow_right (by norm_num) (lcm_three_le_product hl₁ hl₂ hl₃)
    _ ≤ 20 ^ (max (max l₁ l₂) l₃ ^ 3) :=
      Nat.pow_le_pow_right (by norm_num) (product_le_max_cube l₁ l₂ l₃)

end BGS.Markoff
