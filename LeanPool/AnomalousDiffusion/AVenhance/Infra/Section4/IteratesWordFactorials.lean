/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordGrouping

/-! Factorial cancellation for the actual binomially grouped forcing terms. -/

@[expose] public section

namespace AVenhance.Infra.Section4

/-- Shifted analytic scalar weights absorb the exact coefficient multiplicity. -/
theorem iterate_choose_factorial_shift_le (n j a : ℕ) (hj : j ≤ n) :
    Nat.choose n j * j.factorial * (n - j + a).factorial ≤ (n + a).factorial := by
  have hchoose := Nat.choose_le_choose j (by omega : n ≤ n + a)
  have hm := Nat.mul_le_mul_right ((n - j + a).factorial)
    (Nat.mul_le_mul_right j.factorial hchoose)
  have he := Nat.choose_mul_factorial_mul_factorial (by omega : j ≤ n + a)
  have hn : n + a - j = n - j + a := by omega
  rw [hn] at he
  exact hm.trans_eq he

end AVenhance.Infra.Section4
