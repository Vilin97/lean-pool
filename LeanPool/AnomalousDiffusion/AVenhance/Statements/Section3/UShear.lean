/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SpaceLap

/-! Statement file: `uShear` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance

/-- `e.ukm.explicit` (label 2738, lines 2731-2749): `u_{m,k} = ∇^⊥ ψ_{m,k}`, written out:
`2π a_m ε_m cos(2π x₁/ε_m) e₂` if `k ∈ 4ℤ+1`, `-2π a_m ε_m cos(2π x₂/ε_m) e₁` if `k ∈ 4ℤ+3`,
`0` if `k ∈ 2ℤ`. -/
def uShear (β : ℝ) (Λ : ℕ) (m : ℕ) (k : ℤ) (x : Vec 2) : Vec 2 :=
  if k % 4 = 1 then
    ![0, 2 * Real.pi * a β Λ m * epsilon β Λ m *
      Real.cos (2 * Real.pi * x 0 / epsilon β Λ m)]
  else if k % 4 = 3 then
    ![-(2 * Real.pi * a β Λ m * epsilon β Λ m *
      Real.cos (2 * Real.pi * x 1 / epsilon β Λ m)), 0]
  else 0

end AVenhance
