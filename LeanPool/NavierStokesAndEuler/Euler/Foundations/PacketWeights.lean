/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Bound

/-!
Exact weight identities used in the proposed packet's Gevrey estimates (18)--(19).
These lemmas do not assert the nonlinear PDE estimates or an Euler blowup theorem.
-/

@[expose] public section

noncomputable section

namespace EulerPacketWeights

/-- Factorial weight at radius `ρ` for the Gevrey-two energy series. -/
noncomputable def weight (ρ : ℝ) (n : ℕ) : ℝ :=
  ρ ^ n / (n.factorial : ℝ) ^ 2

theorem weight_pos {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) : 0 < weight ρ n := by
  unfold weight
  positivity

theorem factorial_cast_ne_zero (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by
  exact_mod_cast n.factorial_ne_zero

/-- The binomial gain that compensates a Gevrey-2 derivative in a non-top commutator. -/
theorem choose_add_lower (j l : ℕ) (hl : 1 ≤ l) :
    j + 1 ≤ (j + l).choose l := by
  rw [← Nat.choose_symm_add]
  have h := Nat.choose_le_choose j (Nat.add_le_add_left hl j)
  simpa only [Nat.choose_succ_self_right] using h

/-- Equation (18)'s source weight ratio, written without truncated natural subtraction. -/
theorem shifted_source_ratio (ρ : ℝ) (hρ : ρ ≠ 0) (j l : ℕ) :
    ((j + l + 1 : ℕ) : ℝ) * weight ρ (j + l + 1) * ((j + l).choose l : ℝ) /
        (weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1)) =
      1 / ((j + l + 1).choose l : ℝ) := by
  have hl₀ : l ≤ j + l := Nat.le_add_left l j
  have hl₁ : l ≤ j + l + 1 := hl₀.trans (Nat.le_add_right _ _)
  have hsub : j + l + 1 - l = j + 1 := by omega
  rw [Nat.cast_choose ℝ hl₀, Nat.cast_choose ℝ hl₁]
  simp only [Nat.add_sub_cancel_right, hsub]
  unfold weight
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_add, pow_one]
  field_simp [factorial_cast_ne_zero, hρ]

/-- Equation (19)'s external-commutator ratio. -/
theorem external_commutator_ratio (ρ : ℝ) (hρ : ρ ≠ 0) (j l : ℕ) :
    weight ρ (j + l) * ((j + l).choose l : ℝ) /
        (weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1)) =
      ρ⁻¹ * ((j + 1 : ℕ) : ℝ) / ((j + l).choose l : ℝ) := by
  rw [Nat.cast_choose ℝ (Nat.le_add_left l j)]
  simp only [Nat.add_sub_cancel_right]
  unfold weight
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_add, pow_one]
  field_simp [factorial_cast_ne_zero, hρ]

/-- The source ratio in (18) is at most one, uniformly in the derivative indices. -/
theorem shifted_source_ratio_le_one (ρ : ℝ) (hρ : ρ ≠ 0) (j l : ℕ) :
    ((j + l + 1 : ℕ) : ℝ) * weight ρ (j + l + 1) * ((j + l).choose l : ℝ) /
        (weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1)) ≤ 1 := by
  rw [shifted_source_ratio ρ hρ j l]
  have hn : 0 < (j + l + 1).choose l :=
    Nat.choose_pos ((Nat.le_add_left l j).trans (Nat.le_add_right _ _))
  have hp : (0 : ℝ) < ((j + l + 1).choose l : ℝ) := by exact_mod_cast hn
  apply (div_le_one hp).2
  exact_mod_cast hn

/-- The non-top ratio in (19) is at most the inverse radius, with no order loss. -/
theorem external_commutator_ratio_le (ρ : ℝ) (hρ : 0 < ρ) (j l : ℕ)
    (hl : 1 ≤ l) :
    weight ρ (j + l) * ((j + l).choose l : ℝ) /
        (weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1)) ≤ ρ⁻¹ := by
  rw [external_commutator_ratio ρ hρ.ne' j l]
  have hp : (0 : ℝ) < ((j + l).choose l : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left l j)
  have hb : ((j + 1 : ℕ) : ℝ) ≤ ((j + l).choose l : ℝ) := by
    exact_mod_cast choose_add_lower j l hl
  exact (div_le_iff₀ hp).2 (mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hρ.le))

end EulerPacketWeights
