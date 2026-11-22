/-
Copyright (c) 2026 Weighted Horn Cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weighted Horn Cores contributors
-/
module

public import LeanPool.WeightedHornCores.Support
public import LeanPool.WeightedHornCores.RealBudget
public import LeanPool.WeightedHornCores.Rounding
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A real-valued size bound for an unsatisfiable Horn subformula

Choose the integer period to be the ceiling of `W / τ`, but round the total time only once.
This avoids rounding the branching ratio in the exponent of the final estimate.
-/

@[expose] public section

namespace WeightedHornCores

private theorem capacity_at_horizon {W B τ : ℝ} (hW : 0 < W) (hB : 0 ≤ B) (hτ : 0 < τ) :
    let p := ⌈W / τ⌉₊
    let H := ⌊(W + (p : ℝ) * B) / τ⌋₊
    (capacity p H : ℝ) ≤ (1 + (W / τ) / Real.log 2) * (2 : ℝ) ^ (1 + B / τ) := by
  let p := ⌈W / τ⌉₊
  let H := ⌊(W + (p : ℝ) * B) / τ⌋₊
  have hm : 0 < W / τ := div_pos hW hτ
  have hp : 0 < p := Nat.ceil_pos.mpr hm
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have htime : (H : ℝ) ≤ (W + (p : ℝ) * B) / τ :=
    Nat.floor_le (div_nonneg (add_nonneg hW.le (mul_nonneg hp'.le hB)) hτ.le)
  have hfrac : (H : ℝ) / p ≤ (W / τ) / p + B / τ := by
    refine (div_le_div_of_nonneg_right htime hp'.le).trans_eq ?_
    field_simp
  calc
    (capacity p H : ℝ) ≤ _ := capacity_le_rpow hp H
    _ ≤ ((p : ℝ) / Real.log 2) * (2 : ℝ) ^ ((W / τ) / p + B / τ) := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hfrac)
        (div_nonneg hp'.le (Real.log_pos (by norm_num)).le)
    _ = ((p : ℝ) / Real.log 2 * (2 : ℝ) ^ ((W / τ) / p)) * (2 : ℝ) ^ (B / τ) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), mul_assoc]
    _ ≤ (2 * (1 + (W / τ) / Real.log 2)) * (2 : ℝ) ^ (B / τ) :=
      mul_le_mul_of_nonneg_right (rounded_coefficient_le hm) (Real.rpow_nonneg (by norm_num) _)
    _ = (1 + (W / τ) / Real.log 2) * (2 : ℝ) ^ (1 + B / τ) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      ring

/-- A weighted Horn formula with total weight `W`, binary positive-rule weight `B`, maximal
negative arity `a` and loss at least `τ > 0` on every assignment has an unsatisfiable subset
with at most `1 + a * (1 + W / τ / log 2) * 2^(1 + B / τ)` distinct clauses. Positive rules
have at most two premises. Zero weights, empty bodies and arbitrary atom types are allowed. -/
theorem exists_core_real_bound {α : Type*} (F : Finset (Clause α)) (w : Clause α → ℝ)
    (τ : ℝ) (a : ℕ) (hτ : 0 < τ) (hw : ∀ c ∈ F, 0 ≤ w c)
    (hpos : ∀ c ∈ F, c.head.isSome = true → c.body.card ≤ 2)
    (hneg : ∀ c ∈ F, c.head = none → c.body.card ≤ a)
    (hgap : ∀ s, τ ≤ violationWeight F w s) :
    ∃ K ⊆ F, (K.card : ℝ) ≤ 1 + a * ((1 + ((∑ c ∈ F, w c) / τ) / Real.log 2) *
      (2 : ℝ) ^ (1 + branchingWeight F w / τ)) ∧ ¬ ∃ s, Models K s := by
  classical
  let W := ∑ c ∈ F, w c
  let B := branchingWeight F w
  let p := ⌈W / τ⌉₊
  let H := ⌊(W + (p : ℝ) * B) / τ⌋₊
  have hW := hτ.trans_le ((hgap ∅).trans (violationWeight_le_total hw ∅))
  have hB := branchingWeight_nonneg hw
  have hp : 0 < p := Nat.ceil_pos.mpr (div_pos hW hτ)
  have htime : W + p * B < ((H + 1 : ℕ) : ℝ) * τ := by
    rw [← div_lt_iff₀ hτ, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  obtain ⟨K, hK, hcard, hunsat⟩ := exists_core_of_horizon F w τ a p H hp hw hpos hneg hgap htime
  refine ⟨K, hK, ?_, hunsat⟩
  calc
    (K.card : ℝ) ≤ (1 : ℝ) + a * (capacity p H : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (capacity_at_horizon hW hB hτ)
      (Nat.cast_nonneg a)) 1

/-- Even when the formula contains zero-weight clauses, the same bound is attained using
only clauses of strictly positive weight. The parameters are those of the original formula. -/
theorem exists_positive_core {α : Type*} (F : Finset (Clause α)) (w : Clause α → ℝ)
    (τ : ℝ) (a : ℕ) (hτ : 0 < τ) (hw : ∀ c ∈ F, 0 ≤ w c)
    (hpos : ∀ c ∈ F, c.head.isSome = true → c.body.card ≤ 2)
    (hneg : ∀ c ∈ F, c.head = none → c.body.card ≤ a)
    (hgap : ∀ s, τ ≤ violationWeight F w s) :
    ∃ K ⊆ positiveSupport F w, (K.card : ℝ) ≤
      1 + a * ((1 + ((∑ c ∈ F, w c) / τ) / Real.log 2) *
      (2 : ℝ) ^ (1 + branchingWeight F w / τ)) ∧ ¬ ∃ s, Models K s := by
  simpa only [sum_positiveSupport hw, branchingWeight_positiveSupport hw] using
    exists_core_real_bound (positiveSupport F w) w τ a hτ
      (fun c hc => hw c (mem_positiveSupport.mp hc).1)
      (fun c hc => hpos c (mem_positiveSupport.mp hc).1)
      (fun c hc => hneg c (mem_positiveSupport.mp hc).1)
      (fun s => (hgap s).trans_eq (violationWeight_positiveSupport hw s).symm)

end WeightedHornCores
