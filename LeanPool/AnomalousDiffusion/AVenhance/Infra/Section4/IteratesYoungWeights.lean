/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordGrouping
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesRecursion

/-! Dissipation allocation with exact binomial multiplicities. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- A weight for every actual Leibniz term. Terms at coefficient order j
share a geometric budget, divided by their binomial multiplicity. -/
def iterateYoungWeight (κ : ℝ) (n j : ℕ) : ℝ :=
  κ / 16 * (1 / (2 : ℝ)) ^ j / (Nat.choose n j : ℝ)

/-- Every actual split receives a positive dissipation weight. -/
theorem iterateYoungWeight_pos {κ : ℝ} (hκ : 0 < κ) (w : List (Fin 2))
    {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ iterateSpatialSplits w) :
    0 < iterateYoungWeight κ w.length p.1.length := by
  have hs := iterateSpatialSplits_orders w hp
  have hchoose : 0 < Nat.choose w.length p.1.length := Nat.choose_pos (by omega)
  unfold iterateYoungWeight
  positivity

/-- The total allocation absorbs at most one eighth of the dissipation,
independently of derivative order and repeated coordinate letters. -/
theorem iterateYoungWeight_sum_le {κ : ℝ} (hκ : 0 ≤ κ) (w : List (Fin 2)) :
    ((iterateSpatialSplits w).map (fun p => iterateYoungWeight κ w.length p.1.length)).sum ≤ κ / 8
        := by
  rw [iterateSpatialSplits_sum_by_order]
  have heq : (∑ j ∈ Finset.range (w.length + 1),
      (Nat.choose w.length j : ℝ) * iterateYoungWeight κ w.length j) =
      κ / 16 * ∑ j ∈ Finset.range (w.length + 1), (1 / (2 : ℝ)) ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hc : (Nat.choose w.length j : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by have h := Finset.mem_range.mp hj; omega)).ne'
    unfold iterateYoungWeight
    field_simp
  rw [heq]
  have hs := iterate_geometric_kernel_le_two (r := (1 / (2 : ℝ))) (by norm_num) (by norm_num)
      (w.length + 1)
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ κ / 16)
  convert hm using 1
  ring

/-- The exact reciprocal weight introduces one binomial factor and a
geometric factor 2^j, which cancels against the analytic factorial profile. -/
theorem iterateYoungWeight_reciprocal {κ D : ℝ} (hκ : 0 < κ) (n j : ℕ) (hj : j ≤ n) :
    D ^ 2 / iterateYoungWeight κ n j =
      16 / κ * (Nat.choose n j : ℝ) * (2 : ℝ) ^ j * D ^ 2 := by
  have hc : (Nat.choose n j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
  have hp : (1 / (2 : ℝ)) ^ j ≠ 0 := by positivity
  unfold iterateYoungWeight
  field_simp
  have ht : (1 / (2 : ℝ)) ^ j * (2 : ℝ) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    D ^ 2 = D ^ 2 * 1 := by ring
    _ = D ^ 2 * ((1 / (2 : ℝ)) ^ j * (2 : ℝ) ^ j) := by rw [ht]
    _ = _ := by ring

end AVenhance.Infra.Section4
