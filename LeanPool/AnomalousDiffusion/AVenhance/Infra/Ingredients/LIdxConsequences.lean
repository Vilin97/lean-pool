/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScales

/-! The corrected floor index and its cell-containment property. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Ingredients

/-- Half-count of time cells used in the coarse time-index arithmetic. -/
def LIdxConsequences.tauCellHalfCount (β : ℝ) (Λ m : ℕ) : ℕ :=
  8 * (⌈AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ : ℕ) ^ 2 +
    4 * (⌈AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ : ℕ)

theorem LIdxConsequences.tauCellCount_eq_two_mul_half_add_one (β : ℝ) (Λ m : ℕ) :
    tauCellCount β Λ m = 2 * LIdxConsequences.tauCellHalfCount β Λ m + 1 := by
  unfold tauCellCount LIdxConsequences.tauCellHalfCount
  ring

/-- Positivity of all time cells from `e.taum.def` and `e.taum.primeprime.def`
(1108-1136). -/
theorem tau_pos {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    0 < AVenhance.tau β Λ m := by
  by_cases hm : m = 0
  · simp [AVenhance.tau, hm]
  · have hfactor : 0 <
        (4 * (⌈AVenhance.epsilon β Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ : ℝ) + 1)⁻¹ ^ 2 := by
      positivity
    simpa [AVenhance.tau, hm] using
      mul_pos hfactor (AVenhance.Infra.Cutoff.tauPP_pos hβ hβ' hΛ)

/-- `e.taum.prime.supp` (1179-1187), using the corrected floor index:
the small time cell centered at `k τ_m` lies in its assigned large cell. -/
theorem taum_prime_supp {β : ℝ} {Λ m : ℕ} (k : ℤ)
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    Set.Icc ((k : ℝ) * AVenhance.tau β Λ m - AVenhance.tau β Λ m / 2)
        ((k : ℝ) * AVenhance.tau β Λ m + AVenhance.tau β Λ m / 2) ⊆
      Set.Icc ((AVenhance.lIdx β Λ m k : ℝ) * AVenhance.tauPP β Λ m -
          AVenhance.tauPP β Λ m / 2)
        ((AVenhance.lIdx β Λ m k : ℝ) * AVenhance.tauPP β Λ m +
          AVenhance.tauPP β Λ m / 2) := by
  let p := tauCellCount β Λ m
  let r := LIdxConsequences.tauCellHalfCount β Λ m
  have hp : p = 2 * r + 1 := by
    dsimp [p, r]
    exact LIdxConsequences.tauCellCount_eq_two_mul_half_add_one β Λ m
  have hτ : 0 < AVenhance.tau β Λ m := tau_pos hβ hβ' hΛ
  have hlarge : AVenhance.tauPP β Λ m = (p : ℝ) * AVenhance.tau β Λ m := by
    simpa [p] using tauPP_eq_cellCount_mul_tau (β := β) (Λ := Λ) hm
  have hp0 : 0 < (p : ℝ) := by
    rw [hp]
    positivity
  have hfloor : AVenhance.lIdx β Λ m k =
      Int.floor (((k : ℝ) + (r : ℝ)) / (p : ℝ)) := by
    unfold AVenhance.lIdx
    rw [hlarge]
    congr 1
    rw [hp]
    field_simp [ne_of_gt hτ, ne_of_gt hp0]
    push_cast
    ring
  let L := Int.floor (((k : ℝ) + (r : ℝ)) / (p : ℝ))
  have hlo : (L : ℝ) ≤ ((k : ℝ) + (r : ℝ)) / (p : ℝ) := by
    dsimp [L]
    exact Int.floor_le _
  have hhi : ((k : ℝ) + (r : ℝ)) / (p : ℝ) < (L : ℝ) + 1 := by
    dsimp [L]
    exact Int.lt_floor_add_one _
  rw [le_div_iff₀ hp0] at hlo
  rw [div_lt_iff₀ hp0] at hhi
  have hloInt : L * (p : ℤ) ≤ k + (r : ℤ) := by exact_mod_cast hlo
  have hhiInt : k + (r : ℤ) < (L + 1) * (p : ℤ) := by exact_mod_cast hhi
  have hrightInt : k - (r : ℤ) ≤ L * (p : ℤ) := by
    have hpInt : (p : ℤ) = 2 * (r : ℤ) + 1 := by exact_mod_cast hp
    have hhiInt' := hhiInt
    simp only [add_mul, one_mul] at hhiInt'
    omega
  have hloReal : (L : ℝ) * (p : ℝ) ≤ (k : ℝ) + (r : ℝ) := by exact_mod_cast hloInt
  have hrightReal : (k : ℝ) - (r : ℝ) ≤ (L : ℝ) * (p : ℝ) := by
    exact_mod_cast hrightInt
  intro t ht
  change ((k : ℝ) * AVenhance.tau β Λ m - AVenhance.tau β Λ m / 2 ≤ t ∧
      t ≤ (k : ℝ) * AVenhance.tau β Λ m + AVenhance.tau β Λ m / 2) at ht
  change ((AVenhance.lIdx β Λ m k : ℝ) * AVenhance.tauPP β Λ m -
      AVenhance.tauPP β Λ m / 2 ≤ t ∧
      t ≤ (AVenhance.lIdx β Λ m k : ℝ) * AVenhance.tauPP β Λ m +
        AVenhance.tauPP β Λ m / 2)
  rw [hfloor, hlarge]
  constructor
  · have hpcast : (p : ℝ) = 2 * (r : ℝ) + 1 := by exact_mod_cast hp
    nlinarith [mul_le_mul_of_nonneg_right hloReal hτ.le]
  · have hpcast : (p : ℝ) = 2 * (r : ℝ) + 1 := by exact_mod_cast hp
    nlinarith [mul_le_mul_of_nonneg_right hrightReal hτ.le]

end AVenhance.Infra.Ingredients
