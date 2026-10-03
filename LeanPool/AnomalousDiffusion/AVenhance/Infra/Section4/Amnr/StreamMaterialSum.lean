/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.StreamMaterialRates

/-! Material jets of the actual locally finite stream increment. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Filter
open scoped Topology
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- Fine cutoffs have three possible indices on a fixed open time
neighborhood. This controls all differentiated stream sums. -/
theorem amnr_zeta_local_finite {β : ℝ} (I : AVenhance.Ingredients β) (m : ℕ) (t : ℝ) :
    ∃ s : Finset ℤ, s.card ≤ 3 ∧ ∀ u : ℝ,
      |u - t| < AVenhance.tau β I.Λ m / 8 → ∀ k : ℤ, k ∉ s → I.zetaMK m k u = 0 := by
  classical
  let τ := AVenhance.tau β I.Λ m
  have hτ : 0 < τ := I.tau_pos' m
  let a : ℤ := ⌊t / τ⌋
  refine ⟨Finset.Icc (a - 1) (a + 1), ?_, ?_⟩
  · simp only [Int.card_Icc]
    omega
  · intro u hu k hk
    by_contra hne
    have hsup : |u - (k : ℝ) * τ| ≤ 2 / 3 * τ := by
      have hmem : (u - (k : ℝ) * τ) / τ ∈ Set.Icc (-(2 / 3) : ℝ) (2 / 3) := by
        by_contra hnot
        apply hne
        have hh := I.zeta_le_ind ((u - (k : ℝ) * τ) / τ)
        rw [AVenhance.indIcc_eq_zero_of_not_mem hnot] at hh
        exact le_antisymm hh (I.zeta_nonneg _)
      have hh := abs_le.mpr hmem
      rw [abs_div, abs_of_pos hτ, div_le_iff₀ hτ] at hh
      exact hh
    have habs : |t - k * τ| < τ := by
      have htri := abs_add_le (t - u) (u - k * τ)
      have heq : t - k * τ = (t - u) + (u - k * τ) := by ring
      rw [← heq, abs_sub_comm t u] at htri
      linarith
    have hfloor : (a : ℝ) ≤ t / τ := Int.floor_le (t / τ)
    have hceil : t / τ < (a : ℝ) + 1 := Int.lt_floor_add_one (t / τ)
    have hdist := abs_lt.mp habs
    have htlo : (a : ℝ) * τ ≤ t := (le_div_iff₀ hτ).mp hfloor
    have hthi : t < ((a : ℝ) + 1) * τ := (div_lt_iff₀ hτ).mp hceil
    have hki : a - 1 ≤ k ∧ k ≤ a + 1 := by
      constructor
      · have : (a : ℝ) - 1 < (k : ℝ) := by nlinarith [hdist.2]
        have : a - 1 < k := by exact_mod_cast this
        omega
      · have : (k : ℝ) < (a : ℝ) + 2 := by nlinarith [hdist.1]
        have : k < a + 2 := by exact_mod_cast this
        omega
    exact hk (Finset.mem_Icc.mpr hki)

end AVenhance.Infra.Section4
