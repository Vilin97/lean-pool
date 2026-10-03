/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.FluxStructure
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.ChiM

/-! Pointwise finite support of the summed corrector in its mode index. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section3

open AVenhance

/-- Bounded window of integer indices that can support the time cutoff. -/
def ChiMSupport.xiMKIndexWindow {β : ℝ} (I : Ingredients β) (m : ℕ) (t : ℝ) :
    Set ℤ :=
  {k | (k : ℝ) ∈ Set.Icc
    (t / tau β I.Λ m - 5 / 4) (t / tau β I.Λ m + 5 / 4)}

theorem ChiMSupport.xiMKIndexWindow_finite {β : ℝ} (I : Ingredients β)
    {m : ℕ} (_hm : 1 ≤ m) (t : ℝ) : (ChiMSupport.xiMKIndexWindow I m t).Finite := by
  let τ := tau β I.Λ m
  let lo : ℤ := ⌈t / τ - 5 / 4⌉
  let hi : ℤ := ⌊t / τ + 5 / 4⌋
  have hfinite : (Set.Icc lo hi).Finite := Set.finite_Icc lo hi
  apply hfinite.subset
  intro k hk
  rcases hk with ⟨hlo, hhi⟩
  constructor
  · exact Int.ceil_le.mpr (by simpa [lo] using hlo)
  · exact Int.le_floor.mpr (by simpa [hi] using hhi)

/-- A nonzero `xiMK` index must lie in a real interval of length `5/2`. -/
theorem xiMK_index_mem_window {β : ℝ} (I : Ingredients β) {m : ℕ}
    (_hm : 1 ≤ m) (k : ℤ) (t : ℝ) (hxi : I.xiMK m k t ≠ 0) :
    k ∈ ChiMSupport.xiMKIndexWindow I m t := by
  have hτ : 0 < tau β I.Λ m := Infra.Ingredients.tau_pos
    I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
  let u := (t - (k : ℝ) * tau β I.Λ m) / tau β I.Λ m
  have hu : u ∈ Set.Icc (-(5 / 4 : ℝ)) (5 / 4) := by
    by_contra hout
    exact hxi (xiMK_eq_zero_outside I k t (by simpa [u] using hout))
  have hlo : (-(5 / 4 : ℝ)) * tau β I.Λ m ≤
      t - (k : ℝ) * tau β I.Λ m := (le_div_iff₀ hτ).mp hu.1
  have hhi : t - (k : ℝ) * tau β I.Λ m ≤
      (5 / 4 : ℝ) * tau β I.Λ m := (div_le_iff₀ hτ).mp hu.2
  change (k : ℝ) ∈ Set.Icc
    (t / tau β I.Λ m - 5 / 4) (t / tau β I.Λ m + 5 / 4)
  constructor
  · field_simp [ne_of_gt hτ]
    nlinarith
  · field_simp [ne_of_gt hτ]
    nlinarith

/-- At a fixed time, only finitely many terms occur in the `chiM` sum. -/
theorem xiMK_support_finite {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (t : ℝ) : {k : ℤ | I.xiMK m k t ≠ 0}.Finite := by
  apply (ChiMSupport.xiMKIndexWindow_finite I hm t).subset
  intro k hk
  exact xiMK_index_mem_window I hm k t hk

end AVenhance.Infra.Section3
