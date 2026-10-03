/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.DyadicKernelInfinite

/-!
# The complete bilateral dyadic decomposition of the Hilbert kernel

At a fixed nonzero spatial point, all sufficiently low dyadic pieces vanish.
The existing one-sided telescoping identity therefore extends to the exact
sum over every integer scale in the paper's notation.
-/

@[expose] public section

open Function Set
open scoped BigOperators

namespace QuadraticCarleson


/-- A point beyond the outer support radius contributes no dyadic piece. -/
theorem dyadicPsi_eq_zero_of_zpow_le {j : ℤ} {t : ℝ}
    (ht : (2 : ℝ) ^ (j - 1) ≤ |t|) : dyadicPsi j t = 0 := by
  by_contra h
  exact (not_lt_of_ge ht) (dyadicPsi_support_subset j h).2

/-- Beyond the outer radius, the cutoff remaining in the telescoped
one-sided sum vanishes exactly. -/
theorem dyadicCutoff_lowerEndpoint_eq_zero {j : ℤ} {t : ℝ}
    (ht : (2 : ℝ) ^ (j - 1) ≤ |t|) :
    dyadicCutoff ((2⁻¹ : ℝ) ^ (j - 1) * t) = 0 := by
  apply dyadicCutoff_eq_zero
  rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2⁻¹) _)]
  have hm := mul_le_mul_of_nonneg_left ht
    (zpow_pos (by norm_num : (0 : ℝ) < 2⁻¹) (j - 1)).le
  have hid : (2⁻¹ : ℝ) ^ (j - 1) * (2 : ℝ) ^ (j - 1) = 1 := by
    rw [inv_zpow]
    exact inv_mul_cancel₀ (zpow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
  rw [hid] at hm
  exact (by norm_num : (1 / 2 : ℝ) ≤ 1).trans hm

/-- Every nonzero spatial point admits a lower scale at which the
telescoping cutoff vanishes and below which every dyadic piece is zero. -/
theorem exists_dyadicPsi_lower_cutoff {t : ℝ} (ht : t ≠ 0) :
    ∃ j₀ : ℤ, dyadicCutoff ((2⁻¹ : ℝ) ^ (j₀ - 1) * t) = 0 ∧
      ∀ j : ℤ, j < j₀ → dyadicPsi j t = 0 := by
  obtain ⟨n, hn⟩ := exists_mem_Ico_zpow (abs_pos.mpr ht)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, dyadicCutoff_lowerEndpoint_eq_zero (by simpa using hn.1), ?_⟩
  intro j hj
  apply dyadicPsi_eq_zero_of_zpow_le
  have hpow : (2 : ℝ) ^ (j - 1) ≤ (2 : ℝ) ^ n :=
    (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr (by omega)
  exact hpow.trans hn.1

/-- The exact dyadic decomposition of `1 / t` over all integer scales. -/
theorem hasSum_dyadicPsi {t : ℝ} (ht : t ≠ 0) :
    HasSum (fun j : ℤ ↦ dyadicPsi j t) (1 / t) := by
  obtain ⟨j₀, hcutoff, hzero⟩ := exists_dyadicPsi_lower_cutoff ht
  have hinj : Injective (fun n : ℕ ↦ j₀ + (n : ℤ)) := by
    intro a b hab
    dsimp only at hab
    omega
  have hout : ∀ j : ℤ, j ∉ range (fun n : ℕ ↦ j₀ + (n : ℤ)) →
      dyadicPsi j t = 0 := by
    intro j hj
    apply hzero
    by_contra h
    apply hj
    refine ⟨(j - j₀).toNat, ?_⟩
    dsimp only
    omega
  apply (hinj.hasSum_iff hout).mp
  simpa only [Function.comp_def, hcutoff, sub_zero] using
    hasSum_dyadicPsi_add_nat j₀ ht

/-- The paper's bilateral dyadic series is the Hilbert kernel away from zero. -/
theorem tsum_dyadicPsi {t : ℝ} (ht : t ≠ 0) :
    (∑' j : ℤ, dyadicPsi j t) = 1 / t :=
  (hasSum_dyadicPsi ht).tsum_eq


end QuadraticCarleson
