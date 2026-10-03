/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # RelativeError item 11: the scalar dissipation lower bound

If `e(t) + 2κ ∫_0^t D = N` on `[0,1]` and `D ≥ 4π² e` (Poincaré) with `D ≥ 0` continuous, then
`κ ∫_0^1 D ≥ min (1/4) (2π²κ) N`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace AVenhance.Infra.Section5.RelativeError

theorem dissipation_lower_scalar {κ N : ℝ} {e D : ℝ → ℝ} (hκ : 0 < κ) (hN : 0 ≤ N)
    (hD0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ D s) (hDc : ContinuousOn D (Icc (0 : ℝ) 1))
    (hid : ∀ t ∈ Icc (0 : ℝ) 1, e t + 2 * κ * ∫ s in (0 : ℝ)..t, D s = N)
    (hP : ∀ s ∈ Icc (0 : ℝ) 1, 4 * Real.pi ^ 2 * e s ≤ D s) :
    min (1 / 4) (2 * Real.pi ^ 2 * κ) * N ≤ κ * ∫ s in (0 : ℝ)..1, D s := by
  have hint : IntervalIntegrable D volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hDc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] D := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with s hs
    exact hD0 s ⟨hs.1.le, hs.2⟩
  have hmono (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ s in (0 : ℝ)..t, D s) ≤ ∫ s in (0 : ℝ)..1, D s :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 hnonneg hint
  by_cases hA : N / 4 ≤ κ * ∫ s in (0 : ℝ)..1, D s
  · calc min (1 / 4) (2 * Real.pi ^ 2 * κ) * N ≤ (1 / 4) * N :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hN
      _ = N / 4 := by ring
      _ ≤ _ := hA
  · rw [not_le] at hA
    have hlow (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : 2 * Real.pi ^ 2 * N ≤ D s := by
      have h1 := hid s hs
      have h2 := hmono s hs
      have h3 : N / 2 ≤ e s := by nlinarith
      have h4 := hP s hs
      nlinarith [Real.pi_pos, sq_nonneg Real.pi]
    have hI : (∫ _ in (0 : ℝ)..1, 2 * Real.pi ^ 2 * N) ≤ ∫ s in (0 : ℝ)..1, D s :=
      intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const hint hlow
    rw [intervalIntegral.integral_const, smul_eq_mul] at hI
    have h5 : 2 * Real.pi ^ 2 * κ * N ≤ κ * ∫ s in (0 : ℝ)..1, D s := by
      have := mul_le_mul_of_nonneg_left (by simpa using hI : 2 * Real.pi ^ 2 * N ≤ _) hκ.le
      linarith
    calc min (1 / 4) (2 * Real.pi ^ 2 * κ) * N ≤ (2 * Real.pi ^ 2 * κ) * N :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hN
      _ ≤ _ := h5

end AVenhance.Infra.Section5.RelativeError
