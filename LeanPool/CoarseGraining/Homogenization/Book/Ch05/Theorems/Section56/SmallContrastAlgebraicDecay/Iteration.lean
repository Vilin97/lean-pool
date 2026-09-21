/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAlgebraicDecay.IterationConstants

/-! # Iteration -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open scoped BigOperators

noncomputable section

namespace SmallContrastAlgebraicDecay

/-!
# The pure algebraic decay theorem for the Section 5.6 recurrence
-/

theorem algebraic_decay_of_threeQuarter_recursion
    {L : ℕ} {θ α0 B : ℝ}
    (hL_pos : 0 < L) (hθ_pos : 0 < θ) (hθ_lt_one : θ < 1)
    (hα0_pos : 0 < α0) (hB_nonneg : 0 ≤ B) :
    ∃ α δ K : ℝ, 0 < α ∧ 0 < δ ∧ 0 < K ∧
      ∀ F : ℕ → ℝ,
        (∀ m, 0 ≤ F m) →
        (∀ m, F m ≤ δ) →
        (∀ m, 8 * L + 4 ≤ m →
          F m ≤ θ * F (m - L) + (F (threeQuarterScale m)) ^ (2 : ℕ) +
            B * Real.rpow (3 : ℝ) (-α0 * (m : ℝ))) →
        ∀ m, F m ≤ K * Real.rpow (3 : ℝ) (-α * (m : ℝ)) := by
  obtain ⟨α, hα_pos, hα_le_α0, hlam_lt_one⟩ :=
    exists_decay_rate_for_lag_contraction hL_pos hθ_pos hθ_lt_one hα0_pos
  let lam : ℝ := θ * Real.rpow (3 : ℝ) (α * (L : ℝ))
  have hlam_lt : lam < 1 := by simpa [lam] using hlam_lt_one
  have hlam_nonneg : 0 ≤ lam := by
    dsimp [lam]
    exact mul_nonneg hθ_pos.le (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  let ε : ℝ := (1 - lam) / 4
  have hε_pos : 0 < ε := by
    dsimp [ε]
    nlinarith
  have hbudget : lam + ε + ε ≤ 1 := by
    dsimp [ε]
    nlinarith
  let K : ℝ := max 1 (B / ε)
  have hK_pos : 0 < K := by
    dsimp [K]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hK_nonneg : 0 ≤ K := hK_pos.le
  have hB_le_epsK : B ≤ ε * K := by
    have hB_div_le : B / ε ≤ K := by
      dsimp [K]
      exact le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_left hB_div_le hε_pos.le
    field_simp [hε_pos.ne'] at hmul
    nlinarith
  let Aabs : ℝ := K / ε
  have hAabs_nonneg : 0 ≤ Aabs := by
    dsimp [Aabs]
    positivity
  obtain ⟨Cabs, hCabs_nonneg, hAbs⟩ :=
    exists_decay_absorption_const (β := α / 2) (A := Aabs)
      (by positivity) hAabs_nonneg
  let Nabs : ℕ := Nat.ceil Cabs
  let N : ℕ := max (8 * L + 4) (2 * Nabs)
  have hN_ge_base : 8 * L + 4 ≤ N := by
    dsimp [N]
    exact le_max_left _ _
  have hN_ge_abs2 : 2 * Nabs ≤ N := by
    dsimp [N]
    exact le_max_right _ _
  have hCabs_le_Nabs : Cabs ≤ (Nabs : ℝ) := by
    simpa [Nabs] using Nat.le_ceil Cabs
  let δ : ℝ := min 1 (K * Real.rpow (3 : ℝ) (-α * (N : ℝ)))
  have hdecay_pos : ∀ m : ℕ, 0 < Real.rpow (3 : ℝ) (-α * (m : ℝ)) := by
    intro m
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
  have hdecay_nonneg : ∀ m : ℕ, 0 ≤ Real.rpow (3 : ℝ) (-α * (m : ℝ)) := by
    intro m
    exact (hdecay_pos m).le
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min zero_lt_one (mul_pos hK_pos (hdecay_pos N))
  refine ⟨α, δ, K, hα_pos, hδ_pos, hK_pos, ?_⟩
  intro F hF_nonneg hF_small hrec
  let decay : ℕ → ℝ := fun m => Real.rpow (3 : ℝ) (-α * (m : ℝ))
  let source : ℕ → ℝ := fun m => B * Real.rpow (3 : ℝ) (-α0 * (m : ℝ))
  have hbase : ∀ m, m < N → F m ≤ K * decay m := by
    intro m hmN
    have hm_le_N : m ≤ N := le_of_lt hmN
    have hδ_le : δ ≤ K * decay N := by
      dsimp [δ]
      exact min_le_right _ _
    have hdecay_N_le_m : decay N ≤ decay m := by
      dsimp [decay]
      have hm_le_N_real : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm_le_N
      exact Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3) (by nlinarith)
    calc
      F m ≤ δ := hF_small m
      _ ≤ K * decay N := hδ_le
      _ ≤ K * decay m :=
        mul_le_mul_of_nonneg_left hdecay_N_le_m hK_nonneg
  have hq_lt : ∀ m, N ≤ m → threeQuarterScale m < m := by
    intro m hNm
    have hlarge : 8 * L + 4 ≤ m := hN_ge_base.trans hNm
    exact (lagged_scale_window hL_pos hlarge).1.trans
      (lagged_scale_window hL_pos hlarge).2.1
  have hshift_lt : ∀ m, N ≤ m → m - L < m := by
    intro m hNm
    have hlarge : 8 * L + 4 ≤ m := hN_ge_base.trans hNm
    exact (lagged_scale_window hL_pos hlarge).2.1
  have hrec_core :
      ∀ m, N ≤ m →
        F m ≤ θ * F (m - L) + (F (threeQuarterScale m)) ^ (2 : ℕ) + source m := by
    intro m hNm
    have hlarge : 8 * L + 4 ≤ m := hN_ge_base.trans hNm
    simpa [source] using hrec m hlarge
  have hshift :
      ∀ m, N ≤ m →
        θ * (K * decay (m - L)) ≤ lam * (K * decay m) := by
    intro m hNm
    have hlarge : 8 * L + 4 ≤ m := hN_ge_base.trans hNm
    have hL_le_m : L ≤ m := by omega
    have hcast_sub : ((m - L : ℕ) : ℝ) = (m : ℝ) - (L : ℝ) := by
      simpa using (Nat.cast_sub hL_le_m : ((m - L : ℕ) : ℝ) = (m : ℝ) - (L : ℝ))
    have hdecay_shift :
        decay (m - L) =
          decay m * Real.rpow (3 : ℝ) (α * (L : ℝ)) := by
      dsimp [decay]
      rw [hcast_sub]
      calc
        Real.rpow (3 : ℝ) (-α * ((m : ℝ) - (L : ℝ))) =
            Real.rpow (3 : ℝ) (-α * (m : ℝ) + α * (L : ℝ)) := by ring_nf
        _ = Real.rpow (3 : ℝ) (-α * (m : ℝ)) *
            Real.rpow (3 : ℝ) (α * (L : ℝ)) := by
              exact Real.rpow_add (by norm_num : (0 : ℝ) < 3)
                (-α * (m : ℝ)) (α * (L : ℝ))
    calc
      θ * (K * decay (m - L))
          = θ * (K * (decay m * Real.rpow (3 : ℝ) (α * (L : ℝ)))) := by
            rw [hdecay_shift]
      _ = (θ * Real.rpow (3 : ℝ) (α * (L : ℝ))) * (K * decay m) := by
            ring
      _ = lam * (K * decay m) := by
            rfl
      _ ≤ lam * (K * decay m) := le_rfl
  have hsource_bound :
      ∀ m, N ≤ m → source m ≤ ε * (K * decay m) := by
    intro m hNm
    have hdecay0_le : Real.rpow (3 : ℝ) (-α0 * (m : ℝ)) ≤ decay m := by
      dsimp [decay]
      exact Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3) (by nlinarith)
    calc
      source m = B * Real.rpow (3 : ℝ) (-α0 * (m : ℝ)) := rfl
      _ ≤ B * decay m := mul_le_mul_of_nonneg_left hdecay0_le hB_nonneg
      _ ≤ (ε * K) * decay m :=
          mul_le_mul_of_nonneg_right hB_le_epsK (hdecay_nonneg m)
      _ = ε * (K * decay m) := by ring
  have hquad :
      ∀ m, N ≤ m →
        (K * decay (threeQuarterScale m)) ^ (2 : ℕ) ≤ ε * (K * decay m) := by
    intro m hNm
    have hNabs_le_half : Nabs ≤ m / 2 := by
      have h2 : 2 * Nabs ≤ m := hN_ge_abs2.trans hNm
      have h2' : Nabs * 2 ≤ m := by simpa [mul_comm] using h2
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 h2'
    have hCabs_le_half : Cabs ≤ ((m / 2 : ℕ) : ℝ) :=
      hCabs_le_Nabs.trans (by exact_mod_cast hNabs_le_half)
    have hAbs_half :
        Aabs * Real.rpow (3 : ℝ) (-2 * (α / 2) * ((m / 2 : ℕ) : ℝ)) ≤ 1 / 4 :=
      hAbs hCabs_le_half
    have hK_decay_half_le_eps :
        K * decay (m / 2) ≤ ε := by
      have hrewrite :
          Real.rpow (3 : ℝ) (-2 * (α / 2) * ((m / 2 : ℕ) : ℝ)) =
            decay (m / 2) := by
        dsimp [decay]
        congr 1
        ring
      have hmain : (K / ε) * decay (m / 2) ≤ 1 / 4 := by
        rw [hrewrite] at hAbs_half
        simpa [Aabs] using hAbs_half
      have hmul := mul_le_mul_of_nonneg_left hmain hε_pos.le
      field_simp [hε_pos.ne'] at hmul
      nlinarith
    have hdecay_sq_le :
        (decay (threeQuarterScale m)) ^ (2 : ℕ) ≤ decay m * decay (m / 2) := by
      simpa [decay] using threeQuarterScale_decay_sq_le hα_pos.le m
    have htarget_nonneg : 0 ≤ K * decay m :=
      mul_nonneg hK_nonneg (hdecay_nonneg m)
    calc
      (K * decay (threeQuarterScale m)) ^ (2 : ℕ)
          = K ^ (2 : ℕ) * (decay (threeQuarterScale m)) ^ (2 : ℕ) := by
            ring
      _ ≤ K ^ (2 : ℕ) * (decay m * decay (m / 2)) :=
            mul_le_mul_of_nonneg_left hdecay_sq_le (sq_nonneg K)
      _ = K * decay m * (K * decay (m / 2)) := by ring
      _ ≤ K * decay m * ε := by
            exact mul_le_mul_of_nonneg_left hK_decay_half_le_eps htarget_nonneg
      _ = ε * (K * decay m) := by ring
  exact
    algebraic_decay_induction_core
      (F := F) (decay := decay) (source := source)
      (q := threeQuarterScale) (L := L) (N := N)
      (K := K) (θ := θ) (lam := lam) (ε := ε)
      hK_nonneg hθ_pos.le hdecay_nonneg hF_nonneg hbase hq_lt hshift_lt
      hrec_core hshift hquad hsource_bound hbudget

end SmallContrastAlgebraicDecay

end

end Section56
end Ch05
end Book
end Homogenization
