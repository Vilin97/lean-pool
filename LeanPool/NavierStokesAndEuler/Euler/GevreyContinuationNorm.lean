/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyMetricEstimate

@[expose] public section

/-! Actual complete-Sobolev control from a positive-radius finite Gevrey bound, for parabolic
  continuation. -/

noncomputable section

namespace EulerGevreyContinuationNorm

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse
  EulerJetProductBounds EulerH6Pressure EulerSobolevGevreyOperators EulerPacketWeights
    EulerGevreyMetricEstimate

/-- At every retained derivative order, the Gevrey weight is bounded below by one positive fixed-cutoff weight. -/
theorem weight_lower (ρ δ : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hδ1 : δ ≤ 1)
    (n N : ℕ) (hn : n ≤ N) : weight δ N ≤ weight ρ n := by
  have hρ : 0 ≤ ρ := hδ.le.trans hδρ
  have hp : δ^N ≤ ρ^n := (pow_le_pow_of_le_one hδ.le hδ1 hn).trans (pow_le_pow_left₀ hδ.le hδρ n)
  have hf : (n.factorial : ℝ) ≤ (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hn
  have hsq : (n.factorial : ℝ)^2 ≤ (N.factorial : ℝ)^2 := by
    nlinarith [show (0 : ℝ) ≤ (n.factorial : ℝ) from Nat.cast_nonneg _]
  exact div_le_div₀ (pow_nonneg hρ n) hp (by positivity) hsq

variable (period : ℝ) [Fact (0 < period)]

/-- Each actual derivative coordinate is bounded by its genuine homogeneous derivative-sum norm. -/
theorem word_le_level {s : ℕ} (u : SobolevSpace period s) (w : SobolevWord s) :
    ‖u.val w‖ ≤ levelNorm period (toJet period u) w.1.val := by
  rw [levelNorm_eq_words]
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin w.1.val → Fin 4)))
    (fun v _ => norm_nonneg ((toJet period u).word v)) (Finset.mem_univ w.2)
  rw [toJet_word period u (by have := w.1.isLt; omega) w.2] at h
  exact h

/-- Every derivative coordinate through the full energy order is contained in one retained external/base block. -/
theorem level_le_block {s : ℕ} (u : SobolevSpace period s) (N m : ℕ) (hm : m ≤ N+6) :
    levelNorm period (toJet period u) m ≤ blockNorm period (toJet period u) 6 (min m N) := by
  let n := min m N
  have hn : n ≤ m := Nat.min_le_left m N
  have hr : m-n ≤ 6 := by dsimp [n]; omega
  have he : n+(m-n) = m := Nat.add_sub_of_le hn
  have h := Finset.single_le_sum (s := Finset.range 7)
    (fun r _ => (levelNorm_nonneg (toJet period u) : 0 ≤ levelNorm period (toJet period u) (n+r)))
    (show m-n ∈ Finset.range 7 by exact Finset.mem_range.mpr (by omega))
  rw [he] at h
  exact h

/-- A finite actual Gevrey bound controls the complete energy-order Sobolev norm on every positive-radius interval. -/
theorem norm_le_weighted {s : ℕ} (N : ℕ) (hS : s ≤ N+6) (ρ δ : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hδ1 : δ ≤ 1) (u : SobolevSpace period s) :
    ‖u‖ ≤ weightedNorm period 6 N ρ u / weight δ N := by
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hw : 0 < weight δ N := weight_pos hδ N
  change ‖u.val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (weightedNorm_nonneg period 6 N ρ hρ u) hw.le)).mpr
  intro w
  have hm : w.1.val ≤ N+6 := (Nat.le_of_lt_succ w.1.isLt).trans hS
  let n := min w.1.val N
  have hn : n ≤ N := Nat.min_le_right w.1.val N
  have hc := (word_le_level period u w).trans (level_le_block period u N w.1.val hm)
  have hh := Finset.single_le_sum (s := Finset.range (N+1))
    (fun i _ => mul_nonneg (weight_pos hρ i).le (show 0 ≤ blockNorm period (toJet period u) 6 i
      from blockNorm_nonneg _))
    (show n ∈ Finset.range (N+1) by exact Finset.mem_range.mpr (by omega))
  have hle : weight δ N*‖u.val w‖ ≤ weightedNorm period 6 N ρ u := by
    calc
      _ ≤ weight ρ n*‖u.val w‖ := mul_le_mul_of_nonneg_right (weight_lower ρ δ hδ hδρ hδ1 n N hn)
        (norm_nonneg _)
      _ ≤ weight ρ n*blockNorm period (toJet period u) 6 n := mul_le_mul_of_nonneg_left hc
        (weight_pos hρ n).le
      _ ≤ _ := hh
  exact (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using hle)

/-- A metric Gevrey bound gives the actual finite-Sobolev state bound needed by the uniform local restart theorem. -/
theorem norm_le_metric {s : ℕ} (N : ℕ) (hN : N+6 ≤ s) (hS : s ≤ N+6) (ρ δ : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hδ1 : δ ≤ 1)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) (c : ℝ) (hc : 0 < c)
    (hK : ∀ v, c^2*‖v‖^2 ≤ inner ℝ (K v) v) :
    ‖u‖ ≤ metricAmplification c*energyNorm period N hN ρ K u / weight δ N := by
  exact (norm_le_weighted period N hS ρ δ hδ hδρ hδ1 u).trans
    (div_le_div_of_nonneg_right (weightedNorm_le_energy period N hN ρ (hδ.trans_le hδρ) K u c hc
      hK) (weight_pos hδ N).le)

end EulerGevreyContinuationNorm
