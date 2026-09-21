/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleGeometry
import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleLevelSet
import LeanPool.QuadraticCarleson.QuadraticCarleson.OscillatoryPacketSum
import LeanPool.QuadraticCarleson.QuadraticCarleson.StationaryPacketSum

/-!
# Pointwise lower bound for the negative-endpoint counterexample

This module assembles the exact off-support operator identity, the oscillatory
left tail, the stationary right tail, and the Bohr-set harmonic main term. The
only remaining numerical input is a single inequality saying that the two
proved errors fit inside half of the main-term lower bound.
-/

open Finset Set

namespace QuadraticCarleson


private theorem paperBohrIndex_toNat_le {N : ℕ} {k : ℤ}
    (hN : 20 ≤ N) (hk : k ∈ paperBohrIndices N) : k.toNat ≤ N := by
  have hkpos : 0 ≤ k := (paperBohrIndices_pos hN hk).le
  have hkcast : (k.toNat : ℝ) = k := by
    exact_mod_cast Int.toNat_of_nonneg hkpos
  have hkupper := (mem_paperBohrIndices.mp hk).2
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hreal : (k.toNat : ℝ) ≤ N := by
    rw [hkcast]
    linarith
  exact_mod_cast hreal

private theorem sum_Icc_split_at {N k : ℕ} (hk : k ≤ N) (f : ℕ → ℂ) :
    ∑ j ∈ Finset.Icc 1 N, f j =
      (∑ j ∈ Finset.Icc 1 k, f j) +
        ∑ j ∈ Finset.Icc (k + 1) N, f j := by
  rw [← Finset.sum_union]
  · apply Finset.sum_congr
    · ext j
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    · intro j hj
      rfl
  · simp only [Finset.disjoint_left, Finset.mem_Icc]
    omega

/-- The full normalized off-support packet sum splits exactly at the translate
index selected by the Bohr witness. -/
theorem counterexampleOffSupportSum_split
    {N : ℕ} {k : ℤ} (hN : 20 ≤ N) (hk : k ∈ paperBohrIndices N)
    (modulation x : ℝ) :
    (N : ℝ)⁻¹ • ∑ j ∈ Finset.Icc 1 N,
        offSupportKernelAction modulation (j : ℝ) (packetScale N j) x =
      (N : ℝ)⁻¹ • ∑ j ∈ Finset.Icc 1 k.toNat,
          offSupportKernelAction modulation (j : ℝ) (packetScale N j) x +
        (N : ℝ)⁻¹ • ∑ j ∈ Finset.Icc (k.toNat + 1) N,
          offSupportKernelAction modulation (j : ℝ) (packetScale N j) x := by
  rw [sum_Icc_split_at (paperBohrIndex_toNat_le hN hk), smul_add]

/-- A single error-budget inequality converts the proved packet estimates into
the genuine pointwise lower bound for the canonical lacunary operator.

The inequality is later discharged by the paper's choice
`A = c₀ log N`, with an explicit sufficiently small `c₀`. -/
theorem paperTranslatedBohrSet_pointwise_of_error_budget
    {N : ℕ} {L A c : ℝ}
    (hN : 100 ≤ N) (hA : 0 < A) (hLA : (2 : ℝ) ^ L = A)
    (hbudget : 14 * A / N + 28 * packetScale N 1 +
        128 * offSupportOscillatoryConstant / ((N : ℝ) * A ^ 2) ≤
          Real.log N / (4 * N) - counterexampleHeight c N) :
    ∀ x ∈ paperTranslatedBohrSet N L, ∃ n : ℕ,
      counterexampleHeight c N ≤
        ‖quadraticHilbertSchwartz ((2 : ℝ) ^ n)
          (counterexampleSchwartz N) x‖ := by
  intro x hx
  obtain ⟨k, n, hk, hnlo, hnhi, hbohr, hmain⟩ :=
    paperTranslatedBohrSet_phase_witness hN hx
  have hkn : (k, n) ∈ paperMainTermIndices N L :=
    mem_paperMainTermIndices.mpr ⟨hk, hnlo, hnhi⟩
  have hτ : x - k ∈ Set.Ico ((1 : ℝ) / 4) (1 / 2) := hbohr.1
  have hxform : (k : ℝ) + (x - k) = x := by ring
  have hoff : ∀ j ∈ Finset.Icc 1 N, x ∉ packetInterval N j := by
    intro j hj
    rw [← hxform]
    exact packetPoint_not_mem_packetInterval hN hk hτ hj
  let oscillatory : ℂ :=
    (N : ℝ)⁻¹ • ∑ j ∈ Finset.Icc 1 k.toNat,
      offSupportKernelAction ((2 : ℝ) ^ n) (j : ℝ) (packetScale N j) x
  let stationary : ℂ :=
    (N : ℝ)⁻¹ • ∑ j ∈ Finset.Icc (k.toNat + 1) N,
      offSupportKernelAction ((2 : ℝ) ^ n) (j : ℝ) (packetScale N j) x
  have hoperator :
      quadraticHilbertSchwartz ((2 : ℝ) ^ n) (counterexampleSchwartz N) x =
        oscillatory + stationary := by
    rw [quadraticHilbertSchwartz_counterexample_eq_offSupport_sum N _ x hoff,
      counterexampleOffSupportSum_split (by omega) hk]
  have hosc : ‖oscillatory‖ ≤
      128 * offSupportOscillatoryConstant / ((N : ℝ) * A ^ 2) := by
    simpa only [oscillatory, hxform] using
      paperOscillatoryPacketSum_norm_le hN hkn hA hLA hτ
  have hscale : packetScale N (k.toNat + 1) ≤ packetScale N 1 := by
    simpa using (stationary_packetScale_le_first
      (N := N) (k := (0 : ℤ)) (j := k.toNat + 1)
      (by simp))
  have hstationary :
      ‖harmonicPhaseSum N k.toNat ((2 ^ n : ℕ) : ℤ) (x - k)‖ -
          (14 * A / N + 28 * packetScale N (k.toNat + 1)) ≤
        ‖stationary‖ := by
    simpa only [stationary, hxform] using
      norm_stationaryPacketAction_ge_harmonicPhaseSum_sub_error
        hN hkn hLA hA hτ.1 hτ.2
  have hstationary' :
      Real.log N / (4 * N) -
          (14 * A / N + 28 * packetScale N 1) ≤ ‖stationary‖ := by
    nlinarith
  have hstationary_le_operator : ‖stationary‖ ≤
      ‖quadraticHilbertSchwartz ((2 : ℝ) ^ n) (counterexampleSchwartz N) x‖ +
        ‖oscillatory‖ := by
    rw [hoperator]
    calc
      ‖stationary‖ = ‖(oscillatory + stationary) - oscillatory‖ := by
        congr 1
        abel
      _ ≤ ‖oscillatory + stationary‖ + ‖oscillatory‖ := norm_sub_le _ _
  refine ⟨n, ?_⟩
  nlinarith

end QuadraticCarleson
