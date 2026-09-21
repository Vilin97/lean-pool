/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleMainTerm
import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleOperatorAction

/-!
# Spatial geometry of the negative-endpoint packets

An admissible point has the form `x = k + τ`, where `k` is one of the paper's
translate indices and `τ ∈ (1/4,1/2)`.  This file records the elementary
separation from all packet intervals, together with lower bounds that retain
the integer separation from the packet centre.
-/

open Finset MeasureTheory Set

namespace QuadraticCarleson


private theorem paperBohrIndex_cast_toNat {N : ℕ} {k : ℤ}
    (hN : 100 ≤ N) (hk : k ∈ paperBohrIndices N) :
    (k.toNat : ℝ) = k := by
  have hkpos : 0 < k := paperBohrIndices_pos (by omega) hk
  exact_mod_cast Int.toNat_of_nonneg hkpos.le

private theorem packetScale_lt_half {N j : ℕ} (hN : 100 ≤ N) (hj : 1 ≤ j) :
    packetScale N j < (1 / 2 : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  have hNj : 1 < N * j := by
    calc
      1 < N := by omega
      _ = N * 1 := by simp
      _ ≤ N * j := Nat.mul_le_mul_left N hj
  have hexp : -((N * j : ℕ) : ℤ) < (-1 : ℤ) := by omega
  have hpow : packetScale N j < (2 : ℝ) ^ (-1 : ℤ) := by
    unfold packetScale
    exact zpow_lt_zpow_right₀ (by norm_num) hexp
  norm_num at hpow ⊢
  exact hpow

/-- Distance to a packet on the left of the translate, retaining the integer
separation from its centre. -/
theorem packetPoint_abs_sub_left_ge
    {N : ℕ} {k : ℤ} {τ : ℝ} {j : ℕ}
    (hN : 100 ≤ N) (hk : k ∈ paperBohrIndices N)
    (hτ : τ ∈ Ico (1 / 4 : ℝ) (1 / 2 : ℝ)) (hj : j ≤ k.toNat) :
    ((k.toNat - j : ℕ) : ℝ) + 1 / 4 ≤
      |(k : ℝ) + τ - (j : ℝ)| := by
  have hkcast : (k.toNat : ℝ) = k := paperBohrIndex_cast_toNat hN hk
  rw [abs_of_nonneg]
  · rw [Nat.cast_sub hj, hkcast]
    linarith [hτ.1]
  · have hjR : (j : ℝ) ≤ k := by
      calc
        (j : ℝ) ≤ k.toNat := by exact_mod_cast hj
        _ = k := hkcast
    have hdiff : (0 : ℝ) ≤ (k.toNat - j : ℕ) := by positivity
    linarith [hτ.1, hjR]

/-- Distance to a packet on the right of the translate, retaining the integer
separation from its centre. -/
theorem packetPoint_abs_sub_right_ge
    {N : ℕ} {k : ℤ} {τ : ℝ} {j : ℕ}
    (hN : 100 ≤ N) (hk : k ∈ paperBohrIndices N)
    (hτ : τ ∈ Ico (1 / 4 : ℝ) (1 / 2 : ℝ))
    (hj : k.toNat + 1 ≤ j) :
    ((j - (k.toNat + 1) : ℕ) : ℝ) + 1 / 2 ≤
      |(k : ℝ) + τ - (j : ℝ)| := by
  have hkcast : (k.toNat : ℝ) = k := paperBohrIndex_cast_toNat hN hk
  rw [abs_of_nonpos]
  · rw [Nat.cast_sub hj, Nat.cast_add, hkcast]
    linarith [hτ.2]
  · have hjR : k + 1 ≤ (j : ℝ) := by
      calc
        k + 1 = (k.toNat : ℝ) + 1 := by rw [hkcast]
        _ ≤ (j : ℝ) := by exact_mod_cast hj
    have hdiff : (0 : ℝ) ≤ (j - (k.toNat + 1) : ℕ) := by positivity
    linarith [hτ.2, hjR]

/-- Equivalent right-hand estimate written with the full integer separation
from `k`, rather than separation from the next centre. -/
theorem packetPoint_abs_sub_right_ge' {N : ℕ} {k : ℤ} {τ : ℝ} {j : ℕ}
    (hN : 100 ≤ N) (hk : k ∈ paperBohrIndices N)
    (hτ : τ ∈ Ico (1 / 4 : ℝ) (1 / 2 : ℝ))
    (hj : k.toNat + 1 ≤ j) :
    ((j - k.toNat : ℕ) : ℝ) - 1 / 2 ≤
      |(k : ℝ) + τ - (j : ℝ)| := by
  have hkcast : (k.toNat : ℝ) = k := paperBohrIndex_cast_toNat hN hk
  have hjk : k.toNat ≤ j := by omega
  have h := packetPoint_abs_sub_right_ge hN hk hτ hj
  have hsub : ((j - k.toNat : ℕ) : ℝ) = (j : ℝ) - k := by
    rw [Nat.cast_sub hjk, hkcast]
  have hsubnext : ((j - (k.toNat + 1) : ℕ) : ℝ) = (j : ℝ) - k - 1 := by
    rw [Nat.cast_sub hj, Nat.cast_add, hkcast]
    norm_num
    ring
  rw [hsub]
  rw [hsubnext] at h
  linarith

/-- Every packet centre is at least a quarter away from an admissible point. -/
theorem packetPoint_abs_sub_ge_quarter
    {N : ℕ} {k : ℤ} {τ : ℝ} {j : ℕ}
    (hN : 100 ≤ N) (hk : k ∈ paperBohrIndices N)
    (hτ : τ ∈ Ico (1 / 4 : ℝ) (1 / 2 : ℝ)) :
    (1 / 4 : ℝ) ≤ |(k : ℝ) + τ - (j : ℝ)| := by
  by_cases hleft : j ≤ k.toNat
  · have h := packetPoint_abs_sub_left_ge hN hk hτ hleft
    have hnonneg : (0 : ℝ) ≤ ((k.toNat - j : ℕ) : ℝ) := by positivity
    linarith
  · have hright : k.toNat + 1 ≤ j := by omega
    have h := packetPoint_abs_sub_right_ge hN hk hτ hright
    linarith

/-- The admissible point is strictly farther from every packet centre than the
corresponding packet half-length. -/
theorem packetPoint_not_mem_packetInterval
    {N : ℕ} {k : ℤ} {τ : ℝ} {j : ℕ}
    (hN : 100 ≤ N) (hk : k ∈ paperBohrIndices N)
    (hτ : τ ∈ Ico (1 / 4 : ℝ) (1 / 2 : ℝ))
    (hj : j ∈ Finset.Icc 1 N) :
    (k : ℝ) + τ ∉ packetInterval N j := by
  have hjpos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hdist : (1 / 4 : ℝ) ≤ |(k : ℝ) + τ - (j : ℝ)| := by
    by_cases hleft : j ≤ k.toNat
    · have h := packetPoint_abs_sub_left_ge hN hk hτ hleft
      have hnonneg : (0 : ℝ) ≤ ((k.toNat - j : ℕ) : ℝ) := by positivity
      linarith
    · have hright : k.toNat + 1 ≤ j := by omega
      have h := packetPoint_abs_sub_right_ge hN hk hτ hright
      linarith
  have hscale : packetScale N j / 2 < (1 / 4 : ℝ) := by
    have hs := packetScale_lt_half hN hjpos
    linarith
  intro hx
  rw [packetInterval] at hx
  have habs : |(k : ℝ) + τ - (j : ℝ)| ≤ packetScale N j / 2 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  linarith

/-- Every admissible point lies off all packet intervals in the truncated
family. -/
theorem packetPoint_not_mem_any_packetInterval
    {N : ℕ} {k : ℤ} {τ : ℝ}
    (hN : 100 ≤ N) (hk : k ∈ paperBohrIndices N)
    (hτ : τ ∈ Ico (1 / 4 : ℝ) (1 / 2 : ℝ)) :
    ∀ j ∈ Finset.Icc 1 N, (k : ℝ) + τ ∉ packetInterval N j := by
  intro j hj
  exact packetPoint_not_mem_packetInterval hN hk hτ hj

/-- In particular, every wave packet vanishes at an admissible point. -/
theorem packetPoint_wavePacket_eq_zero
    {N : ℕ} {k : ℤ} {τ : ℝ} {j : ℕ}
    (hN : 100 ≤ N) (hk : k ∈ paperBohrIndices N)
    (hτ : τ ∈ Ico (1 / 4 : ℝ) (1 / 2 : ℝ))
    (hj : j ∈ Finset.Icc 1 N) :
    wavePacket (j : ℝ) (packetScale N j) ((k : ℝ) + τ) = 0 := by
  apply not_ne_iff.mp
  intro hne
  exact packetPoint_not_mem_packetInterval hN hk hτ hj
    (wavePacket_support_subset_packetInterval N j hne)

/-- The support formulation of the same off-packet statement. -/
theorem packetPoint_not_mem_wavePacket_support
    {N : ℕ} {k : ℤ} {τ : ℝ} {j : ℕ}
    (hN : 100 ≤ N) (hk : k ∈ paperBohrIndices N)
    (hτ : τ ∈ Ico (1 / 4 : ℝ) (1 / 2 : ℝ))
    (hj : j ∈ Finset.Icc 1 N) :
    (k : ℝ) + τ ∉ Function.support (wavePacket (j : ℝ) (packetScale N j)) := by
  intro hx
  exact packetPoint_not_mem_packetInterval hN hk hτ hj
    (wavePacket_support_subset_packetInterval N j hx)

end QuadraticCarleson
