/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleMainTerm
import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleOperatorAction
import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleStationaryMain

/-!
# Stationary packet sum

The packets to the right of a translate are off support at `k + τ`, and their
kernel actions can be replaced by their finite phase main terms. This file
keeps the dyadic window and its resulting geometric decay explicit.
-/

open Finset Set

namespace QuadraticCarleson


private theorem geom_half_sum_le_two (m : ℕ) :
    ∑ i ∈ Finset.range m, ((1 : ℝ) / 2) ^ i ≤ 2 := by
  have hstrong : ∀ m : ℕ,
      ∑ i ∈ Finset.range m, ((1 : ℝ) / 2) ^ i ≤
        2 - 2 * ((1 : ℝ) / 2) ^ m := by
    intro q
    induction q with
    | zero => norm_num
    | succ q ih =>
        rw [Finset.sum_range_succ, pow_succ]
        nlinarith
  exact hstrong m |>.trans (by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) m])

/-- At a right-hand stationary packet, `k + τ` is strictly to the left of the
packet. -/
theorem stationary_point_not_mem_packetInterval {N : ℕ} {k : ℤ} {τ : ℝ}
    (hN : 0 < N) (hk : 0 ≤ k) (hτ : τ ≤ 1 / 2) {j : ℕ}
    (hj : k.toNat + 1 ≤ j) :
    (k : ℝ) + τ ∉ packetInterval N j := by
  rw [packetInterval]
  intro hx
  have hkNat : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
  have hkReal : (k.toNat : ℝ) = k := by exact_mod_cast hkNat
  have hjpos : 0 < j := by omega
  have ht : packetScale N j < 1 := packetScale_lt_one hN hjpos
  have hjReal : (k : ℝ) + 1 ≤ j := by
    rw [← hkReal]
    exact_mod_cast hj
  linarith [hx.1, ht]

/-- The separation in the stationary window gives a uniform reciprocal
denominator bound. -/
theorem stationary_packet_reciprocal_le {N : ℕ} {k : ℤ} {τ : ℝ}
    (hk : 0 ≤ k) (hτ : τ ≤ 1 / 2) {j : ℕ}
    (hj : k.toNat + 1 ≤ j) :
    packetScale N j / |((k : ℝ) + τ) - j| ^ 2 ≤ 4 * packetScale N j := by
  have hkNat : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
  have hkReal : (k.toNat : ℝ) = k := by exact_mod_cast hkNat
  have hjReal : (k : ℝ) + 1 ≤ j := by
    rw [← hkReal]
    exact_mod_cast hj
  have hdist : (1 : ℝ) / 2 ≤ |((k : ℝ) + τ) - j| := by
    rw [abs_of_nonpos]
    · linarith
    · linarith
  have hsq : (1 : ℝ) / 4 ≤ |((k : ℝ) + τ) - j| ^ 2 := by nlinarith
  have hpos : 0 < |((k : ℝ) + τ) - j| ^ 2 := by positivity
  apply (div_le_iff₀ hpos).mpr
  nlinarith [packetScale_pos N j]

/-- Packet scales decrease along the right-hand stationary tail. -/
theorem stationary_packetScale_le_first {N : ℕ} {k : ℤ} {j : ℕ}
    (hj : k.toNat + 1 ≤ j) :
    packetScale N j ≤ packetScale N (k.toNat + 1) := by
  unfold packetScale
  apply zpow_le_zpow_right₀ (by norm_num)
  have hNj : N * (k.toNat + 1) ≤ N * j := Nat.mul_le_mul_left N hj
  have hNj' : (N * (k.toNat + 1) : ℤ) ≤ (N * j : ℤ) := by exact_mod_cast hNj
  omega

/-- The upper edge of the exact exponent window supplies the geometric
decay of the modulation-scale errors to the right of `k`. -/
theorem stationary_modulation_scale_le {N n : ℕ} {L A : ℝ} {k : ℤ}
    (hN : 0 < N) (hk : 0 ≤ k)
    (hn : (n : ℝ) < (N : ℝ) * k + L + N)
    (hA : (2 : ℝ) ^ L = A) {j : ℕ}
    (hj : k.toNat + 1 ≤ j) :
    (2 ^ n : ℝ) * packetScale N j ≤
      A * ((1 : ℝ) / 2) ^ (j - (k.toNat + 1)) := by
  have hkNat : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
  have hkReal : (k.toNat : ℝ) = k := by exact_mod_cast hkNat
  let d : ℕ := j - (k.toNat + 1)
  have hjdecomp : j = k.toNat + 1 + d := by
    dsimp [d]
    omega
  have hNd : (d : ℝ) ≤ (N : ℝ) * d := by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hexp : (n : ℝ) - (N * j : ℕ) ≤ L - d := by
    rw [hjdecomp]
    push_cast
    rw [hkReal]
    nlinarith
  calc
    (2 ^ n : ℝ) * packetScale N j =
        (2 : ℝ) ^ ((n : ℝ) - (N * j : ℕ)) := by
      rw [packetScale, ← Real.rpow_natCast, ← Real.rpow_intCast]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      push_cast
      ring
    _ ≤ (2 : ℝ) ^ (L - d) := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = A * ((1 : ℝ) / 2) ^ d := by
      rw [← hA, ← Real.rpow_natCast, Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
        div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [Real.rpow_neg_eq_inv_rpow]
      norm_num

/-- Summing the preceding dyadic decay costs only the geometric constant two. -/
theorem stationary_modulation_scale_sum_le {N n : ℕ} {L A : ℝ} {k : ℤ}
    (hN : 0 < N) (hk : 0 ≤ k)
    (hn : (n : ℝ) < (N : ℝ) * k + L + N)
    (hA : (2 : ℝ) ^ L = A) (hApos : 0 < A) :
    ∑ j ∈ Finset.Icc (k.toNat + 1) N,
      (2 ^ n : ℝ) * packetScale N j ≤ 2 * A := by
  let s := Finset.Icc (k.toNat + 1) N
  let e : ℕ → ℕ := fun j ↦ j - (k.toNat + 1)
  have hstart : 1 ≤ k.toNat + 1 := by omega
  have heinj : Set.InjOn e s := by
    intro a ha b hb hab
    dsimp [e] at hab
    have ha' := (Finset.mem_Icc.mp ha).1
    have hb' := (Finset.mem_Icc.mp hb).1
    omega
  have himage : Finset.image e s ⊆ Finset.range N := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    have hj' := Finset.mem_Icc.mp hj
    simp only [Finset.mem_range]
    dsimp [e]
    omega
  calc
    ∑ j ∈ s, (2 ^ n : ℝ) * packetScale N j ≤
        ∑ j ∈ s, A * ((1 : ℝ) / 2) ^ e j := by
      apply Finset.sum_le_sum
      intro j hj
      exact stationary_modulation_scale_le hN hk hn hA (Finset.mem_Icc.mp hj).1
    _ ≤ ∑ d ∈ Finset.range N, A * ((1 : ℝ) / 2) ^ d := by
      apply Finset.sum_le_sum_of_injOn e heinj himage
      · intro j hj
        exact le_rfl
      · intro d hd hnot
        positivity
    _ = A * ∑ d ∈ Finset.range N, ((1 : ℝ) / 2) ^ d := by
      rw [Finset.mul_sum]
    _ ≤ A * 2 := by gcongr; exact geom_half_sum_le_two N
    _ = 2 * A := by ring

/-- The packet-scale tail is at most one first packet-scale after the outer
normalization. -/
theorem stationary_packetScale_sum_le {N : ℕ} {k : ℤ}
    (hN : 0 < N) :
    ∑ j ∈ Finset.Icc (k.toNat + 1) N, packetScale N j ≤
      (N : ℝ) * packetScale N (k.toNat + 1) := by
  let s := Finset.Icc (k.toNat + 1) N
  calc
    ∑ j ∈ s, packetScale N j ≤ ∑ _j ∈ s, packetScale N (k.toNat + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact stationary_packetScale_le_first (Finset.mem_Icc.mp hj).1
    _ = (s.card : ℝ) * packetScale N (k.toNat + 1) := by simp
    _ ≤ (N : ℝ) * packetScale N (k.toNat + 1) := by
      apply mul_le_mul_of_nonneg_right
      · rw [Nat.cast_le]
        simp only [s, Nat.card_Icc]
        omega
      · exact (packetScale_pos N _).le

/-- The normalized right-hand stationary packet actions differ from their
kernel main terms by `O(A/N)` plus the first (hence tiny) packet scale. -/
theorem stationaryPacketSum_sub_kernelMain_le {N n : ℕ} {L A τ : ℝ} {k : ℤ}
    (hN : 100 ≤ N) (hkn : (k, n) ∈ paperMainTermIndices N L)
    (hA : (2 : ℝ) ^ L = A) (hApos : 0 < A)
    (_hτ0 : 1 / 4 ≤ τ) (hτ1 : τ < 1 / 2) :
    ‖(N : ℝ)⁻¹ • (∑ j ∈ Finset.Icc (k.toNat + 1) N,
        offSupportKernelAction (2 ^ n : ℝ) (j : ℝ) (packetScale N j) ((k : ℝ) + τ) ) -
      (N : ℝ)⁻¹ • (∑ j ∈ Finset.Icc (k.toNat + 1) N,
        phase ((2 ^ n : ℝ) * (((k : ℝ) + τ) - j) ^ 2) /
          (((k : ℝ) + τ - j : ℝ) : ℂ))‖ ≤
      14 * A / N + 28 * packetScale N (k.toNat + 1) := by
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hkpos : 0 < k := paperBohrIndices_pos (by omega)
    (mem_paperMainTermIndices.mp hkn).1
  have hk : 0 ≤ k := hkpos.le
  have hn := (mem_paperMainTermIndices.mp hkn).2.2
  have hτle : τ ≤ 1 / 2 := hτ1.le
  let s := Finset.Icc (k.toNat + 1) N
  have herr : ∀ j ∈ s,
      ‖offSupportKernelAction (2 ^ n : ℝ) (j : ℝ) (packetScale N j) ((k : ℝ) + τ) -
          phase ((2 ^ n : ℝ) * (((k : ℝ) + τ) - j) ^ 2) /
            (((k : ℝ) + τ - j : ℝ) : ℂ)‖ ≤
        7 * ((2 ^ n : ℝ) * packetScale N j + 4 * packetScale N j) := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have hx := stationary_point_not_mem_packetInterval hNpos hk hτle hj'.1
    calc
      _ ≤ (7 : ℝ) * max (|(2 ^ n : ℝ)| * packetScale N j)
          (packetScale N j / |((k : ℝ) + τ) - j| ^ 2) :=
        offSupportKernelAction_sub_main_le (packetScale_pos N j) hx
      _ ≤ (7 : ℝ) * ((2 ^ n : ℝ) * packetScale N j + 4 * packetScale N j) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply max_le
        · rw [abs_of_nonneg (pow_nonneg (by norm_num) n)]
          exact le_add_of_nonneg_right (show 0 ≤ (4 : ℝ) * packetScale N j by
            exact mul_nonneg (by norm_num) (packetScale_pos N j).le)
        · exact (stationary_packet_reciprocal_le hk hτle hj'.1).trans
            (le_add_of_nonneg_left (mul_nonneg (pow_nonneg (by norm_num) n)
              (packetScale_pos N j).le))
  have hsum : ‖∑ j ∈ s,
      (offSupportKernelAction (2 ^ n : ℝ) (j : ℝ) (packetScale N j) ((k : ℝ) + τ) -
        phase ((2 ^ n : ℝ) * (((k : ℝ) + τ) - j) ^ 2) /
          (((k : ℝ) + τ - j : ℝ) : ℂ))‖ ≤
      (7 : ℝ) * (2 * A + 4 * (N : ℝ) * packetScale N (k.toNat + 1)) := by
    calc
      _ ≤ ∑ j ∈ s, ‖(offSupportKernelAction (2 ^ n : ℝ) (j : ℝ) (packetScale N j)
          ((k : ℝ) + τ) - phase ((2 ^ n : ℝ) * (((k : ℝ) + τ) - j) ^ 2) /
            (((k : ℝ) + τ - j : ℝ) : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ s, (7 : ℝ) * ((2 ^ n : ℝ) * packetScale N j + 4 * packetScale N j) :=
        Finset.sum_le_sum herr
      _ = (7 : ℝ) * (∑ j ∈ s, (2 ^ n : ℝ) * packetScale N j +
          4 * ∑ j ∈ s, packetScale N j) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
        have hfour : (∑ j ∈ s, 4 * packetScale N j) =
            4 * ∑ j ∈ s, packetScale N j := by rw [Finset.mul_sum]
        rw [hfour]
      _ ≤ (7 : ℝ) * (2 * A + 4 * (N : ℝ) * packetScale N (k.toNat + 1)) := by
        have hmod : ∑ j ∈ s, (2 ^ n : ℝ) * packetScale N j ≤ 2 * A := by
          simpa only [s] using stationary_modulation_scale_sum_le hNpos hk hn hA hApos
        have hscale : ∑ j ∈ s, packetScale N j ≤
            (N : ℝ) * packetScale N (k.toNat + 1) := by
          simpa only [s] using stationary_packetScale_sum_le hNpos
        nlinarith
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hNr.le)]
  calc
    _ ≤ (N : ℝ)⁻¹ * ((7 : ℝ) * (2 * A + 4 * (N : ℝ) * packetScale N (k.toNat + 1))) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNr.le)
    _ = 14 * A / N + 28 * packetScale N (k.toNat + 1) := by
      field_simp
      ring

/-- In the stationary window the normalized action retains the norm of the
harmonic phase main term up to the explicit packet error. This is the form
used when transferring the main-term lower bound to the operator. -/
theorem norm_stationaryPacketAction_ge_harmonicPhaseSum_sub_error
    {N n : ℕ} {L A τ : ℝ} {k : ℤ}
    (hN : 100 ≤ N) (hkn : (k, n) ∈ paperMainTermIndices N L)
    (hA : (2 : ℝ) ^ L = A) (hApos : 0 < A)
    (hτ0 : 1 / 4 ≤ τ) (hτ1 : τ < 1 / 2) :
    ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.Icc (k.toNat + 1) N,
        offSupportKernelAction (2 ^ n : ℝ) (j : ℝ) (packetScale N j) ((k : ℝ) + τ)‖ ≥
      ‖harmonicPhaseSum N k.toNat ((2 ^ n : ℕ) : ℤ) τ‖ -
        (14 * A / N + 28 * packetScale N (k.toNat + 1)) := by
  let S : ℂ := (N : ℝ)⁻¹ • ∑ j ∈ Finset.Icc (k.toNat + 1) N,
    offSupportKernelAction (2 ^ n : ℝ) (j : ℝ) (packetScale N j) ((k : ℝ) + τ)
  let M : ℂ := (N : ℝ)⁻¹ • ∑ j ∈ Finset.Icc (k.toNat + 1) N,
    phase ((2 ^ n : ℝ) * (((k : ℝ) + τ) - j) ^ 2) /
      (((k : ℝ) + τ - j : ℝ) : ℂ)
  have herr : ‖S - M‖ ≤ 14 * A / N + 28 * packetScale N (k.toNat + 1) := by
    exact stationaryPacketSum_sub_kernelMain_le hN hkn hA hApos hτ0 hτ1
  have hM_eq : M = (1 / (N : ℂ)) * ∑ j ∈ Finset.Icc (k.toNat + 1) N,
      phase ((2 ^ n : ℝ) * (((k : ℝ) + τ) - j) ^ 2) /
        (((k : ℝ) + τ - j : ℝ) : ℂ) := by
    dsimp [M]
    rw [Complex.ofReal_inv, one_div]
    rfl
  have hMnorm : ‖M‖ =
      ‖harmonicPhaseSum N k.toNat ((2 ^ n : ℕ) : ℤ) τ‖ := by
    rw [hM_eq]
    convert norm_stationaryKernelMain_eq_harmonicPhaseSum hN hkn
      (x := (k : ℝ) + τ) using 1
    all_goals ring_nf
  have hbasic : ‖M‖ - ‖S‖ ≤ ‖S - M‖ := by
    simpa only [norm_sub_rev] using norm_sub_norm_le M S
  change ‖S‖ ≥ _
  rw [hMnorm] at hbasic
  linarith

end QuadraticCarleson
