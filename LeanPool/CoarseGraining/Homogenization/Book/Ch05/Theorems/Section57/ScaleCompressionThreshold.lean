/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ScaleCompression

/-! # Scale Compression Threshold -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Compression of the explicit bad-scale threshold

The quantitative tail theorem exposes three deterministic cutoffs.  This file
collapses them to a fixed polynomial in the selected denominator `Blead`, after
the final tail denominator is chosen as `2 * Blead`.
-/

noncomputable section

theorem pow_three_nat_mono {m n : ℕ} (hmn : m ≤ n) :
    (3 : ℝ) ^ m ≤ (3 : ℝ) ^ n :=
  pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hmn

theorem pow_three_natCeil_log_div_log_le_three_mul_self
    {x : ℝ} (hx : 1 ≤ x) :
    (3 : ℝ) ^ Nat.ceil (Real.log x / Real.log 3) ≤ 3 * x := by
  simpa [Real.rpow_natCast] using
    rpow_three_natCeil_log_div_log_le_three_mul (x := x) hx

theorem pow_three_nat_add (a b : ℕ) :
    (3 : ℝ) ^ (a + b) = (3 : ℝ) ^ a * (3 : ℝ) ^ b := by
  exact pow_add (3 : ℝ) a b

theorem pow_three_nat_add_five (a b c d e : ℕ) :
    (3 : ℝ) ^ (a + b + c + d + e) =
      (3 : ℝ) ^ a * (3 : ℝ) ^ b * (3 : ℝ) ^ c *
        (3 : ℝ) ^ d * (3 : ℝ) ^ e := by
  rw [show a + b + c + d + e = (((a + b) + c) + d) + e by omega]
  simp [pow_add, mul_assoc]

theorem pow_three_explicit_threshold_le_const_mul_Blead_four
    {M η Blead : ℝ} {R Qcut : ℕ}
    (hη : 0 < η) (hBlead : 1 ≤ Blead) :
    let Btail : ℝ := 2 * Blead
    let cgap : ℝ := Blead ^ (-η) - Btail ^ (-η)
    let ρgap : ℝ := (3 : ℝ) ^ η
    let Qpref : ℕ :=
      max (Nat.ceil (max 0 (Real.log M)))
        (max R (Nat.ceil ((2 * max 0 (-(Real.log cgap))) /
          Real.log ρgap)))
    let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
    let Q : ℕ := max Qpref (max Qlead Qcut)
    let Cgap : ℝ :=
      (2 * max 0 (-(Real.log (1 - (2 : ℝ) ^ (-η))))) /
        (η * Real.log 3)
    let C : ℝ :=
      18 * (3 : ℝ) ^ (Nat.ceil (max 0 (Real.log M)) + R + Qcut) *
        Real.exp (Real.log 3 * Cgap)
    (3 : ℝ) ^ Q * max 1 Btail ≤ C * Blead ^ (4 : ℕ) := by
  intro Btail cgap ρgap Qpref Qlead Q Cgap C
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hBlead_pos : 0 < Blead := lt_of_lt_of_le zero_lt_one hBlead
  have hBtail_eq : Btail = 2 * Blead := rfl
  have hBtail_ge_one : 1 ≤ Btail := by
    dsimp [Btail]
    nlinarith
  have hmaxBtail : max 1 Btail = Btail := max_eq_right hBtail_ge_one
  have hcgap_pos : 0 < cgap := by
    simpa [Btail, cgap] using
      gap_two_mul_rpow_pos (B := Blead) (η := η) hBlead_pos hη
  have hρgap_pos : 0 < ρgap := by
    dsimp [ρgap]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) η
  have hlogρ : Real.log ρgap = η * Real.log (3 : ℝ) := by
    dsimp [ρgap]
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
  have hlogρ_pos : 0 < Real.log ρgap := by
    rw [hlogρ]
    exact mul_pos hη hlog3
  let A : ℕ := Nat.ceil (max 0 (Real.log M))
  let G : ℕ :=
    Nat.ceil ((2 * max 0 (-(Real.log cgap))) / Real.log ρgap)
  have hQ_le : Q ≤ A + R + G + Qlead + Qcut := by
    dsimp [Q, Qpref, A, G]
    omega
  have hpowQ :
      (3 : ℝ) ^ Q ≤ (3 : ℝ) ^ (A + R + G + Qlead + Qcut) :=
    pow_three_nat_mono hQ_le
  have hlead :
      (3 : ℝ) ^ Qlead ≤ 3 * Blead := by
    simpa [Qlead] using
      pow_three_natCeil_log_div_log_le_three_mul_self hBlead
  have hgap_log :
      max 0 (-(Real.log cgap)) ≤
        η * Real.log Blead +
          max 0 (-(Real.log (1 - (2 : ℝ) ^ (-η)))) := by
    simpa [Btail, cgap] using
      max_zero_neg_log_gap_two_mul_le (B := Blead) (η := η) hBlead hη
  have hGarg_nonneg :
      0 ≤ (2 * max 0 (-(Real.log cgap))) / Real.log ρgap := by
    positivity
  have hGpow_raw :
      (3 : ℝ) ^ G ≤
        3 * Real.exp
          (Real.log (3 : ℝ) *
            ((2 * max 0 (-(Real.log cgap))) / Real.log ρgap)) := by
    simpa [G, Real.rpow_natCast] using
      rpow_three_natCeil_le_three_mul_exp hGarg_nonneg
  have hGarg_bound :
      (2 * max 0 (-(Real.log cgap))) / Real.log ρgap ≤
        2 * Real.log Blead / Real.log (3 : ℝ) + Cgap := by
    have hmul := mul_le_mul_of_nonneg_left hgap_log (by norm_num : (0 : ℝ) ≤ 2)
    rw [hlogρ]
    dsimp [Cgap]
    have hden_pos : 0 < η * Real.log (3 : ℝ) := mul_pos hη hlog3
    calc
      (2 * max 0 (-(Real.log cgap))) / (η * Real.log (3 : ℝ))
          ≤ (2 * (η * Real.log Blead +
              max 0 (-(Real.log (1 - (2 : ℝ) ^ (-η)))))) /
              (η * Real.log (3 : ℝ)) :=
            div_le_div_of_nonneg_right hmul hden_pos.le
      _ = 2 * Real.log Blead / Real.log (3 : ℝ) +
            (2 * max 0 (-(Real.log (1 - (2 : ℝ) ^ (-η))))) /
              (η * Real.log (3 : ℝ)) := by
            field_simp [hη.ne', hlog3.ne']
  have hGexp :
      Real.exp
          (Real.log (3 : ℝ) *
            ((2 * max 0 (-(Real.log cgap))) / Real.log ρgap)) ≤
        Real.exp (2 * Real.log Blead + Real.log (3 : ℝ) * Cgap) := by
    refine Real.exp_le_exp.mpr ?_
    calc
      Real.log (3 : ℝ) *
          ((2 * max 0 (-(Real.log cgap))) / Real.log ρgap)
          ≤ Real.log (3 : ℝ) *
              (2 * Real.log Blead / Real.log (3 : ℝ) + Cgap) :=
            mul_le_mul_of_nonneg_left hGarg_bound hlog3.le
      _ = 2 * Real.log Blead + Real.log (3 : ℝ) * Cgap := by
            field_simp [hlog3.ne']
  have hGpow :
      (3 : ℝ) ^ G ≤
        3 * Real.exp (Real.log (3 : ℝ) * Cgap) * Blead ^ (2 : ℕ) := by
    calc
      (3 : ℝ) ^ G
          ≤ 3 * Real.exp
              (Real.log (3 : ℝ) *
                ((2 * max 0 (-(Real.log cgap))) / Real.log ρgap)) :=
            hGpow_raw
      _ ≤ 3 * Real.exp (2 * Real.log Blead + Real.log (3 : ℝ) * Cgap) :=
            mul_le_mul_of_nonneg_left hGexp (by norm_num)
      _ = 3 * Real.exp (Real.log (3 : ℝ) * Cgap) * Blead ^ (2 : ℕ) := by
            rw [Real.exp_add]
            have hsq : Real.exp (2 * Real.log Blead) = Blead ^ (2 : ℕ) := by
              have hlogpow :
                  Real.log (Blead ^ (2 : ℝ)) = 2 * Real.log Blead :=
                Real.log_rpow hBlead_pos 2
              calc
                Real.exp (2 * Real.log Blead)
                    = Real.exp (Real.log (Blead ^ (2 : ℝ))) := by rw [hlogpow]
                _ = Blead ^ (2 : ℝ) :=
                    Real.exp_log (Real.rpow_pos_of_pos hBlead_pos 2)
                _ = Blead ^ (2 : ℕ) := Real.rpow_natCast Blead 2
            rw [hsq]
            ring
  have hconst_nonneg : 0 ≤ (3 : ℝ) ^ (A + R + Qcut) := by positivity
  have hG_nonneg : 0 ≤ (3 : ℝ) ^ G := by positivity
  have hlead_nonneg : 0 ≤ (3 : ℝ) ^ Qlead := by positivity
  have hpow_decomp :
      (3 : ℝ) ^ (A + R + G + Qlead + Qcut) =
        (3 : ℝ) ^ (A + R + Qcut) * (3 : ℝ) ^ G * (3 : ℝ) ^ Qlead := by
    rw [show A + R + G + Qlead + Qcut = (A + R + Qcut) + G + Qlead by omega]
    simp [pow_add, mul_assoc, mul_left_comm, mul_comm]
  calc
    (3 : ℝ) ^ Q * max 1 Btail
        ≤ (3 : ℝ) ^ (A + R + G + Qlead + Qcut) * max 1 Btail :=
          mul_le_mul_of_nonneg_right hpowQ (by positivity)
    _ = (3 : ℝ) ^ (A + R + Qcut) * (3 : ℝ) ^ G *
          (3 : ℝ) ^ Qlead * Btail := by rw [hpow_decomp, hmaxBtail]
    _ ≤ (3 : ℝ) ^ (A + R + Qcut) *
          (3 * Real.exp (Real.log (3 : ℝ) * Cgap) * Blead ^ (2 : ℕ)) *
          (3 * Blead) * Btail := by
          gcongr
    _ = C * Blead ^ (4 : ℕ) := by
          dsimp [C, Btail]
          ring

end

end Section57
end Ch05
end Book
end Homogenization
