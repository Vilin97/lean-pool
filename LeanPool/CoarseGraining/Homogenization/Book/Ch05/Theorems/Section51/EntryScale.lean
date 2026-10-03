/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section55.AnnealedConvergence

/-! # Entry Scale -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section51

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# Entry-scale arithmetic for Theorem `t.annealed.convergence`

The lemmas in this file are pure scale bookkeeping: they show that the
manuscript two-ceiling scale with a sufficiently large universal constant
dominates the fixed perturbative entry, shifted-moment tail, and algebraic
burn-in scales.
-/

theorem widetildeThetaAtScale_nonneg
    {d : ℕ} [NeZero d] (P : Ch04.RestrictionCoeffLaw d)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℤ) :
    0 ≤ widetildeThetaAtScale P m hP4 := by
  unfold widetildeThetaAtScale Ch04.widetildeThetaAtScale
  exact mul_nonneg
    (Ch04.LambdaMomentAtScale_nonneg P m hP4.xi hP4.sUpper_pos)
    (Ch04.lambdaInvMomentAtScale_nonneg P m hP4.xi hP4.sLower_pos)

theorem log_two_add_ge_half {T : ℝ} (hT : 0 ≤ T) :
    (1 / 2 : ℝ) ≤ Real.log (2 + T) := by
  have hlog_two_le : Real.log (2 : ℝ) ≤ Real.log (2 + T) :=
    Real.log_le_log (by norm_num)
      (by simpa using add_le_add_left hT (2 : ℝ))
  have hhalf_le_log_two : (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) := by
    linarith [Real.log_two_gt_d9]
  exact hhalf_le_log_two.trans hlog_two_le

theorem log_two_add_nonneg {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ Real.log (2 + T) := by
  exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (log_two_add_ge_half hT)

theorem natCeil_le_add_one {x : ℝ} (hx : 0 ≤ x) :
    (Nat.ceil x : ℝ) ≤ x + 1 :=
  (Nat.ceil_lt_add_one hx).le

theorem natCeil_add_nat_le_natCeil_mul_logSq
    {A C T : ℝ} {R : ℕ}
    (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hC : A + 4 * ((R : ℝ) + 1) ≤ C) :
    Nat.ceil (A * (Real.log (2 + T)) ^ (2 : ℕ)) + R ≤
      Nat.ceil (C * (Real.log (2 + T)) ^ (2 : ℕ)) := by
  let L : ℝ := Real.log (2 + T)
  have hL_half : (1 / 2 : ℝ) ≤ L := by
    simpa [L] using log_two_add_ge_half hT
  have hLsq_nonneg : 0 ≤ L ^ (2 : ℕ) := sq_nonneg L
  have hone_le_four_Lsq : (1 : ℝ) ≤ 4 * L ^ (2 : ℕ) := by
    have hL_nonneg : 0 ≤ L := le_trans (by norm_num) hL_half
    have hsq : (1 / 2 : ℝ) * (1 / 2 : ℝ) ≤ L * L :=
      mul_le_mul hL_half hL_half (by norm_num) hL_nonneg
    calc
      (1 : ℝ) = 4 * ((1 / 2 : ℝ) * (1 / 2 : ℝ)) := by norm_num
      _ ≤ 4 * (L * L) := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 4 * L ^ (2 : ℕ) := by ring
  have hx_nonneg : 0 ≤ A * L ^ (2 : ℕ) :=
    mul_nonneg hA hLsq_nonneg
  have hceil_left :
      (Nat.ceil (A * L ^ (2 : ℕ)) : ℝ) ≤ A * L ^ (2 : ℕ) + 1 :=
    natCeil_le_add_one hx_nonneg
  have hleft_real :
      (Nat.ceil (A * L ^ (2 : ℕ)) + R : ℝ) ≤
        C * L ^ (2 : ℕ) := by
    have hRplus :
        ((R : ℝ) + 1) ≤ 4 * ((R : ℝ) + 1) * L ^ (2 : ℕ) := by
      have hR1_nonneg : 0 ≤ (R : ℝ) + 1 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hone_le_four_Lsq hR1_nonneg
      calc
        (R : ℝ) + 1 = ((R : ℝ) + 1) * 1 := by ring
        _ ≤ ((R : ℝ) + 1) * (4 * L ^ (2 : ℕ)) := hmul
        _ = 4 * ((R : ℝ) + 1) * L ^ (2 : ℕ) := by ring
    calc
      (Nat.ceil (A * L ^ (2 : ℕ)) + R : ℝ)
          = (Nat.ceil (A * L ^ (2 : ℕ)) : ℝ) + (R : ℝ) := by norm_num
      _ ≤ A * L ^ (2 : ℕ) + ((R : ℝ) + 1) := by
            calc
              (Nat.ceil (A * L ^ (2 : ℕ)) : ℝ) + (R : ℝ)
                  ≤ (A * L ^ (2 : ℕ) + 1) + (R : ℝ) :=
                    add_le_add_left hceil_left (R : ℝ)
              _ = A * L ^ (2 : ℕ) + ((R : ℝ) + 1) := by ring
      _ ≤ A * L ^ (2 : ℕ) +
            4 * ((R : ℝ) + 1) * L ^ (2 : ℕ) :=
            add_le_add_right hRplus (A * L ^ (2 : ℕ))
      _ = (A + 4 * ((R : ℝ) + 1)) * L ^ (2 : ℕ) := by ring
      _ ≤ C * L ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_right hC hLsq_nonneg
  have hceil_right :
      C * L ^ (2 : ℕ) ≤
        (Nat.ceil (C * L ^ (2 : ℕ)) : ℝ) := Nat.le_ceil _
  exact_mod_cast hleft_real.trans hceil_right

theorem natCeil_two_log_terms_le_natCeil_large_log
    {Acoef Aarg Bcoef Barg C xi T : ℝ}
    (hT : 0 ≤ T) (hxi : 1 ≤ xi)
    (hAcoef : 0 ≤ Acoef) (hAarg : 0 ≤ Aarg)
    (hBcoef : 0 ≤ Bcoef) (hBarg : 0 ≤ Barg)
    (hAarg_le_C : Aarg ≤ C) (hBarg_le_C : Barg ≤ C)
    (hsum_le_C : Acoef + Bcoef + 4 ≤ C) :
    Nat.ceil (Acoef * xi * Real.log (2 + Aarg * xi * T)) +
        Nat.ceil (Bcoef * Real.log (2 + Barg * T)) ≤
      Nat.ceil (C * xi * Real.log (2 + C * xi * T)) := by
  have hxi_nonneg : 0 ≤ xi := le_trans zero_le_one hxi
  have hC_nonneg : 0 ≤ C := by
    have hsum_nonneg : 0 ≤ Acoef + Bcoef + 4 := by positivity
    exact hsum_nonneg.trans hsum_le_C
  let L : ℝ := Real.log (2 + C * xi * T)
  have hargC_ge_one : 1 ≤ 2 + C * xi * T := by
    have hprod : 0 ≤ C * xi * T := by positivity
    exact le_trans (by norm_num : (1 : ℝ) ≤ 2)
      (by simpa using add_le_add_left hprod (2 : ℝ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg hargC_ge_one
  have hL_half : (1 / 2 : ℝ) ≤ L := by
    dsimp [L]
    exact log_two_add_ge_half (by positivity : 0 ≤ C * xi * T)
  have hAarg_arg :
      2 + Aarg * xi * T ≤ 2 + C * xi * T := by
    have hmul := mul_le_mul_of_nonneg_right hAarg_le_C
      (by positivity : 0 ≤ xi * T)
    calc
      2 + Aarg * xi * T = 2 + Aarg * (xi * T) := by ring
      _ = Aarg * (xi * T) + 2 := by ring
      _ ≤ C * (xi * T) + 2 := add_le_add_left hmul 2
      _ = 2 + C * (xi * T) := by ring
      _ = 2 + C * xi * T := by ring
  have hBarg_arg :
      2 + Barg * T ≤ 2 + C * xi * T := by
    have hBarg_le_Cxi : Barg ≤ C * xi := by
      have hmul := mul_le_mul_of_nonneg_left hxi hC_nonneg
      calc
        Barg ≤ C := hBarg_le_C
        _ = C * 1 := by ring
        _ ≤ C * xi := hmul
    have hmul := mul_le_mul_of_nonneg_right hBarg_le_Cxi hT
    calc
      2 + Barg * T = Barg * T + 2 := by ring
      _ ≤ C * xi * T + 2 := add_le_add_left hmul 2
      _ = 2 + C * xi * T := by ring
  have hlogA :
      Real.log (2 + Aarg * xi * T) ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by positivity) hAarg_arg
  have hlogB :
      Real.log (2 + Barg * T) ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by positivity) hBarg_arg
  have hlogA_nonneg : 0 ≤ Real.log (2 + Aarg * xi * T) := by
    exact Real.log_nonneg (by
      have hprod : 0 ≤ Aarg * xi * T := by positivity
      exact le_trans (by norm_num : (1 : ℝ) ≤ 2)
        (by simpa using add_le_add_left hprod (2 : ℝ)))
  have hlogB_nonneg : 0 ≤ Real.log (2 + Barg * T) := by
    exact Real.log_nonneg (by
      have hprod : 0 ≤ Barg * T := by positivity
      exact le_trans (by norm_num : (1 : ℝ) ≤ 2)
        (by simpa using add_le_add_left hprod (2 : ℝ)))
  have hx_nonneg :
      0 ≤ Acoef * xi * Real.log (2 + Aarg * xi * T) := by positivity
  have hy_nonneg :
      0 ≤ Bcoef * Real.log (2 + Barg * T) := by positivity
  have hceilx :
      (Nat.ceil (Acoef * xi * Real.log (2 + Aarg * xi * T)) : ℝ) ≤
        Acoef * xi * Real.log (2 + Aarg * xi * T) + 1 :=
    natCeil_le_add_one hx_nonneg
  have hceily :
      (Nat.ceil (Bcoef * Real.log (2 + Barg * T)) : ℝ) ≤
        Bcoef * Real.log (2 + Barg * T) + 1 :=
    natCeil_le_add_one hy_nonneg
  have hx_le : Acoef * xi * Real.log (2 + Aarg * xi * T) ≤
      Acoef * xi * L := by
    exact mul_le_mul_of_nonneg_left hlogA (mul_nonneg hAcoef hxi_nonneg)
  have hy_le : Bcoef * Real.log (2 + Barg * T) ≤
      Bcoef * xi * L := by
    calc
      Bcoef * Real.log (2 + Barg * T) ≤ Bcoef * L :=
        mul_le_mul_of_nonneg_left hlogB hBcoef
      _ ≤ Bcoef * xi * L := by
        have hBL_nonneg : 0 ≤ Bcoef * L := mul_nonneg hBcoef hL_nonneg
        have hmul := mul_le_mul_of_nonneg_right hxi hBL_nonneg
        calc
          Bcoef * L = 1 * (Bcoef * L) := by ring
          _ ≤ xi * (Bcoef * L) := hmul
          _ = Bcoef * xi * L := by ring
  have htwo_le : (2 : ℝ) ≤ 4 * xi * L := by
    have hxiL : (1 / 2 : ℝ) ≤ xi * L := by
      simpa using
        mul_le_mul hxi hL_half (by norm_num : (0 : ℝ) ≤ 1 / 2) hxi_nonneg
    calc
      (2 : ℝ) = 4 * (1 / 2 : ℝ) := by norm_num
      _ ≤ 4 * (xi * L) := mul_le_mul_of_nonneg_left hxiL (by norm_num)
      _ = 4 * xi * L := by ring
  have hceil_sum :
      (Nat.ceil (Acoef * xi * Real.log (2 + Aarg * xi * T)) : ℝ) +
          (Nat.ceil (Bcoef * Real.log (2 + Barg * T)) : ℝ) ≤
        Acoef * xi * Real.log (2 + Aarg * xi * T) +
          Bcoef * Real.log (2 + Barg * T) + 2 := by
    calc
      (Nat.ceil (Acoef * xi * Real.log (2 + Aarg * xi * T)) : ℝ) +
          (Nat.ceil (Bcoef * Real.log (2 + Barg * T)) : ℝ)
          ≤ (Acoef * xi * Real.log (2 + Aarg * xi * T) + 1) +
            (Bcoef * Real.log (2 + Barg * T) + 1) :=
            add_le_add hceilx hceily
      _ = Acoef * xi * Real.log (2 + Aarg * xi * T) +
            Bcoef * Real.log (2 + Barg * T) + 2 := by ring
  have hlogs_sum :
      Acoef * xi * Real.log (2 + Aarg * xi * T) +
          Bcoef * Real.log (2 + Barg * T) + 2 ≤
        Acoef * xi * L + Bcoef * xi * L + 2 := by
    calc
      Acoef * xi * Real.log (2 + Aarg * xi * T) +
          Bcoef * Real.log (2 + Barg * T) + 2
          = (Acoef * xi * Real.log (2 + Aarg * xi * T) +
            Bcoef * Real.log (2 + Barg * T)) + 2 := by ring
      _ ≤ (Acoef * xi * L + Bcoef * xi * L) + 2 :=
          add_le_add_left (add_le_add hx_le hy_le) 2
      _ = Acoef * xi * L + Bcoef * xi * L + 2 := by ring
  have htwo_absorb :
      Acoef * xi * L + Bcoef * xi * L + 2 ≤
        Acoef * xi * L + Bcoef * xi * L + 4 * xi * L := by
    exact add_le_add_right htwo_le (Acoef * xi * L + Bcoef * xi * L)
  have hleft_real :
      (Nat.ceil (Acoef * xi * Real.log (2 + Aarg * xi * T)) +
          Nat.ceil (Bcoef * Real.log (2 + Barg * T)) : ℝ) ≤
        C * xi * L := by
    calc
      (Nat.ceil (Acoef * xi * Real.log (2 + Aarg * xi * T)) +
          Nat.ceil (Bcoef * Real.log (2 + Barg * T)) : ℝ)
          =
            (Nat.ceil (Acoef * xi * Real.log (2 + Aarg * xi * T)) : ℝ) +
              (Nat.ceil (Bcoef * Real.log (2 + Barg * T)) : ℝ) := by norm_num
      _ ≤ Acoef * xi * Real.log (2 + Aarg * xi * T) +
            Bcoef * Real.log (2 + Barg * T) + 2 := hceil_sum
      _ ≤ Acoef * xi * L + Bcoef * xi * L + 2 := hlogs_sum
      _ ≤ Acoef * xi * L + Bcoef * xi * L + 4 * xi * L := htwo_absorb
      _ = (Acoef + Bcoef + 4) * xi * L := by ring
      _ ≤ C * xi * L := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsum_le_C hxi_nonneg) hL_nonneg
  have hceil_right :
      C * xi * L ≤
        (Nat.ceil (C * xi * Real.log (2 + C * xi * T)) : ℝ) := by
    simpa [L] using Nat.le_ceil (C * xi * Real.log (2 + C * xi * T))
  exact_mod_cast hleft_real.trans hceil_right

end

end Section51
end Ch05
end Book
end Homogenization
