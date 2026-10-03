/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleMinimalQuantitative
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section51.EntryScale

/-! # Scale Compression -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Deterministic scale compression

This file contains scalar estimates used to compress the explicit quantitative
minimal-scale threshold to the manuscript `exp(C log^2(2 + thetaHat))` form.
-/

noncomputable section

open Section51

theorem log_max_one_le_log_two_add {θ : ℝ} (hθ : 0 ≤ θ) :
    Real.log (max 1 θ) ≤ Real.log (2 + θ) := by
  have hmax_pos : 0 < max 1 θ := lt_of_lt_of_le zero_lt_one (le_max_left 1 θ)
  have hle : max 1 θ ≤ 2 + θ := by
    exact max_le (by linarith) (by linarith)
  exact Real.log_le_log hmax_pos hle

theorem log_two_add_sq_ge_quarter {θ : ℝ} (hθ : 0 ≤ θ) :
    (1 / 4 : ℝ) ≤ (Real.log (2 + θ)) ^ (2 : ℕ) := by
  have hhalf : (1 / 2 : ℝ) ≤ Real.log (2 + θ) :=
    Section51.log_two_add_ge_half hθ
  nlinarith [sq_nonneg (Real.log (2 + θ) - 1 / 2)]

theorem log_two_add_le_two_mul_sq {θ : ℝ} (hθ : 0 ≤ θ) :
    Real.log (2 + θ) ≤ 2 * (Real.log (2 + θ)) ^ (2 : ℕ) := by
  let L : ℝ := Real.log (2 + θ)
  have hhalf : (1 / 2 : ℝ) ≤ L := by
    simpa [L] using Section51.log_two_add_ge_half hθ
  have hnonneg : 0 ≤ L := by linarith
  nlinarith [sq_nonneg (L - 1 / 2)]

theorem rpow_max_one_le_exp_logSq {θ p : ℝ}
    (hθ : 0 ≤ θ) (hp : 0 ≤ p) :
    (max 1 θ) ^ p ≤
      Real.exp ((2 * p) * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
  have hmax_pos : 0 < max 1 θ := lt_of_lt_of_le zero_lt_one (le_max_left 1 θ)
  have hlogmax_nonneg : 0 ≤ Real.log (max 1 θ) :=
    Real.log_nonneg (le_max_left 1 θ)
  have hlog_le_sq :
      p * Real.log (max 1 θ) ≤
        (2 * p) * (Real.log (2 + θ)) ^ (2 : ℕ) := by
    have hlog_le : Real.log (max 1 θ) ≤ Real.log (2 + θ) :=
      log_max_one_le_log_two_add hθ
    have hL_le : Real.log (2 + θ) ≤
        2 * (Real.log (2 + θ)) ^ (2 : ℕ) :=
      log_two_add_le_two_mul_sq hθ
    calc
      p * Real.log (max 1 θ) ≤ p * Real.log (2 + θ) :=
        mul_le_mul_of_nonneg_left hlog_le hp
      _ ≤ p * (2 * (Real.log (2 + θ)) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hL_le hp
      _ = (2 * p) * (Real.log (2 + θ)) ^ (2 : ℕ) := by ring
  calc
    (max 1 θ) ^ p =
        Real.exp (Real.log (max 1 θ) * p) := by
          simpa [mul_comm] using
            (Real.rpow_def_of_pos (x := max 1 θ) (y := p) hmax_pos)
    _ = Real.exp (p * Real.log (max 1 θ)) := by rw [mul_comm]
    _ ≤ Real.exp ((2 * p) * (Real.log (2 + θ)) ^ (2 : ℕ)) :=
        Real.exp_le_exp.mpr hlog_le_sq

theorem const_mul_rpow_max_one_le_exp_logSq {A θ p : ℝ}
    (hA : 0 < A) (hθ : 0 ≤ θ) (hp : 0 ≤ p) :
    A * (max 1 θ) ^ p ≤
      Real.exp
        ((4 * max 0 (Real.log A) + 2 * p) *
          (Real.log (2 + θ)) ^ (2 : ℕ)) := by
  let L2 : ℝ := (Real.log (2 + θ)) ^ (2 : ℕ)
  have hL2_nonneg : 0 ≤ L2 := by dsimp [L2]; positivity
  have hlogA_le :
      Real.log A ≤ 4 * max 0 (Real.log A) * L2 := by
    have hlogA_le_max : Real.log A ≤ max 0 (Real.log A) :=
      le_max_right 0 (Real.log A)
    have hmax_nonneg : 0 ≤ max 0 (Real.log A) := le_max_left 0 (Real.log A)
    have hquarter : (1 / 4 : ℝ) ≤ L2 := by
      simpa [L2] using log_two_add_sq_ge_quarter hθ
    have hscale : max 0 (Real.log A) ≤
        4 * max 0 (Real.log A) * L2 := by
      nlinarith [mul_le_mul_of_nonneg_left hquarter hmax_nonneg]
    exact hlogA_le_max.trans hscale
  have hrpow :=
    rpow_max_one_le_exp_logSq (θ := θ) (p := p) hθ hp
  calc
    A * (max 1 θ) ^ p
        ≤ A * Real.exp ((2 * p) * L2) :=
          mul_le_mul_of_nonneg_left (by simpa [L2] using hrpow) hA.le
    _ = Real.exp (Real.log A + (2 * p) * L2) := by
          rw [Real.exp_add, Real.exp_log hA]
    _ ≤ Real.exp ((4 * max 0 (Real.log A) + 2 * p) * L2) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith

theorem max_one_mul_sq_le_const_mul_max_one_sq {A θ : ℝ}
    (hθ : 0 ≤ θ) :
    max 1 (A * θ ^ (2 : ℕ)) ≤
      max 1 A * (max 1 θ) ^ (2 : ℕ) := by
  have hmaxA_one : 1 ≤ max 1 A := le_max_left 1 A
  have hmaxθ_one : 1 ≤ max 1 θ := le_max_left 1 θ
  have hmaxθ_sq_one : 1 ≤ (max 1 θ) ^ (2 : ℕ) := by nlinarith
  refine max_le ?_ ?_
  · have hprod_nonneg :
        0 ≤ max 1 A * (max 1 θ) ^ (2 : ℕ) := by positivity
    nlinarith
  · have hA_le : A ≤ max 1 A := le_max_right 1 A
    have hθ_le : θ ≤ max 1 θ := le_max_right 1 θ
    have hθ_sq_le : θ ^ (2 : ℕ) ≤ (max 1 θ) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ hθ hθ_le 2
    exact mul_le_mul hA_le hθ_sq_le (sq_nonneg θ) (le_trans (by norm_num) hmaxA_one)

theorem rpow_max_one_mul_sq_le_const_mul_rpow {A θ r : ℝ}
    (hθ : 0 ≤ θ) (hr : 0 ≤ r) :
    (max 1 (A * θ ^ (2 : ℕ))) ^ r ≤
      (max 1 A) ^ r * (max 1 θ) ^ (2 * r) := by
  have hleft_nonneg : 0 ≤ max 1 (A * θ ^ (2 : ℕ)) :=
    le_trans zero_le_one (le_max_left 1 _)
  have hmaxA_pos : 0 < max 1 A :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 A)
  have hmaxθ_pos : 0 < max 1 θ :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 θ)
  have hprod_nonneg :
      0 ≤ max 1 A * (max 1 θ) ^ (2 : ℕ) := by positivity
  have hbase_le :
      max 1 (A * θ ^ (2 : ℕ)) ≤
        max 1 A * (max 1 θ) ^ (2 : ℕ) :=
    max_one_mul_sq_le_const_mul_max_one_sq hθ
  calc
    (max 1 (A * θ ^ (2 : ℕ))) ^ r
        ≤ (max 1 A * (max 1 θ) ^ (2 : ℕ)) ^ r :=
          Real.rpow_le_rpow hleft_nonneg hbase_le hr
    _ = (max 1 A) ^ r * ((max 1 θ) ^ (2 : ℕ)) ^ r := by
          rw [Real.mul_rpow hmaxA_pos.le (sq_nonneg (max 1 θ))]
    _ = (max 1 A) ^ r * (max 1 θ) ^ (2 * r) := by
          rw [← Real.rpow_natCast (max 1 θ) 2]
          rw [← Real.rpow_mul hmaxθ_pos.le]
          ring_nf

theorem rpow_max_one_le_rpow_max_one_of_exponent_le {θ p q : ℝ}
    (hpq : p ≤ q) :
    (max 1 θ) ^ p ≤ (max 1 θ) ^ q := by
  exact Real.rpow_le_rpow_of_exponent_le (le_max_left 1 θ) hpq

theorem mixedBottomTailDenominator_mul_sq_le_const_mul_rpow
    {A B θ η τ σ : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 < η) (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) :
    let rτ : ℝ := τ / η
    let rσ : ℝ := σ / η
    let C : ℝ := max ((max 1 A) ^ rτ) ((max 1 B) ^ rσ)
    mixedBottomTailDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ))
        η τ σ ≤
      C * (max 1 θ) ^ (2 * max rτ rσ) := by
  intro rτ rσ C
  have hrτ_nonneg : 0 ≤ rτ := by dsimp [rτ]; positivity
  have hrσ_nonneg : 0 ≤ rσ := by dsimp [rσ]; positivity
  have hmaxθ_pos : 0 < max 1 θ :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 θ)
  have hxτ_nonneg : 0 ≤ (max 1 θ) ^ (2 * rτ) :=
    (Real.rpow_pos_of_pos hmaxθ_pos _).le
  have hxσ_nonneg : 0 ≤ (max 1 θ) ^ (2 * rσ) :=
    (Real.rpow_pos_of_pos hmaxθ_pos _).le
  have hCτ_nonneg : 0 ≤ (max 1 A) ^ rτ :=
    (Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 A)) _).le
  have hCσ_nonneg : 0 ≤ (max 1 B) ^ rσ :=
    (Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 B)) _).le
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact le_trans hCτ_nonneg (le_max_left _ _)
  have hxmax_nonneg : 0 ≤ (max 1 θ) ^ (2 * max rτ rσ) :=
    (Real.rpow_pos_of_pos hmaxθ_pos _).le
  have hCτ_le_C : (max 1 A) ^ rτ ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  have hCσ_le_C : (max 1 B) ^ rσ ≤ C := by
    dsimp [C]
    exact le_max_right _ _
  have hpowτ :
      (max 1 (A * θ ^ (2 : ℕ))) ^ rτ ≤
        C * (max 1 θ) ^ (2 * max rτ rσ) := by
    have hterm :=
      rpow_max_one_mul_sq_le_const_mul_rpow
        (A := A) (θ := θ) (r := rτ) hθ hrτ_nonneg
    have hpow_mono :
        (max 1 θ) ^ (2 * rτ) ≤
          (max 1 θ) ^ (2 * max rτ rσ) := by
      refine rpow_max_one_le_rpow_max_one_of_exponent_le ?_
      nlinarith [le_max_left rτ rσ]
    calc
      (max 1 (A * θ ^ (2 : ℕ))) ^ rτ
          ≤ (max 1 A) ^ rτ * (max 1 θ) ^ (2 * rτ) := hterm
      _ ≤ (max 1 A) ^ rτ * (max 1 θ) ^ (2 * max rτ rσ) :=
          mul_le_mul_of_nonneg_left hpow_mono hCτ_nonneg
      _ ≤ C * (max 1 θ) ^ (2 * max rτ rσ) :=
          mul_le_mul_of_nonneg_right hCτ_le_C hxmax_nonneg
  have hpowσ :
      (max 1 (B * θ ^ (2 : ℕ))) ^ rσ ≤
        C * (max 1 θ) ^ (2 * max rτ rσ) := by
    have hterm :=
      rpow_max_one_mul_sq_le_const_mul_rpow
        (A := B) (θ := θ) (r := rσ) hθ hrσ_nonneg
    have hpow_mono :
        (max 1 θ) ^ (2 * rσ) ≤
          (max 1 θ) ^ (2 * max rτ rσ) := by
      refine rpow_max_one_le_rpow_max_one_of_exponent_le ?_
      nlinarith [le_max_right rτ rσ]
    calc
      (max 1 (B * θ ^ (2 : ℕ))) ^ rσ
          ≤ (max 1 B) ^ rσ * (max 1 θ) ^ (2 * rσ) := hterm
      _ ≤ (max 1 B) ^ rσ * (max 1 θ) ^ (2 * max rτ rσ) :=
          mul_le_mul_of_nonneg_left hpow_mono hCσ_nonneg
      _ ≤ C * (max 1 θ) ^ (2 * max rτ rσ) :=
          mul_le_mul_of_nonneg_right hCσ_le_C hxmax_nonneg
  simpa [mixedBottomTailDenominator, rτ, rσ, C] using max_le hpowτ hpowσ

theorem selectedBlead_mul_sq_le_const_mul_rpow
    {A B θ η τ σ U V : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 < η) (hτ : 0 ≤ τ) (hσ : 0 ≤ σ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) :
    let rτ : ℝ := τ / η
    let rσ : ℝ := σ / η
    let Cden : ℝ := max ((max 1 A) ^ rτ) ((max 1 B) ^ rσ)
    let p : ℝ := 2 * max rτ rσ
    let C : ℝ := Cden * max U V
    max
        (mixedBottomTailDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ))
          η τ σ * U)
        (mixedBottomTailDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ))
          η τ σ * V) ≤
      C * (max 1 θ) ^ p := by
  intro rτ rσ Cden p C
  have hDen_pos :
      0 < mixedBottomTailDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ))
        η τ σ :=
    mixedBottomTailDenominator_pos
  have hDen_nonneg :
      0 ≤ mixedBottomTailDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ))
        η τ σ := hDen_pos.le
  have hUV_nonneg : 0 ≤ max U V := by
    by_cases hUV : U ≤ V
    · simpa [max_eq_right hUV] using hV
    · simpa [max_eq_left (le_of_not_ge hUV)] using hU
  have hDen_to_max :
      max
          (mixedBottomTailDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ))
            η τ σ * U)
          (mixedBottomTailDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ))
            η τ σ * V) ≤
        mixedBottomTailDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ))
          η τ σ * max U V := by
    refine max_le ?_ ?_
    · exact mul_le_mul_of_nonneg_left (le_max_left U V) hDen_nonneg
    · exact mul_le_mul_of_nonneg_left (le_max_right U V) hDen_nonneg
  have hDen_bound :
      mixedBottomTailDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ))
          η τ σ ≤
        Cden * (max 1 θ) ^ p := by
    simpa [rτ, rσ, Cden, p] using
      mixedBottomTailDenominator_mul_sq_le_const_mul_rpow
        (A := A) (B := B) (θ := θ) (η := η) (τ := τ) (σ := σ)
        hθ hη hτ hσ
  calc
    max
        (mixedBottomTailDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ))
          η τ σ * U)
        (mixedBottomTailDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ))
          η τ σ * V)
        ≤ mixedBottomTailDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ))
          η τ σ * max U V := hDen_to_max
    _ ≤ (Cden * (max 1 θ) ^ p) * max U V :=
        mul_le_mul_of_nonneg_right hDen_bound hUV_nonneg
    _ = C * (max 1 θ) ^ p := by ring

theorem two_rpow_neg_lt_one {η : ℝ} (hη : 0 < η) :
    (2 : ℝ) ^ (-η) < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by linarith)

theorem gap_two_mul_rpow_eq {B η : ℝ} (hB : 0 < B) :
    B ^ (-η) - (2 * B) ^ (-η) =
      B ^ (-η) * (1 - (2 : ℝ) ^ (-η)) := by
  have htwo_nonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hB_nonneg : 0 ≤ B := hB.le
  have hmul :
      (2 * B) ^ (-η) = (2 : ℝ) ^ (-η) * B ^ (-η) := by
    rw [Real.mul_rpow htwo_nonneg hB_nonneg]
  rw [hmul]
  ring

theorem gap_two_mul_rpow_pos {B η : ℝ} (hB : 0 < B) (hη : 0 < η) :
    0 < B ^ (-η) - (2 * B) ^ (-η) := by
  rw [gap_two_mul_rpow_eq hB]
  exact mul_pos (Real.rpow_pos_of_pos hB _)
    (sub_pos.mpr (two_rpow_neg_lt_one hη))

theorem max_zero_neg_log_gap_two_mul_le {B η : ℝ}
    (hB : 1 ≤ B) (hη : 0 < η) :
    max 0 (-(Real.log (B ^ (-η) - (2 * B) ^ (-η)))) ≤
      η * Real.log B + max 0 (-(Real.log (1 - (2 : ℝ) ^ (-η)))) := by
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  let c : ℝ := 1 - (2 : ℝ) ^ (-η)
  have hc_pos : 0 < c := by
    dsimp [c]
    exact sub_pos.mpr (two_rpow_neg_lt_one hη)
  have hBpow_pos : 0 < B ^ (-η) := Real.rpow_pos_of_pos hB_pos _
  have hlogB_nonneg : 0 ≤ Real.log B := Real.log_nonneg hB
  have hmain :
      -(Real.log (B ^ (-η) - (2 * B) ^ (-η))) =
        η * Real.log B - Real.log c := by
    rw [gap_two_mul_rpow_eq hB_pos]
    rw [Real.log_mul hBpow_pos.ne' hc_pos.ne']
    rw [Real.log_rpow hB_pos]
    dsimp [c]
    ring
  rw [hmain]
  refine max_le ?_ ?_
  · have hηlog_nonneg : 0 ≤ η * Real.log B := mul_nonneg hη.le hlogB_nonneg
    have hmax_nonneg : 0 ≤ max 0 (-(Real.log c)) := le_max_left 0 _
    nlinarith
  · have hneglog_le : -(Real.log c) ≤ max 0 (-(Real.log c)) := le_max_right 0 _
    nlinarith [mul_nonneg hη.le hlogB_nonneg]

theorem rpow_three_natCeil_le_three_mul_exp {y : ℝ} (hy : 0 ≤ y) :
    Real.rpow (3 : ℝ) ((Nat.ceil y : ℕ) : ℝ) ≤
      3 * Real.exp (Real.log (3 : ℝ) * y) := by
  have hceil : ((Nat.ceil y : ℕ) : ℝ) < y + 1 :=
    Nat.ceil_lt_add_one hy
  have hpow_le :
      Real.rpow (3 : ℝ) ((Nat.ceil y : ℕ) : ℝ) ≤
        Real.rpow (3 : ℝ) (y + 1) :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hceil.le
  calc
    Real.rpow (3 : ℝ) ((Nat.ceil y : ℕ) : ℝ)
        ≤ Real.rpow (3 : ℝ) (y + 1) := hpow_le
    _ = Real.exp (Real.log (3 : ℝ) * (y + 1)) := by
          simpa using
            (Real.rpow_def_of_pos (x := (3 : ℝ)) (y := y + 1)
              (by norm_num : (0 : ℝ) < 3))
    _ = 3 * Real.exp (Real.log (3 : ℝ) * y) := by
          rw [show Real.log (3 : ℝ) * (y + 1) =
              Real.log (3 : ℝ) + Real.log (3 : ℝ) * y by ring]
          rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

theorem pow_three_natCeil_le_three_mul_exp {y : ℝ} (hy : 0 ≤ y) :
    (3 : ℝ) ^ (Nat.ceil y) ≤
      3 * Real.exp (Real.log (3 : ℝ) * y) := by
  simpa [Real.rpow_natCast] using rpow_three_natCeil_le_three_mul_exp hy

end

end Section57
end Ch05
end Book
end Homogenization
