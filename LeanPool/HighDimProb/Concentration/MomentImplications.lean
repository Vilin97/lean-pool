/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Concentration.OrliczToTail
import LeanPool.HighDimProb.Concentration.TailToOrlicz
import LeanPool.HighDimProb.Analysis.RealInequalities
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Scalar moment implications

Verified Wikipedia references:
* Moment: https://en.wikipedia.org/wiki/Moment_(mathematics)
* Sub-Gaussian distribution: https://en.wikipedia.org/wiki/Sub-Gaussian_distribution
* Orlicz space: https://en.wikipedia.org/wiki/Orlicz_space
* Heavy-tailed/subExponential context: https://en.wikipedia.org/wiki/Heavy-tailed_distribution

This file starts the moment side of the scalar concentration implication graph.

The current proved bridges use a natural absolute-moment normal form. In
addition to fixed low moments, the file contains a crude all-natural-exponent
factorial bound under a probability-measure assumption.

The factorial bound yields a reusable linear-in-`q` real-Lp growth theorem.
The sharp natural-exponent `sqrt(q)` real-Lp growth theorem is proved and
packaged through `SubGaussianMomentNatSqrt`.  This file also contains the
ceiling/exponent-monotonicity bridge from those natural-exponent theorems to
the full finite-`ENNReal` `SubGaussianMoment` predicate.
-/

namespace HighDimProb

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Natural absolute moment, kept in `ENNReal` form to match layer-cake APIs. -/
def absMomentNat {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (q : ℕ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (|X ω| ^ q) ∂P

/-- Finiteness predicate for natural absolute moments. -/
def finiteAbsMomentNat {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (q : ℕ) : Prop :=
  absMomentNat P X q < ∞

/--
Natural-exponent subGaussian moment growth, in the factorial normal form
currently proved from `Psi2Bound` and `SubGaussianTail`.
-/
def SubGaussianMomentNat {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ q : ℕ, 1 ≤ q →
      absMomentNat P X q ≤
        ENNReal.ofReal (Real.exp (1 / 4) * K ^ q * (Nat.factorial q : ℝ)) * 2

/--
Natural-exponent subGaussian moment growth in the sharp `sqrt(q)` real-Lp
normal form.

This supplements `SubGaussianMomentNat`, whose current meaning is the
factorial absolute-moment normal form.  It is deliberately natural-exponent
only; the full `SubGaussianMoment` predicate quantifies over all finite
`ENNReal` exponents.
-/
def SubGaussianMomentNatSqrt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  0 < K ∧
    ∀ q : ℕ, 1 ≤ q →
      realLpNorm P X (q : ENNReal) ≤
        ENNReal.ofReal (K * Real.sqrt (q : ℝ))

/-- The `eLpNorm` integrand at a natural exponent is exactly `absMomentNat`. -/
theorem lintegral_enorm_rpow_nat_eq_absMomentNat
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : RealRandomVariable Ω) (q : ℕ) :
    (∫⁻ ω, ‖X ω‖ₑ ^ (q : ℝ) ∂P) = absMomentNat P X q := by
  unfold absMomentNat
  apply lintegral_congr_ae
  exact ae_of_all P fun ω => by
    change ‖X ω‖ₑ ^ (q : ℝ) = ENNReal.ofReal (|X ω| ^ q)
    rw [ENNReal.rpow_natCast]
    rw [← ofReal_norm (X ω)]
    rw [← ENNReal.ofReal_pow (norm_nonneg (X ω))]
    rw [Real.norm_eq_abs]

/--
Finite natural absolute moment plus measurability gives Mathlib `MemLp` at the
corresponding natural exponent.

The measurability hypothesis is explicit because `finiteAbsMomentNat` only
records finiteness of the `lintegral`.
-/
theorem memLp_of_finiteAbsMomentNat
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {q : ℕ}
    (hq : q ≠ 0) (hX : IsRealRandomVariable P X)
    (hfin : finiteAbsMomentNat P X q) :
    MemLpRealRandomVariable P X (q : ENNReal) := by
  refine ⟨hX.aestronglyMeasurable, ?_⟩
  have hp0 : (q : ENNReal) ≠ 0 := by
    exact_mod_cast hq
  have hptop : (q : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hptop]
  change (∫⁻ ω, ‖X ω‖ₑ ^ (q : ℝ) ∂P) < ∞
  rw [lintegral_enorm_rpow_nat_eq_absMomentNat]
  simpa [finiteAbsMomentNat] using hfin

/-- First-moment convenience wrapper for `memLp_of_finiteAbsMomentNat`. -/
theorem memLp_one_of_finiteAbsMomentNat_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω}
    (hX : IsRealRandomVariable P X) (hfin : finiteAbsMomentNat P X 1) :
    MemLpRealRandomVariable P X (1 : ENNReal) := by
  simpa only [Nat.cast_one] using
    (memLp_of_finiteAbsMomentNat (P := P) (X := X) (q := 1)
      (by norm_num) hX hfin)

/-- Second-moment convenience wrapper for `memLp_of_finiteAbsMomentNat`. -/
theorem memLp_two_of_finiteAbsMomentNat_two
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω}
    (hX : IsRealRandomVariable P X) (hfin : finiteAbsMomentNat P X 2) :
    MemLpRealRandomVariable P X (2 : ENNReal) := by
  simpa only [Nat.cast_ofNat] using
    (memLp_of_finiteAbsMomentNat (P := P) (X := X) (q := 2)
      (by norm_num) hX hfin)

/--
An `ENNReal` absolute-moment bound controls Mathlib's extended real `Lp`
seminorm at the matching natural exponent.
-/
theorem realLpNorm_nat_le_of_absMomentNat_le_ennreal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {q : ℕ} {B : ENNReal}
    (hq : q ≠ 0) (hbound : absMomentNat P X q ≤ B) :
    realLpNorm P X (q : ENNReal) ≤ B ^ (1 / (q : ℝ)) := by
  have hp0 : (q : ENNReal) ≠ 0 := by
    exact_mod_cast hq
  have hptop : (q : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hq
  rw [realLpNorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
  have hlin : (∫⁻ ω, ‖X ω‖ₑ ^ (q : ENNReal).toReal ∂P) ≤ B := by
    change (∫⁻ ω, ‖X ω‖ₑ ^ (q : ℝ) ∂P) ≤ B
    rw [lintegral_enorm_rpow_nat_eq_absMomentNat]
    exact hbound
  simpa [ENNReal.toReal_natCast] using
    (ENNReal.rpow_le_rpow hlin (by positivity : 0 ≤ (1 / (q : ℝ))))

/--
A real-valued absolute-moment bound controls Mathlib's extended real `Lp`
seminorm at the matching natural exponent.
-/
theorem realLpNorm_nat_le_of_absMomentNat_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {q : ℕ} {B : ℝ}
    (hq : q ≠ 0) (hB : 0 ≤ B)
    (hbound : absMomentNat P X q ≤ ENNReal.ofReal B) :
    realLpNorm P X (q : ENNReal) ≤ ENNReal.ofReal (B ^ (1 / (q : ℝ))) := by
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hq
  have hnonneg : 0 ≤ 1 / (q : ℝ) := by positivity
  have h :=
    realLpNorm_nat_le_of_absMomentNat_le_ennreal
      (P := P) (X := X) (q := q) (B := ENNReal.ofReal B) hq hbound
  rwa [ENNReal.ofReal_rpow_of_nonneg hB hnonneg] at h

private lemma eight_le_eight_pow_succ (n : ℕ) : (8 : ℝ) ≤ 8 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hpow_nonneg : 0 ≤ (8 : ℝ) ^ (n + 1) := by positivity
      calc
        (8 : ℝ) ≤ 8 ^ (n + 1) := ih
        _ ≤ 8 ^ (n + 1) * 8 := by nlinarith
        _ = 8 ^ (Nat.succ n + 1) := by
          rw [show Nat.succ n + 1 = Nat.succ (n + 1) by omega]
          exact (pow_succ (8 : ℝ) (n + 1)).symm

private lemma eight_le_eight_pow (q : ℕ) (hq : 1 ≤ q) : (8 : ℝ) ≤ 8 ^ q := by
  cases q with
  | zero => cases hq
  | succ n =>
      simpa [Nat.succ_eq_add_one] using eight_le_eight_pow_succ n

private lemma two_mul_exp_quarter_le_eight :
    2 * Real.exp ((1 : ℝ) / 4) ≤ 8 := by
  have h_exp_quarter_le_exp_one : Real.exp ((1 : ℝ) / 4) ≤ Real.exp 1 := by
    exact Real.exp_le_exp_of_le (by norm_num)
  have h_exp_one_lt_three : Real.exp 1 < 3 := Real.exp_one_lt_three
  nlinarith

private lemma two_mul_exp_quarter_rpow_inv_natCast_le_eight
    (q : ℕ) (hq : 1 ≤ q) :
    (2 * Real.exp ((1 : ℝ) / 4)) ^ (1 / (q : ℝ)) ≤ 8 := by
  have hbase_nonneg : 0 ≤ 2 * Real.exp ((1 : ℝ) / 4) := by positivity
  have hbase_le_pow : 2 * Real.exp ((1 : ℝ) / 4) ≤ (8 : ℝ) ^ q := by
    exact two_mul_exp_quarter_le_eight.trans (eight_le_eight_pow q hq)
  have hroot_le :
      (2 * Real.exp ((1 : ℝ) / 4)) ^ (1 / (q : ℝ)) ≤
        ((8 : ℝ) ^ q) ^ (1 / (q : ℝ)) := by
    exact Real.rpow_le_rpow hbase_nonneg hbase_le_pow (by positivity)
  have hqpos : 0 < (q : ℝ) := by
    have hqNat : 0 < q := hq
    exact_mod_cast hqNat
  have hroot_pow : ((8 : ℝ) ^ q) ^ (1 / (q : ℝ)) = 8 := by
    rw [← Real.rpow_natCast (8 : ℝ) q]
    rw [← Real.rpow_mul (by norm_num : 0 ≤ (8 : ℝ))]
    have hcancel : (q : ℝ) * (1 / (q : ℝ)) = 1 := by
      field_simp [hqpos.ne']
    rw [hcancel, Real.rpow_one]
  rw [hroot_pow] at hroot_le
  exact hroot_le

private lemma factorial_rpow_inv_natCast_le (q : ℕ) (hq : 1 ≤ q) :
    ((Nat.factorial q : ℝ) ^ (1 / (q : ℝ))) ≤ (q : ℝ) := by
  have hqpos : 0 < (q : ℝ) := by
    have hqNat : 0 < q := hq
    exact_mod_cast hqNat
  have hfac_nonneg : 0 ≤ (Nat.factorial q : ℝ) := by positivity
  have hfac_le_pow : (Nat.factorial q : ℝ) ≤ (q : ℝ) ^ q := by
    exact_mod_cast Nat.factorial_le_pow q
  have hroot_le :
      ((Nat.factorial q : ℝ) ^ (1 / (q : ℝ))) ≤
        (((q : ℝ) ^ q) ^ (1 / (q : ℝ))) := by
    exact Real.rpow_le_rpow hfac_nonneg hfac_le_pow (by positivity)
  have hroot_pow : (((q : ℝ) ^ q) ^ (1 / (q : ℝ))) = (q : ℝ) := by
    rw [← Real.rpow_natCast (q : ℝ) q]
    rw [← Real.rpow_mul hqpos.le]
    have hcancel : (q : ℝ) * (1 / (q : ℝ)) = 1 := by
      field_simp [hqpos.ne']
    rw [hcancel, Real.rpow_one]
  rw [hroot_pow] at hroot_le
  exact hroot_le

private lemma pow_rpow_inv_natCast_of_pos {K : ℝ} (hK : 0 < K)
    {q : ℕ} (hq : 1 ≤ q) :
    ((K ^ q) ^ (1 / (q : ℝ))) = K := by
  have hqpos : 0 < (q : ℝ) := by
    have hqNat : 0 < q := hq
    exact_mod_cast hqNat
  rw [← Real.rpow_natCast K q]
  rw [← Real.rpow_mul hK.le]
  have hcancel : (q : ℝ) * (1 / (q : ℝ)) = 1 := by
    field_simp [hqpos.ne']
  rw [hcancel, Real.rpow_one]

private lemma factorial_moment_root_le_linear {K : ℝ} (hK : 0 < K)
    {q : ℕ} (hq : 1 ≤ q) :
    (Real.exp ((1 : ℝ) / 4) * K ^ q * (Nat.factorial q : ℝ) * 2) ^
        (1 / (q : ℝ)) ≤ 8 * K * (q : ℝ) := by
  have hconst_nonneg : 0 ≤ 2 * Real.exp ((1 : ℝ) / 4) := by positivity
  have hKpow_nonneg : 0 ≤ K ^ q := by positivity
  have hfac_nonneg : 0 ≤ (Nat.factorial q : ℝ) := by positivity
  calc
    (Real.exp ((1 : ℝ) / 4) * K ^ q * (Nat.factorial q : ℝ) * 2) ^
        (1 / (q : ℝ))
        = ((2 * Real.exp ((1 : ℝ) / 4)) * K ^ q *
            (Nat.factorial q : ℝ)) ^ (1 / (q : ℝ)) := by
          congr 1
          ring
    _ = (2 * Real.exp ((1 : ℝ) / 4)) ^ (1 / (q : ℝ)) *
          (K ^ q) ^ (1 / (q : ℝ)) *
          ((Nat.factorial q : ℝ) ^ (1 / (q : ℝ))) := by
          rw [Real.mul_rpow (mul_nonneg hconst_nonneg hKpow_nonneg) hfac_nonneg]
          rw [Real.mul_rpow hconst_nonneg hKpow_nonneg]
    _ ≤ 8 * K * (q : ℝ) := by
          rw [pow_rpow_inv_natCast_of_pos hK hq]
          have hconst := two_mul_exp_quarter_rpow_inv_natCast_le_eight q hq
          have hfac := factorial_rpow_inv_natCast_le q hq
          have hfac_root_nonneg :
              0 ≤ ((Nat.factorial q : ℝ) ^ (1 / (q : ℝ))) := by positivity
          have h8K_nonneg : 0 ≤ (8 : ℝ) * K := by positivity
          have hleft :
              (2 * Real.exp ((1 : ℝ) / 4)) ^ (1 / (q : ℝ)) * K ≤ 8 * K := by
            exact mul_le_mul_of_nonneg_right hconst hK.le
          have hprod :
              ((2 * Real.exp ((1 : ℝ) / 4)) ^ (1 / (q : ℝ)) * K) *
                  ((Nat.factorial q : ℝ) ^ (1 / (q : ℝ))) ≤
                (8 * K) * (q : ℝ) := by
            exact mul_le_mul hleft hfac hfac_root_nonneg h8K_nonneg
          simpa [mul_assoc] using hprod

private lemma two_rpow_inv_natCast_le_eight
    (q : ℕ) (hq : 1 ≤ q) :
    (2 : ℝ) ^ (1 / (q : ℝ)) ≤ 8 := by
  have hbase_nonneg : 0 ≤ (2 : ℝ) := by norm_num
  have hbase_le_pow : (2 : ℝ) ≤ (8 : ℝ) ^ q := by
    exact (by norm_num : (2 : ℝ) ≤ 8).trans (eight_le_eight_pow q hq)
  have hroot_le :
      (2 : ℝ) ^ (1 / (q : ℝ)) ≤
        ((8 : ℝ) ^ q) ^ (1 / (q : ℝ)) := by
    exact Real.rpow_le_rpow hbase_nonneg hbase_le_pow (by positivity)
  have hqpos : 0 < (q : ℝ) := by
    have hqNat : 0 < q := hq
    exact_mod_cast hqNat
  have hroot_pow : ((8 : ℝ) ^ q) ^ (1 / (q : ℝ)) = 8 := by
    rw [← Real.rpow_natCast (8 : ℝ) q]
    rw [← Real.rpow_mul (by norm_num : 0 ≤ (8 : ℝ))]
    have hcancel : (q : ℝ) * (1 / (q : ℝ)) = 1 := by
      field_simp [hqpos.ne']
    rw [hcancel, Real.rpow_one]
  rw [hroot_pow] at hroot_le
  exact hroot_le

private lemma psi1_factorial_moment_root_le_linear {K : ℝ} (hK : 0 < K)
    {q : ℕ} (hq : 1 ≤ q) :
    (2 * K ^ q * (Nat.factorial q : ℝ)) ^
        (1 / (q : ℝ)) ≤ 8 * K * (q : ℝ) := by
  have hconst_nonneg : 0 ≤ (2 : ℝ) := by norm_num
  have hKpow_nonneg : 0 ≤ K ^ q := by positivity
  have hfac_nonneg : 0 ≤ (Nat.factorial q : ℝ) := by positivity
  calc
    (2 * K ^ q * (Nat.factorial q : ℝ)) ^ (1 / (q : ℝ))
        = (2 : ℝ) ^ (1 / (q : ℝ)) *
          (K ^ q) ^ (1 / (q : ℝ)) *
          ((Nat.factorial q : ℝ) ^ (1 / (q : ℝ))) := by
          rw [Real.mul_rpow (mul_nonneg hconst_nonneg hKpow_nonneg) hfac_nonneg]
          rw [Real.mul_rpow hconst_nonneg hKpow_nonneg]
    _ ≤ 8 * K * (q : ℝ) := by
          rw [pow_rpow_inv_natCast_of_pos hK hq]
          have hconst := two_rpow_inv_natCast_le_eight q hq
          have hfac := factorial_rpow_inv_natCast_le q hq
          have hfac_root_nonneg :
              0 ≤ ((Nat.factorial q : ℝ) ^ (1 / (q : ℝ))) := by positivity
          have h8K_nonneg : 0 ≤ (8 : ℝ) * K := by positivity
          have hleft :
              (2 : ℝ) ^ (1 / (q : ℝ)) * K ≤ 8 * K := by
            exact mul_le_mul_of_nonneg_right hconst hK.le
          have hprod :
              ((2 : ℝ) ^ (1 / (q : ℝ)) * K) *
                  ((Nat.factorial q : ℝ) ^ (1 / (q : ℝ))) ≤
                (8 * K) * (q : ℝ) := by
            exact mul_le_mul hleft hfac hfac_root_nonneg h8K_nonneg
          simpa [mul_assoc] using hprod

private lemma pow_le_factorial_mul_exp_quarter_mul_exp_sq
    {a : ℝ} (ha : 0 ≤ a) (q : ℕ) :
    a ^ q ≤ (Nat.factorial q : ℝ) * Real.exp (1 / 4) * Real.exp (a ^ 2) := by
  have hfac_pos : 0 < (Nat.factorial q : ℝ) := by
    exact_mod_cast Nat.factorial_pos q
  have hpow_div : a ^ q / (Nat.factorial q : ℝ) ≤ Real.exp a :=
    Real.pow_div_factorial_le_exp a ha q
  have hpow_le : a ^ q ≤ (Nat.factorial q : ℝ) * Real.exp a := by
    calc
      a ^ q = (Nat.factorial q : ℝ) * (a ^ q / (Nat.factorial q : ℝ)) := by
        field_simp [hfac_pos.ne']
      _ ≤ (Nat.factorial q : ℝ) * Real.exp a := by
        exact mul_le_mul_of_nonneg_left hpow_div hfac_pos.le
  have hquad : a ≤ a ^ 2 + (1 / 4 : ℝ) := by
    nlinarith [sq_nonneg (a - (1 / 2 : ℝ))]
  calc
    a ^ q ≤ (Nat.factorial q : ℝ) * Real.exp a := hpow_le
    _ ≤ (Nat.factorial q : ℝ) * Real.exp (a ^ 2 + (1 / 4 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le hquad)
        (by positivity)
    _ = (Nat.factorial q : ℝ) * Real.exp (1 / 4) * Real.exp (a ^ 2) := by
      rw [Real.exp_add]
      ring

/--
Pointwise all-natural-exponent domination by the exponential-square integrand.

The constant is intentionally crude: `exp(1/4) * K^q * q!`.
-/
theorem abs_pow_le_exp_sq_factorial
    {x K : ℝ} (hK : 0 < K) (q : ℕ) :
    |x| ^ q ≤
      Real.exp (1 / 4) * K ^ q * (Nat.factorial q : ℝ) *
        Real.exp ((|x| / K) ^ 2) := by
  let a : ℝ := |x| / K
  have ha : 0 ≤ a := div_nonneg (abs_nonneg _) hK.le
  have hpow := pow_le_factorial_mul_exp_quarter_mul_exp_sq ha q
  have hscale : |x| ^ q = K ^ q * a ^ q := by
    simp only [a]
    rw [div_pow]
    field_simp [pow_ne_zero q hK.ne']
  calc
    |x| ^ q = K ^ q * a ^ q := hscale
    _ ≤ K ^ q *
        ((Nat.factorial q : ℝ) * Real.exp (1 / 4) * Real.exp (a ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hpow (pow_nonneg hK.le q)
    _ =
        Real.exp (1 / 4) * K ^ q * (Nat.factorial q : ℝ) *
          Real.exp ((|x| / K) ^ 2) := by
      simp only [a]
      ring

/--
Pointwise all-natural-exponent domination by the exponential-linear integrand.

This is the subExponential analogue of `abs_pow_le_exp_sq_factorial`, using
`x^q / q! <= exp x` after scaling by `K`.
-/
theorem abs_pow_le_exp_linear_factorial
    {x K : ℝ} (hK : 0 < K) (q : ℕ) :
    |x| ^ q ≤ K ^ q * (Nat.factorial q : ℝ) * Real.exp (|x| / K) := by
  let a : ℝ := |x| / K
  have ha : 0 ≤ a := div_nonneg (abs_nonneg _) hK.le
  have hfac_pos : 0 < (Nat.factorial q : ℝ) := by
    exact_mod_cast Nat.factorial_pos q
  have hpow_div : a ^ q / (Nat.factorial q : ℝ) ≤ Real.exp a :=
    Real.pow_div_factorial_le_exp a ha q
  have hpow_le : a ^ q ≤ (Nat.factorial q : ℝ) * Real.exp a := by
    calc
      a ^ q = (Nat.factorial q : ℝ) * (a ^ q / (Nat.factorial q : ℝ)) := by
        field_simp [hfac_pos.ne']
      _ ≤ (Nat.factorial q : ℝ) * Real.exp a := by
        exact mul_le_mul_of_nonneg_left hpow_div hfac_pos.le
  have hscale : |x| ^ q = K ^ q * a ^ q := by
    simp only [a]
    rw [div_pow]
    field_simp [pow_ne_zero q hK.ne']
  calc
    |x| ^ q = K ^ q * a ^ q := hscale
    _ ≤ K ^ q * ((Nat.factorial q : ℝ) * Real.exp a) := by
      exact mul_le_mul_of_nonneg_left hpow_le (pow_nonneg hK.le q)
    _ = K ^ q * (Nat.factorial q : ℝ) * Real.exp (|x| / K) := by
      simp only [a]
      ring

private lemma sq_le_scale_sq_mul_exp_sub_one {x K : ℝ} (hK : 0 < K) :
    |x| ^ 2 ≤ K ^ 2 * (Real.exp ((|x| / K) ^ 2) - 1) := by
  let z : ℝ := (|x| / K) ^ 2
  have hz_le : z ≤ Real.exp z - 1 := by
    have h := Real.add_one_le_exp z
    linarith
  have hz_eq : |x| ^ 2 = K ^ 2 * z := by
    simp only [z]
    field_simp [hK.ne']
  calc
    |x| ^ 2 = K ^ 2 * z := hz_eq
    _ ≤ K ^ 2 * (Real.exp z - 1) := by
      exact mul_le_mul_of_nonneg_left hz_le (sq_nonneg K)

private lemma abs_le_scale_mul_exp_sub_one {x K : ℝ} (hK : 0 < K) :
    |x| ≤ K * (Real.exp (|x| / K) - 1) := by
  let z : ℝ := |x| / K
  have hz_le : z ≤ Real.exp z - 1 := by
    have h := Real.add_one_le_exp z
    linarith
  have hz_eq : |x| = K * z := by
    simp only [z]
    field_simp [hK.ne']
  calc
    |x| = K * z := hz_eq
    _ ≤ K * (Real.exp z - 1) := by
      exact mul_le_mul_of_nonneg_left hz_le hK.le

/-- A `psi_2` bound controls the second absolute natural moment. -/
theorem absMomentNat_two_le_of_psi2Bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {K : ℝ} (hψ : Psi2Bound P X K) :
    absMomentNat P X 2 ≤ ENNReal.ofReal (K ^ 2) := by
  rcases hψ with ⟨hK, hψ_int⟩
  unfold absMomentNat
  calc
    (∫⁻ ω, ENNReal.ofReal (|X ω| ^ 2) ∂P)
        ≤ ∫⁻ ω,
            ENNReal.ofReal (K ^ 2 * (Real.exp ((|X ω| / K) ^ 2) - 1)) ∂P := by
          refine lintegral_mono ?_
          intro ω
          exact ENNReal.ofReal_le_ofReal
            (sq_le_scale_sq_mul_exp_sub_one (x := X ω) hK)
    _ = ∫⁻ ω,
          ENNReal.ofReal (K ^ 2) *
            ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2) - 1) ∂P := by
          apply lintegral_congr_ae
          exact ae_of_all P fun ω => by
            change ENNReal.ofReal (K ^ 2 * (Real.exp ((|X ω| / K) ^ 2) - 1)) =
              ENNReal.ofReal (K ^ 2) *
                ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2) - 1)
            rw [ENNReal.ofReal_mul (sq_nonneg K)]
    _ = ENNReal.ofReal (K ^ 2) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2) - 1) ∂P := by
          rw [lintegral_const_mul']
          exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (K ^ 2) * 1 := by
          gcongr
    _ = ENNReal.ofReal (K ^ 2) := by simp

/-- A `psi_2` bound gives finiteness of the second absolute natural moment. -/
theorem finiteAbsMomentNat_two_of_psi2Bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {K : ℝ} (hψ : Psi2Bound P X K) :
    finiteAbsMomentNat P X 2 := by
  unfold finiteAbsMomentNat
  exact lt_of_le_of_lt (absMomentNat_two_le_of_psi2Bound hψ) ENNReal.ofReal_lt_top

/--
A probability-measure `psi_2` bound controls every natural absolute moment.

This is a crude factorial-growth estimate:
`E |X|^q <= 2 * exp(1/4) * K^q * q!`.
It is useful for finiteness and future refinement, but it is not the sharp
`(K * sqrt q)^q` growth theorem.
-/
theorem absMomentNat_le_of_psi2Bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ} (hψ : Psi2Bound P X K) (q : ℕ) :
    absMomentNat P X q ≤
      ENNReal.ofReal (Real.exp (1 / 4) * K ^ q * (Nat.factorial q : ℝ)) * 2 := by
  rcases hψ with ⟨hK, hψ_int⟩
  have h_exp :
      (∫⁻ ω, ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2)) ∂P) ≤
        (2 : ENNReal) := by
    exact lintegral_exp_sq_div_le_two_of_psi2Bound
      (P := P) (X := X) (K := K) ⟨hK, hψ_int⟩
  let C : ℝ := Real.exp (1 / 4) * K ^ q * (Nat.factorial q : ℝ)
  have hC_nonneg : 0 ≤ C := by
    simp only [C]
    positivity
  unfold absMomentNat
  calc
    (∫⁻ ω, ENNReal.ofReal (|X ω| ^ q) ∂P)
        ≤ ∫⁻ ω, ENNReal.ofReal (C * Real.exp ((|X ω| / K) ^ 2)) ∂P := by
          refine lintegral_mono ?_
          intro ω
          exact ENNReal.ofReal_le_ofReal
            (by
              simpa [C, mul_assoc] using
                abs_pow_le_exp_sq_factorial (x := X ω) (K := K) hK q)
    _ = ∫⁻ ω,
          ENNReal.ofReal C *
            ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2)) ∂P := by
          apply lintegral_congr_ae
          exact ae_of_all P fun ω => by
            change ENNReal.ofReal (C * Real.exp ((|X ω| / K) ^ 2)) =
              ENNReal.ofReal C *
                ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2))
            rw [ENNReal.ofReal_mul hC_nonneg]
    _ = ENNReal.ofReal C *
          ∫⁻ ω, ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2)) ∂P := by
          rw [lintegral_const_mul']
          exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * 2 := by
          gcongr
    _ = ENNReal.ofReal (Real.exp (1 / 4) * K ^ q * (Nat.factorial q : ℝ)) * 2 := by
          rfl

/-- A probability-measure `psi_2` bound gives finiteness of every natural absolute moment. -/
theorem finiteAbsMomentNat_of_psi2Bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ} (hψ : Psi2Bound P X K) (q : ℕ) :
    finiteAbsMomentNat P X q := by
  unfold finiteAbsMomentNat
  refine lt_of_le_of_lt (absMomentNat_le_of_psi2Bound (P := P) (X := X) (K := K) hψ q) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by norm_num)

/--
A probability-measure `psi_2` bound gives a sharp natural absolute-moment
growth bound with `sqrt(q)` scale.

The constant is deliberately non-optimal but sharper than the factorial route:
`E |X|^q <= (4 * K * sqrt(q))^q`.
-/
theorem absMomentNat_le_sqrt_growth_of_psi2Bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ} {q : ℕ}
    (hψ : Psi2Bound P X K) (hq : 1 ≤ q) :
    absMomentNat P X q ≤ ENNReal.ofReal ((4 * K * Real.sqrt (q : ℝ)) ^ q) := by
  have hK : 0 < K := hψ.1
  have hcoef_nonneg : 0 ≤ (2 * K * Real.sqrt (q : ℝ)) ^ q := by positivity
  unfold absMomentNat
  calc
    (∫⁻ ω, ENNReal.ofReal (|X ω| ^ q) ∂P)
        ≤ ∫⁻ ω,
            ENNReal.ofReal ((2 * K * Real.sqrt (q : ℝ)) ^ q) *
              ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2)) ∂P := by
          refine lintegral_mono ?_
          intro ω
          have hpoint :=
            pow_le_two_mul_scale_sqrt_mul_exp_sq_div
              (x := |X ω|) (K := K) (q := q) (abs_nonneg _) hK hq
          calc
            ENNReal.ofReal (|X ω| ^ q)
                ≤ ENNReal.ofReal
                    ((2 * K * Real.sqrt (q : ℝ)) ^ q *
                      Real.exp ((|X ω| / K) ^ 2)) := by
                  exact ENNReal.ofReal_le_ofReal hpoint
            _ = ENNReal.ofReal ((2 * K * Real.sqrt (q : ℝ)) ^ q) *
                  ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2)) := by
                  rw [ENNReal.ofReal_mul hcoef_nonneg]
    _ = ENNReal.ofReal ((2 * K * Real.sqrt (q : ℝ)) ^ q) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp ((|X ω| / K) ^ 2)) ∂P := by
          rw [lintegral_const_mul']
          exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2 * K * Real.sqrt (q : ℝ)) ^ q) * 2 := by
          gcongr
          exact lintegral_exp_sq_div_le_two_of_psi2Bound
            (P := P) (X := X) (K := K) hψ
    _ = ENNReal.ofReal (((2 * K * Real.sqrt (q : ℝ)) ^ q) * 2) := by
          rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num]
          rw [ENNReal.ofReal_mul hcoef_nonneg]
    _ ≤ ENNReal.ofReal ((4 * K * Real.sqrt (q : ℝ)) ^ q) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hbase_nonneg : 0 ≤ 2 * K * Real.sqrt (q : ℝ) := by positivity
          have h :=
            two_mul_pow_le_two_mul_pow
              (a := 2 * K * Real.sqrt (q : ℝ)) hbase_nonneg hq
          calc
            ((2 * K * Real.sqrt (q : ℝ)) ^ q) * 2
                = 2 * (2 * K * Real.sqrt (q : ℝ)) ^ q := by ring
            _ ≤ (2 * (2 * K * Real.sqrt (q : ℝ))) ^ q := h
            _ = (4 * K * Real.sqrt (q : ℝ)) ^ q := by ring

/--
A probability-measure `psi_2` bound gives the book-style natural real-Lp growth
bound `||X||_q <= 4 * K * sqrt(q)`.
-/
theorem realLpNorm_nat_le_sqrt_of_psi2Bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ} {q : ℕ}
    (hψ : Psi2Bound P X K) (hq : 1 ≤ q) :
    realLpNorm P X (q : ENNReal) ≤
      ENNReal.ofReal (4 * K * Real.sqrt (q : ℝ)) := by
  have hqposNat : 0 < q := hq
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqposNat
  have hscale_pos : 0 < 4 * K * Real.sqrt (q : ℝ) :=
    mul_pos (mul_pos (by norm_num) hψ.1) (Real.sqrt_pos_of_pos hqpos)
  have hq_ne : q ≠ 0 := by
    exact Nat.ne_of_gt hqposNat
  let B : ℝ := (4 * K * Real.sqrt (q : ℝ)) ^ q
  have hB_nonneg : 0 ≤ B := by
    simpa [B] using pow_nonneg hscale_pos.le q
  have hbound : absMomentNat P X q ≤ ENNReal.ofReal B := by
    simpa [B] using
      absMomentNat_le_sqrt_growth_of_psi2Bound
        (P := P) (X := X) (K := K) (q := q) hψ hq
  have hnorm :=
    realLpNorm_nat_le_of_absMomentNat_le
      (P := P) (X := X) (q := q) (B := B) hq_ne hB_nonneg hbound
  have hroot :
      B ^ (1 / (q : ℝ)) = 4 * K * Real.sqrt (q : ℝ) := by
    simpa [B] using
      pow_rpow_inv_natCast_of_pos (K := 4 * K * Real.sqrt (q : ℝ)) hscale_pos hq
  exact hnorm.trans_eq (by rw [hroot])

/--
A probability-measure `psi_2` bound gives a crude linear real-Lp growth bound
at every nonzero natural exponent:
`||X||_q <= 8 * K * q`.

This is the clean consequence of the existing factorial-growth estimate, using
`q! <= q^q`.  It is weaker than the sharp `sqrt(q)` subGaussian moment growth.
-/
theorem realLpNorm_nat_le_linear_of_psi2Bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ} {q : ℕ}
    (hψ : Psi2Bound P X K) (hq : 1 ≤ q) :
    realLpNorm P X (q : ENNReal) ≤ ENNReal.ofReal (8 * K * (q : ℝ)) := by
  have hK_nonneg : 0 ≤ K := hψ.1.le
  have hq_ne : q ≠ 0 := by
    have hqpos : 0 < q := hq
    exact Nat.ne_of_gt hqpos
  let B : ℝ := Real.exp ((1 : ℝ) / 4) * K ^ q * (Nat.factorial q : ℝ) * 2
  have hB_nonneg : 0 ≤ B := by
    simp only [B]
    positivity
  have hbound : absMomentNat P X q ≤ ENNReal.ofReal B := by
    have h := absMomentNat_le_of_psi2Bound (P := P) (X := X) (K := K) hψ q
    let C : ℝ := Real.exp ((1 : ℝ) / 4) * K ^ q * (Nat.factorial q : ℝ)
    have hC_nonneg : 0 ≤ C := by
      simp only [C]
      positivity
    have hC_eq : ENNReal.ofReal C * 2 = ENNReal.ofReal (C * 2) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num]
      rw [ENNReal.ofReal_mul hC_nonneg]
    refine h.trans_eq ?_
    simpa [B, C, mul_assoc, mul_left_comm, mul_comm] using hC_eq
  have hnorm :=
    realLpNorm_nat_le_of_absMomentNat_le
      (P := P) (X := X) (q := q) (B := B) hq_ne hB_nonneg hbound
  exact hnorm.trans
    (ENNReal.ofReal_le_ofReal
      (by simpa [B] using factorial_moment_root_le_linear (K := K) hψ.1 hq))

/--
SubGaussian tail control gives a second absolute natural-moment bound after the
existing `K -> 2 * K` tail-to-Orlicz scale loss.
-/
theorem absMomentNat_two_le_of_subGaussianTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X) (hTail : SubGaussianTail P X K) :
    absMomentNat P X 2 ≤ ENNReal.ofReal ((2 * K) ^ 2) := by
  exact absMomentNat_two_le_of_psi2Bound
    (P := P) (X := X) (K := 2 * K)
    (psi2Bound_of_subGaussianTail (P := P) (X := X) (K := K) hX hTail)

/--
SubGaussian tail control gives finiteness of the second absolute natural moment.
-/
theorem finiteAbsMomentNat_two_of_subGaussianTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X) (hTail : SubGaussianTail P X K) :
    finiteAbsMomentNat P X 2 := by
  unfold finiteAbsMomentNat
  exact lt_of_le_of_lt
    (absMomentNat_two_le_of_subGaussianTail (P := P) (X := X) (K := K) hX hTail)
    ENNReal.ofReal_lt_top

/--
SubGaussian tail control gives every natural absolute moment after the existing
`K -> 2 * K` tail-to-Orlicz scale loss.

The bound is factorial-growth, not the sharp `sqrt(q)` growth estimate.
-/
theorem absMomentNat_le_of_subGaussianTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X) (hTail : SubGaussianTail P X K) (q : ℕ) :
    absMomentNat P X q ≤
      ENNReal.ofReal
        (Real.exp (1 / 4) * (2 * K) ^ q * (Nat.factorial q : ℝ)) * 2 := by
  exact absMomentNat_le_of_psi2Bound
    (P := P) (X := X) (K := 2 * K)
    (psi2Bound_of_subGaussianTail (P := P) (X := X) (K := K) hX hTail) q

/-- SubGaussian tail control gives finiteness of every natural absolute moment. -/
theorem finiteAbsMomentNat_of_subGaussianTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X) (hTail : SubGaussianTail P X K) (q : ℕ) :
    finiteAbsMomentNat P X q := by
  exact finiteAbsMomentNat_of_psi2Bound
    (P := P) (X := X) (K := 2 * K)
    (psi2Bound_of_subGaussianTail (P := P) (X := X) (K := K) hX hTail) q

/--
SubGaussian tail control gives a crude linear real-Lp growth bound after the
existing `K -> 2 * K` tail-to-Orlicz scale loss:
`||X||_q <= 16 * K * q`.
-/
theorem realLpNorm_nat_le_linear_of_subGaussianTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ} {q : ℕ}
    (hX : IsRealRandomVariable P X) (hTail : SubGaussianTail P X K) (hq : 1 ≤ q) :
    realLpNorm P X (q : ENNReal) ≤ ENNReal.ofReal (16 * K * (q : ℝ)) := by
  have h :=
    realLpNorm_nat_le_linear_of_psi2Bound
      (P := P) (X := X) (K := 2 * K) (q := q)
      (psi2Bound_of_subGaussianTail (P := P) (X := X) (K := K) hX hTail) hq
  have hscale : 8 * (2 * K) * (q : ℝ) = 16 * K * (q : ℝ) := by ring
  exact h.trans_eq (by rw [hscale])

/--
SubGaussian tail control gives the book-style natural real-Lp growth bound
after the existing `K -> 2 * K` tail-to-Orlicz scale loss:
`||X||_q <= 8 * K * sqrt(q)`.
-/
theorem realLpNorm_nat_le_sqrt_of_subGaussianTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ} {q : ℕ}
    (hX : IsRealRandomVariable P X) (hTail : SubGaussianTail P X K) (hq : 1 ≤ q) :
    realLpNorm P X (q : ENNReal) ≤
      ENNReal.ofReal (8 * K * Real.sqrt (q : ℝ)) := by
  have h :=
    realLpNorm_nat_le_sqrt_of_psi2Bound
      (P := P) (X := X) (K := 2 * K) (q := q)
      (psi2Bound_of_subGaussianTail (P := P) (X := X) (K := K) hX hTail) hq
  have hscale : 4 * (2 * K) * Real.sqrt (q : ℝ) =
      8 * K * Real.sqrt (q : ℝ) := by ring
  exact h.trans_eq (by rw [hscale])

/--
A probability-measure `psi_2` bound gives the sharp natural-exponent
subGaussian moment interface with scale `4 * K`.
-/
theorem subGaussianMomentNatSqrt_of_psi2Bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ} (hψ : Psi2Bound P X K) :
    SubGaussianMomentNatSqrt P X (4 * K) := by
  refine ⟨mul_pos (by norm_num) hψ.1, ?_⟩
  intro q hq
  have h :=
    realLpNorm_nat_le_sqrt_of_psi2Bound
      (P := P) (X := X) (K := K) (q := q) hψ hq
  have hscale :
      (4 * K) * Real.sqrt (q : ℝ) =
        4 * K * Real.sqrt (q : ℝ) := by ring
  exact h.trans_eq (by rw [hscale])

/--
SubGaussian tail control gives the sharp natural-exponent subGaussian moment
interface with scale `8 * K`, after the existing `K -> 2 * K` tail-to-Orlicz
scale loss.
-/
theorem subGaussianMomentNatSqrt_of_subGaussianTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X) (hTail : SubGaussianTail P X K) :
    SubGaussianMomentNatSqrt P X (8 * K) := by
  refine ⟨mul_pos (by norm_num) hTail.1, ?_⟩
  intro q hq
  have h :=
    realLpNorm_nat_le_sqrt_of_subGaussianTail
      (P := P) (X := X) (K := K) (q := q) hX hTail hq
  have hscale :
      (8 * K) * Real.sqrt (q : ℝ) =
        8 * K * Real.sqrt (q : ℝ) := by ring
  exact h.trans_eq (by rw [hscale])

/--
Lp monotonicity promotes a finite `ENNReal` exponent to the natural ceiling of
its real value.
-/
theorem realLpNorm_le_natCeil_of_realExponent
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {X : RealRandomVariable Omega} {p : ENNReal}
    (hX : IsRealRandomVariable P X)
    (hp_ne_top : Not (p = (Top.top : ENNReal))) :
    realLpNorm P X p <=
      realLpNorm P X (Nat.ceil (ENNReal.toReal p) : ENNReal) := by
  have hp_toReal_le :
      p <= (Nat.ceil (ENNReal.toReal p) : ENNReal) := by
    calc
      p = ENNReal.ofReal (ENNReal.toReal p) := (ENNReal.ofReal_toReal hp_ne_top).symm
      _ <= ENNReal.ofReal (Nat.ceil (ENNReal.toReal p) : Real) :=
        ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
      _ = (Nat.ceil (ENNReal.toReal p) : ENNReal) :=
        ENNReal.ofReal_natCast _
  exact
    MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      hp_toReal_le hX.aestronglyMeasurable

/-- For finite `p >= 1`, the natural ceiling only loses a factor `2` under sqrt. -/
theorem sqrt_natCeil_toReal_le_two_sqrt
    {p : ENNReal} (hp : 1 <= p) (hp_ne_top : Not (p = (Top.top : ENNReal))) :
    Real.sqrt (Nat.ceil (ENNReal.toReal p) : Real) <=
      2 * Real.sqrt (ENNReal.toReal p) := by
  have hp_toReal_one : (1 : Real) <= ENNReal.toReal p := by
    simpa [ENNReal.toReal_one] using ENNReal.toReal_mono hp_ne_top hp
  have hp_toReal_nonneg : 0 <= ENNReal.toReal p := by
    linarith
  have hceil_le_four :
      (Nat.ceil (ENNReal.toReal p) : Real) <= 4 * ENNReal.toReal p := by
    have hceil_lt :
        (Nat.ceil (ENNReal.toReal p) : Real) < ENNReal.toReal p + 1 :=
      Nat.ceil_lt_add_one hp_toReal_nonneg
    nlinarith
  calc
    Real.sqrt (Nat.ceil (ENNReal.toReal p) : Real)
        <= Real.sqrt (4 * ENNReal.toReal p) := Real.sqrt_le_sqrt hceil_le_four
    _ = Real.sqrt 4 * Real.sqrt (ENNReal.toReal p) := by
      rw [Real.sqrt_mul (by norm_num : 0 <= (4 : Real))]
    _ = 2 * Real.sqrt (ENNReal.toReal p) := by
      have hsqrt_four : Real.sqrt 4 = (2 : Real) := by
        rw [show (4 : Real) = 2 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
      rw [hsqrt_four]

/-- For finite `p >= 1`, the natural ceiling only loses a factor `2` linearly. -/
theorem natCeil_toReal_le_two_mul_toReal
    {p : ENNReal} (hp : 1 <= p) (hp_ne_top : Not (p = (Top.top : ENNReal))) :
    (Nat.ceil (ENNReal.toReal p) : Real) <= 2 * ENNReal.toReal p := by
  have hp_toReal_one : (1 : Real) <= ENNReal.toReal p := by
    simpa [ENNReal.toReal_one] using ENNReal.toReal_mono hp_ne_top hp
  have hp_toReal_nonneg : 0 <= ENNReal.toReal p := by
    linarith
  have hceil_lt :
      (Nat.ceil (ENNReal.toReal p) : Real) < ENNReal.toReal p + 1 :=
    Nat.ceil_lt_add_one hp_toReal_nonneg
  linarith

/--
A probability-measure `psi_2` bound gives real-`Lp` sqrt growth at every finite
`ENNReal` exponent `p >= 1`.
-/
theorem realLpNorm_le_sqrt_of_psi2Bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {X : RealRandomVariable Omega} {K : Real}
    (hX : IsRealRandomVariable P X) (hpsi : Psi2Bound P X K)
    {p : ENNReal} (hp : 1 <= p) (hp_ne_top : Not (p = (Top.top : ENNReal))) :
    realLpNorm P X p <= ENNReal.ofReal (8 * K * Real.sqrt (ENNReal.toReal p)) := by
  let q : Nat := Nat.ceil (ENNReal.toReal p)
  have hp_toReal_one : (1 : Real) <= ENNReal.toReal p := by
    simpa [ENNReal.toReal_one] using ENNReal.toReal_mono hp_ne_top hp
  have hq : 1 <= q := by
    have hq_real : (1 : Real) <= (q : Real) := hp_toReal_one.trans (Nat.le_ceil _)
    exact_mod_cast hq_real
  have hmono :=
    realLpNorm_le_natCeil_of_realExponent
      (P := P) (X := X) (p := p) hX hp_ne_top
  have hnat :=
    realLpNorm_nat_le_sqrt_of_psi2Bound
      (P := P) (X := X) (K := K) (q := q) hpsi hq
  have hsqrtq :
      Real.sqrt (q : Real) <= 2 * Real.sqrt (ENNReal.toReal p) := by
    change Real.sqrt (Nat.ceil (ENNReal.toReal p) : Real) <=
      2 * Real.sqrt (ENNReal.toReal p)
    exact sqrt_natCeil_toReal_le_two_sqrt (p := p) hp hp_ne_top
  have hscale :
      4 * K * Real.sqrt (q : Real) <= 8 * K * Real.sqrt (ENNReal.toReal p) := by
    have hK_nonneg : 0 <= 4 * K := mul_nonneg (by norm_num) hpsi.1.le
    calc
      4 * K * Real.sqrt (q : Real)
          <= 4 * K * (2 * Real.sqrt (ENNReal.toReal p)) := by
            exact mul_le_mul_of_nonneg_left hsqrtq hK_nonneg
      _ = 8 * K * Real.sqrt (ENNReal.toReal p) := by ring
  exact hmono.trans (hnat.trans (ENNReal.ofReal_le_ofReal hscale))

/--
A `psi_2` bound gives the full finite-`ENNReal` subGaussian moment interface
with scale `8 * K`.
-/
theorem subGaussianMoment_of_psi2Bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {X : RealRandomVariable Omega} {K : Real}
    (hX : IsRealRandomVariable P X) (hpsi : Psi2Bound P X K) :
    SubGaussianMoment P X (8 * K) := by
  refine And.intro (mul_pos (by norm_num) hpsi.1) ?_
  intro p hp hp_ne_top
  have h :=
    realLpNorm_le_sqrt_of_psi2Bound
      (P := P) (X := X) (K := K) hX hpsi hp hp_ne_top
  have hscale :
      (8 * K) * Real.sqrt (ENNReal.toReal p) =
        8 * K * Real.sqrt (ENNReal.toReal p) := by ring
  rw [hscale]
  exact h

/--
SubGaussian tail control gives real-`Lp` sqrt growth at every finite `ENNReal`
exponent `p >= 1`, after the existing `K -> 2 * K` tail-to-Orlicz scale loss.
-/
theorem realLpNorm_le_sqrt_of_subGaussianTail
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {X : RealRandomVariable Omega} {K : Real}
    (hX : IsRealRandomVariable P X) (hTail : SubGaussianTail P X K)
    {p : ENNReal} (hp : 1 <= p) (hp_ne_top : Not (p = (Top.top : ENNReal))) :
    realLpNorm P X p <= ENNReal.ofReal (16 * K * Real.sqrt (ENNReal.toReal p)) := by
  have h :=
    realLpNorm_le_sqrt_of_psi2Bound
      (P := P) (X := X) (K := 2 * K)
      hX (psi2Bound_of_subGaussianTail (P := P) (X := X) (K := K) hX hTail)
      hp hp_ne_top
  have hscale :
      8 * (2 * K) * Real.sqrt (ENNReal.toReal p) =
        16 * K * Real.sqrt (ENNReal.toReal p) := by ring
  exact h.trans_eq (by rw [hscale])

/--
SubGaussian tail control gives the full finite-`ENNReal` subGaussian moment
interface with scale `16 * K`.
-/
theorem subGaussianMoment_of_subGaussianTail
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {X : RealRandomVariable Omega} {K : Real}
    (hX : IsRealRandomVariable P X) (hTail : SubGaussianTail P X K) :
    SubGaussianMoment P X (16 * K) := by
  refine And.intro (mul_pos (by norm_num) hTail.1) ?_
  intro p hp hp_ne_top
  have h :=
    realLpNorm_le_sqrt_of_subGaussianTail
      (P := P) (X := X) (K := K) hX hTail hp hp_ne_top
  have hscale :
      (16 * K) * Real.sqrt (ENNReal.toReal p) =
        16 * K * Real.sqrt (ENNReal.toReal p) := by ring
  rw [hscale]
  exact h

/-- A `psi_2` bound gives the natural factorial-growth subGaussian moment form. -/
theorem subGaussianMomentNat_of_psi2Bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ} (hψ : Psi2Bound P X K) :
    SubGaussianMomentNat P X K := by
  exact ⟨hψ.1, fun q _ =>
    absMomentNat_le_of_psi2Bound (P := P) (X := X) (K := K) hψ q⟩

/--
SubGaussian tail control gives the natural factorial-growth subGaussian moment
form after the existing `K -> 2 * K` tail-to-Orlicz scale loss.
-/
theorem subGaussianMomentNat_of_subGaussianTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X) (hTail : SubGaussianTail P X K) :
    SubGaussianMomentNat P X (2 * K) := by
  refine ⟨mul_pos two_pos hTail.1, ?_⟩
  intro q _
  exact absMomentNat_le_of_subGaussianTail
    (P := P) (X := X) (K := K) hX hTail q

/-- A `psi_1` bound controls the first absolute natural moment. -/
theorem absMomentNat_one_le_of_psi1Bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : RealRandomVariable Ω} {K : ℝ} (hψ : Psi1Bound P X K) :
    absMomentNat P X 1 ≤ ENNReal.ofReal K := by
  rcases hψ with ⟨hK, hψ_int⟩
  unfold absMomentNat
  simp only [pow_one]
  calc
    (∫⁻ ω, ENNReal.ofReal |X ω| ∂P)
        ≤ ∫⁻ ω, ENNReal.ofReal (K * (Real.exp (|X ω| / K) - 1)) ∂P := by
          refine lintegral_mono ?_
          intro ω
          exact ENNReal.ofReal_le_ofReal
            (abs_le_scale_mul_exp_sub_one (x := X ω) hK)
    _ = ∫⁻ ω,
          ENNReal.ofReal K *
            ENNReal.ofReal (Real.exp (|X ω| / K) - 1) ∂P := by
          apply lintegral_congr_ae
          exact ae_of_all P fun ω => by
            change ENNReal.ofReal (K * (Real.exp (|X ω| / K) - 1)) =
              ENNReal.ofReal K * ENNReal.ofReal (Real.exp (|X ω| / K) - 1)
            rw [ENNReal.ofReal_mul hK.le]
    _ = ENNReal.ofReal K *
          ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K) - 1) ∂P := by
          rw [lintegral_const_mul']
          exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * 1 := by
          gcongr
    _ = ENNReal.ofReal K := by simp

/--
SubExponential tail control gives a first absolute natural-moment bound after
the existing `K -> 3 * K` tail-to-Orlicz scale loss.
-/
theorem absMomentNat_one_le_of_subExponentialTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X) (hTail : SubExponentialTail P X K) :
    absMomentNat P X 1 ≤ ENNReal.ofReal (3 * K) := by
  exact absMomentNat_one_le_of_psi1Bound
    (P := P) (X := X) (K := 3 * K)
    (psi1Bound_of_subExponentialTail (P := P) (X := X) (K := K) hX hTail)

/--
A probability-measure `psi_1` bound controls every natural absolute moment.

The bound is the standard factorial-growth estimate
`E |X|^q <= 2 * K^q * q!`, obtained from `x^q / q! <= exp x`.
-/
theorem absMomentNat_le_of_psi1Bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ} (hψ : Psi1Bound P X K) (q : ℕ) :
    absMomentNat P X q ≤
      ENNReal.ofReal (2 * K ^ q * (Nat.factorial q : ℝ)) := by
  have h_exp :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K)) ∂P) ≤
        (2 : ENNReal) := by
    exact lintegral_exp_abs_div_le_two_of_psi1Bound
      (P := P) (X := X) (K := K) hψ
  rcases hψ with ⟨hK, _⟩
  let C : ℝ := K ^ q * (Nat.factorial q : ℝ)
  have hC_nonneg : 0 ≤ C := by
    simp only [C]
    positivity
  unfold absMomentNat
  calc
    (∫⁻ ω, ENNReal.ofReal (|X ω| ^ q) ∂P)
        ≤ ∫⁻ ω, ENNReal.ofReal (C * Real.exp (|X ω| / K)) ∂P := by
          refine lintegral_mono ?_
          intro ω
          exact ENNReal.ofReal_le_ofReal
            (by
              simpa [C, mul_assoc] using
                abs_pow_le_exp_linear_factorial (x := X ω) (K := K) hK q)
    _ = ∫⁻ ω,
          ENNReal.ofReal C *
            ENNReal.ofReal (Real.exp (|X ω| / K)) ∂P := by
          apply lintegral_congr_ae
          exact ae_of_all P fun ω => by
            change ENNReal.ofReal (C * Real.exp (|X ω| / K)) =
              ENNReal.ofReal C *
                ENNReal.ofReal (Real.exp (|X ω| / K))
            rw [ENNReal.ofReal_mul hC_nonneg]
    _ = ENNReal.ofReal C *
          ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K)) ∂P := by
          rw [lintegral_const_mul']
          exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * 2 := by
          gcongr
    _ = ENNReal.ofReal (2 * K ^ q * (Nat.factorial q : ℝ)) := by
          rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num]
          rw [← ENNReal.ofReal_mul hC_nonneg]
          congr 1
          simp [C]
          ring

/--
SubExponential tail control gives every natural absolute moment after the
existing `K -> 3 * K` tail-to-Orlicz scale loss.
-/
theorem absMomentNat_le_of_subExponentialTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ}
    (hX : IsRealRandomVariable P X) (hTail : SubExponentialTail P X K) (q : ℕ) :
    absMomentNat P X q ≤
      ENNReal.ofReal (2 * (3 * K) ^ q * (Nat.factorial q : ℝ)) := by
  exact absMomentNat_le_of_psi1Bound
    (P := P) (X := X) (K := 3 * K)
    (psi1Bound_of_subExponentialTail (P := P) (X := X) (K := K) hX hTail) q

/--
A probability-measure `psi_1` bound gives natural real-Lp growth
`||X||_q <= 8 * K * q`.
-/
theorem realLpNorm_nat_le_linear_of_psi1Bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ} {q : ℕ}
    (hψ : Psi1Bound P X K) (hq : 1 ≤ q) :
    realLpNorm P X (q : ENNReal) ≤ ENNReal.ofReal (8 * K * (q : ℝ)) := by
  have hq_ne : q ≠ 0 := by
    have hqpos : 0 < q := hq
    exact Nat.ne_of_gt hqpos
  let B : ℝ := 2 * K ^ q * (Nat.factorial q : ℝ)
  have hB_nonneg : 0 ≤ B := by
    simp only [B]
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hψ.1.le q)) (by positivity)
  have hbound : absMomentNat P X q ≤ ENNReal.ofReal B := by
    simpa [B] using absMomentNat_le_of_psi1Bound (P := P) (X := X) (K := K) hψ q
  have hnorm :=
    realLpNorm_nat_le_of_absMomentNat_le
      (P := P) (X := X) (q := q) (B := B) hq_ne hB_nonneg hbound
  exact hnorm.trans
    (ENNReal.ofReal_le_ofReal
      (by simpa [B] using psi1_factorial_moment_root_le_linear (K := K) hψ.1 hq))

/--
SubExponential tail control gives natural real-Lp growth after the
`K -> 3 * K` tail-to-Orlicz scale loss: `||X||_q <= 24 * K * q`.
-/
theorem realLpNorm_nat_le_linear_of_subExponentialTail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : RealRandomVariable Ω} {K : ℝ} {q : ℕ}
    (hX : IsRealRandomVariable P X) (hTail : SubExponentialTail P X K)
    (hq : 1 ≤ q) :
    realLpNorm P X (q : ENNReal) ≤ ENNReal.ofReal (24 * K * (q : ℝ)) := by
  have h :=
    realLpNorm_nat_le_linear_of_psi1Bound
      (P := P) (X := X) (K := 3 * K) (q := q)
      (psi1Bound_of_subExponentialTail (P := P) (X := X) (K := K) hX hTail) hq
  have hscale : 8 * (3 * K) * (q : ℝ) = 24 * K * (q : ℝ) := by ring
  exact h.trans_eq (by rw [hscale])

/--
A probability-measure `psi_1` bound gives linear real-`Lp` growth at every
finite `ENNReal` exponent `p >= 1`.
-/
theorem realLpNorm_le_linear_of_psi1Bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {X : RealRandomVariable Omega} {K : Real}
    (hX : IsRealRandomVariable P X) (hψ : Psi1Bound P X K)
    {p : ENNReal} (hp : 1 <= p) (hp_ne_top : Not (p = (Top.top : ENNReal))) :
    realLpNorm P X p <= ENNReal.ofReal (16 * K * ENNReal.toReal p) := by
  let q : Nat := Nat.ceil (ENNReal.toReal p)
  have hp_toReal_one : (1 : Real) <= ENNReal.toReal p := by
    simpa [ENNReal.toReal_one] using ENNReal.toReal_mono hp_ne_top hp
  have hq : 1 <= q := by
    have hq_real : (1 : Real) <= (q : Real) := hp_toReal_one.trans (Nat.le_ceil _)
    exact_mod_cast hq_real
  have hmono :=
    realLpNorm_le_natCeil_of_realExponent
      (P := P) (X := X) (p := p) hX hp_ne_top
  have hnat :=
    realLpNorm_nat_le_linear_of_psi1Bound
      (P := P) (X := X) (K := K) (q := q) hψ hq
  have hceil :
      (q : Real) <= 2 * ENNReal.toReal p := by
    change (Nat.ceil (ENNReal.toReal p) : Real) <= 2 * ENNReal.toReal p
    exact natCeil_toReal_le_two_mul_toReal (p := p) hp hp_ne_top
  have hscale :
      8 * K * (q : Real) <= 16 * K * ENNReal.toReal p := by
    have hcoef_nonneg : 0 <= 8 * K := mul_nonneg (by norm_num) hψ.1.le
    calc
      8 * K * (q : Real)
          <= 8 * K * (2 * ENNReal.toReal p) := by
            exact mul_le_mul_of_nonneg_left hceil hcoef_nonneg
      _ = 16 * K * ENNReal.toReal p := by ring
  exact hmono.trans (hnat.trans (ENNReal.ofReal_le_ofReal hscale))

/--
A `psi_1` bound gives the full finite-`ENNReal` subExponential moment
interface with scale `16 * K`.
-/
theorem subExponentialMoment_of_psi1Bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {X : RealRandomVariable Omega} {K : Real}
    (hX : IsRealRandomVariable P X) (hψ : Psi1Bound P X K) :
    SubExponentialMoment P X (16 * K) := by
  refine And.intro (mul_pos (by norm_num) hψ.1) ?_
  intro p hp hp_ne_top
  have h :=
    realLpNorm_le_linear_of_psi1Bound
      (P := P) (X := X) (K := K) hX hψ hp hp_ne_top
  have hscale :
      (16 * K) * ENNReal.toReal p =
        16 * K * ENNReal.toReal p := by ring
  rw [hscale]
  exact h

/--
SubExponential tail control gives linear real-`Lp` growth at every finite
`ENNReal` exponent `p >= 1`, after the `K -> 3 * K` tail-to-Orlicz scale loss.
-/
theorem realLpNorm_le_linear_of_subExponentialTail
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {X : RealRandomVariable Omega} {K : Real}
    (hX : IsRealRandomVariable P X) (hTail : SubExponentialTail P X K)
    {p : ENNReal} (hp : 1 <= p) (hp_ne_top : Not (p = (Top.top : ENNReal))) :
    realLpNorm P X p <= ENNReal.ofReal (48 * K * ENNReal.toReal p) := by
  have h :=
    realLpNorm_le_linear_of_psi1Bound
      (P := P) (X := X) (K := 3 * K)
      hX (psi1Bound_of_subExponentialTail (P := P) (X := X) (K := K) hX hTail)
      hp hp_ne_top
  have hscale :
      16 * (3 * K) * ENNReal.toReal p =
        48 * K * ENNReal.toReal p := by ring
  exact h.trans_eq (by rw [hscale])

/--
SubExponential tail control gives the full finite-`ENNReal` subExponential
moment interface with scale `48 * K`.
-/
theorem subExponentialMoment_of_subExponentialTail
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {X : RealRandomVariable Omega} {K : Real}
    (hX : IsRealRandomVariable P X) (hTail : SubExponentialTail P X K) :
    SubExponentialMoment P X (48 * K) := by
  refine And.intro (mul_pos (by norm_num) hTail.1) ?_
  intro p hp hp_ne_top
  have h :=
    realLpNorm_le_linear_of_subExponentialTail
      (P := P) (X := X) (K := K) hX hTail hp hp_ne_top
  have hscale :
      (48 * K) * ENNReal.toReal p =
        48 * K * ENNReal.toReal p := by ring
  rw [hscale]
  exact h

/--
Typed target for the future all-natural-exponent subGaussian moment theorem.

This statement records the intended absolute-moment normal form without
claiming the full proof yet.
-/
abbrev subGaussianMomentNatOfSubGaussianTailStatement
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  IsRealRandomVariable P X →
    SubGaussianTail P X K →
      ∀ q : ℕ, 1 ≤ q →
        absMomentNat P X q ≤ ENNReal.ofReal ((2 * K * Real.sqrt (q : ℝ)) ^ q)

/--
Compatibility statement for the deterministic real-analysis route to sharp
moment growth.

The proved helper is stronger, with constant `2`; this statement preserves the
looser constant-`4` normal form used by earlier theorem-planning docs.
-/
abbrev powLeSqrtGrowthMulExpSqStatement : Prop :=
  ∀ x : ℝ, 0 ≤ x →
    ∀ q : ℕ, 1 ≤ q →
      x ^ q ≤ (4 * Real.sqrt (q : ℝ)) ^ q * Real.exp (x ^ 2 / 4)

/-- The deterministic real inequality target is realized by a stronger constant-`2` theorem. -/
theorem powLeSqrtGrowthMulExpSq : powLeSqrtGrowthMulExpSqStatement := by
  intro x hx q hq
  exact pow_le_four_sqrt_mul_exp_sq (x := x) hx (q := q) hq

/--
Compatibility statement for the book-style `psi_2` natural-exponent
moment-growth theorem.

The current main theorem proves constant `4`; this statement keeps the looser
constant `8` form available for older statement-layer references.
-/
abbrev sqrtMomentGrowthOfPsi2Statement
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  Psi2Bound P X K →
    ∀ q : ℕ, 1 ≤ q →
      realLpNorm P X (q : ENNReal) ≤
        ENNReal.ofReal (8 * K * Real.sqrt (q : ℝ))

/-- The typed `psi_2` sharp moment-growth target follows from the sharper constant-`4` theorem. -/
theorem sqrtMomentGrowthOfPsi2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : RealRandomVariable Ω) (K : ℝ) :
    sqrtMomentGrowthOfPsi2Statement P X K := by
  intro hψ q hq
  exact (realLpNorm_nat_le_sqrt_of_psi2Bound
      (P := P) (X := X) (K := K) (q := q) hψ hq).trans
    (ENNReal.ofReal_le_ofReal (by
      have hscale_nonneg : 0 ≤ K * Real.sqrt (q : ℝ) :=
        mul_nonneg hψ.1.le (Real.sqrt_nonneg _)
      nlinarith))

/--
Compatibility statement for the book-style subGaussian-tail natural-exponent
moment-growth theorem.

The current main theorem proves constant `8`; this statement keeps the looser
constant `16` form available for older statement-layer references.
-/
abbrev sqrtMomentGrowthOfSubGaussianTailStatement
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : RealRandomVariable Ω) (K : ℝ) : Prop :=
  IsRealRandomVariable P X →
    SubGaussianTail P X K →
      ∀ q : ℕ, 1 ≤ q →
        realLpNorm P X (q : ENNReal) ≤
          ENNReal.ofReal (16 * K * Real.sqrt (q : ℝ))

/--
The typed subGaussian-tail sharp moment-growth target follows from the sharper
constant-`8` tail theorem.
-/
theorem sqrtMomentGrowthOfSubGaussianTail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : RealRandomVariable Ω) (K : ℝ) :
    sqrtMomentGrowthOfSubGaussianTailStatement P X K := by
  intro hX hTail q hq
  exact (realLpNorm_nat_le_sqrt_of_subGaussianTail
      (P := P) (X := X) (K := K) (q := q) hX hTail hq).trans
    (ENNReal.ofReal_le_ofReal (by
      have hscale_nonneg : 0 ≤ K * Real.sqrt (q : ℝ) :=
        mul_nonneg hTail.1.le (Real.sqrt_nonneg _)
      nlinarith))

end

end HighDimProb
