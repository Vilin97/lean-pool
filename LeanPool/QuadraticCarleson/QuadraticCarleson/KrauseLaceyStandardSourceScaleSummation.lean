/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStandardSourceInterpolation
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyScaleSummation

/-!
# Physical-scale summation for the scalar-standard contribution

The source's fixed-physical-scale estimate contains the factor `j * 2⁻ʲ`
before taking the `L^q` norm. This module absorbs its `q`-th root into the
same geometric ratio used by the rest of the Krause--Lacey summation. The
last theorem is uniform over every finite set of nonnegative physical
scales, so no interval-cardinality loss remains.
-/

open Function MeasureTheory Set
open scoped ENNReal BigOperators

namespace QuadraticCarleson
namespace KrauseLaceyBadScale


/-- Elementary exponential domination used to absorb the source factor
`j` into geometric physical-scale decay. -/
theorem nat_sq_le_four_mul_two_pow : ∀ n : ℕ,
    (n : ℝ) ^ 2 ≤ 4 * (2 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
      by_cases hn : n ≤ 2
      · interval_cases n <;> norm_num
      · have hn3 : 3 ≤ n := by omega
        calc
          ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by
            norm_num only [Nat.cast_add, Nat.cast_one]
            have hn0 : 0 ≤ (n : ℝ) := by positivity
            have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
            nlinarith
          _ ≤ 2 * (4 * (2 : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = 4 * (2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

theorem nat_le_two_mul_two_rpow_half (n : ℕ) :
    (n : ℝ) ≤ 2 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  rw [← sq_le_sq₀ (by positivity : (0 : ℝ) ≤ n)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))]
  calc
    (n : ℝ) ^ 2 ≤ 4 * (2 : ℝ) ^ n := nat_sq_le_four_mul_two_pow n
    _ = (2 * (2 : ℝ) ^ ((n : ℝ) / 2)) ^ 2 := by
      rw [mul_pow, show (4 : ℝ) = 2 ^ 2 by norm_num,
        ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
        show (n : ℝ) / 2 * (2 : ℕ) = n by norm_num,
        Real.rpow_natCast]

theorem int_le_two_mul_two_rpow_half {j : ℤ} (hj : 0 ≤ j) :
    (j : ℝ) ≤ 2 * (2 : ℝ) ^ ((j : ℝ) / 2) := by
  have h := nat_le_two_mul_two_rpow_half j.toNat
  have hjnat : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj
  have hjnatr : (j.toNat : ℝ) = (j : ℝ) := by exact_mod_cast hjnat
  rw [hjnatr] at h
  exact h

/-- The polynomial factor in the squared estimate is absorbed by half of
the available exponential decay. -/
theorem int_div_two_zpow_le_decay {j : ℤ} (hj : 0 ≤ j) :
    (j : ℝ) / (2 : ℝ) ^ j ≤
      2 * (2 : ℝ) ^ (-(j : ℝ) / 2) := by
  rw [div_le_iff₀ (zpow_pos (by norm_num) j)]
  calc
    (j : ℝ) ≤ 2 * (2 : ℝ) ^ ((j : ℝ) / 2) :=
      int_le_two_mul_two_rpow_half hj
    _ = (2 * (2 : ℝ) ^ (-(j : ℝ) / 2)) * (2 : ℝ) ^ j := by
      rw [← Real.rpow_intCast]
      rw [mul_assoc]
      congr 1
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- After the `q`-th root, the fixed-scale source decay is controlled by
twice the project-wide geometric summation ratio. -/
theorem int_ratio_rpow_le_two_mul_scaleDecayRatio_zpow
    {q : ℝ} (hq : 2 ≤ q) {j : ℤ} (hj : 0 ≤ j) :
    ((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q) ≤
      2 * (scaleDecayRatio q) ^ j := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hratio0 : 0 ≤ (j : ℝ) / (2 : ℝ) ^ j := by positivity
  have hroot := Real.rpow_le_rpow hratio0
    (int_div_two_zpow_le_decay hj) (by positivity : (0 : ℝ) ≤ 1 / q)
  calc
    ((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q) ≤
        (2 * (2 : ℝ) ^ (-(j : ℝ) / 2)) ^ (1 / q) := hroot
    _ = (2 : ℝ) ^ (1 / q) *
        (2 : ℝ) ^ ((-(j : ℝ) / 2) * (1 / q)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (Real.rpow_nonneg (by norm_num) _)]
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (2 : ℝ) ^ ((-(j : ℝ) / 2) * (1 / q)) := by
      gcongr
      have hq1 : (1 : ℝ) ≤ q := by linarith
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          ((div_le_one hq0).2 hq1)
    _ ≤ 2 * (2 : ℝ) ^ (-(j : ℝ) / (5 * q)) := by
      have hjr : 0 ≤ (j : ℝ) := by exact_mod_cast hj
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_)
        (by norm_num)
      field_simp
      nlinarith
    _ = 2 * (scaleDecayRatio q) ^ j := by
      unfold scaleDecayRatio
      congr 1
      rw [← Real.rpow_intCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

theorem int_ratio_rpow_le_two_mul_scaleDecayRatio_toNat_pow
    {q : ℝ} (hq : 2 ≤ q) {j : ℤ} (hj : 0 ≤ j) :
    ((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q) ≤
      2 * (scaleDecayRatio q) ^ j.toNat := by
  calc
    ((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q) ≤
        2 * (scaleDecayRatio q) ^ j :=
      int_ratio_rpow_le_two_mul_scaleDecayRatio_zpow hq hj
    _ = 2 * (scaleDecayRatio q) ^ j.toNat := by
      congr 1
      rw [← zpow_natCast, Int.toNat_of_nonneg hj]

/-- Uniform source-scale summation. The finite set need not be an interval;
only nonnegativity of its physical indices is used. -/
theorem finite_int_ratio_rpow_sum_le_forty_mul_q
    {q : ℝ} (hq : 2 ≤ q) (S : Finset ℤ)
    (hS : ∀ j ∈ S, 0 ≤ j) :
    (∑ j ∈ S, ((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q)) ≤ 40 * q := by
  let r : ℝ := scaleDecayRatio q
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hr0 : 0 ≤ r := scaleDecayRatio_nonneg
  have hr1 : r < 1 := scaleDecayRatio_lt_one hq0
  have hinj : Set.InjOn Int.toNat (↑S : Set ℤ) := by
    intro a ha b hb hab
    have ha0 := hS a (by simpa using ha)
    have hb0 := hS b (by simpa using hb)
    have haeq : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
    have hbeq : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
    exact haeq.symm.trans ((congrArg (fun n : ℕ ↦ (n : ℤ)) hab).trans hbeq)
  calc
    (∑ j ∈ S, ((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q)) ≤
        ∑ j ∈ S, 2 * r ^ j.toNat := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [r] using
        int_ratio_rpow_le_two_mul_scaleDecayRatio_toNat_pow hq (hS j hj)
    _ = ∑ n ∈ S.image Int.toNat, 2 * r ^ n := by
      rw [Finset.sum_image hinj]
    _ = 2 * ∑ n ∈ S.image Int.toNat, r ^ n := by
      rw [Finset.mul_sum]
    _ ≤ 2 * ∑' n : ℕ, r ^ n := by
      gcongr
      exact (summable_geometric_of_norm_lt_one
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)).sum_le_tsum
          (S.image Int.toNat) (fun n hn ↦ pow_nonneg hr0 n)
    _ ≤ 2 * (20 * q) := by
      gcongr
      simpa only [r] using scaleDecayRatio_sum_le_twenty_mul_q hq
    _ = 40 * q := by ring

/-- The part of the scalar-standard fixed-scale `L^q` bound which is
independent of its physical index. -/
noncomputable def standardSourceNormBudget
    (f : ℝ → ℂ) (I₀ : RealInterval) (q : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal
      ((80 * positiveDyadicAmplitudeBound * intervalL1Average f I₀) ^ (q - 2)) *
    ENNReal.ofReal
      ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀) *
        ∫ x, ‖f x‖)) ^ (1 / q)

/-- Factorization of the exact fixed-physical-scale interpolation estimate
into a scale-independent source budget and the `q`-th root of `j * 2⁻ʲ`.
This is the form needed before applying the finite geometric sum above. -/
theorem eLpNorm_energyStandardFixedPhysicalSourceAction_le_budget_mul_ratio
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ j : ℤ) (hk₀ : 1 ≤ k₀) (hk₀j : k₀ ≤ j)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : ℤ → Finset RealInterval)
    (hN : ∀ s ∈ standardSourceGaps k₀ j,
      N s ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ s ∈ standardSourceGaps k₀ j, ∀ I ∈ N s,
      scale I + 2 = j) {q : ℝ} (hq : 2 ≤ q) :
    eLpNorm (energyStandardFixedPhysicalSourceAction S f I₀ k₀ scale
        (standardSourceGaps k₀ j) N) (ENNReal.ofReal q) volume ≤
      standardSourceNormBudget f I₀ q *
        ENNReal.ofReal (((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q)) := by
  have hj0 : 0 ≤ j := le_trans (by omega : 0 ≤ k₀) hk₀j
  have hjr0 : 0 ≤ (j : ℝ) := by exact_mod_cast hj0
  have hpow0 : 0 ≤ (2 : ℝ) ^ j := (zpow_pos (by norm_num) j).le
  have hratio0 : 0 ≤ (j : ℝ) / (2 : ℝ) ^ j := div_nonneg hjr0 hpow0
  have hC0 : 0 ≤
      (2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀) *
        ∫ x, ‖f x‖ := by
    positivity [intervalL1Average_nonneg f I₀]
  apply (eLpNorm_energyStandardFixedPhysicalSourceAction_le_j_mul
    hf I₀ k₀ j hk₀ hk₀j scale hlam hsub N hN hfixed hq).trans_eq
  have hrearrange :
      (j : ℝ) *
          ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
            (2 : ℝ) ^ j) * ∫ x, ‖f x‖) =
        ((j : ℝ) / (2 : ℝ) ^ j) *
          ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀) *
            ∫ x, ‖f x‖) := by ring
  rw [hrearrange, ENNReal.ofReal_mul hratio0]
  change
    (ENNReal.ofReal
          ((80 * positiveDyadicAmplitudeBound * intervalL1Average f I₀) ^ (q - 2)) *
        (ENNReal.ofReal ((j : ℝ) / (2 : ℝ) ^ j) *
          ENNReal.ofReal
            ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀) *
              ∫ x, ‖f x‖))) ^ (1 / q) = _
  rw [show
    ENNReal.ofReal
          ((80 * positiveDyadicAmplitudeBound * intervalL1Average f I₀) ^ (q - 2)) *
        (ENNReal.ofReal ((j : ℝ) / (2 : ℝ) ^ j) *
          ENNReal.ofReal
            ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀) *
              ∫ x, ‖f x‖)) =
      (ENNReal.ofReal
          ((80 * positiveDyadicAmplitudeBound * intervalL1Average f I₀) ^ (q - 2)) *
        ENNReal.ofReal
          ((2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀) *
            ∫ x, ‖f x‖)) *
        ENNReal.ofReal ((j : ℝ) / (2 : ℝ) ^ j) by ac_rfl]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / q)]
  rw [ENNReal.ofReal_rpow_of_nonneg hratio0 (by positivity : (0 : ℝ) ≤ 1 / q)]
  rfl

/-- Minkowski aggregation of fixed-physical-scale source actions. The
geometric estimate is deliberately separated from the definition of the
scale-indexed actions, so it can be applied after the standard/nonstandard
classification has been assembled. -/
theorem eLpNorm_finset_sum_le_budget_mul_forty_mul_q
    {q : ℝ} (hq : 2 ≤ q) {B : ℝ≥0∞} (S : Finset ℤ)
    (F : ℤ → ℝ → ℂ)
    (hbound : ∀ j ∈ S,
      eLpNorm (F j) (ENNReal.ofReal q) volume ≤
        B * ENNReal.ofReal (((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q)))
    (hS : ∀ j ∈ S, 0 ≤ j) :
    eLpNorm (∑ j ∈ S, F j) (ENNReal.ofReal q) volume ≤
      B * ENNReal.ofReal (40 * q) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hsum := finite_int_ratio_rpow_sum_le_forty_mul_q hq S hS
  have hratio_nonneg : ∀ j ∈ S,
      0 ≤ ((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q) := by
    intro j hj
    apply Real.rpow_nonneg
    exact div_nonneg (by exact_mod_cast hS j hj)
      (zpow_pos (by norm_num) j).le
  have hofsum :
      (∑ j ∈ S, ENNReal.ofReal (((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q))) =
        ENNReal.ofReal
          (∑ j ∈ S, ((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q)) := by
    exact (ENNReal.ofReal_sum_of_nonneg hratio_nonneg).symm
  calc
    eLpNorm (∑ j ∈ S, F j) (ENNReal.ofReal q) volume ≤
        ∑ j ∈ S, eLpNorm (F j) (ENNReal.ofReal q) volume :=
      eLpNorm_sum_le hp1
    _ ≤ ∑ j ∈ S,
        B * ENNReal.ofReal (((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q)) := by
      exact Finset.sum_le_sum (fun j hj ↦ hbound j hj)
    _ = B * ∑ j ∈ S,
        ENNReal.ofReal (((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q)) := by
      rw [Finset.mul_sum]
    _ = B * ENNReal.ofReal
        (∑ j ∈ S, ((j : ℝ) / (2 : ℝ) ^ j) ^ (1 / q)) := by rw [hofsum]
    _ ≤ B * ENNReal.ofReal (40 * q) := by
      gcongr


end KrauseLaceyBadScale
end QuadraticCarleson
