/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.Attic.SampCert.Foundations.Basic
import Mathlib.Data.ENNReal.Basic
import LeanPool.HopfieldNet.Attic.SampCert.Samplers.Uniform.Code

/-!
# ``UniformSample`` Properties

This file proves normalization and evaluation properties of the ``UniformSample`` sampler.
-/

noncomputable section

open PMF Classical Finset Nat ENNReal

namespace SLang

-- theorem rw1_old (n : PNat) :
--    (((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ / ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ↑↑n)) : ENNReal)
--    = (((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ / ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ↑↑n)) : NNReal)  := by
--   simp only [PNat.val_ofNat, reduceSucc, ne_eq, _root_.mul_eq_zero, inv_eq_zero, pow_eq_zero_iff',
--     OfNat.ofNat_ne_zero, log_eq_zero_iff, gt_iff_lt, ofNat_pos, mul_lt_iff_lt_one_right, lt_one_iff,
--     PNat.ne_zero, not_ofNat_le_one, or_self, not_false_eq_true, and_true, cast_eq_zero,
--     ENNReal.coe_div, pow_eq_zero_iff, ENNReal.coe_inv, ENNReal.coe_pow, coe_ofNat, ENNReal.coe_mul,
--     coe_natCast]

theorem rw1 (n : PNat) :
  ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ↑↑n)⁻¹ : ENNReal)
   = ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ((2 ^ log 2 ((2 : PNat) * ↑n))⁻¹ * ↑↑n)⁻¹ : NNReal) := by
  simp only [PNat.val_ofNat, reduceSucc, mul_inv_rev, inv_inv, ENNReal.coe_mul, ne_eq,
    pow_eq_zero_iff', OfNat.ofNat_ne_zero, log_eq_zero_iff, gt_iff_lt, ofNat_pos,
    mul_lt_iff_lt_one_right, lt_one_iff, PNat.ne_zero, not_ofNat_le_one, or_self, not_false_eq_true,
    and_true, ENNReal.coe_inv, ENNReal.coe_pow, coe_ofNat, cast_eq_zero, coe_natCast]
  congr
  rw [mul_comm]
  rw [ENNReal.mul_inv]
  · simp only [inv_inv]
  · simp only [ne_eq, cast_eq_zero, PNat.ne_zero, not_false_eq_true, inv_eq_top, log_eq_zero_iff,
    gt_iff_lt, ofNat_pos, mul_lt_iff_lt_one_right, lt_one_iff, not_ofNat_le_one, or_self,
    pow_eq_zero_iff, OfNat.ofNat_ne_zero]
  · simp only [ne_eq, natCast_ne_top, not_false_eq_true, ENNReal.inv_eq_zero, pow_eq_top_iff,
    two_ne_top, log_eq_zero_iff, gt_iff_lt, ofNat_pos, mul_lt_iff_lt_one_right, lt_one_iff,
    PNat.ne_zero, not_ofNat_le_one, or_self, and_true]

theorem rw2 (n : PNat) : ((↑↑n)⁻¹ : ENNReal) = ((↑↑n)⁻¹ : NNReal) := by
  simp

/--
The sample space of ``uniformP2 (2*n)`` is large enough to fit the sample
space for ``uniform(n)``.
-/
@[simp]
lemma double_large_enough (n : PNat) (x : Nat) (support : x < n) :
  x < 2 ^ (log 2 ↑(2 * n)) := by
  have A : ∀ m : ℕ, m < 2 ^ (log 2 ↑(2 * m)) := by
    intro m
    cases m
    · simp
    · rename_i m
      have H1 := @Nat.lt_pow_succ_log_self 2 le.refl (succ m)
      have H2 := @Nat.log_mul_base 2 (succ m) le.refl (succ_ne_zero m)
      rw [Nat.mul_comm]
      rw [H2]
      exact H1
  exact Nat.lt_trans support (A ↑n)

/--
Simplify a ``uniformPowerOfTwoSample`` when guarded to be within the support.

Note that the support of ``uniformPowerOfTwoSample`` (namely ``[0, 2 ^ log 2 (2 * n))``) is
larger than support restriction ``[0, n)`` imposed by the guard.
-/
@[simp]
lemma rw_ite (n : PNat) (x : Nat) :
  (if x < n then (UniformPowerOfTwoSample (2 * n)) x else 0)
  = if x < n then 1 / 2 ^ log 2 ((2 : PNat) * n) else 0 := by
  split
  rw [UniformPowerOfTwoSample_apply]
  simp only [PNat.mul_coe, one_div]
  apply double_large_enough
  trivial
  trivial

-- Inline?
lemma tsum_comp (n : PNat) :
  (∑' (x : ↑{i : ℕ | decide (↑n ≤ i) = true}ᶜ), (fun i => UniformPowerOfTwoSample (2 * n) i) ↑x)
    = ∑' (i : ↑{i : ℕ| decide (↑n ≤ i) = false}), UniformPowerOfTwoSample (2 * n) ↑i := by
  apply tsum_congr_set_coe
  simp
  ext x
  simp


lemma uniformPowerOfTwoSample_autopilot (n : PNat) :
  (1 - ∑' (i : ℕ), if ↑n ≤ i then UniformPowerOfTwoSample (2 * n) i else 0)
    = ∑' (i : ℕ), if i < ↑n then UniformPowerOfTwoSample (2 * n) i else 0 := by
  have X : (∑' (i : ℕ), if decide (↑n ≤ i) = true then UniformPowerOfTwoSample (2 * n) i else 0) +
    (∑' (i : ℕ), if decide (↑n ≤ i) = false then UniformPowerOfTwoSample (2 * n) i else 0) = 1 := by
    have A := UniformPowerOfTwoSample_normalizes (2 * n)
    have B := @tsum_add_tsum_compl ENNReal ℕ _ _ (fun i => UniformPowerOfTwoSample (2 * n) i) _ _ { i : ℕ | decide (↑n ≤ i) = true} ENNReal.summable ENNReal.summable
    rw [A] at B
    clear A
    have C := @tsum_split_coe_right _ (fun i => ↑n ≤ i) (fun i => UniformPowerOfTwoSample (2 * n) i)
    rw [C] at B
    clear C
    have D := @tsum_split_coe_left _ (fun i => ↑n ≤ i) (fun i => UniformPowerOfTwoSample (2 * n) i)
    rw [tsum_comp n] at B
    rw [D] at B
    clear D
    trivial
  apply ENNReal.sub_eq_of_eq_add_rev
  · have Y := tsum_split_less (fun i => ↑n ≤ i) (fun i => UniformPowerOfTwoSample (2 * n) i)
    rw [UniformPowerOfTwoSample_normalizes (2 * n)] at Y
    simp at Y
    clear X
    by_contra
    rename_i h
    rw [h] at Y
    contradiction
  · simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_le, one_div] at X
    rw [X]

/--
Evaluation of the ``UniformSample`` distribution inside its support.
-/
@[simp]
theorem UniformSample_apply (n : PNat) (x : Nat) (support : x < n) :
  UniformSample n x = 1 / n := by
  simp only [UniformSample, Bind.bind, Pure.pure, SLang.bind_apply, probUntil_apply,
    decide_eq_true_eq, rw_ite, one_div, ite_mul, zero_mul, SLang.pure_apply]
  rw [ENNReal.tsum_eq_add_tsum_ite x]
  simp only [support, ↓reduceIte, mul_one]
  have A : ∀ x_1, @ite ℝ≥0∞ (x_1 = x) (propDecidable (x_1 = x)) 0
          (@ite ℝ≥0∞ (x_1 < ↑n) (decLt x_1 ↑n)
          ((2 ^ log 2 (↑(2 : ℕ+) * ↑n))⁻¹ * (1 - ∑' (x : ℕ), @ite ℝ≥0∞ (x < ↑n) (decLt x ↑n) 0 (UniformPowerOfTwoSample (2 * n) x))⁻¹ *
          @ite ℝ≥0∞ (x = x_1) (propDecidable (x = x_1)) 1 0)
          0) = 0 := by
    intro x1
    split
    · simp only
    · split
      · split
        · rename_i h1 h2 h3
          subst h3
          contradiction
        · simp only [mul_zero]
      · simp only
  conv =>
    left
    right
    right
    intro x1
    rw [A]
  clear A
  simp only [tsum_zero, add_zero]
  have A : ∀ x : ℕ, (@ite ℝ≥0∞ (x < ↑n) (decLt x ↑n) 0 (UniformPowerOfTwoSample (2 * n) x))
           =
           (@ite ℝ≥0∞ (↑n ≤ x) (decLe ↑n x) (UniformPowerOfTwoSample (2 * n) x) 0) := by
    intro x
    split
    · split
      · rename_i h1 h2
        rw [← not_lt] at h2
        contradiction
      · simp only
    · split
      · rename_i h1 h2
        simp only
      · rename_i h1 h2
        simp only [not_lt] at h1
        contradiction
  conv =>
    left
    right
    right
    right
    right
    intro x
    rw [A]
  rw [uniformPowerOfTwoSample_autopilot]
  simp only [rw_ite, one_div, sum_simple]
  rw [rw1 n]
  rw [rw2 n]
  rw [mul_inv]
  simp only [PNat.val_ofNat, reduceSucc, inv_inv, isUnit_iff_ne_zero, ne_eq, pow_eq_zero_iff',
    OfNat.ofNat_ne_zero, log_eq_zero_iff, gt_iff_lt, ofNat_pos, mul_lt_iff_lt_one_right, lt_one_iff,
    PNat.ne_zero, not_ofNat_le_one, or_self, not_false_eq_true, and_true,
    IsUnit.inv_mul_cancel_left, cast_eq_zero, ENNReal.coe_inv, coe_natCast]

/--
Evaluation of the ``UniformSample`` distribution outside of its support.
-/
@[simp]
theorem UniformSample_apply_out (n : PNat) (x : Nat) (support : x ≥ n) :
  UniformSample n x = 0 := by
  simp [UniformSample, support]

/--
Sum of the ``UniformSample`` distribution over a subset of its support.
-/
lemma UniformSample_support_Sum (n : PNat) (m : ℕ) (h : m ≤ n) :
  (Finset.sum (range m) fun i => UniformSample n i) = m / n := by
  induction m
  · simp
  · rename_i m IH
    simp at *
    have A : m ≤ ↑n := by exact lt_succ.mp (le.step h)
    have IH' := IH A
    clear IH
    rw [sum_range_succ]
    simp [IH']
    rw [UniformSample_apply ↑n m h]
    rw [ENNReal.div_add_div_same]

/--
Sum of the ``UniformSample`` distribution inside its support.
-/
lemma UniformSample_support_Sum' (n : PNat) :
  (Finset.sum (range n) fun i => UniformSample n i) = 1 := by
  rw [UniformSample_support_Sum n n le.refl]
  apply ENNReal.div_self
  · simp
  · simp

/--
Sum over the whole space of ``UniformSample`` is ``1``.
-/
@[simp]
theorem UniformSample_normalizes (n : PNat) :
  ∑' a : ℕ, UniformSample n a = 1 := by
  rw [← @sum_add_tsum_nat_add' _ _ _ _ _ _ n]
  · simp [UniformSample_support_Sum']
  · exact ENNReal.summable

/--
``UniformSample`` is a proper distribution
-/
theorem UniformSample_HasSum_1  (n : PNat) :
  HasSum (UniformSample n) 1 := by
  have A : Summable (UniformSample n) := by exact ENNReal.summable
  have B := Summable.hasSum A
  rw [UniformSample_normalizes n] at B
  trivial

/--
Conversion of ``UniformSample`` from a ``SLang`` term to a ``PMF``.
-/
noncomputable def UniformSample_PMF (n : PNat) : PMF ℕ := ⟨ UniformSample n , UniformSample_HasSum_1 n⟩

/--
Evaluation of ``UniformSample`` on ``ℕ`` guarded by its support, when inside the support.
-/
theorem UniformSample_apply_ite (a b : ℕ) (c : PNat) (i1 : b ≤ c) :
  (if a < b then (UniformSample c) a else 0) = if a < b then 1 / (c : ENNReal) else 0 := by
  split
  rename_i i2
  rw [UniformSample_apply]
  · exact Nat.lt_of_lt_of_le i2 i1
  · trivial

/--
Evaluation of ``UniformSample`` on ``ℕ`` guarded by its support, when outside the support.
-/
theorem UniformSample_apply' (n : PNat) (x : Nat) :
  (UniformSample n) x = if x < n then (1 : ENNReal) / n else 0 := by
  split
  · rename_i h
    simp [h]
  · rename_i h
    apply UniformSample_apply_out
    exact Nat.not_lt.mp h

end SLang
