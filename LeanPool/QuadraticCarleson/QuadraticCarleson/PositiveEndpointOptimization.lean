/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.Definitions
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Scalar optimization in the positive endpoint argument

This file isolates the numerical part of the high--low decomposition in the
positive endpoint proof of arXiv:2609.04101v1.  In particular it records the
two choices of magnitude thresholds and scale cutoffs made at the end of the
proof and turns membership in a magnitude level into the corresponding Orlicz
weight.

We use exponential notation for real powers of two.  Thus
`lacunaryScale k = 2^(2^k)` and
`lacunaryAmplitude k = 2^(2^(2^k))`, exactly the paper's lacunary choice.
-/

open Filter Set
open scoped Topology

namespace QuadraticCarleson
namespace PositiveEndpointOptimization


/-- Membership in the `k`th magnitude band.  This is the scalar content of
the paper's set `F_k`, applied to `t = |f x|`. -/
def InMagnitudeLevel (A : ℕ → ℝ) (k : ℕ) (t : ℝ) : Prop :=
  if k = 0 then 0 ≤ t ∧ t ≤ A 0
  else A (k - 1) < t ∧ t ≤ A k

theorem InMagnitudeLevel.nonneg {A : ℕ → ℝ} {k : ℕ} {t : ℝ}
    (hA : ∀ j, 0 ≤ A j) (h : InMagnitudeLevel A k t) : 0 ≤ t := by
  by_cases hk : k = 0
  · simp only [InMagnitudeLevel, hk] at h
    exact h.1
  · simp only [InMagnitudeLevel, hk] at h
    exact (hA (k - 1)).trans h.1.le

theorem InMagnitudeLevel.lower {A : ℕ → ℝ} {k : ℕ} {t : ℝ}
    (hk : k ≠ 0) (h : InMagnitudeLevel A k t) : A (k - 1) < t := by
  simp only [InMagnitudeLevel, hk] at h
  exact h.1

/-- All iterated paper logarithms are nonnegative on nonnegative inputs. -/
theorem paperLog_nonnegative (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ paperLog n t := by
  induction n with
  | zero => simpa using ht
  | succ n ih =>
      rw [paperLog_succ]
      exact Real.log_nonneg (by linarith)

/-- Monotonicity of the shifted iterated logarithms on the half-line used in
the endpoint estimates. -/
theorem paperLog_mono {n : ℕ} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    paperLog n s ≤ paperLog n t := by
  have ht : 0 ≤ t := hs.trans hst
  induction n with
  | zero => simpa using hst
  | succ n ih =>
      rw [paperLog_succ, paperLog_succ]
      apply Real.strictMonoOn_log.monotoneOn
      · show 0 < 10 + paperLog n s
        linarith [paperLog_nonnegative n hs]
      · show 0 < 10 + paperLog n t
        linarith [paperLog_nonnegative n ht]
      · simpa [add_comm] using add_le_add_left ih 10

/-- The ordinary dyadic scale `2^k`, regarded as a real number. -/
noncomputable def dyadicScale (k : ℕ) : ℝ := (2 : ℝ) ^ k

/-- The full-operator magnitude threshold `2^(2^k)`. -/
noncomputable def fullAmplitude (k : ℕ) : ℝ :=
  Real.exp (Real.log 2 * dyadicScale k)

/-- The full-operator cutoff `B_k = C 2^k`. -/
noncomputable def fullCutoff (C : ℝ) (k : ℕ) : ℝ := C * dyadicScale k

theorem dyadicScale_pos (k : ℕ) : 0 < dyadicScale k := by
  simp [dyadicScale]

theorem fullAmplitude_pos (k : ℕ) : 0 < fullAmplitude k := by
  exact Real.exp_pos _

theorem fullAmplitude_eq_two_pow (k : ℕ) :
    fullAmplitude k = (2 : ℝ) ^ (2 ^ k : ℕ) := by
  rw [fullAmplitude, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ (2 ^ k : ℕ)),
    Real.log_pow (2 : ℝ) (2 ^ k : ℕ)]
  congr 1
  norm_num [dyadicScale]
  ring

theorem dyadicScale_succ (k : ℕ) : dyadicScale (k + 1) = 2 * dyadicScale k := by
  simp [dyadicScale, pow_succ, mul_comm]

/-- A point in a nonzero full-operator magnitude level pays for its cutoff by
one copy of the paper's `log₁`. -/
theorem fullCutoff_le_paperLog_one_of_mem
    {C t : ℝ} {k : ℕ} (hC : 0 ≤ C) (hk : k ≠ 0)
    (ht : InMagnitudeLevel fullAmplitude k t) :
    fullCutoff C k ≤ 4 * C * paperLog 1 t := by
  have hlower : fullAmplitude (k - 1) < t := ht.lower hk
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)
  have hlog : Real.log 2 * dyadicScale (k - 1) ≤ paperLog 1 t := by
    rw [paperLog_succ, paperLog_zero,
      Real.le_log_iff_exp_le (by linarith [ht.nonneg (fun j ↦ (fullAmplitude_pos j).le)])]
    exact (le_of_lt hlower).trans (by linarith)
  rw [← hk']
  simp only [fullCutoff, dyadicScale_succ]
  have hd : 2 * dyadicScale (k - 1) ≤ 4 * paperLog 1 t := by
    nlinarith [Real.log_two_gt_d9, dyadicScale_pos (k - 1)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hd hC

theorem fullWeightedLevel_le_orlicz
    {C t : ℝ} {k : ℕ} (hC : 0 ≤ C) (hk : k ≠ 0)
    (ht : InMagnitudeLevel fullAmplitude k t) :
    fullCutoff C k * t ≤ 4 * C * (t * paperLog 1 t) := by
  have ht0 : 0 ≤ t := ht.nonneg (fun j ↦ (fullAmplitude_pos j).le)
  exact (mul_le_mul_of_nonneg_right
    (fullCutoff_le_paperLog_one_of_mem hC hk ht) ht0).trans_eq (by ring)

theorem one_le_paperLog_one {t : ℝ} (ht : 0 ≤ t) : 1 ≤ paperLog 1 t := by
  rw [paperLog_succ, paperLog_zero, Real.le_log_iff_exp_le (by linarith)]
  have hexp : Real.exp 1 < 10 := Real.exp_one_lt_d9.trans (by norm_num)
  exact hexp.le.trans (by linarith)

/-- The same full endpoint conversion including the bottom magnitude band. -/
theorem fullWeightedLevel_le_orlicz_all
    {C t : ℝ} {k : ℕ} (hC : 0 ≤ C)
    (ht : InMagnitudeLevel fullAmplitude k t) :
    fullCutoff C k * t ≤ 4 * C * (t * paperLog 1 t) := by
  by_cases hk : k = 0
  · subst k
    have ht0 : 0 ≤ t := ht.nonneg (fun j ↦ (fullAmplitude_pos j).le)
    have hlog := one_le_paperLog_one ht0
    simp only [fullCutoff, dyadicScale, pow_zero, mul_one]
    nlinarith [mul_nonneg hC ht0,
      mul_le_mul_of_nonneg_left hlog (mul_nonneg hC ht0)]
  · exact fullWeightedLevel_le_orlicz hC hk ht

/-- The double-exponential scale `2^(2^k)`. -/
noncomputable def lacunaryScale (k : ℕ) : ℝ :=
  Real.exp (Real.log 2 * dyadicScale k)

/-- The paper's lacunary threshold `A_k = 2^(2^(2^k))`. -/
noncomputable def lacunaryAmplitude (k : ℕ) : ℝ :=
  Real.exp (Real.log 2 * lacunaryScale k)

/-- The paper's lacunary cutoff `B_k = C 2^(2^k)`. -/
noncomputable def lacunaryCutoff (C : ℝ) (k : ℕ) : ℝ :=
  C * lacunaryScale k

theorem lacunaryScale_pos (k : ℕ) : 0 < lacunaryScale k := by
  exact Real.exp_pos _

theorem lacunaryAmplitude_pos (k : ℕ) : 0 < lacunaryAmplitude k := by
  exact Real.exp_pos _

theorem lacunaryScale_eq_two_pow (k : ℕ) :
    lacunaryScale k = (2 : ℝ) ^ (2 ^ k : ℕ) := by
  rw [lacunaryScale, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ (2 ^ k : ℕ)),
    Real.log_pow (2 : ℝ) (2 ^ k : ℕ)]
  congr 1
  norm_num [dyadicScale]
  ring

theorem lacunaryAmplitude_eq_two_pow (k : ℕ) :
    lacunaryAmplitude k = (2 : ℝ) ^ (2 ^ (2 ^ k) : ℕ) := by
  rw [lacunaryAmplitude, lacunaryScale_eq_two_pow,
    ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ (2 ^ (2 ^ k) : ℕ)),
    Real.log_pow (2 : ℝ) (2 ^ (2 ^ k) : ℕ)]
  congr 1
  norm_num
  ring

theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  linarith [Real.log_two_gt_d9]

theorem dyadicScale_ge_one (k : ℕ) : 1 ≤ dyadicScale k := by
  exact one_le_pow₀ (by norm_num)

theorem dyadicScale_ge_nat_succ (k : ℕ) : (k : ℝ) + 1 ≤ dyadicScale k := by
  induction k with
  | zero => simp [dyadicScale]
  | succ k ih =>
      rw [dyadicScale_succ]
      push_cast
      nlinarith [dyadicScale_ge_one k]

/-- The first shifted logarithm at the bottom of a lacunary level already
sees the exponent `log 2 * 2^(2^(k-1))`. -/
theorem paperLog_one_lacunary_lower
    {t : ℝ} {k : ℕ} (hk : k ≠ 0)
    (ht : InMagnitudeLevel lacunaryAmplitude k t) :
    Real.log 2 * lacunaryScale (k - 1) ≤ paperLog 1 t := by
  have hlower : lacunaryAmplitude (k - 1) < t := ht.lower hk
  rw [paperLog_succ, paperLog_zero,
    Real.le_log_iff_exp_le (by linarith [ht.nonneg (fun j ↦ (lacunaryAmplitude_pos j).le)])]
  exact (le_of_lt hlower).trans (by linarith)

/-- At a nontrivial lacunary magnitude level, `log₂` dominates the dyadic
index scale.  The factor `8` only absorbs the shift from `k` to `k-1` and the
fact that `log 2 > 1/2`. -/
theorem dyadicScale_le_eight_mul_paperLog_two_of_mem
    {t : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (ht : InMagnitudeLevel lacunaryAmplitude k t) :
    dyadicScale k ≤ 8 * paperLog 2 t := by
  have hk0 : k ≠ 0 := by omega
  have ht0 : 0 ≤ t := ht.nonneg (fun j ↦ (lacunaryAmplitude_pos j).le)
  have h1 := paperLog_one_lacunary_lower hk0 ht
  have hspos := lacunaryScale_pos (k - 1)
  have hhalf : lacunaryScale (k - 1) / 2 ≤ paperLog 1 t := by
    nlinarith [half_lt_log_two]
  have hdkm1 : 2 ≤ dyadicScale (k - 1) := by
    have hnat : (2 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show 2 ≤ (k - 1 : ℕ) + 1 by omega)
    exact hnat.trans (dyadicScale_ge_nat_succ (k - 1))
  have hexp :
      Real.exp (dyadicScale (k - 1) / 4) * 2 ≤ lacunaryScale (k - 1) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [half_lt_log_two]
  have htarget : dyadicScale k / 8 ≤ paperLog 2 t := by
    rw [paperLog_succ]
    apply (Real.le_log_iff_exp_le
      (by linarith [paperLog_nonnegative 1 ht0])).2
    calc
      Real.exp (dyadicScale k / 8) =
          Real.exp (dyadicScale (k - 1) / 4) := by
            have hsucc : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
            have hd : dyadicScale k = 2 * dyadicScale (k - 1) := by
              calc
                dyadicScale k = dyadicScale (k - 1 + 1) := by rw [hsucc]
                _ = 2 * dyadicScale (k - 1) := dyadicScale_succ _
            rw [hd]
            congr 1
            ring
      _ ≤ lacunaryScale (k - 1) / 2 := by nlinarith
      _ ≤ paperLog 1 t := hhalf
      _ ≤ 10 + paperLog 1 t := by linarith
  linarith

theorem dyadicScale_sq_le_sixtyfour_mul_paperLog_two_sq_of_mem
    {t : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (ht : InMagnitudeLevel lacunaryAmplitude k t) :
    dyadicScale k ^ 2 ≤ 64 * paperLog 2 t ^ 2 := by
  have h := dyadicScale_le_eight_mul_paperLog_two_of_mem hk ht
  have hp : 0 ≤ paperLog 2 t :=
    paperLog_nonnegative 2 (ht.nonneg (fun j ↦ (lacunaryAmplitude_pos j).le))
  have hs := mul_self_le_mul_self (dyadicScale_pos k).le h
  nlinarith

theorem lacunaryScale_ge_one (k : ℕ) : 1 ≤ lacunaryScale k := by
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  exact mul_nonneg (half_lt_log_two.le.trans' (by norm_num)) (dyadicScale_pos k).le

/-- The logarithmic loss of a block of `B_k` lacunary modulations is at most
linear in `2^k`. -/
theorem paperLog_one_lacunaryCutoff_le
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    paperLog 1 (lacunaryCutoff C k) ≤
      (paperLog 1 C + 1) * dyadicScale k := by
  have htenC : 0 < 10 + C := by linarith
  have hs1 := lacunaryScale_ge_one k
  have harg :
      10 + lacunaryCutoff C k ≤ (10 + C) * lacunaryScale k := by
    dsimp [lacunaryCutoff]
    nlinarith
  rw [paperLog_succ, paperLog_zero]
  calc
    Real.log (10 + lacunaryCutoff C k)
        ≤ Real.log ((10 + C) * lacunaryScale k) := by
          apply Real.strictMonoOn_log.monotoneOn
          · show 0 < 10 + lacunaryCutoff C k
            dsimp [lacunaryCutoff]
            nlinarith [mul_nonneg hC (lacunaryScale_pos k).le]
          · show 0 < (10 + C) * lacunaryScale k
            exact mul_pos htenC (lacunaryScale_pos k)
          · exact harg
    _ = Real.log (10 + C) + Real.log (lacunaryScale k) := by
          rw [Real.log_mul (ne_of_gt htenC) (ne_of_gt (lacunaryScale_pos k))]
    _ = paperLog 1 C + Real.log 2 * dyadicScale k := by
          rw [paperLog_succ, paperLog_zero]
          simp [lacunaryScale]
    _ ≤ (paperLog 1 C + 1) * dyadicScale k := by
          have hlogC : 0 ≤ paperLog 1 C := by
            rw [paperLog_succ, paperLog_zero]
            exact Real.log_nonneg (by linarith)
          have hlog2 : Real.log 2 ≤ 1 := by
            linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
          nlinarith [dyadicScale_ge_one k]

/-- Consequently, the `log₁(B_k)^2` factor in the lacunary high-frequency
estimate is absorbed by `log₂(t)^2` on `F_k`. -/
theorem paperLog_one_lacunaryCutoff_sq_le_paperLog_two_sq_of_mem
    {C t : ℝ} {k : ℕ} (hC : 0 ≤ C) (hk : 2 ≤ k)
    (ht : InMagnitudeLevel lacunaryAmplitude k t) :
    paperLog 1 (lacunaryCutoff C k) ^ 2 ≤
      64 * (paperLog 1 C + 1) ^ 2 * paperLog 2 t ^ 2 := by
  have hcut := paperLog_one_lacunaryCutoff_le hC k
  have hcut0 : 0 ≤ paperLog 1 (lacunaryCutoff C k) := by
    apply paperLog_nonnegative
    exact mul_nonneg hC (lacunaryScale_pos k).le
  have hconst : 0 ≤ paperLog 1 C + 1 := by
    have := paperLog_nonnegative 1 hC
    linarith
  have hscale := dyadicScale_sq_le_sixtyfour_mul_paperLog_two_sq_of_mem hk ht
  calc
    paperLog 1 (lacunaryCutoff C k) ^ 2
        ≤ ((paperLog 1 C + 1) * dyadicScale k) ^ 2 := by nlinarith
    _ = (paperLog 1 C + 1) ^ 2 * dyadicScale k ^ 2 := by ring
    _ ≤ (paperLog 1 C + 1) ^ 2 * (64 * paperLog 2 t ^ 2) := by
          exact mul_le_mul_of_nonneg_left hscale (sq_nonneg _)
    _ = 64 * (paperLog 1 C + 1) ^ 2 * paperLog 2 t ^ 2 := by ring

/-- Three iterated logarithms of a value in the `k`th lacunary band retain a
linear amount of the level index. -/
theorem sub_three_mul_log_two_le_paperLog_three_of_mem
    {t : ℝ} {k : ℕ} (hk : 6 ≤ k)
    (ht : InMagnitudeLevel lacunaryAmplitude k t) :
    ((k : ℝ) - 3) * Real.log 2 ≤ paperLog 3 t := by
  have h2 := dyadicScale_le_eight_mul_paperLog_two_of_mem (by omega) ht
  have ht0 : 0 ≤ t := ht.nonneg (fun j ↦ (lacunaryAmplitude_pos j).le)
  have hdivpos : 0 < dyadicScale k / 8 :=
    div_pos (dyadicScale_pos k) (by norm_num)
  have harg : dyadicScale k / 8 ≤ 10 + paperLog 2 t := by
    nlinarith
  have hlogdiv :
      Real.log (dyadicScale k / 8) = ((k : ℝ) - 3) * Real.log 2 := by
    rw [Real.log_div (ne_of_gt (dyadicScale_pos k)) (by norm_num : (8 : ℝ) ≠ 0)]
    unfold dyadicScale
    rw [Real.log_pow]
    have height : (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
    rw [height, Real.log_pow]
    push_cast
    ring
  rw [paperLog_succ]
  rw [← hlogdiv]
  apply Real.strictMonoOn_log.monotoneOn
  · exact hdivpos
  · show 0 < 10 + paperLog 2 t
    linarith [paperLog_nonnegative 2 ht0]
  · exact harg

/-- The fourth iterated logarithm supplies Kalton's additional
`log₁(k+2)` loss.  This is the last numerical step behind the paper's
`L(log₂ L)^2 log₄ L` weight. -/
theorem paperLog_one_index_le_two_mul_paperLog_four_of_mem
    {t : ℝ} {k : ℕ} (hk : 6 ≤ k)
    (ht : InMagnitudeLevel lacunaryAmplitude k t) :
    paperLog 1 ((k : ℝ) + 2) ≤ 2 * paperLog 4 t := by
  have ht0 : 0 ≤ t := ht.nonneg (fun j ↦ (lacunaryAmplitude_pos j).le)
  have h3 := sub_three_mul_log_two_le_paperLog_three_of_mem hk ht
  have h3lower : ((k : ℝ) - 3) / 2 ≤ paperLog 3 t := by
    have hkreal : (3 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (show 3 ≤ k by omega)
    have hk3 : 0 ≤ (k : ℝ) - 3 := sub_nonneg.mpr hkreal
    calc
      ((k : ℝ) - 3) / 2 = ((k : ℝ) - 3) * (1 / 2 : ℝ) := by ring
      _ ≤ ((k : ℝ) - 3) * Real.log 2 :=
        mul_le_mul_of_nonneg_left half_lt_log_two.le hk3
      _ ≤ paperLog 3 t := h3
  have hbase : 0 < 10 + paperLog 3 t := by
    linarith [paperLog_nonnegative 3 ht0]
  have hsq : (k : ℝ) + 12 ≤ (10 + paperLog 3 t) ^ 2 := by
    have hkreal : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [sq_nonneg (paperLog 3 t - ((k : ℝ) - 3) / 2)]
  rw [paperLog_succ, paperLog_zero, paperLog_succ]
  have hlog :
      Real.log ((k : ℝ) + 12) ≤ Real.log ((10 + paperLog 3 t) ^ 2) := by
    apply Real.strictMonoOn_log.monotoneOn
    · show 0 < (k : ℝ) + 12
      have hk0 : (0 : ℝ) ≤ k := by positivity
      linarith
    · exact sq_pos_of_pos hbase
    · exact hsq
  rw [Real.log_pow] at hlog
  norm_num at hlog ⊢
  convert hlog using 1 <;> ring

/-- Complete pointwise conversion of the lacunary low-frequency loss on a
magnitude band into the paper's endpoint Orlicz weight. -/
theorem lacunaryLowWeight_le_orlicz_of_mem
    {C t : ℝ} {k : ℕ} (hC : 0 ≤ C) (hk : 6 ≤ k)
    (ht : InMagnitudeLevel lacunaryAmplitude k t) :
    paperLog 1 ((k : ℝ) + 2) *
          paperLog 1 (lacunaryCutoff C k) ^ 2 * t ≤
      128 * (paperLog 1 C + 1) ^ 2 *
        (t * paperLog 2 t ^ 2 * paperLog 4 t) := by
  have ht0 : 0 ≤ t := ht.nonneg (fun j ↦ (lacunaryAmplitude_pos j).le)
  have hindex := paperLog_one_index_le_two_mul_paperLog_four_of_mem hk ht
  have hblock := paperLog_one_lacunaryCutoff_sq_le_paperLog_two_sq_of_mem
    hC (by omega) ht
  have hi0 : 0 ≤ paperLog 1 ((k : ℝ) + 2) := by
    apply paperLog_nonnegative
    positivity
  have hb0 : 0 ≤ paperLog 1 (lacunaryCutoff C k) ^ 2 := sq_nonneg _
  have h4 : 0 ≤ paperLog 4 t := paperLog_nonnegative 4 ht0
  have hconst : 0 ≤ 64 * (paperLog 1 C + 1) ^ 2 * paperLog 2 t ^ 2 := by positivity
  have hprod :
      paperLog 1 ((k : ℝ) + 2) * paperLog 1 (lacunaryCutoff C k) ^ 2 ≤
        (2 * paperLog 4 t) *
          (64 * (paperLog 1 C + 1) ^ 2 * paperLog 2 t ^ 2) :=
    mul_le_mul hindex hblock hb0 (mul_nonneg (by norm_num) h4)
  have := mul_le_mul_of_nonneg_right hprod ht0
  calc
    paperLog 1 ((k : ℝ) + 2) *
          paperLog 1 (lacunaryCutoff C k) ^ 2 * t
        ≤ ((2 * paperLog 4 t) *
          (64 * (paperLog 1 C + 1) ^ 2 * paperLog 2 t ^ 2)) * t := this
    _ = 128 * (paperLog 1 C + 1) ^ 2 *
        (t * paperLog 2 t ^ 2 * paperLog 4 t) := by ring

/-- The corresponding pointwise conversion for the lacunary high-frequency
second factor. -/
theorem lacunaryHighWeight_le_orlicz_of_mem
    {C t : ℝ} {k : ℕ} (hC : 0 ≤ C) (hk : 2 ≤ k)
    (ht : InMagnitudeLevel lacunaryAmplitude k t) :
    paperLog 1 (lacunaryCutoff C k) ^ 2 * t ≤
      64 * (paperLog 1 C + 1) ^ 2 * (t * paperLog 2 t ^ 2) := by
  have ht0 : 0 ≤ t := ht.nonneg (fun j ↦ (lacunaryAmplitude_pos j).le)
  have h := paperLog_one_lacunaryCutoff_sq_le_paperLog_two_sq_of_mem hC hk ht
  exact (mul_le_mul_of_nonneg_right h ht0).trans_eq (by ring)

theorem dyadicScale_le_thirtytwo {k : ℕ} (hk : k < 6) :
    dyadicScale k ≤ 32 := by
  interval_cases k <;> norm_num [dyadicScale]

/-- The first six lacunary levels contribute only a fixed multiple of `L¹`.
Together with `lacunaryLowWeight_le_orlicz_of_mem`, this accounts for every
magnitude band. -/
theorem lacunaryLowWeight_smallLevel_le_L1
    {C t : ℝ} {k : ℕ} (hC : 0 ≤ C) (hk : k < 6) (ht : 0 ≤ t) :
    paperLog 1 ((k : ℝ) + 2) *
          paperLog 1 (lacunaryCutoff C k) ^ 2 * t ≤
      paperLog 1 7 * (32 * (paperLog 1 C + 1)) ^ 2 * t := by
  have hkreal : (k : ℝ) + 2 ≤ 7 := by exact_mod_cast (show k + 2 ≤ 7 by omega)
  have hindex : paperLog 1 ((k : ℝ) + 2) ≤ paperLog 1 7 :=
    paperLog_mono (by positivity) hkreal
  have hblock0 : 0 ≤ paperLog 1 (lacunaryCutoff C k) := by
    apply paperLog_nonnegative
    exact mul_nonneg hC (lacunaryScale_pos k).le
  have hconstant0 : 0 ≤ paperLog 1 C + 1 := by
    linarith [paperLog_nonnegative 1 hC]
  have hblock : paperLog 1 (lacunaryCutoff C k) ≤
      32 * (paperLog 1 C + 1) := by
    have h := paperLog_one_lacunaryCutoff_le hC k
    have hd := dyadicScale_le_thirtytwo hk
    calc
      paperLog 1 (lacunaryCutoff C k)
          ≤ (paperLog 1 C + 1) * dyadicScale k := h
      _ ≤ (paperLog 1 C + 1) * 32 :=
        mul_le_mul_of_nonneg_left hd hconstant0
      _ = 32 * (paperLog 1 C + 1) := by ring
  have hblocksq : paperLog 1 (lacunaryCutoff C k) ^ 2 ≤
      (32 * (paperLog 1 C + 1)) ^ 2 := by nlinarith
  have hi0 := paperLog_nonnegative 1 (by positivity : (0 : ℝ) ≤ (k : ℝ) + 2)
  have hseven0 := paperLog_nonnegative 1 (by norm_num : (0 : ℝ) ≤ 7)
  have hprod := mul_le_mul hindex hblocksq (sq_nonneg _) hseven0
  exact mul_le_mul_of_nonneg_right hprod ht

/-- The scalar prefactor produced by Cauchy--Schwarz in the high-frequency
estimate.  The paper writes its first factor as `2^(-2 β B)`. -/
noncomputable def highFrequencyPrefactor
    (β : ℝ) (A B : ℝ) : ℝ :=
  Real.exp (-2 * β * Real.log 2 * B) * A / B

theorem highFrequencyPrefactor_nonneg
    {β A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ highFrequencyPrefactor β A B := by
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le hA) hB

/-- For the full-operator choices, the high-frequency prefactor is bounded by
a genuinely geometric sequence as soon as `C` is chosen with `2 β C > 1`.
This is the numerical optimization hidden in the paper's `C = O(1)`. -/
theorem fullHighFrequencyPrefactor_le_geometric
    {β C : ℝ} (hC : 1 ≤ C) (hdecay : 1 < 2 * β * C) (k : ℕ) :
    highFrequencyPrefactor β (fullAmplitude k) (fullCutoff C k) ≤
      Real.exp (-((2 * β * C - 1) * Real.log 2) * (k : ℝ)) := by
  let δ : ℝ := (2 * β * C - 1) * Real.log 2
  have hδ : 0 < δ := mul_pos (sub_pos.mpr hdecay) (half_lt_log_two.trans' (by norm_num))
  have hden : 0 < fullCutoff C k :=
    mul_pos (zero_lt_one.trans_le hC) (dyadicScale_pos k)
  have hden1 : 1 ≤ fullCutoff C k := by
    dsimp [fullCutoff]
    nlinarith [dyadicScale_ge_one k]
  have hnum :
      Real.exp (-2 * β * Real.log 2 * fullCutoff C k) * fullAmplitude k =
        Real.exp (-δ * dyadicScale k) := by
    unfold fullAmplitude
    rw [← Real.exp_add]
    congr 1
    dsimp [fullCutoff, fullAmplitude, δ]
    ring
  rw [highFrequencyPrefactor, hnum]
  calc
    Real.exp (-δ * dyadicScale k) / fullCutoff C k
        ≤ Real.exp (-δ * dyadicScale k) := by
          apply (div_le_iff₀ hden).2
          exact le_mul_of_one_le_right (Real.exp_pos _).le hden1
    _ ≤ Real.exp (-δ * (k : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have hk := dyadicScale_ge_nat_succ k
          nlinarith
    _ = Real.exp (-((2 * β * C - 1) * Real.log 2) * (k : ℝ)) := rfl

theorem summable_fullHighFrequencyPrefactor
    {β C : ℝ} (hC : 1 ≤ C) (hdecay : 1 < 2 * β * C) :
    Summable (fun k : ℕ ↦
      highFrequencyPrefactor β (fullAmplitude k) (fullCutoff C k)) := by
  let δ : ℝ := (2 * β * C - 1) * Real.log 2
  have hδ : 0 < δ := mul_pos (sub_pos.mpr hdecay) (half_lt_log_two.trans' (by norm_num))
  have hs : Summable (fun k : ℕ ↦ Real.exp (-δ * (k : ℝ))) := by
    simpa using Real.summable_pow_mul_exp_neg_nat_mul 0 hδ
  exact hs.of_nonneg_of_le
    (fun k ↦ highFrequencyPrefactor_nonneg (fullAmplitude_pos k).le
      (mul_nonneg (zero_le_one.trans hC) (dyadicScale_pos k).le))
    (fun k ↦ fullHighFrequencyPrefactor_le_geometric hC hdecay k)

theorem one_le_paperLog_one_lacunaryCutoff
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    1 ≤ paperLog 1 (lacunaryCutoff C k) := by
  have hb0 : 0 ≤ lacunaryCutoff C k :=
    mul_nonneg hC (lacunaryScale_pos k).le
  rw [paperLog_succ, paperLog_zero,
    Real.le_log_iff_exp_le (by linarith)]
  have hexp : Real.exp 1 < 10 := Real.exp_one_lt_d9.trans (by norm_num)
  linarith

/-- The lacunary high-frequency prefactor has the same geometric majorant.
Its denominator is the paper's rebalanced `log₁(B_k)^2`. -/
theorem lacunaryHighFrequencyPrefactor_le_geometric
    {β C : ℝ} (hC : 1 ≤ C) (hdecay : 1 < 2 * β * C) (k : ℕ) :
    Real.exp (-2 * β * Real.log 2 * lacunaryCutoff C k) * lacunaryAmplitude k /
        paperLog 1 (lacunaryCutoff C k) ^ 2 ≤
      Real.exp (-((2 * β * C - 1) * Real.log 2) * (k : ℝ)) := by
  let δ : ℝ := (2 * β * C - 1) * Real.log 2
  have hδ : 0 < δ := mul_pos (sub_pos.mpr hdecay) (half_lt_log_two.trans' (by norm_num))
  have hlog := one_le_paperLog_one_lacunaryCutoff (zero_le_one.trans hC) k
  have hden : 0 < paperLog 1 (lacunaryCutoff C k) ^ 2 := by positivity
  have hden1 : 1 ≤ paperLog 1 (lacunaryCutoff C k) ^ 2 := by nlinarith
  have hnum :
      Real.exp (-2 * β * Real.log 2 * lacunaryCutoff C k) * lacunaryAmplitude k =
        Real.exp (-δ * lacunaryScale k) := by
    unfold lacunaryAmplitude
    rw [← Real.exp_add]
    congr 1
    dsimp [lacunaryCutoff, lacunaryAmplitude, δ]
    ring
  rw [hnum]
  calc
    Real.exp (-δ * lacunaryScale k) /
          paperLog 1 (lacunaryCutoff C k) ^ 2
        ≤ Real.exp (-δ * lacunaryScale k) := by
          apply (div_le_iff₀ hden).2
          exact le_mul_of_one_le_right (Real.exp_pos _).le hden1
    _ ≤ Real.exp (-δ * (k : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have hs1 := lacunaryScale_ge_one k
          have hsdk : dyadicScale k ≤ lacunaryScale k := by
            rw [← Real.exp_log (dyadicScale_pos k)]
            apply Real.exp_le_exp.mpr
            unfold dyadicScale
            rw [Real.log_pow (2 : ℝ) k]
            have hk := dyadicScale_ge_nat_succ k
            have hkd : (k : ℝ) ≤ dyadicScale k := by linarith
            calc
              (k : ℝ) * Real.log 2 = Real.log 2 * (k : ℝ) := by ring
              _ ≤ Real.log 2 * dyadicScale k :=
                mul_le_mul_of_nonneg_left hkd
                  (half_lt_log_two.le.trans' (by norm_num))
          have hk := dyadicScale_ge_nat_succ k
          nlinarith
    _ = Real.exp (-((2 * β * C - 1) * Real.log 2) * (k : ℝ)) := rfl

theorem summable_lacunaryHighFrequencyPrefactor
    {β C : ℝ} (hC : 1 ≤ C) (hdecay : 1 < 2 * β * C) :
    Summable (fun k : ℕ ↦
      Real.exp (-2 * β * Real.log 2 * lacunaryCutoff C k) * lacunaryAmplitude k /
        paperLog 1 (lacunaryCutoff C k) ^ 2) := by
  let δ : ℝ := (2 * β * C - 1) * Real.log 2
  have hδ : 0 < δ := mul_pos (sub_pos.mpr hdecay) (half_lt_log_two.trans' (by norm_num))
  have hs : Summable (fun k : ℕ ↦ Real.exp (-δ * (k : ℝ))) := by
    simpa using Real.summable_pow_mul_exp_neg_nat_mul 0 hδ
  exact hs.of_nonneg_of_le
    (fun k ↦ div_nonneg
      (mul_nonneg (Real.exp_pos _).le (lacunaryAmplitude_pos k).le) (sq_nonneg _))
    (fun k ↦ lacunaryHighFrequencyPrefactor_le_geometric hC hdecay k)

/-- Explicit finite bound for the full high-frequency scalar series. -/
theorem tsum_fullHighFrequencyPrefactor_le
    {β C : ℝ} (hC : 1 ≤ C) (hdecay : 1 < 2 * β * C) :
    ∑' k : ℕ, highFrequencyPrefactor β (fullAmplitude k) (fullCutoff C k) ≤
      (1 - Real.exp (-((2 * β * C - 1) * Real.log 2)))⁻¹ := by
  let δ : ℝ := (2 * β * C - 1) * Real.log 2
  have hδ : 0 < δ := mul_pos (sub_pos.mpr hdecay) (half_lt_log_two.trans' (by norm_num))
  have hp := summable_fullHighFrequencyPrefactor hC hdecay
  have hs : Summable (fun k : ℕ ↦ Real.exp (-δ * (k : ℝ))) := by
    simpa using Real.summable_pow_mul_exp_neg_nat_mul 0 hδ
  calc
    ∑' k : ℕ, highFrequencyPrefactor β (fullAmplitude k) (fullCutoff C k)
        ≤ ∑' k : ℕ, Real.exp (-δ * (k : ℝ)) :=
          hp.tsum_le_tsum
            (fun k ↦ fullHighFrequencyPrefactor_le_geometric hC hdecay k) hs
    _ = ∑' k : ℕ, (Real.exp (-δ)) ^ k := by
          apply tsum_congr
          intro k
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
    _ = (1 - Real.exp (-δ))⁻¹ := by
          rw [tsum_geometric_of_lt_one (Real.exp_pos _).le]
          exact (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hδ))
    _ = (1 - Real.exp (-((2 * β * C - 1) * Real.log 2)))⁻¹ := rfl

/-- Explicit finite bound for the lacunary high-frequency scalar series. -/
theorem tsum_lacunaryHighFrequencyPrefactor_le
    {β C : ℝ} (hC : 1 ≤ C) (hdecay : 1 < 2 * β * C) :
    ∑' k : ℕ, Real.exp (-2 * β * Real.log 2 * lacunaryCutoff C k) *
        lacunaryAmplitude k / paperLog 1 (lacunaryCutoff C k) ^ 2 ≤
      (1 - Real.exp (-((2 * β * C - 1) * Real.log 2)))⁻¹ := by
  let δ : ℝ := (2 * β * C - 1) * Real.log 2
  have hδ : 0 < δ := mul_pos (sub_pos.mpr hdecay) (half_lt_log_two.trans' (by norm_num))
  have hp := summable_lacunaryHighFrequencyPrefactor hC hdecay
  have hs : Summable (fun k : ℕ ↦ Real.exp (-δ * (k : ℝ))) := by
    simpa using Real.summable_pow_mul_exp_neg_nat_mul 0 hδ
  calc
    ∑' k : ℕ, Real.exp (-2 * β * Real.log 2 * lacunaryCutoff C k) *
          lacunaryAmplitude k / paperLog 1 (lacunaryCutoff C k) ^ 2
        ≤ ∑' k : ℕ, Real.exp (-δ * (k : ℝ)) :=
          hp.tsum_le_tsum
            (fun k ↦ lacunaryHighFrequencyPrefactor_le_geometric hC hdecay k) hs
    _ = ∑' k : ℕ, (Real.exp (-δ)) ^ k := by
          apply tsum_congr
          intro k
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
    _ = (1 - Real.exp (-δ))⁻¹ := by
          rw [tsum_geometric_of_lt_one (Real.exp_pos _).le]
          exact (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hδ))
    _ = (1 - Real.exp (-((2 * β * C - 1) * Real.log 2)))⁻¹ := rfl

/-- Finite-sum form of the full-operator conversion for scalar samples lying
in their corresponding magnitude bands. -/
theorem sum_fullCutoff_mul_le_sum_orlicz
    {C : ℝ} (hC : 0 ≤ C) (s : Finset ℕ) (mass : ℕ → ℝ)
    (hlevel : ∀ k ∈ s, InMagnitudeLevel fullAmplitude k (mass k)) :
    ∑ k ∈ s, fullCutoff C k * mass k ≤
      4 * C * ∑ k ∈ s, mass k * paperLog 1 (mass k) := by
  calc
    ∑ k ∈ s, fullCutoff C k * mass k
        ≤ ∑ k ∈ s, 4 * C * (mass k * paperLog 1 (mass k)) := by
          exact Finset.sum_le_sum fun k hk ↦
            fullWeightedLevel_le_orlicz_all hC (hlevel k hk)
    _ = 4 * C * ∑ k ∈ s, mass k * paperLog 1 (mass k) := by
          rw [Finset.mul_sum]

/-- Finite-sum form of the lacunary high-frequency weight conversion. -/
theorem sum_lacunaryHighWeight_le_sum_orlicz
    {C : ℝ} (hC : 0 ≤ C) (s : Finset ℕ) (mass : ℕ → ℝ)
    (hlevel : ∀ k ∈ s, InMagnitudeLevel lacunaryAmplitude k (mass k))
    (hlarge : ∀ k ∈ s, 2 ≤ k) :
    ∑ k ∈ s, paperLog 1 (lacunaryCutoff C k) ^ 2 * mass k ≤
      64 * (paperLog 1 C + 1) ^ 2 *
        ∑ k ∈ s, mass k * paperLog 2 (mass k) ^ 2 := by
  calc
    ∑ k ∈ s, paperLog 1 (lacunaryCutoff C k) ^ 2 * mass k
        ≤ ∑ k ∈ s, 64 * (paperLog 1 C + 1) ^ 2 *
            (mass k * paperLog 2 (mass k) ^ 2) := by
          exact Finset.sum_le_sum fun k hk ↦
            lacunaryHighWeight_le_orlicz_of_mem hC (hlarge k hk) (hlevel k hk)
    _ = 64 * (paperLog 1 C + 1) ^ 2 *
        ∑ k ∈ s, mass k * paperLog 2 (mass k) ^ 2 := by
          rw [Finset.mul_sum]

/-- Finite-sum form of the complete lacunary low-frequency conversion.  The
six initial bands are deliberately omitted: in the analytic proof they are a
finite `L¹` contribution. -/
theorem sum_lacunaryLowWeight_le_sum_orlicz
    {C : ℝ} (hC : 0 ≤ C) (s : Finset ℕ) (mass : ℕ → ℝ)
    (hlevel : ∀ k ∈ s, InMagnitudeLevel lacunaryAmplitude k (mass k))
    (hlarge : ∀ k ∈ s, 6 ≤ k) :
    ∑ k ∈ s, paperLog 1 ((k : ℝ) + 2) *
        paperLog 1 (lacunaryCutoff C k) ^ 2 * mass k ≤
      128 * (paperLog 1 C + 1) ^ 2 *
        ∑ k ∈ s, mass k * paperLog 2 (mass k) ^ 2 * paperLog 4 (mass k) := by
  calc
    ∑ k ∈ s, paperLog 1 ((k : ℝ) + 2) *
        paperLog 1 (lacunaryCutoff C k) ^ 2 * mass k
      ≤ ∑ k ∈ s, 128 * (paperLog 1 C + 1) ^ 2 *
          (mass k * paperLog 2 (mass k) ^ 2 * paperLog 4 (mass k)) := by
        exact Finset.sum_le_sum fun k hk ↦
          lacunaryLowWeight_le_orlicz_of_mem hC (hlarge k hk) (hlevel k hk)
    _ = 128 * (paperLog 1 C + 1) ^ 2 *
        ∑ k ∈ s, mass k * paperLog 2 (mass k) ^ 2 * paperLog 4 (mass k) := by
      rw [Finset.mul_sum]

end PositiveEndpointOptimization
end QuadraticCarleson
