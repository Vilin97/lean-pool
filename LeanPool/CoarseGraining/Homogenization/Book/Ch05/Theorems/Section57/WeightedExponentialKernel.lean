/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ExponentialKernel

/-! # Weighted Exponential Kernel -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open scoped BigOperators
open Filter
open scoped Topology

/-!
# Weighted superexponential kernels

The no-loss bad-scale proof keeps finite maxima as probability-level union
prefactors.  These prefactors are exponential in the summation variables, but
the tail parameter is superexponential in the same variables.  The kernels in
this file absorb those finite-union weights without spending any power of the
main bad scale.
-/

noncomputable section

noncomputable def weightedGeometricExpKernelConst (w R : ℝ) : ℝ :=
  ∑' k : ℕ, w ^ k * Real.exp (-(R ^ k - 1))

noncomputable def weightedLinearExpKernelConst (w R : ℝ) : ℝ :=
  ∑' k : ℕ, (((k : ℝ) + 1) * w ^ k * Real.exp (-(R ^ k - 1)))

private theorem tendsto_linear_ratio :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
  have hinv :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcongr :
      (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1)) =
        fun n : ℕ => 1 + (1 : ℝ) / ((n : ℝ) + 1) := by
    funext n
    have hden : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hden]
    ring
  rw [hcongr]
  simpa using (tendsto_const_nhds.add hinv)

private theorem tendsto_exp_neg_mul_pow
    {w R : ℝ} (_hw : 0 < w) (hR : 1 < R) :
    Tendsto (fun n : ℕ => Real.exp (-(R ^ n * (R - 1)))) atTop (𝓝 0) := by
  have hdelta : 0 < R - 1 := sub_pos.mpr hR
  have hpow : Tendsto (fun n : ℕ => R ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hR
  have hprod :
      Tendsto (fun n : ℕ => (R - 1) * R ^ n) atTop atTop :=
    hpow.const_mul_atTop hdelta
  have hneg :
      Tendsto (fun n : ℕ => -((R - 1) * R ^ n)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hprod
  have hexp :
      Tendsto (fun n : ℕ => Real.exp (-((R - 1) * R ^ n))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  simpa [mul_comm, mul_left_comm, mul_assoc] using hexp

theorem summable_weightedLinearExpKernel
    {w R : ℝ} (hw : 0 < w) (hR : 1 < R) :
    Summable fun k : ℕ =>
      (((k : ℝ) + 1) * w ^ k * Real.exp (-(R ^ k - 1))) := by
  let f : ℕ → ℝ :=
    fun k => (((k : ℝ) + 1) * w ^ k * Real.exp (-(R ^ k - 1)))
  have hf_pos : ∀ k : ℕ, 0 < f k := by
    intro k
    dsimp [f]
    positivity
  refine summable_of_ratio_test_tendsto_lt_one (f := f) (l := 0)
    (by norm_num) ?_ ?_
  · filter_upwards with k
    exact ne_of_gt (hf_pos k)
  · have hratio_eq :
        (fun n : ℕ => ‖f (n + 1)‖ / ‖f n‖) =ᶠ[atTop]
          fun n : ℕ =>
            (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
              w * Real.exp (-(R ^ n * (R - 1))) := by
      filter_upwards with n
      have hn_pos : 0 < (n : ℝ) + 1 := by positivity
      have hw_pow_pos : 0 < w ^ n := pow_pos hw n
      have hR_pow_pos : 0 < R ^ n := pow_pos (lt_trans zero_lt_one hR) n
      have hf_n_pos := hf_pos n
      have hf_succ_pos := hf_pos (n + 1)
      have hw_ne : w ≠ 0 := hw.ne'
      have hw_pow_ne : w ^ n ≠ 0 := ne_of_gt hw_pow_pos
      calc
        ‖f (n + 1)‖ / ‖f n‖
            = f (n + 1) / f n := by
              rw [Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_pos hf_succ_pos, abs_of_pos hf_n_pos]
        _ = (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
              w * Real.exp (-(R ^ n * (R - 1))) := by
              dsimp [f]
              rw [pow_succ w n, pow_succ R n]
              field_simp [hn_pos.ne', hw_ne, hw_pow_ne, Real.exp_ne_zero]
              have hexp_eq :
                  Real.exp (-(R ^ n * R - 1)) =
                    Real.exp (-(R ^ n - 1)) *
                      Real.exp (-(R ^ n * (R - 1))) := by
                rw [← Real.exp_add]
                congr 1
                ring
              rw [hexp_eq]
              simp only [Nat.cast_add, Nat.cast_one]
              ring_nf
    refine Tendsto.congr' hratio_eq.symm ?_
    have hfrac := tendsto_linear_ratio
    have hexp := tendsto_exp_neg_mul_pow (w := w) (R := R) hw hR
    have hprod :
        Tendsto
          (fun n : ℕ =>
            (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
              w * Real.exp (-(R ^ n * (R - 1))))
          atTop (𝓝 (1 * w * 0)) :=
      (hfrac.mul tendsto_const_nhds).mul hexp
    simpa using hprod

theorem summable_weightedGeometricExpKernel
    {w R : ℝ} (hw : 0 < w) (hR : 1 < R) :
    Summable fun k : ℕ => w ^ k * Real.exp (-(R ^ k - 1)) := by
  have hlinear := summable_weightedLinearExpKernel (w := w) (R := R) hw hR
  refine Summable.of_nonneg_of_le ?_ ?_ hlinear
  · intro k
    positivity
  · intro k
    have hk : 1 ≤ (k : ℝ) + 1 := by
      have hk0 : 0 ≤ (k : ℝ) := by positivity
      linarith
    have hterm_nonneg : 0 ≤ w ^ k * Real.exp (-(R ^ k - 1)) := by positivity
    calc
      w ^ k * Real.exp (-(R ^ k - 1))
          ≤ ((k : ℝ) + 1) * (w ^ k * Real.exp (-(R ^ k - 1))) :=
            by nlinarith
      _ = ((k : ℝ) + 1) * w ^ k * Real.exp (-(R ^ k - 1)) := by ring

theorem weightedGeometricExpKernelConst_pos
    {w R : ℝ} (hw : 0 < w) (hR : 1 < R) :
    0 < weightedGeometricExpKernelConst w R := by
  dsimp [weightedGeometricExpKernelConst]
  have hsum := summable_weightedGeometricExpKernel (w := w) (R := R) hw hR
  have hzero : (0 : ℝ) < w ^ (0 : ℕ) * Real.exp (-(R ^ (0 : ℕ) - 1)) := by
    positivity
  exact hsum.tsum_pos (fun k => by positivity) 0 hzero

theorem weightedLinearExpKernelConst_pos
    {w R : ℝ} (hw : 0 < w) (hR : 1 < R) :
    0 < weightedLinearExpKernelConst w R := by
  dsimp [weightedLinearExpKernelConst]
  have hsum := summable_weightedLinearExpKernel (w := w) (R := R) hw hR
  have hzero :
      (0 : ℝ) <
        (((0 : ℕ) : ℝ) + 1) * w ^ (0 : ℕ) *
          Real.exp (-(R ^ (0 : ℕ) - 1)) := by
    positivity
  exact hsum.tsum_pos (fun k => by positivity) 0 hzero

theorem exp_neg_rpow_mul_pow_le_exp_neg_mul_weighted_kernel
    {A ρ η : ℝ} (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η) (k : ℕ) :
    Real.exp (-((A * ρ ^ k) ^ η)) ≤
      Real.exp (-(A ^ η)) *
        Real.exp (-(((ρ ^ η) ^ k) - 1)) := by
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hρ_pos : 0 < ρ := lt_trans zero_lt_one hρ
  have hAη_pos : 0 < A ^ η := Real.rpow_pos_of_pos hA_pos η
  have hAη_ge_one : 1 ≤ A ^ η :=
    Real.one_le_rpow hA hη.le
  have hR_gt_one : 1 < ρ ^ η := Real.one_lt_rpow hρ hη
  have hR_pos : 0 < ρ ^ η := lt_trans zero_lt_one hR_gt_one
  have hRk_ge_one : 1 ≤ (ρ ^ η) ^ k := one_le_pow₀ hR_gt_one.le
  have hρ_pow_nonneg : 0 ≤ ρ ^ k := pow_nonneg hρ_pos.le k
  have hρkη :
      (ρ ^ k) ^ η = (ρ ^ η) ^ k := by
    exact (Real.rpow_pow_comm hρ_pos.le η k).symm
  have hmain :
      A ^ η + ((ρ ^ η) ^ k - 1) ≤ (A * ρ ^ k) ^ η := by
    have hprod :
        A ^ η + ((ρ ^ η) ^ k - 1) ≤ A ^ η * (ρ ^ η) ^ k := by
      nlinarith [hAη_ge_one, hRk_ge_one]
    calc
      A ^ η + ((ρ ^ η) ^ k - 1)
          ≤ A ^ η * (ρ ^ η) ^ k := hprod
      _ = (A * ρ ^ k) ^ η := by
        rw [Real.mul_rpow hA_pos.le hρ_pow_nonneg, hρkη]
  calc
    Real.exp (-((A * ρ ^ k) ^ η))
        ≤ Real.exp (-(A ^ η + ((ρ ^ η) ^ k - 1))) := by
          exact Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-(A ^ η)) *
          Real.exp (-(((ρ ^ η) ^ k) - 1)) := by
          rw [← Real.exp_add]
          congr 1
          ring

theorem summable_weighted_geometric_exp_neg_rpow_mul_pow
    {A ρ η w : ℝ} (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η) (hw : 0 < w) :
    Summable fun k : ℕ => w ^ k * Real.exp (-((A * ρ ^ k) ^ η)) := by
  have hR : 1 < ρ ^ η := Real.one_lt_rpow hρ hη
  have hmajor :
      Summable fun k : ℕ =>
        Real.exp (-(A ^ η)) *
          (w ^ k * Real.exp (-(((ρ ^ η) ^ k) - 1))) :=
    (summable_weightedGeometricExpKernel (w := w) (R := ρ ^ η) hw hR).mul_left _
  have hpoint :
      ∀ k : ℕ,
        w ^ k * Real.exp (-((A * ρ ^ k) ^ η)) ≤
          Real.exp (-(A ^ η)) *
            (w ^ k * Real.exp (-(((ρ ^ η) ^ k) - 1))) := by
    intro k
    have hwk_nonneg : 0 ≤ w ^ k := by positivity
    have hbase :=
      exp_neg_rpow_mul_pow_le_exp_neg_mul_weighted_kernel
        (A := A) (ρ := ρ) (η := η) hA hρ hη k
    calc
      w ^ k * Real.exp (-((A * ρ ^ k) ^ η))
          ≤ w ^ k *
              (Real.exp (-(A ^ η)) *
                Real.exp (-(((ρ ^ η) ^ k) - 1))) :=
            mul_le_mul_of_nonneg_left hbase hwk_nonneg
      _ = Real.exp (-(A ^ η)) *
            (w ^ k * Real.exp (-(((ρ ^ η) ^ k) - 1))) := by ring
  refine Summable.of_nonneg_of_le ?_ hpoint hmajor
  intro k
  positivity

theorem summable_weighted_linear_exp_neg_rpow_mul_pow
    {A ρ η w : ℝ} (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η) (hw : 0 < w) :
    Summable fun k : ℕ =>
      (((k : ℝ) + 1) * w ^ k * Real.exp (-((A * ρ ^ k) ^ η))) := by
  have hR : 1 < ρ ^ η := Real.one_lt_rpow hρ hη
  have hmajor :
      Summable fun k : ℕ =>
        Real.exp (-(A ^ η)) *
          (((k : ℝ) + 1) * w ^ k *
            Real.exp (-(((ρ ^ η) ^ k) - 1))) :=
    (summable_weightedLinearExpKernel (w := w) (R := ρ ^ η) hw hR).mul_left _
  have hpoint :
      ∀ k : ℕ,
        ((k : ℝ) + 1) * w ^ k * Real.exp (-((A * ρ ^ k) ^ η)) ≤
          Real.exp (-(A ^ η)) *
            (((k : ℝ) + 1) * w ^ k *
              Real.exp (-(((ρ ^ η) ^ k) - 1))) := by
    intro k
    have hfactor_nonneg : 0 ≤ ((k : ℝ) + 1) * w ^ k := by positivity
    have hbase :=
      exp_neg_rpow_mul_pow_le_exp_neg_mul_weighted_kernel
        (A := A) (ρ := ρ) (η := η) hA hρ hη k
    calc
      ((k : ℝ) + 1) * w ^ k * Real.exp (-((A * ρ ^ k) ^ η))
          ≤ ((k : ℝ) + 1) * w ^ k *
              (Real.exp (-(A ^ η)) *
                Real.exp (-(((ρ ^ η) ^ k) - 1))) :=
            mul_le_mul_of_nonneg_left hbase hfactor_nonneg
      _ = Real.exp (-(A ^ η)) *
            (((k : ℝ) + 1) * w ^ k *
              Real.exp (-(((ρ ^ η) ^ k) - 1))) := by ring
  refine Summable.of_nonneg_of_le ?_ hpoint hmajor
  intro k
  positivity

theorem tsum_weighted_geometric_exp_neg_rpow_mul_pow_le_const
    {A ρ η w : ℝ} (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η) (hw : 0 < w) :
    (∑' k : ℕ, w ^ k * Real.exp (-((A * ρ ^ k) ^ η))) ≤
      Real.exp (-(A ^ η)) * weightedGeometricExpKernelConst w (ρ ^ η) := by
  have hR : 1 < ρ ^ η := Real.one_lt_rpow hρ hη
  have hmajor :
      Summable fun k : ℕ =>
        Real.exp (-(A ^ η)) *
          (w ^ k * Real.exp (-(((ρ ^ η) ^ k) - 1))) := by
    exact (summable_weightedGeometricExpKernel (w := w) (R := ρ ^ η) hw hR).mul_left _
  have hpoint :
      ∀ k : ℕ,
        w ^ k * Real.exp (-((A * ρ ^ k) ^ η)) ≤
          Real.exp (-(A ^ η)) *
            (w ^ k * Real.exp (-(((ρ ^ η) ^ k) - 1))) := by
    intro k
    have hwk_nonneg : 0 ≤ w ^ k := by positivity
    have hbase :=
      exp_neg_rpow_mul_pow_le_exp_neg_mul_weighted_kernel
        (A := A) (ρ := ρ) (η := η) hA hρ hη k
    calc
      w ^ k * Real.exp (-((A * ρ ^ k) ^ η))
          ≤ w ^ k *
              (Real.exp (-(A ^ η)) *
                Real.exp (-(((ρ ^ η) ^ k) - 1))) :=
            mul_le_mul_of_nonneg_left hbase hwk_nonneg
      _ = Real.exp (-(A ^ η)) *
            (w ^ k * Real.exp (-(((ρ ^ η) ^ k) - 1))) := by ring
  have hlhs :
      Summable fun k : ℕ => w ^ k * Real.exp (-((A * ρ ^ k) ^ η)) := by
    refine Summable.of_nonneg_of_le ?_ hpoint hmajor
    intro k
    positivity
  calc
    (∑' k : ℕ, w ^ k * Real.exp (-((A * ρ ^ k) ^ η)))
        ≤ ∑' k : ℕ,
            Real.exp (-(A ^ η)) *
              (w ^ k * Real.exp (-(((ρ ^ η) ^ k) - 1))) :=
          Summable.tsum_le_tsum hpoint hlhs hmajor
    _ = Real.exp (-(A ^ η)) * weightedGeometricExpKernelConst w (ρ ^ η) := by
          rw [(summable_weightedGeometricExpKernel (w := w) (R := ρ ^ η) hw hR).tsum_mul_left]
          rfl

theorem tsum_weighted_linear_exp_neg_rpow_mul_pow_le_const
    {A ρ η w : ℝ} (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η) (hw : 0 < w) :
    (∑' k : ℕ, (((k : ℝ) + 1) * w ^ k *
      Real.exp (-((A * ρ ^ k) ^ η)))) ≤
      Real.exp (-(A ^ η)) * weightedLinearExpKernelConst w (ρ ^ η) := by
  have hR : 1 < ρ ^ η := Real.one_lt_rpow hρ hη
  have hmajor :
      Summable fun k : ℕ =>
        Real.exp (-(A ^ η)) *
          (((k : ℝ) + 1) * w ^ k *
            Real.exp (-(((ρ ^ η) ^ k) - 1))) := by
    exact (summable_weightedLinearExpKernel (w := w) (R := ρ ^ η) hw hR).mul_left _
  have hpoint :
      ∀ k : ℕ,
        ((k : ℝ) + 1) * w ^ k * Real.exp (-((A * ρ ^ k) ^ η)) ≤
          Real.exp (-(A ^ η)) *
            (((k : ℝ) + 1) * w ^ k *
              Real.exp (-(((ρ ^ η) ^ k) - 1))) := by
    intro k
    have hfactor_nonneg : 0 ≤ ((k : ℝ) + 1) * w ^ k := by positivity
    have hbase :=
      exp_neg_rpow_mul_pow_le_exp_neg_mul_weighted_kernel
        (A := A) (ρ := ρ) (η := η) hA hρ hη k
    calc
      ((k : ℝ) + 1) * w ^ k * Real.exp (-((A * ρ ^ k) ^ η))
          ≤ ((k : ℝ) + 1) * w ^ k *
              (Real.exp (-(A ^ η)) *
                Real.exp (-(((ρ ^ η) ^ k) - 1))) :=
            mul_le_mul_of_nonneg_left hbase hfactor_nonneg
      _ = Real.exp (-(A ^ η)) *
            (((k : ℝ) + 1) * w ^ k *
              Real.exp (-(((ρ ^ η) ^ k) - 1))) := by ring
  have hlhs :
      Summable fun k : ℕ =>
        ((k : ℝ) + 1) * w ^ k * Real.exp (-((A * ρ ^ k) ^ η)) := by
    refine Summable.of_nonneg_of_le ?_ hpoint hmajor
    intro k
    positivity
  calc
    (∑' k : ℕ, (((k : ℝ) + 1) * w ^ k *
        Real.exp (-((A * ρ ^ k) ^ η))))
        ≤ ∑' k : ℕ,
            Real.exp (-(A ^ η)) *
              (((k : ℝ) + 1) * w ^ k *
                Real.exp (-(((ρ ^ η) ^ k) - 1))) :=
          Summable.tsum_le_tsum hpoint hlhs hmajor
    _ = Real.exp (-(A ^ η)) * weightedLinearExpKernelConst w (ρ ^ η) := by
          rw [(summable_weightedLinearExpKernel (w := w) (R := ρ ^ η) hw hR).tsum_mul_left]
          rfl

end

end Section57
end Ch05
end Book
end Homogenization
