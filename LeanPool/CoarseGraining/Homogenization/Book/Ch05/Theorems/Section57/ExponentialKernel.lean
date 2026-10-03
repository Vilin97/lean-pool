/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleUnion

/-! # Exponential Kernel -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open scoped BigOperators

/-!
# Exponential kernels for the bad-scale summation

These are pure real-variable summability facts used to sum the fixed-pair
probability kernels in the quantitative minimal-scale proof.
-/

noncomputable section

noncomputable def geometricExpKernelConst (ρ η : ℝ) : ℝ :=
  ∑' k : ℕ, Real.exp ((k : ℝ) * (-(ρ ^ η - 1)))

noncomputable def linearExpKernelConst (ρ η : ℝ) : ℝ :=
  ∑' k : ℕ, (((k : ℝ) + 1) *
    Real.exp ((k : ℝ) * (-(ρ ^ η - 1))))

theorem geometricExpKernelConst_pos
    {ρ η : ℝ} (hρ : 1 < ρ) (hη : 0 < η) :
    0 < geometricExpKernelConst ρ η := by
  dsimp [geometricExpKernelConst]
  let f : ℕ → ℝ := fun k => Real.exp ((k : ℝ) * (-(ρ ^ η - 1)))
  have hsum : Summable f := by
    exact Real.summable_exp_nat_mul_iff.mpr
      (by
        have hδ_pos : 0 < ρ ^ η - 1 :=
          sub_pos.mpr (Real.one_lt_rpow hρ hη)
        linarith)
  have hzero : (0 : ℝ) < f 0 := by
    positivity
  simpa [f] using hsum.tsum_pos (fun k => by positivity) 0 hzero

theorem summable_linear_exp_kernel
    {ρ η : ℝ} (hρ : 1 < ρ) (hη : 0 < η) :
    Summable fun k : ℕ => (((k : ℝ) + 1) *
      Real.exp ((k : ℝ) * (-(ρ ^ η - 1)))) := by
  let δ : ℝ := ρ ^ η - 1
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact sub_pos.mpr (Real.one_lt_rpow hρ hη)
  have hlinear :
      Summable fun k : ℕ => (k : ℝ) * Real.exp (-δ * (k : ℝ)) := by
    simpa [pow_one, mul_comm, mul_left_comm, mul_assoc] using
      Real.summable_pow_mul_exp_neg_nat_mul 1 hδ_pos
  have hgeom :
      Summable fun k : ℕ => Real.exp (-δ * (k : ℝ)) := by
    have hbase : Summable fun k : ℕ => Real.exp ((k : ℝ) * (-δ)) :=
      Real.summable_exp_nat_mul_iff.mpr (by linarith)
    refine hbase.congr ?_
    intro k
    congr 1
    ring
  have hsum :
      Summable fun k : ℕ =>
        (k : ℝ) * Real.exp (-δ * (k : ℝ)) +
          Real.exp (-δ * (k : ℝ)) :=
    hlinear.add hgeom
  refine hsum.congr ?_
  intro k
  dsimp [δ]
  ring_nf

theorem linearExpKernelConst_pos
    {ρ η : ℝ} (hρ : 1 < ρ) (hη : 0 < η) :
    0 < linearExpKernelConst ρ η := by
  dsimp [linearExpKernelConst]
  have hsum := summable_linear_exp_kernel hρ hη
  have hzero :
      (0 : ℝ) <
        (((0 : ℕ) : ℝ) + 1) *
          Real.exp (((0 : ℕ) : ℝ) * (-(ρ ^ η - 1))) := by
    positivity
  exact hsum.tsum_pos (fun k => by positivity) 0 hzero

theorem exp_neg_rpow_mul_pow_le_exp_neg_mul_exp_neg_nat
    {A ρ η : ℝ} (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η) (k : ℕ) :
    Real.exp (-((A * ρ ^ k) ^ η)) ≤
      Real.exp (-(A ^ η)) *
        Real.exp (-((ρ ^ η - 1) * (k : ℝ))) := by
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hρ_pos : 0 < ρ := lt_trans zero_lt_one hρ
  have hAη_pos : 0 < A ^ η := Real.rpow_pos_of_pos hA_pos η
  have hAη_ge_one : 1 ≤ A ^ η := by
    exact Real.one_le_rpow hA hη.le
  have hρ_pow_nonneg : 0 ≤ ρ ^ k := pow_nonneg hρ_pos.le k
  let r : ℝ := ρ ^ η
  have hr_gt_one : 1 < r := by
    dsimp [r]
    exact Real.one_lt_rpow hρ hη
  have hr_nonneg : 0 ≤ r := le_of_lt (lt_trans zero_lt_one hr_gt_one)
  have hbern :
      1 + (k : ℝ) * (r - 1) ≤ r ^ k := by
    exact one_add_mul_sub_le_pow (by linarith : (-1 : ℝ) ≤ r) k
  have hρkη :
      (ρ ^ k) ^ η = r ^ k := by
    dsimp [r]
    exact (Real.rpow_pow_comm hρ_pos.le η k).symm
  have hmain :
      A ^ η + (ρ ^ η - 1) * (k : ℝ) ≤ (A * ρ ^ k) ^ η := by
    have hmul_lower :
        A ^ η * (1 + (k : ℝ) * (r - 1)) ≤ A ^ η * r ^ k :=
      mul_le_mul_of_nonneg_left hbern hAη_pos.le
    have hleft_le :
        A ^ η + (r - 1) * (k : ℝ) ≤
          A ^ η * (1 + (k : ℝ) * (r - 1)) := by
      have hdelta_nonneg : 0 ≤ r - 1 := by linarith
      have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
      have hterm_nonneg : 0 ≤ (k : ℝ) * (r - 1) :=
        mul_nonneg hk_nonneg hdelta_nonneg
      nlinarith [hAη_ge_one, hterm_nonneg]
    calc
      A ^ η + (ρ ^ η - 1) * (k : ℝ)
          = A ^ η + (r - 1) * (k : ℝ) := by simp [r]
      _ ≤ A ^ η * (1 + (k : ℝ) * (r - 1)) := hleft_le
      _ ≤ A ^ η * r ^ k := hmul_lower
      _ = (A * ρ ^ k) ^ η := by
        rw [Real.mul_rpow hA_pos.le hρ_pow_nonneg, hρkη]
  calc
    Real.exp (-((A * ρ ^ k) ^ η))
        ≤ Real.exp (-(A ^ η + (ρ ^ η - 1) * (k : ℝ))) := by
          exact Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-(A ^ η)) *
          Real.exp (-((ρ ^ η - 1) * (k : ℝ))) := by
          rw [← Real.exp_add]
          congr 1
          ring

theorem summable_exp_neg_rpow_mul_pow
    {A ρ η : ℝ} (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η) :
    Summable fun k : ℕ => Real.exp (-((A * ρ ^ k) ^ η)) := by
  let δ : ℝ := ρ ^ η - 1
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact sub_pos.mpr (Real.one_lt_rpow hρ hη)
  have hgeom :
      Summable fun k : ℕ => Real.exp (-((δ) * (k : ℝ))) := by
    have hbase : Summable fun k : ℕ => Real.exp ((k : ℝ) * (-δ)) :=
      Real.summable_exp_nat_mul_iff.mpr (by linarith)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
  have hscaled :
      Summable fun k : ℕ =>
        Real.exp (-(A ^ η)) * Real.exp (-(δ * (k : ℝ))) :=
    hgeom.mul_left _
  refine Summable.of_nonneg_of_le ?_ ?_ hscaled
  · intro k
    positivity
  · intro k
    simpa [δ] using
      exp_neg_rpow_mul_pow_le_exp_neg_mul_exp_neg_nat
        (A := A) (ρ := ρ) (η := η) hA hρ hη k

theorem tsum_exp_neg_rpow_mul_pow_le
    {A ρ η : ℝ} (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η) :
    (∑' k : ℕ, Real.exp (-((A * ρ ^ k) ^ η))) ≤
      ∑' k : ℕ,
        Real.exp (-(A ^ η)) *
          Real.exp (-((ρ ^ η - 1) * (k : ℝ))) := by
  have hf := summable_exp_neg_rpow_mul_pow
    (A := A) (ρ := ρ) (η := η) hA hρ hη
  let δ : ℝ := ρ ^ η - 1
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact sub_pos.mpr (Real.one_lt_rpow hρ hη)
  have hgeom :
      Summable fun k : ℕ => Real.exp (-(δ * (k : ℝ))) := by
    have hbase : Summable fun k : ℕ => Real.exp ((k : ℝ) * (-δ)) :=
      Real.summable_exp_nat_mul_iff.mpr (by linarith)
    refine hbase.congr ?_
    intro k
    congr 1
    ring
  have hg :
      Summable fun k : ℕ =>
        Real.exp (-(A ^ η)) *
          Real.exp (-((ρ ^ η - 1) * (k : ℝ))) := by
    simpa [δ] using hgeom.mul_left (Real.exp (-(A ^ η)))
  exact Summable.tsum_le_tsum
    (fun k =>
      exp_neg_rpow_mul_pow_le_exp_neg_mul_exp_neg_nat
        (A := A) (ρ := ρ) (η := η) hA hρ hη k)
    hf hg

theorem tsum_exp_neg_rpow_mul_pow_le_const
    {A ρ η : ℝ} (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η) :
    (∑' k : ℕ, Real.exp (-((A * ρ ^ k) ^ η))) ≤
      Real.exp (-(A ^ η)) * geometricExpKernelConst ρ η := by
  have hgeom :
      Summable fun k : ℕ => Real.exp (-((ρ ^ η - 1) * (k : ℝ))) := by
    let δ : ℝ := ρ ^ η - 1
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact sub_pos.mpr (Real.one_lt_rpow hρ hη)
    have hbase : Summable fun k : ℕ => Real.exp ((k : ℝ) * (-δ)) :=
      Real.summable_exp_nat_mul_iff.mpr (by linarith)
    refine hbase.congr ?_
    intro k
    dsimp [δ]
    congr 1
    ring
  calc
    (∑' k : ℕ, Real.exp (-((A * ρ ^ k) ^ η)))
        ≤ ∑' k : ℕ,
            Real.exp (-(A ^ η)) *
              Real.exp (-((ρ ^ η - 1) * (k : ℝ))) :=
        tsum_exp_neg_rpow_mul_pow_le (A := A) (ρ := ρ) (η := η)
            hA hρ hη
    _ = Real.exp (-(A ^ η)) * geometricExpKernelConst ρ η := by
          rw [hgeom.tsum_mul_left]
          congr 1
          dsimp [geometricExpKernelConst]
          apply tsum_congr
          intro k
          congr 1
          ring

theorem tsum_linear_mul_exp_neg_rpow_mul_pow_le_const
    {A ρ η : ℝ} (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η) :
    (∑' k : ℕ, (((k : ℝ) + 1) *
      Real.exp (-((A * ρ ^ k) ^ η)))) ≤
      Real.exp (-(A ^ η)) * linearExpKernelConst ρ η := by
  have hlinear := summable_linear_exp_kernel hρ hη
  have hmajor :
      Summable fun k : ℕ =>
        Real.exp (-(A ^ η)) *
          (((k : ℝ) + 1) *
            Real.exp ((k : ℝ) * (-(ρ ^ η - 1)))) :=
    hlinear.mul_left _
  have hpoint :
      ∀ k : ℕ,
        (((k : ℝ) + 1) * Real.exp (-((A * ρ ^ k) ^ η))) ≤
          Real.exp (-(A ^ η)) *
            (((k : ℝ) + 1) *
              Real.exp ((k : ℝ) * (-(ρ ^ η - 1)))) := by
    intro k
    have hk_nonneg : 0 ≤ (k : ℝ) + 1 := by positivity
    have hbase :=
      exp_neg_rpow_mul_pow_le_exp_neg_mul_exp_neg_nat
        (A := A) (ρ := ρ) (η := η) hA hρ hη k
    calc
      (((k : ℝ) + 1) * Real.exp (-((A * ρ ^ k) ^ η)))
          ≤ ((k : ℝ) + 1) *
              (Real.exp (-(A ^ η)) *
                Real.exp (-((ρ ^ η - 1) * (k : ℝ)))) :=
            mul_le_mul_of_nonneg_left hbase hk_nonneg
      _ = Real.exp (-(A ^ η)) *
            (((k : ℝ) + 1) *
              Real.exp ((k : ℝ) * (-(ρ ^ η - 1)))) := by
            ring_nf
  have hlhs :
      Summable fun k : ℕ =>
        (((k : ℝ) + 1) * Real.exp (-((A * ρ ^ k) ^ η))) := by
    refine Summable.of_nonneg_of_le ?_ hpoint hmajor
    intro k
    positivity
  calc
    (∑' k : ℕ, (((k : ℝ) + 1) *
        Real.exp (-((A * ρ ^ k) ^ η))))
        ≤ ∑' k : ℕ,
            Real.exp (-(A ^ η)) *
              (((k : ℝ) + 1) *
                Real.exp ((k : ℝ) * (-(ρ ^ η - 1)))) :=
          Summable.tsum_le_tsum hpoint hlhs hmajor
    _ = Real.exp (-(A ^ η)) * linearExpKernelConst ρ η := by
          rw [hlinear.tsum_mul_left]
          rfl

theorem summable_linear_mul_exp_neg_rpow_mul_pow
    {A ρ η : ℝ} (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η) :
    Summable fun k : ℕ => (((k : ℝ) + 1) *
      Real.exp (-((A * ρ ^ k) ^ η))) := by
  have hlinear := summable_linear_exp_kernel hρ hη
  have hmajor :
      Summable fun k : ℕ =>
        Real.exp (-(A ^ η)) *
          (((k : ℝ) + 1) *
            Real.exp ((k : ℝ) * (-(ρ ^ η - 1)))) :=
    hlinear.mul_left _
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro k
    positivity
  · intro k
    have hk_nonneg : 0 ≤ (k : ℝ) + 1 := by positivity
    have hbase :=
      exp_neg_rpow_mul_pow_le_exp_neg_mul_exp_neg_nat
        (A := A) (ρ := ρ) (η := η) hA hρ hη k
    calc
      (((k : ℝ) + 1) * Real.exp (-((A * ρ ^ k) ^ η)))
          ≤ ((k : ℝ) + 1) *
              (Real.exp (-(A ^ η)) *
                Real.exp (-((ρ ^ η - 1) * (k : ℝ)))) :=
            mul_le_mul_of_nonneg_left hbase hk_nonneg
      _ = Real.exp (-(A ^ η)) *
            (((k : ℝ) + 1) *
              Real.exp ((k : ℝ) * (-(ρ ^ η - 1)))) := by
            ring_nf

theorem summable_exp_neg_two_rpow_mul_pow
    {A ρ₁ ρ₂ η : ℝ} (hA : 1 ≤ A) (hρ₁ : 1 < ρ₁)
    (hρ₂ : 1 < ρ₂) (hη : 0 < η) :
    Summable fun p : ℕ × ℕ =>
      Real.exp (-((A * ρ₁ ^ p.1 * ρ₂ ^ p.2) ^ η)) := by
  let F : ℕ × ℕ → ℝ := fun p =>
    Real.exp (-((A * ρ₁ ^ p.1 * ρ₂ ^ p.2) ^ η))
  have hrow : ∀ i : ℕ, Summable fun j : ℕ => F (i, j) := by
    intro i
    have hρ₁_pow : 1 ≤ ρ₁ ^ i :=
      one_le_pow₀ hρ₁.le
    have hA_i : 1 ≤ A * ρ₁ ^ i := by
      have hA_nonneg : 0 ≤ A := le_trans zero_le_one hA
      have hmul := mul_le_mul hA hρ₁_pow
        (by norm_num : (0 : ℝ) ≤ 1) hA_nonneg
      simpa using hmul
    simpa [F, mul_assoc] using
      summable_exp_neg_rpow_mul_pow
        (A := A * ρ₁ ^ i) (ρ := ρ₂) (η := η) hA_i hρ₂ hη
  have hrow_le :
      ∀ i : ℕ, (∑' j : ℕ, F (i, j)) ≤
        Real.exp (-((A * ρ₁ ^ i) ^ η)) * geometricExpKernelConst ρ₂ η := by
    intro i
    have hρ₁_pow : 1 ≤ ρ₁ ^ i :=
      one_le_pow₀ hρ₁.le
    have hA_i : 1 ≤ A * ρ₁ ^ i := by
      have hA_nonneg : 0 ≤ A := le_trans zero_le_one hA
      have hmul := mul_le_mul hA hρ₁_pow
        (by norm_num : (0 : ℝ) ≤ 1) hA_nonneg
      simpa using hmul
    simpa [F, mul_assoc] using
      tsum_exp_neg_rpow_mul_pow_le_const
        (A := A * ρ₁ ^ i) (ρ := ρ₂) (η := η) hA_i hρ₂ hη
  have houter :
      Summable fun i : ℕ => ∑' j : ℕ, F (i, j) := by
    have hbase :
        Summable fun i : ℕ => Real.exp (-((A * ρ₁ ^ i) ^ η)) :=
      summable_exp_neg_rpow_mul_pow (A := A) (ρ := ρ₁) (η := η)
        hA hρ₁ hη
    have hmajor :
        Summable fun i : ℕ =>
          Real.exp (-((A * ρ₁ ^ i) ^ η)) *
            geometricExpKernelConst ρ₂ η :=
      hbase.mul_right _
    refine Summable.of_nonneg_of_le ?_ hrow_le hmajor
    intro i
    exact tsum_nonneg fun j => by
      dsimp [F]
      positivity
  exact (summable_prod_of_nonneg (f := F) (fun p => by
    dsimp [F]
    positivity)).2 ⟨hrow, houter⟩

theorem tsum_exp_neg_two_rpow_mul_pow_le_const
    {A ρ₁ ρ₂ η : ℝ} (hA : 1 ≤ A) (hρ₁ : 1 < ρ₁)
    (hρ₂ : 1 < ρ₂) (hη : 0 < η) :
    (∑' p : ℕ × ℕ,
      Real.exp (-((A * ρ₁ ^ p.1 * ρ₂ ^ p.2) ^ η))) ≤
      Real.exp (-(A ^ η)) *
        geometricExpKernelConst ρ₁ η * geometricExpKernelConst ρ₂ η := by
  let F : ℕ × ℕ → ℝ := fun p =>
    Real.exp (-((A * ρ₁ ^ p.1 * ρ₂ ^ p.2) ^ η))
  have hF : Summable F := by
    simpa [F] using
      summable_exp_neg_two_rpow_mul_pow
        (A := A) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (η := η) hA hρ₁ hρ₂ hη
  have hrow_le :
      ∀ i : ℕ, (∑' j : ℕ, F (i, j)) ≤
        Real.exp (-((A * ρ₁ ^ i) ^ η)) * geometricExpKernelConst ρ₂ η := by
    intro i
    have hρ₁_pow : 1 ≤ ρ₁ ^ i :=
      one_le_pow₀ hρ₁.le
    have hA_i : 1 ≤ A * ρ₁ ^ i := by
      have hA_nonneg : 0 ≤ A := le_trans zero_le_one hA
      have hmul := mul_le_mul hA hρ₁_pow
        (by norm_num : (0 : ℝ) ≤ 1) hA_nonneg
      simpa using hmul
    simpa [F, mul_assoc] using
      tsum_exp_neg_rpow_mul_pow_le_const
        (A := A * ρ₁ ^ i) (ρ := ρ₂) (η := η) hA_i hρ₂ hη
  have hbase :
      Summable fun i : ℕ => Real.exp (-((A * ρ₁ ^ i) ^ η)) :=
    summable_exp_neg_rpow_mul_pow (A := A) (ρ := ρ₁) (η := η)
      hA hρ₁ hη
  have hmajor :
      Summable fun i : ℕ =>
        Real.exp (-((A * ρ₁ ^ i) ^ η)) *
          geometricExpKernelConst ρ₂ η :=
    hbase.mul_right _
  have hrows :
      Summable fun i : ℕ => ∑' j : ℕ, F (i, j) :=
    hF.prod
  have hC₂_nonneg : 0 ≤ geometricExpKernelConst ρ₂ η :=
    (geometricExpKernelConst_pos hρ₂ hη).le
  calc
    (∑' p : ℕ × ℕ,
        Real.exp (-((A * ρ₁ ^ p.1 * ρ₂ ^ p.2) ^ η)))
        = ∑' i : ℕ, ∑' j : ℕ, F (i, j) := by
          simpa [F] using hF.tsum_prod
    _ ≤ ∑' i : ℕ,
        Real.exp (-((A * ρ₁ ^ i) ^ η)) *
          geometricExpKernelConst ρ₂ η :=
          Summable.tsum_le_tsum hrow_le hrows hmajor
    _ = (∑' i : ℕ, Real.exp (-((A * ρ₁ ^ i) ^ η))) *
          geometricExpKernelConst ρ₂ η :=
          hbase.tsum_mul_right _
    _ ≤ (Real.exp (-(A ^ η)) * geometricExpKernelConst ρ₁ η) *
          geometricExpKernelConst ρ₂ η :=
          mul_le_mul_of_nonneg_right
            (tsum_exp_neg_rpow_mul_pow_le_const
              (A := A) (ρ := ρ₁) (η := η) hA hρ₁ hη)
            hC₂_nonneg
    _ = Real.exp (-(A ^ η)) *
        geometricExpKernelConst ρ₁ η * geometricExpKernelConst ρ₂ η := by
          ring

end

end Section57
end Ch05
end Book
end Homogenization
