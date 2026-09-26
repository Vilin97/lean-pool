/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.ExponentialKernel
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.WeightedExponentialKernel

/-! # Kernel Union -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped BigOperators ENNReal

/-!
# Kernel union bounds for fixed-pair events

This file turns two-parameter stretched-exponential fixed-pair bounds into
countable union bounds over the paired natural indices.
-/

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measureReal_iUnion_unpair_le_exp_two_kernel
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {E : ℕ → ℕ → Set Ω}
    {A ρ₁ ρ₂ η C : ℝ}
    (hC : 0 ≤ C) (hA : 1 ≤ A)
    (hρ₁ : 1 < ρ₁) (hρ₂ : 1 < ρ₂) (hη : 0 < η)
    (hE : ∀ i j : ℕ,
      μ.real (E i j) ≤
        C * Real.exp (-((A * ρ₁ ^ i * ρ₂ ^ j) ^ η))) :
    μ.real (⋃ k : ℕ, E (Nat.unpair k).1 (Nat.unpair k).2) ≤
      C *
        (Real.exp (-(A ^ η)) *
          geometricExpKernelConst ρ₁ η * geometricExpKernelConst ρ₂ η) := by
  let kernel : ℕ × ℕ → ℝ := fun p =>
    Real.exp (-((A * ρ₁ ^ p.1 * ρ₂ ^ p.2) ^ η))
  let f : ℕ → ℝ := fun k =>
    μ.real (E (Nat.unpair k).1 (Nat.unpair k).2)
  let g : ℕ → ℝ := fun k => C * kernel (Nat.unpair k)
  have hkernel_prod : Summable kernel := by
    simpa [kernel] using
      summable_exp_neg_two_rpow_mul_pow
        (A := A) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (η := η) hA hρ₁ hρ₂ hη
  have hunpair_inj : Function.Injective (Nat.unpair : ℕ → ℕ × ℕ) :=
    Nat.pairEquiv.symm.injective
  have hkernel_unpair : Summable fun k : ℕ => kernel (Nat.unpair k) := by
    simpa [Function.comp] using! hkernel_prod.comp_injective hunpair_inj
  have hg : Summable g := by
    simpa [g] using hkernel_unpair.mul_left C
  have hf : Summable f := by
    refine Summable.of_nonneg_of_le ?_ ?_ hg
    · intro k
      dsimp [f]
      positivity
    · intro k
      dsimp [f, g, kernel]
      exact hE (Nat.unpair k).1 (Nat.unpair k).2
  have hkernel_unpair_tsum_le :
      (∑' k : ℕ, kernel (Nat.unpair k)) ≤
        Real.exp (-(A ^ η)) *
          geometricExpKernelConst ρ₁ η * geometricExpKernelConst ρ₂ η := by
    calc
      (∑' k : ℕ, kernel (Nat.unpair k))
          = ∑' p : ℕ × ℕ, kernel p := by
            simpa [kernel, Nat.pairEquiv] using!
              (Nat.pairEquiv.symm.tsum_eq kernel)
      _ ≤ Real.exp (-(A ^ η)) *
          geometricExpKernelConst ρ₁ η * geometricExpKernelConst ρ₂ η := by
            simpa [kernel] using
              tsum_exp_neg_two_rpow_mul_pow_le_const
                (A := A) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (η := η)
                hA hρ₁ hρ₂ hη
  calc
    μ.real (⋃ k : ℕ, E (Nat.unpair k).1 (Nat.unpair k).2)
        ≤ ∑' k : ℕ, f k := by
          simpa [f] using
            measureReal_iUnion_nat_le_tsum
              (μ := μ)
              (E := fun k : ℕ => E (Nat.unpair k).1 (Nat.unpair k).2) hf
    _ ≤ ∑' k : ℕ, g k :=
          Summable.tsum_le_tsum
            (fun k => by
              dsimp [f, g, kernel]
              exact hE (Nat.unpair k).1 (Nat.unpair k).2)
            hf hg
    _ = C * (∑' k : ℕ, kernel (Nat.unpair k)) := by
          simpa [g] using hkernel_unpair.tsum_mul_left C
    _ ≤ C *
        (Real.exp (-(A ^ η)) *
          geometricExpKernelConst ρ₁ η * geometricExpKernelConst ρ₂ η) :=
          mul_le_mul_of_nonneg_left hkernel_unpair_tsum_le hC

theorem measureReal_iUnion_linearRows_le_exp_linear_kernel
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {E : (r : ℕ) → Fin (r + 1) → Set Ω}
    {A ρ η C : ℝ}
    (hC : 0 ≤ C) (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η)
    (hE : ∀ (r : ℕ) (j : Fin (r + 1)),
      μ.real (E r j) ≤ C * Real.exp (-((A * ρ ^ r) ^ η))) :
    μ.real (⋃ r : ℕ, ⋃ j : Fin (r + 1), E r j) ≤
      C * (Real.exp (-(A ^ η)) * linearExpKernelConst ρ η) := by
  let Row : ℕ → Set Ω := fun r => ⋃ j : Fin (r + 1), E r j
  let kernel : ℕ → ℝ := fun r => Real.exp (-((A * ρ ^ r) ^ η))
  let rowMajor : ℕ → ℝ := fun r => C * (((r : ℝ) + 1) * kernel r)
  have hrow_le : ∀ r : ℕ, μ.real (Row r) ≤ rowMajor r := by
    intro r
    have hfinite :
        μ.real (Row r) ≤ ∑ j : Fin (r + 1), μ.real (E r j) := by
      simpa [Row] using
        measureReal_iUnion_fintype_le (μ := μ) (f := fun j : Fin (r + 1) => E r j)
    have hsum :
        (∑ j : Fin (r + 1), μ.real (E r j)) ≤
          ∑ _j : Fin (r + 1), C * kernel r := by
      exact Finset.sum_le_sum fun j _hj => by
        simpa [kernel] using hE r j
    calc
      μ.real (Row r) ≤ ∑ j : Fin (r + 1), μ.real (E r j) := hfinite
      _ ≤ ∑ _j : Fin (r + 1), C * kernel r := hsum
      _ = rowMajor r := by
            simp [rowMajor]
            ring
  have hmajor : Summable rowMajor := by
    have hbase :
        Summable fun r : ℕ => (((r : ℝ) + 1) * kernel r) := by
      simpa [kernel] using
        summable_linear_mul_exp_neg_rpow_mul_pow
          (A := A) (ρ := ρ) (η := η) hA hρ hη
    simpa [rowMajor, mul_assoc] using hbase.mul_left C
  have hrow : Summable fun r : ℕ => μ.real (Row r) := by
    refine Summable.of_nonneg_of_le ?_ hrow_le hmajor
    intro r
    dsimp [Row]
    positivity
  calc
    μ.real (⋃ r : ℕ, ⋃ j : Fin (r + 1), E r j)
        = μ.real (⋃ r : ℕ, Row r) := by simp [Row]
    _ ≤ ∑' r : ℕ, μ.real (Row r) :=
          measureReal_iUnion_nat_le_tsum (μ := μ) (E := Row) hrow
    _ ≤ ∑' r : ℕ, rowMajor r :=
          Summable.tsum_le_tsum hrow_le hrow hmajor
    _ = C * (∑' r : ℕ, (((r : ℝ) + 1) * kernel r)) := by
          have hbase :
              Summable fun r : ℕ => (((r : ℝ) + 1) * kernel r) := by
            simpa [kernel] using
              summable_linear_mul_exp_neg_rpow_mul_pow
                (A := A) (ρ := ρ) (η := η) hA hρ hη
          simpa [rowMajor, mul_assoc] using hbase.tsum_mul_left C
    _ ≤ C * (Real.exp (-(A ^ η)) * linearExpKernelConst ρ η) :=
          mul_le_mul_of_nonneg_left
            (by
              simpa [kernel] using
                tsum_linear_mul_exp_neg_rpow_mul_pow_le_const
                  (A := A) (ρ := ρ) (η := η) hA hρ hη)
            hC

theorem measureReal_iUnion_constRows_le_exp_kernel
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {Q : ℕ} {E : ℕ → Fin Q → Set Ω}
    {A ρ η C : ℝ}
    (hC : 0 ≤ C) (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η)
    (hE : ∀ (r : ℕ) (j : Fin Q),
      μ.real (E r j) ≤ C * Real.exp (-((A * ρ ^ r) ^ η))) :
    μ.real (⋃ r : ℕ, ⋃ j : Fin Q, E r j) ≤
      (Q : ℝ) * C *
        (Real.exp (-(A ^ η)) * geometricExpKernelConst ρ η) := by
  let Row : ℕ → Set Ω := fun r => ⋃ j : Fin Q, E r j
  let kernel : ℕ → ℝ := fun r => Real.exp (-((A * ρ ^ r) ^ η))
  let rowMajor : ℕ → ℝ := fun r => (Q : ℝ) * C * kernel r
  have hrow_le : ∀ r : ℕ, μ.real (Row r) ≤ rowMajor r := by
    intro r
    have hfinite :
        μ.real (Row r) ≤ ∑ j : Fin Q, μ.real (E r j) := by
      simpa [Row] using
        measureReal_iUnion_fintype_le (μ := μ) (f := fun j : Fin Q => E r j)
    have hsum :
        (∑ j : Fin Q, μ.real (E r j)) ≤
          ∑ _j : Fin Q, C * kernel r := by
      exact Finset.sum_le_sum fun j _hj => by
        simpa [kernel] using hE r j
    calc
      μ.real (Row r) ≤ ∑ j : Fin Q, μ.real (E r j) := hfinite
      _ ≤ ∑ _j : Fin Q, C * kernel r := hsum
      _ = rowMajor r := by
            simp [rowMajor]
            ring
  have hmajor : Summable rowMajor := by
    have hbase : Summable kernel := by
      simpa [kernel] using
        summable_exp_neg_rpow_mul_pow
          (A := A) (ρ := ρ) (η := η) hA hρ hη
    simpa [rowMajor, mul_assoc] using hbase.mul_left ((Q : ℝ) * C)
  have hrow : Summable fun r : ℕ => μ.real (Row r) := by
    refine Summable.of_nonneg_of_le ?_ hrow_le hmajor
    intro r
    dsimp [Row]
    positivity
  calc
    μ.real (⋃ r : ℕ, ⋃ j : Fin Q, E r j)
        = μ.real (⋃ r : ℕ, Row r) := by simp [Row]
    _ ≤ ∑' r : ℕ, μ.real (Row r) :=
          measureReal_iUnion_nat_le_tsum (μ := μ) (E := Row) hrow
    _ ≤ ∑' r : ℕ, rowMajor r :=
          Summable.tsum_le_tsum hrow_le hrow hmajor
    _ = (Q : ℝ) * C * (∑' r : ℕ, kernel r) := by
          have hbase : Summable kernel := by
            simpa [kernel] using
              summable_exp_neg_rpow_mul_pow
                (A := A) (ρ := ρ) (η := η) hA hρ hη
          simpa [rowMajor, mul_assoc] using hbase.tsum_mul_left ((Q : ℝ) * C)
    _ ≤ (Q : ℝ) * C *
        (Real.exp (-(A ^ η)) * geometricExpKernelConst ρ η) := by
          have hQC_nonneg : 0 ≤ (Q : ℝ) * C := by positivity
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [kernel] using
                tsum_exp_neg_rpow_mul_pow_le_const
                  (A := A) (ρ := ρ) (η := η) hA hρ hη)
            hQC_nonneg

/-- Linear-row union bound with an exponential finite-union prefactor kept
outside the stochastic scale.  The weighted superexponential kernel absorbs
the prefactor without weakening the leading `A` exponent. -/
theorem measureReal_iUnion_linearRows_le_weighted_exp_linear_kernel
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {E : (r : ℕ) → Fin (r + 1) → Set Ω}
    {A ρ η C w : ℝ}
    (hC : 0 ≤ C) (hw : 0 < w) (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η)
    (hE : ∀ (r : ℕ) (j : Fin (r + 1)),
      μ.real (E r j) ≤ C * (w ^ r * Real.exp (-((A * ρ ^ r) ^ η)))) :
    μ.real (⋃ r : ℕ, ⋃ j : Fin (r + 1), E r j) ≤
      C * (Real.exp (-(A ^ η)) * weightedLinearExpKernelConst w (ρ ^ η)) := by
  let Row : ℕ → Set Ω := fun r => ⋃ j : Fin (r + 1), E r j
  let kernel : ℕ → ℝ := fun r => Real.exp (-((A * ρ ^ r) ^ η))
  let rowMajor : ℕ → ℝ := fun r => C * (((r : ℝ) + 1) * w ^ r * kernel r)
  have hrow_le : ∀ r : ℕ, μ.real (Row r) ≤ rowMajor r := by
    intro r
    have hfinite :
        μ.real (Row r) ≤ ∑ j : Fin (r + 1), μ.real (E r j) := by
      simpa [Row] using
        measureReal_iUnion_fintype_le (μ := μ) (f := fun j : Fin (r + 1) => E r j)
    have hsum :
        (∑ j : Fin (r + 1), μ.real (E r j)) ≤
          ∑ _j : Fin (r + 1), C * (w ^ r * kernel r) := by
      exact Finset.sum_le_sum fun j _hj => by
        simpa [kernel] using hE r j
    calc
      μ.real (Row r) ≤ ∑ j : Fin (r + 1), μ.real (E r j) := hfinite
      _ ≤ ∑ _j : Fin (r + 1), C * (w ^ r * kernel r) := hsum
      _ = rowMajor r := by
            simp [rowMajor]
            ring
  have hmajor : Summable rowMajor := by
    have hbase :
        Summable fun r : ℕ => (((r : ℝ) + 1) * w ^ r * kernel r) := by
      simpa [kernel] using
        summable_weighted_linear_exp_neg_rpow_mul_pow
          (A := A) (ρ := ρ) (η := η) (w := w) hA hρ hη hw
    simpa [rowMajor, mul_assoc] using hbase.mul_left C
  have hrow : Summable fun r : ℕ => μ.real (Row r) := by
    refine Summable.of_nonneg_of_le ?_ hrow_le hmajor
    intro r
    dsimp [Row]
    positivity
  calc
    μ.real (⋃ r : ℕ, ⋃ j : Fin (r + 1), E r j)
        = μ.real (⋃ r : ℕ, Row r) := by simp [Row]
    _ ≤ ∑' r : ℕ, μ.real (Row r) :=
          measureReal_iUnion_nat_le_tsum (μ := μ) (E := Row) hrow
    _ ≤ ∑' r : ℕ, rowMajor r :=
          Summable.tsum_le_tsum hrow_le hrow hmajor
    _ = C * (∑' r : ℕ, (((r : ℝ) + 1) * w ^ r * kernel r)) := by
          have hbase :
              Summable fun r : ℕ => (((r : ℝ) + 1) * w ^ r * kernel r) := by
            simpa [kernel] using
              summable_weighted_linear_exp_neg_rpow_mul_pow
                (A := A) (ρ := ρ) (η := η) (w := w) hA hρ hη hw
          simpa [rowMajor, mul_assoc] using hbase.tsum_mul_left C
    _ ≤ C * (Real.exp (-(A ^ η)) * weightedLinearExpKernelConst w (ρ ^ η)) :=
          mul_le_mul_of_nonneg_left
            (by
              simpa [kernel] using
                tsum_weighted_linear_exp_neg_rpow_mul_pow_le_const
                  (A := A) (ρ := ρ) (η := η) (w := w)
                  hA hρ hη hw)
            hC

/-- Constant-row version of the weighted finite-union kernel bound. -/
theorem measureReal_iUnion_constRows_le_weighted_exp_kernel
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {Q : ℕ} {E : ℕ → Fin Q → Set Ω}
    {A ρ η C w : ℝ}
    (hC : 0 ≤ C) (hw : 0 < w) (hA : 1 ≤ A) (hρ : 1 < ρ) (hη : 0 < η)
    (hE : ∀ (r : ℕ) (j : Fin Q),
      μ.real (E r j) ≤ C * (w ^ r * Real.exp (-((A * ρ ^ r) ^ η)))) :
    μ.real (⋃ r : ℕ, ⋃ j : Fin Q, E r j) ≤
      (Q : ℝ) * C *
        (Real.exp (-(A ^ η)) * weightedGeometricExpKernelConst w (ρ ^ η)) := by
  let Row : ℕ → Set Ω := fun r => ⋃ j : Fin Q, E r j
  let kernel : ℕ → ℝ := fun r => Real.exp (-((A * ρ ^ r) ^ η))
  let rowMajor : ℕ → ℝ := fun r => (Q : ℝ) * C * (w ^ r * kernel r)
  have hrow_le : ∀ r : ℕ, μ.real (Row r) ≤ rowMajor r := by
    intro r
    have hfinite :
        μ.real (Row r) ≤ ∑ j : Fin Q, μ.real (E r j) := by
      simpa [Row] using
        measureReal_iUnion_fintype_le (μ := μ) (f := fun j : Fin Q => E r j)
    have hsum :
        (∑ j : Fin Q, μ.real (E r j)) ≤
          ∑ _j : Fin Q, C * (w ^ r * kernel r) := by
      exact Finset.sum_le_sum fun j _hj => by
        simpa [kernel] using hE r j
    calc
      μ.real (Row r) ≤ ∑ j : Fin Q, μ.real (E r j) := hfinite
      _ ≤ ∑ _j : Fin Q, C * (w ^ r * kernel r) := hsum
      _ = rowMajor r := by
            simp [rowMajor]
            ring
  have hmajor : Summable rowMajor := by
    have hbase : Summable fun r : ℕ => w ^ r * kernel r := by
      simpa [kernel] using
        summable_weighted_geometric_exp_neg_rpow_mul_pow
          (A := A) (ρ := ρ) (η := η) (w := w) hA hρ hη hw
    simpa [rowMajor, mul_assoc] using hbase.mul_left ((Q : ℝ) * C)
  have hrow : Summable fun r : ℕ => μ.real (Row r) := by
    refine Summable.of_nonneg_of_le ?_ hrow_le hmajor
    intro r
    dsimp [Row]
    positivity
  calc
    μ.real (⋃ r : ℕ, ⋃ j : Fin Q, E r j)
        = μ.real (⋃ r : ℕ, Row r) := by simp [Row]
    _ ≤ ∑' r : ℕ, μ.real (Row r) :=
          measureReal_iUnion_nat_le_tsum (μ := μ) (E := Row) hrow
    _ ≤ ∑' r : ℕ, rowMajor r :=
          Summable.tsum_le_tsum hrow_le hrow hmajor
    _ = (Q : ℝ) * C * (∑' r : ℕ, w ^ r * kernel r) := by
          have hbase : Summable fun r : ℕ => w ^ r * kernel r := by
            simpa [kernel] using
              summable_weighted_geometric_exp_neg_rpow_mul_pow
                (A := A) (ρ := ρ) (η := η) (w := w) hA hρ hη hw
          simpa [rowMajor, mul_assoc] using hbase.tsum_mul_left ((Q : ℝ) * C)
    _ ≤ (Q : ℝ) * C *
        (Real.exp (-(A ^ η)) * weightedGeometricExpKernelConst w (ρ ^ η)) := by
          have hQC_nonneg : 0 ≤ (Q : ℝ) * C := by positivity
          exact mul_le_mul_of_nonneg_left
            (by
              simpa [kernel] using
                tsum_weighted_geometric_exp_neg_rpow_mul_pow_le_const
                  (A := A) (ρ := ρ) (η := η) (w := w)
                  hA hρ hη hw)
            hQC_nonneg

end

end Section57
end Ch05
end Book
end Homogenization
