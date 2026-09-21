/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.BrownianMultipleIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Pure powers in iterated kernel spaces

The pointwise product `t ↦ ∏ i, f (t i)` realizes the pure tensor power of a deterministic
`L²` kernel inside the product-measure model `IteratedKernel n`.  This file establishes its
square-integrability, symmetry, and Hilbert-space formulas.  These are the deterministic inputs
for identifying generalized Hermite values with canonical Brownian multiple integrals.
-/

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace Malliavin

/-- The pointwise `n`-fold pure product of a deterministic time function. -/
def iteratedKernelPurePowerFun (n : ℕ) (f : ℝ≥0 → ℝ) : (Fin n → ℝ≥0) → ℝ :=
  fun t ↦ ∏ i, f (t i)

/-- The pure product of an `L²` time kernel is square-integrable on the product time space. -/
theorem memLp_two_iteratedKernelPurePowerFun (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    MemLp (iteratedKernelPurePowerFun n f) 2 (iteratedKernelMeasure n) := by
  have hmeas : AEStronglyMeasurable (iteratedKernelPurePowerFun n f)
      (iteratedKernelMeasure n) := by
    unfold iteratedKernelPurePowerFun iteratedKernelMeasure
    apply Finset.aestronglyMeasurable_fun_prod Finset.univ
    intro i _hi
    exact (Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval
        (fun _ : Fin n ↦ nonnegativeLebesgueMeasure) i)
  rw [memLp_two_iff_integrable_sq hmeas]
  have hsq : Integrable (fun t : ℝ≥0 ↦ f t ^ 2) nonnegativeLebesgueMeasure :=
    (Lp.memLp f).integrable_sq
  have hprod : Integrable
      (fun t : Fin n → ℝ≥0 ↦ ∏ i, (f (t i)) ^ 2) (iteratedKernelMeasure n) := by
    exact Integrable.fintype_prod fun _ : Fin n ↦ hsq
  simpa only [iteratedKernelPurePowerFun, Finset.prod_pow] using hprod

/-- The `n`-fold pure power of a deterministic `L²` time kernel. -/
noncomputable def iteratedKernelPurePower (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) : IteratedKernel n :=
  (memLp_two_iteratedKernelPurePowerFun n f).toLp (iteratedKernelPurePowerFun n f)

/-- The canonical representative of a pure-power kernel is its pointwise coordinate product. -/
theorem coeFn_iteratedKernelPurePower (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (iteratedKernelPurePower n f : (Fin n → ℝ≥0) → ℝ) =ᵐ[iteratedKernelMeasure n]
      iteratedKernelPurePowerFun n f := by
  exact MemLp.coeFn_toLp _

/-- Pointwise pure powers are invariant under every permutation of their coordinates. -/
theorem isSymmetric_iteratedKernelPurePowerFun (n : ℕ)
    (f : ℝ≥0 → ℝ) :
    IsSymmetric n (iteratedKernelPurePowerFun n f) := by
  intro σ t
  simpa only [iteratedKernelPurePowerFun, Function.comp_apply] using
    Equiv.prod_comp σ (fun i ↦ f (t i))

/-- Pure-power kernels are fixed by the `L²` symmetrization operator. -/
theorem symmetrizeL_iteratedKernelPurePower (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
        (iteratedKernelPurePower n f) =
      iteratedKernelPurePower n f := by
  apply symmetrizeL_eq_self_of_ae_symmetric
  intro σ
  have hcoe := coeFn_iteratedKernelPurePower n f
  have hcomp := (measurePreserving_comp_perm nonnegativeLebesgueMeasure n σ
    ).quasiMeasurePreserving.ae_eq_comp hcoe
  filter_upwards [hcomp, hcoe] with t hcomp_t hcoe_t
  rw [hcomp_t, hcoe_t]
  exact isSymmetric_iteratedKernelPurePowerFun n f σ t

/-- The inner product of two pure powers is the corresponding one-particle inner product raised
to the tensor order. -/
theorem inner_iteratedKernelPurePower (n : ℕ)
    (f g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    inner ℝ (iteratedKernelPurePower n f) (iteratedKernelPurePower n g) =
      inner ℝ f g ^ n := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc
    (∫ t, inner ℝ (iteratedKernelPurePower n f t)
        (iteratedKernelPurePower n g t) ∂iteratedKernelMeasure n) =
        ∫ t, ∏ i, inner ℝ (f (t i)) (g (t i)) ∂iteratedKernelMeasure n := by
      apply integral_congr_ae
      filter_upwards [coeFn_iteratedKernelPurePower n f,
        coeFn_iteratedKernelPurePower n g] with t hf hg
      rw [hf, hg]
      simp only [iteratedKernelPurePowerFun, RCLike.inner_apply, conj_trivial,
        Finset.prod_mul_distrib]
    _ = (∫ t, inner ℝ (f t) (g t) ∂nonnegativeLebesgueMeasure) ^ n := by
      simpa only [Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι := Fin n)
          (μ := nonnegativeLebesgueMeasure) (fun t ↦ inner ℝ (f t) (g t)))

/-- Squared norm formula for a pure-power kernel. -/
theorem norm_sq_iteratedKernelPurePower (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖iteratedKernelPurePower n f‖ ^ 2 = (‖f‖ ^ 2) ^ n := by
  rw [← real_inner_self_eq_norm_sq, inner_iteratedKernelPurePower,
    real_inner_self_eq_norm_sq]

/-- Norm formula for a pure-power kernel. -/
theorem norm_iteratedKernelPurePower (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖iteratedKernelPurePower n f‖ = ‖f‖ ^ n := by
  apply (sq_eq_sq₀ (norm_nonneg _) (pow_nonneg (norm_nonneg _) n)).mp
  rw [norm_sq_iteratedKernelPurePower]
  calc
    (‖f‖ ^ 2) ^ n = ‖f‖ ^ (2 * n) := (pow_mul ‖f‖ 2 n).symm
    _ = ‖f‖ ^ (n * 2) := by rw [Nat.mul_comm 2 n]
    _ = (‖f‖ ^ n) ^ 2 := pow_mul ‖f‖ n 2

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
