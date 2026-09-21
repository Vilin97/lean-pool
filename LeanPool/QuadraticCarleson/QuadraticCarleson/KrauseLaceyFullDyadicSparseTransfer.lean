/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import Mathlib.MeasureTheory.Function.L2Space
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySparseReflection
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyFullDyadicReflection
import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteModulationKernelComparison

open Function MeasureTheory Set
open scoped ENNReal NNReal Topology Convolution

namespace QuadraticCarleson.KrauseLaceyFullDyadicSparseTransfer

open KrauseLaceyFullDyadicReflection KrauseLaceySparseReflection


theorem memLp_two_L0Infinity (f : L0Infinity) : MemLp (f : ℝ → ℂ) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm f.measurable_toFun.aestronglyMeasurable]
  obtain ⟨C, hC⟩ := f.bounded_toFun
  have hi := f.integrable.norm.bdd_mul f.measurable_toFun.norm.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by simpa only [norm_norm] using hC x)
  simpa only [pow_two] using hi

noncomputable def finitePositiveDyadicTailMaxOperator (lam : ℝ) (j : ℤ) (N : ℕ) :
    TestOperator := fun f x ↦ ((finitePositiveDyadicTailMaxNNNorm lam j N f x : ℝ) : ℂ)

noncomputable def finiteFullDyadicTailMaxOperator (lam : ℝ) (j : ℤ) (N : ℕ) :
    TestOperator := fun f x ↦ ((finiteFullDyadicTailMaxNNNorm lam j N f x : ℝ) : ℂ)

theorem continuous_positiveDyadicConvolution (lam : ℝ) (j : ℤ)
    (f : L0Infinity) : Continuous (positiveDyadicConvolution lam j f) := by
  have hc := (hasCompactSupport_positiveDyadicQuadraticKernel lam j).continuous_convolution_right
    (ContinuousLinearMap.mul ℂ ℂ) f.integrable.locallyIntegrable
    (continuous_positiveDyadicQuadraticKernel lam j)
  change Continuous (fun x ↦ ∫ y, f y *
    annularQuadraticKernel (positiveDyadicAmplitude j) lam (x - y)) at hc
  change Continuous (fun x ↦ ∫ y,
    annularQuadraticKernel (positiveDyadicAmplitude j) lam (x - y) * f y)
  simpa only [mul_comm] using hc

theorem continuous_finitePositiveDyadicTail (lam : ℝ) (j : ℤ) (n : ℕ)
    (f : L0Infinity) : Continuous (finitePositiveDyadicTail lam j n f) := by
  unfold finitePositiveDyadicTail
  exact continuous_finsetSum _ fun r hr ↦ continuous_positiveDyadicConvolution lam (j + r) f

theorem continuous_finiteFullDyadicTail (lam : ℝ) (j : ℤ) (n : ℕ)
    (f : L0Infinity) : Continuous (finiteFullDyadicTail lam j n f) := by
  have heq : finiteFullDyadicTail lam j n f = fun x ↦
      finitePositiveDyadicTail lam j n f x -
        finitePositiveDyadicTail lam j n (L0Infinity.reflect f) (-x) := by
    funext x
    exact finiteFullDyadicTail_eq_positive_sub_reflect lam j n (memLp_two_L0Infinity f) x
  rw [heq]
  exact (continuous_finitePositiveDyadicTail lam j n f).sub
    ((continuous_finitePositiveDyadicTail lam j n (L0Infinity.reflect f)).comp continuous_neg)

theorem continuous_finitePositiveDyadicTailMaxOperator (lam : ℝ) (j : ℤ) (N : ℕ)
    (f : L0Infinity) : Continuous (finitePositiveDyadicTailMaxOperator lam j N f) := by
  have hm : Continuous (finitePositiveDyadicTailMaxNNNorm lam j N f) :=
    Continuous.finset_sup_apply fun n hn ↦ (continuous_finitePositiveDyadicTail lam j n f).nnnorm
  exact Complex.continuous_ofReal.comp (continuous_subtype_val.comp hm)

theorem continuous_finiteFullDyadicTailMaxOperator (lam : ℝ) (j : ℤ) (N : ℕ)
    (f : L0Infinity) : Continuous (finiteFullDyadicTailMaxOperator lam j N f) := by
  have hm : Continuous (finiteFullDyadicTailMaxNNNorm lam j N f) :=
    Continuous.finset_sup_apply fun n hn ↦ (continuous_finiteFullDyadicTail lam j n f).nnnorm
  exact Complex.continuous_ofReal.comp (continuous_subtype_val.comp hm)

theorem locallyIntegrable_finitePositiveDyadicTailMaxOperator (lam : ℝ) (j : ℤ) (N : ℕ)
    (f : L0Infinity) : LocallyIntegrable (finitePositiveDyadicTailMaxOperator lam j N f) volume :=
  (continuous_finitePositiveDyadicTailMaxOperator lam j N f).locallyIntegrable

theorem locallyIntegrable_finiteFullDyadicTailMaxOperator (lam : ℝ) (j : ℤ) (N : ℕ)
    (f : L0Infinity) : LocallyIntegrable (finiteFullDyadicTailMaxOperator lam j N f) volume :=
  (continuous_finiteFullDyadicTailMaxOperator lam j N f).locallyIntegrable

@[simp] theorem absoluteValue_finitePositiveDyadicTailMaxOperator (lam : ℝ) (j : ℤ) (N : ℕ) :
    absoluteValueOperator (finitePositiveDyadicTailMaxOperator lam j N) =
      finitePositiveDyadicTailMaxOperator lam j N := by
  funext f x
  simp [absoluteValueOperator, finitePositiveDyadicTailMaxOperator]

theorem norm_fullDyadicTailMax_le_positive_add_reflected
    (lam : ℝ) (j : ℤ) (N : ℕ) (f : L0Infinity) (x : ℝ) :
    ‖finiteFullDyadicTailMaxOperator lam j N f x‖ ≤
      ‖finitePositiveDyadicTailMaxOperator lam j N f x‖ +
        ‖reflectedOperator (finitePositiveDyadicTailMaxOperator lam j N) f x‖ := by
  simpa only [finiteFullDyadicTailMaxOperator, finitePositiveDyadicTailMaxOperator,
    reflectedOperator, L0Infinity.reflect, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
    ← NNReal.coe_add, NNReal.coe_le_coe] using
    finiteFullDyadicTailMaxNNNorm_le_positive_add_reflect lam j N (memLp_two_L0Infinity f) x

/-- The finite full dyadic maximum inherits the positive-half sparse bound
with exactly a factor two, uniformly in all scale and modulation parameters. -/
theorem hasSparseOnePBound_fullDyadicTailMax
    (lam : ℝ) (j : ℤ) (N : ℕ) {C p : ℝ} (hC : 0 ≤ C)
    (hpositive : HasSparseOnePBound C p (finitePositiveDyadicTailMaxOperator lam j N)) :
    HasSparseOnePBound (2 * C) p (finiteFullDyadicTailMaxOperator lam j N) := by
  apply hasSparseOnePBound_of_norm_le_add_reflected_of_locallyIntegrable hC
    (T := finitePositiveDyadicTailMaxOperator lam j N)
  · simpa only [absoluteValue_finitePositiveDyadicTailMaxOperator] using hpositive
  · exact locallyIntegrable_finitePositiveDyadicTailMaxOperator lam j N
  · exact norm_fullDyadicTailMax_le_positive_add_reflected lam j N

theorem sparseOnePNorm_le_of_bound {C p : ℝ} {T : TestOperator}
    (hC : 0 ≤ C) (hT : HasSparseOnePBound C p T) : sparseOnePNorm p T ≤ C := by
  exact csInf_le (show BddBelow {D : ℝ | 0 ≤ D ∧ HasSparseOnePBound D p T} from
    ⟨0, fun D hD ↦ hD.1⟩) ⟨hC, hT⟩

theorem isSparseOnePBounded_fullDyadicTailMax
    (lam : ℝ) (j : ℤ) (N : ℕ) {p : ℝ}
    (hpositive : IsSparseOnePBounded p (finitePositiveDyadicTailMaxOperator lam j N)) :
    IsSparseOnePBounded p (finiteFullDyadicTailMaxOperator lam j N) := by
  obtain ⟨C, hC, hb⟩ := hpositive
  exact ⟨2 * C, by positivity, hasSparseOnePBound_fullDyadicTailMax lam j N hC hb⟩

/-- The norm-level transfer has the same exact factor two. The boundedness
premise prevents treating the infimum of an empty set as a sparse bound. -/
theorem sparseOnePNorm_fullDyadicTailMax_le_two_mul_positive
    (lam : ℝ) (j : ℤ) (N : ℕ) {p : ℝ}
    (hpositive : IsSparseOnePBounded p (finitePositiveDyadicTailMaxOperator lam j N)) :
    sparseOnePNorm p (finiteFullDyadicTailMaxOperator lam j N) ≤
      2 * sparseOnePNorm p (finitePositiveDyadicTailMaxOperator lam j N) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hn := sparseOnePNorm_nonneg hpositive
  have hC : 0 ≤ sparseOnePNorm p (finitePositiveDyadicTailMaxOperator lam j N) + ε / 2 := by
    positivity
  have hp := hasSparseOnePBound_of_sparseOnePNorm_lt hpositive
    (show sparseOnePNorm p (finitePositiveDyadicTailMaxOperator lam j N) <
      sparseOnePNorm p (finitePositiveDyadicTailMaxOperator lam j N) + ε / 2 by linarith)
  have hb := sparseOnePNorm_le_of_bound (by positivity)
    (hasSparseOnePBound_fullDyadicTailMax lam j N hC hp)
  linarith

theorem uniform_hasSparseOnePBound_fullDyadicTailMax {C p : ℝ} (hC : 0 ≤ C)
    (hpositive : ∀ (lam : ℝ) (j : ℤ) (N : ℕ),
      HasSparseOnePBound C p (finitePositiveDyadicTailMaxOperator lam j N)) :
    ∀ (lam : ℝ) (j : ℤ) (N : ℕ),
      HasSparseOnePBound (2 * C) p (finiteFullDyadicTailMaxOperator lam j N) :=
  fun lam j N ↦ hasSparseOnePBound_fullDyadicTailMax lam j N hC (hpositive lam j N)


noncomputable def finitePositiveDyadicSuffixMaxOperator (lam : ℝ) (j : ℤ) (N : ℕ) :
    TestOperator := fun f x ↦ ((finitePositiveDyadicSuffixMaxNNNorm lam j N f x : ℝ) : ℂ)

noncomputable def finiteFullDyadicSuffixMaxOperator (lam : ℝ) (j : ℤ) (N : ℕ) :
    TestOperator := fun f x ↦ ((finiteFullDyadicSuffixMaxNNNorm lam j N f x : ℝ) : ℂ)

theorem continuous_finitePositiveDyadicSuffixMaxOperator (lam : ℝ) (j : ℤ) (N : ℕ)
    (f : L0Infinity) : Continuous (finitePositiveDyadicSuffixMaxOperator lam j N f) := by
  have hm : Continuous (finitePositiveDyadicSuffixMaxNNNorm lam j N f) :=
    Continuous.finset_sup_apply fun m hm ↦
      (continuous_finitePositiveDyadicTail lam (j + m) (N - m) f).nnnorm
  exact Complex.continuous_ofReal.comp (continuous_subtype_val.comp hm)

theorem continuous_finiteFullDyadicSuffixMaxOperator (lam : ℝ) (j : ℤ) (N : ℕ)
    (f : L0Infinity) : Continuous (finiteFullDyadicSuffixMaxOperator lam j N f) := by
  have hm : Continuous (finiteFullDyadicSuffixMaxNNNorm lam j N f) :=
    Continuous.finset_sup_apply fun m hm ↦
      (continuous_finiteFullDyadicTail lam (j + m) (N - m) f).nnnorm
  exact Complex.continuous_ofReal.comp (continuous_subtype_val.comp hm)

theorem locallyIntegrable_finitePositiveDyadicSuffixMaxOperator (lam : ℝ) (j : ℤ) (N : ℕ)
    (f : L0Infinity) : LocallyIntegrable (finitePositiveDyadicSuffixMaxOperator lam j N f) volume :=
  (continuous_finitePositiveDyadicSuffixMaxOperator lam j N f).locallyIntegrable

theorem locallyIntegrable_finiteFullDyadicSuffixMaxOperator (lam : ℝ) (j : ℤ) (N : ℕ)
    (f : L0Infinity) : LocallyIntegrable (finiteFullDyadicSuffixMaxOperator lam j N f) volume :=
  (continuous_finiteFullDyadicSuffixMaxOperator lam j N f).locallyIntegrable

@[simp] theorem absoluteValue_finitePositiveDyadicSuffixMaxOperator (lam : ℝ) (j : ℤ) (N : ℕ) :
    absoluteValueOperator (finitePositiveDyadicSuffixMaxOperator lam j N) =
      finitePositiveDyadicSuffixMaxOperator lam j N := by
  funext f x
  simp [absoluteValueOperator, finitePositiveDyadicSuffixMaxOperator]

theorem norm_fullDyadicSuffixMax_le_positive_add_reflected
    (lam : ℝ) (j : ℤ) (N : ℕ) (f : L0Infinity) (x : ℝ) :
    ‖finiteFullDyadicSuffixMaxOperator lam j N f x‖ ≤
      ‖finitePositiveDyadicSuffixMaxOperator lam j N f x‖ +
        ‖reflectedOperator (finitePositiveDyadicSuffixMaxOperator lam j N) f x‖ := by
  simpa only [finiteFullDyadicSuffixMaxOperator, finitePositiveDyadicSuffixMaxOperator,
    reflectedOperator, L0Infinity.reflect, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (NNReal.coe_nonneg _), ← NNReal.coe_add, NNReal.coe_le_coe] using
    finiteFullDyadicSuffixMaxNNNorm_le_positive_add_reflect lam j N (memLp_two_L0Infinity f) x

/-- KL's moving-lower-cutoff maximum, with the exact reflection factor two. -/
theorem hasSparseOnePBound_fullDyadicSuffixMax
    (lam : ℝ) (j : ℤ) (N : ℕ) {C p : ℝ} (hC : 0 ≤ C)
    (hpositive : HasSparseOnePBound C p (finitePositiveDyadicSuffixMaxOperator lam j N)) :
    HasSparseOnePBound (2 * C) p (finiteFullDyadicSuffixMaxOperator lam j N) := by
  apply hasSparseOnePBound_of_norm_le_add_reflected_of_locallyIntegrable hC
    (T := finitePositiveDyadicSuffixMaxOperator lam j N)
  · simpa only [absoluteValue_finitePositiveDyadicSuffixMaxOperator] using hpositive
  · exact locallyIntegrable_finitePositiveDyadicSuffixMaxOperator lam j N
  · exact norm_fullDyadicSuffixMax_le_positive_add_reflected lam j N


end QuadraticCarleson.KrauseLaceyFullDyadicSparseTransfer
