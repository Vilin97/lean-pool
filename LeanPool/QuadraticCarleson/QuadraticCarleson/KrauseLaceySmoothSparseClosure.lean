/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyFiniteRadiusSmoothSparse
public import LeanPool.QuadraticCarleson.QuadraticCarleson.HardyLittlewoodBoundaryControl

/-!
# Deterministic closure of the positive-suffix sparse input

This file only packages the positive dyadic suffix input into the smooth
finite-radius hypothesis used by the endpoint assembly. The factor two is
exactly the positive/reflected suffix comparison.
-/

@[expose] public section

open MeasureTheory

namespace QuadraticCarleson

open QuadraticHilbertMaximalMeasurable
open KrauseLaceyFiniteRadiusSmoothSparse
open KrauseLaceyFullDyadicSparseTransfer
open KrauseLaceySharpSmoothAdapter
open OscillatoryReduction
open HardyLittlewoodBoundaryControl


noncomputable
section

/-- Uniform positive-suffix sparse input, with the finite-radius local
integrability clause made explicit. -/
def HasUniformPositiveSuffixSmoothSparseBound (A : ℝ) : Prop :=
  0 ≤ A ∧ ∀ (lam : ℝ), lam ≠ 0 → ∀ p : ℝ, 1 < p → p < 2 →
      ∀ (j : ℤ) (N : ℕ),
        HasSparseOnePBound (A * holderConjugate p) p
          (finitePositiveDyadicSuffixMaxOperator lam j N) ∧
        sparseOnePNorm p
          (finitePositiveDyadicSuffixMaxOperator lam j N) ≤ A * holderConjugate p

-- The finite supremum's measurable-and-integrable packaging is elaboration intensive.
private theorem locallyIntegrable_finiteRadiusSmoothHighPassMaxTestOperator
    (lam : ℝ) (s : Finset densePositiveRadii) (f : L0Infinity) :
    LocallyIntegrable (finiteRadiusSmoothHighPassMaxTestOperator lam s f) volume := by
  classical
  have hmeas (ε : densePositiveRadii) : Measurable
      (fun x ↦ smoothQuadraticHighPass lam
        (dyadicCeilRadius ε.1.1 ε.1.2) f x) := by
    unfold smoothQuadraticHighPass
    have hk := (measurable_smoothQuadraticHighPassKernel lam
      (dyadicCeilRadius ε.1.1 ε.1.2)).comp
        (measurable_fst.sub measurable_snd)
    have hj : StronglyMeasurable (fun z : ℝ × ℝ ↦
        smoothQuadraticHighPassKernel lam (dyadicCeilRadius ε.1.1 ε.1.2)
          (z.1 - z.2) * f z.2) :=
      (hk.mul (f.measurable_toFun.comp measurable_snd)).stronglyMeasurable
    exact hj.integral_prod_right'.measurable
  have hmax : Measurable (fun x ↦
      (finiteRadiusSmoothHighPassMaxNNNorm lam s f x : ℝ)) := by
    unfold finiteRadiusSmoothHighPassMaxNNNorm
    induction s using Finset.induction_on with
    | empty => simp
    | @insert ε s hε ih =>
        simp only [Finset.sup_insert, NNReal.coe_max, coe_nnnorm]
        exact (hmeas ε).norm.max ih
  rw [locallyIntegrable_iff]
  intro K hK
  change IntegrableOn (fun x ↦
    ((finiteRadiusSmoothHighPassMaxNNNorm lam s f x : ℝ) : ℂ)) K volume
  let C : ℝ := ∑ ε ∈ s, (2 / dyadicCeilRadius ε.1.1 ε.1.2) * ∫ y, ‖f y‖
  refine IntegrableOn.of_bound hK.measure_lt_top
    ((Complex.measurable_ofReal.comp hmax).aestronglyMeasurable.restrict) C ?_
  filter_upwards with x
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (NNReal.coe_nonneg _)]
  unfold finiteRadiusSmoothHighPassMaxNNNorm
  change (↑(s.sup fun ε ↦ ‖smoothQuadraticHighPass lam
    (dyadicCeilRadius ε.1.1 ε.1.2) f x‖₊) : ℝ) ≤ _
  have hsup :
      (s.sup fun ε ↦ ‖smoothQuadraticHighPass lam
        (dyadicCeilRadius ε.1.1 ε.1.2) f x‖₊) ≤
        ∑ ε ∈ s, ‖smoothQuadraticHighPass lam
          (dyadicCeilRadius ε.1.1 ε.1.2) f x‖₊ := by
    apply Finset.sup_le
    intro ε hεs
    exact Finset.single_le_sum
      (fun δ _ ↦ (bot_le : (0 : NNReal) ≤
        ‖smoothQuadraticHighPass lam
          (dyadicCeilRadius δ.1.1 δ.1.2) f x‖₊)) hεs
  calc
    _ ≤ ∑ ε ∈ s, ‖smoothQuadraticHighPass lam
        (dyadicCeilRadius ε.1.1 ε.1.2) f x‖ := by
      have hcoe :
          (↑(s.sup fun ε ↦ ‖smoothQuadraticHighPass lam
            (dyadicCeilRadius ε.1.1 ε.1.2) f x‖₊) : ℝ) ≤
            ↑(∑ ε ∈ s, ‖smoothQuadraticHighPass lam
              (dyadicCeilRadius ε.1.1 ε.1.2) f x‖₊) :=
        NNReal.coe_le_coe.mpr hsup
      rw [NNReal.coe_sum] at hcoe
      simpa only [coe_nnnorm] using hcoe
    _ ≤ C := by
      apply Finset.sum_le_sum
      intro ε hε
      have hi : Integrable (fun y ↦ smoothQuadraticHighPassKernel lam
          (dyadicCeilRadius ε.1.1 ε.1.2) (x - y) * f y) := by
        exact integrable_kernel_mul_l0 f x
          (measurable_smoothQuadraticHighPassKernel _ _)
          (fun t ↦ smoothQuadraticHighPassKernel_norm_le lam
            (dyadicCeilRadius_pos _ _))
      rw [smoothQuadraticHighPass]
      calc
        ‖∫ y, smoothQuadraticHighPassKernel lam
            (dyadicCeilRadius ε.1.1 ε.1.2) (x - y) * f y‖ ≤
            ∫ y, ‖smoothQuadraticHighPassKernel lam
              (dyadicCeilRadius ε.1.1 ε.1.2) (x - y) * f y‖ :=
          norm_integral_le_integral_norm _
        _ ≤ (2 / dyadicCeilRadius ε.1.1 ε.1.2) * ∫ y, ‖f y‖ := by
          calc
            _ ≤ ∫ y, (2 / dyadicCeilRadius ε.1.1 ε.1.2) * ‖f y‖ := by
              apply integral_mono hi.norm (f.integrable.norm.const_mul _)
              intro y
              change ‖smoothQuadraticHighPassKernel lam
                (dyadicCeilRadius ε.1.1 ε.1.2) (x - y) * f y‖ ≤ _
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_right
                (smoothQuadraticHighPassKernel_norm_le lam (dyadicCeilRadius_pos _ _))
                (norm_nonneg _)
            _ = _ := integral_const_mul _ _

theorem hasUniformFiniteRadiusSmoothSparseBound_of_positiveSuffix
    {A : ℝ} (hA : HasUniformPositiveSuffixSmoothSparseBound A) :
    HardyLittlewoodBoundaryControl.HasUniformFiniteRadiusSmoothSparseBound (2 * A) := by
  refine ⟨mul_nonneg (by norm_num) hA.1, ?_⟩
  intro lam hlam s
  refine ⟨fun f ↦ locallyIntegrable_finiteRadiusSmoothHighPassMaxTestOperator lam s f, ?_⟩
  intro p hp hp2
  have hpos : 0 ≤ A * holderConjugate p :=
    mul_nonneg hA.1 (holderConjugate_spec hp).symm.pos.le
  have hsuffix : ∀ (j : ℤ) (N : ℕ),
      HasSparseOnePBound (A * holderConjugate p) p
        (finitePositiveDyadicSuffixMaxOperator lam j N) := by
    intro j N
    exact hA.2 lam hlam p hp hp2 j N |>.1
  have hbound : ∀ (j : ℤ) (N : ℕ),
      sparseOnePNorm p (finitePositiveDyadicSuffixMaxOperator lam j N) ≤
        A * holderConjugate p := by
    intro j N
    exact hA.2 lam hlam p hp hp2 j N |>.2
  have hfinite :=
    hasSparseOnePBound_finiteRadiusSmoothHighPassMax_of_uniform_positive_finiteSuffixMax
      lam s hpos hsuffix
  have habs : absoluteValueOperator
      (finiteRadiusSmoothHighPassMaxTestOperator lam s) =
      finiteRadiusSmoothHighPassMaxTestOperator lam s := by
    funext f x
    simp [absoluteValueOperator, finiteRadiusSmoothHighPassMaxTestOperator]
  have hfiniteAbs : HasSparseOnePBound (2 * (A * holderConjugate p)) p
      (absoluteValueOperator (finiteRadiusSmoothHighPassMaxTestOperator lam s)) := by
    simpa only [habs] using hfinite
  have hnorm : sparseOnePNorm p
      (absoluteValueOperator (finiteRadiusSmoothHighPassMaxTestOperator lam s)) ≤
      2 * (A * holderConjugate p) := by
    exact sparseOnePNorm_le_of_bound (mul_nonneg (by norm_num) hpos) hfiniteAbs
  refine ⟨⟨2 * (A * holderConjugate p), mul_nonneg (by norm_num) hpos, hfiniteAbs⟩, ?_⟩
  calc
    _ ≤ 2 * (A * holderConjugate p) := hnorm
    _ = (2 * A) * holderConjugate p := by ring


end
end QuadraticCarleson
