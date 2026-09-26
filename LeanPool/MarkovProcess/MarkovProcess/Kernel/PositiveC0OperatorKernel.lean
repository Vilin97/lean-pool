/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Kernel.Basic
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.MeasurableRadonFamily
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.PositiveC0OperatorMass
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction


/-!
# Kernels represented by positive operators on `C₀`

A positive contraction on real continuous functions vanishing at infinity determines a
sub-Markov kernel.  Its values are the pointwise Riesz measures of the evaluation functionals.
-/

@[expose] public section

open CompactlySupported Filter MeasureTheory ProbabilityTheory Set
open scoped ZeroAtInfty

namespace MarkovProcess.PositiveC0OperatorKernel

variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]

variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ))
  (hT : PositiveC0OperatorMeasure.IsPositive T)

omit [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] in
private lemma exists_compactlySupported_norm_sub_le (f : C₀(α, ℝ)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : C_c(α, ℝ),
      ‖PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap g - f‖ ≤ ε := by
  have heventually : ∀ᶠ x in cocompact α, dist (f x) 0 < ε :=
    (Metric.tendsto_nhds.mp (zero_at_infty f) ε hε)
  obtain ⟨K, hK, houtside⟩ := mem_cocompact.mp heventually
  obtain ⟨cutoff, hcutoff_one, hcutoff_compact, _hcutoff_support, hcutoff⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  let g : C_c(α, ℝ) :=
    ⟨cutoff * f.toContinuousMap, hasCompactSupport_def.mpr hcutoff_compact |>.mul_right⟩
  refine ⟨g, ?_⟩
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le hε.le).2 fun x ↦ ?_
  rw [Real.norm_eq_abs]
  by_cases hx : x ∈ K
  · change |cutoff x * f x - f x| ≤ ε
    rw [hcutoff_one hx, Pi.one_apply, one_mul, sub_self, abs_zero]
    exact hε.le
  · change |cutoff x * f x - f x| ≤ ε
    have hcutoff_abs : |cutoff x - 1| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith only [(hcutoff x).1], by linarith only [(hcutoff x).2]⟩
    calc
      |cutoff x * f x - f x| = |cutoff x - 1| * |f x| := by
        rw [← abs_mul, sub_mul, one_mul]
      |cutoff x - 1| * |f x| ≤ 1 * |f x| :=
        mul_le_mul_of_nonneg_right hcutoff_abs (abs_nonneg _)
      _ ≤ ε := by
        rw [one_mul, ← Real.norm_eq_abs, ← dist_zero_right]
        exact (houtside (mem_compl hx)).le

/-- The kernel whose value at `x` is the Riesz measure representing evaluation of `T` at `x`. -/
noncomputable def kernel (hT_norm : ‖T‖ ≤ 1) : Kernel α α := by
  letI : ∀ x, IsFiniteMeasure (PositiveC0OperatorMeasure.measure T hT x) :=
    fun x ↦ PositiveC0OperatorMeasure.isFiniteMeasure_measure T hT hT_norm x
  exact
    { toFun := PositiveC0OperatorMeasure.measure T hT
      measurable' :=
        measurable_measure_of_measurable_integral_compactlySupported
          (PositiveC0OperatorMeasure.measure T hT) fun f ↦ by
            rw [show (fun x ↦ ∫ y, f y ∂PositiveC0OperatorMeasure.measure T hT x) =
              fun x ↦ T (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f) x by
                funext x
                exact PositiveC0OperatorMeasure.integral_measure T hT x f]
            exact
              (T (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f)).continuous
                |>.measurable }

/-- The constructed kernel has the pointwise Riesz measure as its value. -/
@[simp]
theorem kernel_apply (hT_norm : ‖T‖ ≤ 1) (x : α) :
    kernel T hT hT_norm x = PositiveC0OperatorMeasure.measure T hT x :=
  rfl

/-- The kernel represented by a positive contraction is sub-Markov. -/
theorem isSubMarkovKernel_kernel (hT_norm : ‖T‖ ≤ 1) :
    IsSubMarkovKernel (kernel T hT hT_norm) := by
  intro x
  rw [kernel_apply]
  exact PositiveC0OperatorMeasure.measure_univ_le_one T hT hT_norm x

/-- The kernel represents `T` on compactly supported continuous functions. -/
theorem integral_kernel_compactlySupported (hT_norm : ‖T‖ ≤ 1) (x : α)
    (f : C_c(α, ℝ)) :
    ∫ y, f y ∂kernel T hT hT_norm x =
      T (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f) x := by
  rw [kernel_apply]
  exact PositiveC0OperatorMeasure.integral_measure T hT x f

/-- Every real continuous function vanishing at infinity is integrable against a kernel value. -/
theorem integrable_kernel (hT_norm : ‖T‖ ≤ 1) (x : α) (f : C₀(α, ℝ)) :
    Integrable f (kernel T hT hT_norm x) := by
  let : IsFiniteMeasure (kernel T hT hT_norm x) :=
    PositiveC0OperatorMeasure.isFiniteMeasure_measure T hT hT_norm x
  exact f.toBCF.integrable _

/-- The kernel represents `T` on every real continuous function vanishing at infinity. -/
theorem integral_kernel (hT_norm : ‖T‖ ≤ 1) (x : α) (f : C₀(α, ℝ)) :
    ∫ y, f y ∂kernel T hT hT_norm x = T f x := by
  let : IsFiniteMeasure (kernel T hT hT_norm x) :=
    PositiveC0OperatorMeasure.isFiniteMeasure_measure T hT hT_norm x
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨g, hg⟩ := exists_compactlySupported_norm_sub_le f (half_pos hε)
  let g₀ : C₀(α, ℝ) := PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap g
  have hmass : (kernel T hT hT_norm x).real Set.univ ≤ 1 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mpr
      (isSubMarkovKernel_kernel T hT hT_norm x)
  have hf_integrable : Integrable f (kernel T hT hT_norm x) := f.toBCF.integrable _
  have hg_integrable : Integrable g₀ (kernel T hT hT_norm x) := g₀.toBCF.integrable _
  have hintegral :
      dist (∫ y, f y ∂kernel T hT hT_norm x)
        (∫ y, g₀ y ∂kernel T hT hT_norm x) ≤ ε / 2 := by
    rw [Real.dist_eq, ← integral_sub hf_integrable hg_integrable]
    calc
      ‖∫ y, (f - g₀) y ∂kernel T hT hT_norm x‖ ≤
          (kernel T hT hT_norm x).real Set.univ * ‖(f - g₀).toBCF‖ :=
        (f - g₀).toBCF.norm_integral_le_mul_norm _
      _ ≤ 1 * (ε / 2) := mul_le_mul hmass (by simpa only [norm_sub_rev] using! hg)
        (norm_nonneg _) zero_le_one
      _ = ε / 2 := one_mul _
  have hoperator : dist (T g₀ x) (T f x) ≤ ε / 2 := by
    rw [Real.dist_eq]
    change |(T g₀ - T f) x| ≤ ε / 2
    rw [← map_sub]
    calc
      |(T (g₀ - f)) x| ≤ ‖T (g₀ - f)‖ :=
        (T (g₀ - f)).toBCF.norm_coe_le_norm x
      _ ≤ ‖T‖ * ‖g₀ - f‖ := T.le_opNorm _
      _ ≤ 1 * (ε / 2) := mul_le_mul hT_norm hg (norm_nonneg _) zero_le_one
      _ = ε / 2 := one_mul _
  calc
    dist (∫ y, f y ∂kernel T hT hT_norm x) (T f x) ≤
        dist (∫ y, f y ∂kernel T hT hT_norm x)
            (∫ y, g₀ y ∂kernel T hT hT_norm x) +
          dist (∫ y, g₀ y ∂kernel T hT hT_norm x) (T f x) :=
      dist_triangle _ _ _
    _ = dist (∫ y, f y ∂kernel T hT hT_norm x)
          (∫ y, g₀ y ∂kernel T hT hT_norm x) + dist (T g₀ x) (T f x) := by
      have hg_rep := integral_kernel_compactlySupported T hT hT_norm x g
      change (∫ y, g₀ y ∂kernel T hT hT_norm x) = T g₀ x at hg_rep
      rw [hg_rep]
    _ ≤ ε / 2 + ε / 2 := add_le_add hintegral hoperator
    _ = ε := add_halves ε

end MarkovProcess.PositiveC0OperatorKernel
