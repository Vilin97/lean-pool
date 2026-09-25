/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Kernel.C0SemigroupJoint
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.PositiveC0OperatorKernel
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.KernelSemigroup
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Topology.Metrizable.Urysohn


/-!
# Kernel semigroups represented by positive contraction semigroups on `C₀`

A strongly continuous semigroup of positive contractions on real continuous functions vanishing
at infinity determines a jointly measurable sub-Markov kernel semigroup.
-/

@[expose] public section

open CompactlySupported MeasureTheory ProbabilityTheory
open scoped ENNReal ZeroAtInfty

namespace MarkovProcess.PositiveC0SemigroupKernel

open MarkovProcess.Semigroup

variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]

variable (S : StronglyContinuousContractionSemigroup C₀(α, ℝ))
  (hS : ∀ t, PositiveC0OperatorMeasure.IsPositive (S t))

/-- The pointwise Riesz kernels are jointly measurable in time and starting state. -/
theorem measurable_kernel : Measurable fun p : NNReal × α ↦
    PositiveC0OperatorKernel.kernel (S p.1) (hS p.1) (S.norm_operator_le_one p.1) p.2 := by
  let : ∀ p : NNReal × α,
      IsFiniteMeasure (PositiveC0OperatorMeasure.measure (S p.1) (hS p.1) p.2) :=
    fun p ↦ PositiveC0OperatorMeasure.isFiniteMeasure_measure
      (S p.1) (hS p.1) (S.norm_operator_le_one p.1) p.2
  have hmeasure : Measurable fun p : NNReal × α ↦
      PositiveC0OperatorMeasure.measure (S p.1) (hS p.1) p.2 :=
    measurable_measure_of_measurable_integral_compactlySupported _ fun f ↦ by
      rw [show (fun p : NNReal × α ↦
          ∫ y, f y ∂PositiveC0OperatorMeasure.measure (S p.1) (hS p.1) p.2) =
          fun p ↦ S p.1 (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f) p.2 by
        funext p
        exact PositiveC0OperatorMeasure.integral_measure (S p.1) (hS p.1) p.2 f]
      exact S.measurable_apply_apply _
  simpa only [PositiveC0OperatorKernel.kernel_apply] using hmeasure

/-- At time zero the represented kernel is the identity kernel. -/
theorem kernel_zero :
    PositiveC0OperatorKernel.kernel (S 0) (hS 0) (S.norm_operator_le_one 0) = Kernel.id := by
  apply Kernel.ext
  intro x
  rw [PositiveC0OperatorKernel.kernel_apply, Kernel.id_apply]
  let : IsFiniteMeasure (Measure.dirac x) := inferInstance
  let : (Measure.dirac x).Regular := inferInstance
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [PositiveC0OperatorMeasure.integral_measure]
  simp only [StronglyContinuousContractionSemigroup.zero_apply]
  simpa only [PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply] using
    (integral_dirac' f x f.continuous.stronglyMeasurable).symm

/-- The represented kernels satisfy the Chapman--Kolmogorov law. -/
theorem kernel_add (s t : NNReal) :
    PositiveC0OperatorKernel.kernel (S (s + t)) (hS (s + t))
        (S.norm_operator_le_one (s + t)) =
      (PositiveC0OperatorKernel.kernel (S t) (hS t) (S.norm_operator_le_one t)).comp
        (PositiveC0OperatorKernel.kernel (S s) (hS s) (S.norm_operator_le_one s)) := by
  apply Kernel.ext
  intro x
  rw [PositiveC0OperatorKernel.kernel_apply]
  let Ks := PositiveC0OperatorKernel.kernel (S s) (hS s) (S.norm_operator_le_one s)
  let Kt := PositiveC0OperatorKernel.kernel (S t) (hS t) (S.norm_operator_le_one t)
  change PositiveC0OperatorMeasure.measure (S (s + t)) (hS (s + t)) x = (Kt.comp Ks) x
  have hKs : IsSubMarkovKernel Ks :=
    PositiveC0OperatorKernel.isSubMarkovKernel_kernel _ _ _
  have hKt : IsSubMarkovKernel Kt :=
    PositiveC0OperatorKernel.isSubMarkovKernel_kernel _ _ _
  let : IsFiniteKernel (Kt.comp Ks) := (hKt.comp hKs).isFiniteKernel
  let : IsFiniteMeasure ((Kt.comp Ks) x) := inferInstance
  let : ((Kt.comp Ks) x).Regular := inferInstance
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let f₀ : C₀(α, ℝ) := PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  have hf_comp : Integrable f₀ ((Kt.comp Ks) x) := f₀.toBCF.integrable _
  rw [PositiveC0OperatorMeasure.integral_measure]
  rw [StronglyContinuousContractionSemigroup.add_apply]
  change S s (S t f₀) x = ∫ z, f₀ z ∂(Kt.comp Ks) x
  calc
    S s (S t f₀) x = ∫ y, S t f₀ y ∂Ks x := by
      exact (PositiveC0OperatorKernel.integral_kernel
        (S s) (hS s) (S.norm_operator_le_one s) x (S t f₀)).symm
    _ = ∫ y, ∫ z, f₀ z ∂Kt y ∂Ks x := by
      congr 1
      funext y
      exact (PositiveC0OperatorKernel.integral_kernel_compactlySupported
        (S t) (hS t) (S.norm_operator_le_one t) y f).symm
    _ = ∫ z, f₀ z ∂(Kt.comp Ks) x := (Kernel.integral_comp hf_comp).symm

/-- The sub-Markov kernel semigroup represented by a positive contraction semigroup on `C₀`. -/
noncomputable def kernelSemigroup : SubMarkovKernelSemigroup α where
  kernel t := PositiveC0OperatorKernel.kernel (S t) (hS t) (S.norm_operator_le_one t)
  measurable_kernel := measurable_kernel S hS
  kernel_zero := kernel_zero S hS
  kernel_add := kernel_add S hS
  isSubMarkovKernel t :=
    PositiveC0OperatorKernel.isSubMarkovKernel_kernel
      (S t) (hS t) (S.norm_operator_le_one t)

/-- Evaluation of the represented kernel semigroup is the fixed-operator Riesz kernel. -/
@[simp]
theorem kernelSemigroup_apply (t : NNReal) :
    kernelSemigroup S hS t =
      PositiveC0OperatorKernel.kernel (S t) (hS t) (S.norm_operator_le_one t) :=
  rfl

end MarkovProcess.PositiveC0SemigroupKernel
