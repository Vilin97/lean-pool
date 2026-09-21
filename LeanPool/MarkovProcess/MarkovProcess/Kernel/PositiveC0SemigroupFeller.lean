/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Feller.Semigroup
import LeanPool.MarkovProcess.MarkovProcess.Kernel.PositiveC0SemigroupKernel

/-!
# Feller property of kernels represented by positive `C₀` semigroups

The kernel semigroup represented by a strongly continuous semigroup of positive contractions
recovers the original operators on `C₀` and therefore satisfies the existing Feller interface.
This file makes no conservativity, stochastic-process, or Hunt-process claim.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ZeroAtInfty

namespace MarkovProcess.PositiveC0SemigroupFeller

open MarkovProcess.Semigroup

variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]

variable (S : StronglyContinuousContractionSemigroup C₀(α, ℝ))
  (hS : ∀ t, PositiveC0OperatorMeasure.IsPositive (S t))

/-- The represented kernel semigroup maps `C₀(α, ℝ)` into itself. -/
theorem mapsC0_kernelSemigroup :
    (PositiveC0SemigroupKernel.kernelSemigroup S hS).MapsC0 := by
  intro t f
  have heq : kernelIntegral (PositiveC0SemigroupKernel.kernelSemigroup S hS t) f = S t f := by
    funext x
    change ∫ y, f y ∂PositiveC0SemigroupKernel.kernelSemigroup S hS t x = S t f x
    rw [PositiveC0SemigroupKernel.kernelSemigroup_apply]
    exact PositiveC0OperatorKernel.integral_kernel
      (S t) (hS t) (S.norm_operator_le_one t) x f
  rw [heq]
  exact ⟨(S t f).continuous, zero_at_infty (S t f)⟩

/-- The represented `C₀`-valued kernel integral is exactly the original semigroup action. -/
@[simp]
theorem kernelSemigroup_c0KernelIntegral
    (hC0 : (PositiveC0SemigroupKernel.kernelSemigroup S hS).MapsC0)
    (t : NNReal) (f : C₀(α, ℝ)) :
    (PositiveC0SemigroupKernel.kernelSemigroup S hS).c0KernelIntegral hC0 t f = S t f := by
  apply ZeroAtInftyContinuousMap.ext
  intro x
  change ∫ y, f y ∂PositiveC0SemigroupKernel.kernelSemigroup S hS t x = S t f x
  rw [PositiveC0SemigroupKernel.kernelSemigroup_apply]
  exact PositiveC0OperatorKernel.integral_kernel
    (S t) (hS t) (S.norm_operator_le_one t) x f

/-- The represented continuous linear `C₀` operator is the original semigroup operator. -/
@[simp]
theorem kernelSemigroup_c0Operator
    (hC0 : (PositiveC0SemigroupKernel.kernelSemigroup S hS).MapsC0)
    (t : NNReal) :
    (PositiveC0SemigroupKernel.kernelSemigroup S hS).c0Operator hC0 t = S t := by
  apply ContinuousLinearMap.ext
  intro f
  exact kernelSemigroup_c0KernelIntegral S hS hC0 t f

/-- The represented `C₀` kernel operators have continuous time orbits. -/
theorem hasContinuousC0Orbits_kernelSemigroup :
    (PositiveC0SemigroupKernel.kernelSemigroup S hS).HasContinuousC0Orbits
      (mapsC0_kernelSemigroup S hS) := by
  intro f
  have heq : (fun t : NNReal ↦
      (PositiveC0SemigroupKernel.kernelSemigroup S hS).c0Operator
        (mapsC0_kernelSemigroup S hS) t f) = fun t ↦ S t f := by
    funext t
    rw [kernelSemigroup_c0Operator]
  rw [heq]
  exact S.continuous f

/-- The represented sub-Markov kernel semigroup satisfies the Feller interface. -/
theorem isFellerKernelSemigroup_kernelSemigroup :
    (PositiveC0SemigroupKernel.kernelSemigroup S hS).IsFellerKernelSemigroup :=
  ⟨mapsC0_kernelSemigroup S hS, hasContinuousC0Orbits_kernelSemigroup S hS⟩

/-- Packaging the represented Feller kernel semigroup recovers the original `C₀` semigroup. -/
theorem c0Semigroup_kernelSemigroup :
    (isFellerKernelSemigroup_kernelSemigroup S hS).c0Semigroup = S := by
  apply StronglyContinuousContractionSemigroup.ext
  intro t
  rw [SubMarkovKernelSemigroup.IsFellerKernelSemigroup.c0Semigroup]
  exact kernelSemigroup_c0Operator S hS _ t

end MarkovProcess.PositiveC0SemigroupFeller
