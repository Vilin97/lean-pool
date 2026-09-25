/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.DenseTime.PrefixKernel
public import LeanPool.MarkovProcess.MarkovProcess.Parameterized.FiniteTimeProjectiveFamily


/-!
# Parameterized kernels on finite prefixes of a countable time enumeration

This file constructs jointly measurable kernels on the first `n` points of an arbitrary
enumeration. Coordinates remain in enumeration order; the enumeration need not be monotone in
physical time. Fiberwise conservativity is used only for Markovness and prefix consistency.
-/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

section

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

/-- The jointly measurable kernel on the first `n` enumerated physical times. -/
def parameterizedDenseTimePrefixKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) : Kernel (Theta × alpha) (Fin n → alpha) :=
  Kernel.mapOfMeasurable
    (P.parameterizedFiniteSetKernel
      (SubMarkovKernelSemigroup.denseTimePhysicalPrefix e ι n))
    (SubMarkovKernelSemigroup.denseTimePrefixReindex e ι n)
    (SubMarkovKernelSemigroup.measurable_denseTimePrefixReindex e ι n)

/-- The parameterized prefix kernel agrees with the ordinary kernel map. -/
theorem parameterizedDenseTimePrefixKernel_eq_map
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) :
    P.parameterizedDenseTimePrefixKernel e ι n =
      (P.parameterizedFiniteSetKernel
        (SubMarkovKernelSemigroup.denseTimePhysicalPrefix e ι n)).map
          (SubMarkovKernelSemigroup.denseTimePrefixReindex e ι n) :=
  Kernel.mapOfMeasurable_eq_map _
    (SubMarkovKernelSemigroup.measurable_denseTimePrefixReindex e ι n)

/-- At a fixed parameter and start, the prefix kernel is the ordinary prefix kernel. -/
theorem parameterizedDenseTimePrefixKernel_apply
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (e : ℕ ≃ D)
    (ι : D ↪ NNReal) (n : ℕ) (theta : Theta) (x : alpha) :
    P.parameterizedDenseTimePrefixKernel e ι n (theta, x) =
      (P.toSubMarkovKernelSemigroup theta).denseTimePrefixKernel e ι n x := by
  rw [parameterizedDenseTimePrefixKernel_eq_map,
    Kernel.map_apply _
      (SubMarkovKernelSemigroup.measurable_denseTimePrefixReindex e ι n),
    parameterizedFiniteSetKernel_apply,
    SubMarkovKernelSemigroup.denseTimePrefixKernel_eq_map,
    Kernel.map_apply _
      (SubMarkovKernelSemigroup.measurable_denseTimePrefixReindex e ι n)]

/-- Fiberwise conservativity makes each parameterized prefix kernel Markov. -/
theorem isMarkovKernel_parameterizedDenseTimePrefixKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (P.parameterizedDenseTimePrefixKernel e ι n) := by
  rw [parameterizedDenseTimePrefixKernel_eq_map]
  let : IsMarkovKernel
      (P.parameterizedFiniteSetKernel
        (SubMarkovKernelSemigroup.denseTimePhysicalPrefix e ι n)) :=
    P.isMarkovKernel_parameterizedFiniteSetKernel hP _
  exact Kernel.IsMarkovKernel.map _
    (SubMarkovKernelSemigroup.measurable_denseTimePrefixReindex e ι n)

/-- Parameterized prefix kernels restrict exactly to every earlier enumeration prefix. -/
theorem parameterizedDenseTimePrefixKernel_map_restrictPath
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) {m n : ℕ} (h : m ≤ n) :
    P.parameterizedDenseTimePrefixKernel e ι m =
      (P.parameterizedDenseTimePrefixKernel e ι n).map
        (FiniteOrderedTimes.restrictPath (Fin.castLEOrderEmb h)) := by
  apply Kernel.ext
  intro q
  obtain ⟨theta, x⟩ := q
  rw [Kernel.map_apply _
      (FiniteOrderedTimes.measurable_restrictPath (Fin.castLEOrderEmb h)),
    parameterizedDenseTimePrefixKernel_apply,
    parameterizedDenseTimePrefixKernel_apply]
  have hrestrict := congrArg (fun K : Kernel alpha (Fin m → alpha) ↦ K x)
    ((hP theta).denseTimePrefixKernel_map_restrictPath
      (P.toSubMarkovKernelSemigroup theta) e ι h)
  change (P.toSubMarkovKernelSemigroup theta).denseTimePrefixKernel e ι m x =
    ((P.toSubMarkovKernelSemigroup theta).denseTimePrefixKernel e ι n).map
      (FiniteOrderedTimes.restrictPath (Fin.castLEOrderEmb h)) x at hrestrict
  rw [Kernel.map_apply _
    (FiniteOrderedTimes.measurable_restrictPath (Fin.castLEOrderEmb h))] at hrestrict
  exact hrestrict

end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess

end PortComputability
