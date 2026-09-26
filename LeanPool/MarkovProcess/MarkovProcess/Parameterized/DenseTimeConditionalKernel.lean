/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Parameterized.DenseTimePrefixKernel
public import LeanPool.MarkovProcess.MarkovProcess.Time.DenseTimeHistory
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel


/-!
# Conditional kernels for parameterized finite dense-time prefixes

This file disintegrates the jointly parameterized law of a finite dense-time prefix and its next
observation. The resulting conditional kernel is one jointly measurable version. No comparison
with separately chosen fixed-parameter conditional versions is asserted.
-/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

section

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

/-- The jointly parameterized law of an `n`-prefix and its next enumerated observation. -/
def parameterizedNextObservationJoint
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (e : ℕ ≃ D)
    (iota : D ↪ NNReal) (n : ℕ) :
    Kernel (Theta × alpha) ((Fin n → alpha) × alpha) :=
  Kernel.mapOfMeasurable (P.parameterizedDenseTimePrefixKernel e iota (n + 1))
    (DenseTimeHistory.splitLast n) (DenseTimeHistory.splitLast n).measurable

variable [StandardBorelSpace alpha] [Nonempty alpha]

omit [StandardBorelSpace alpha] [Nonempty alpha] in
/-- The first marginal of the joint law is the preceding parameterized prefix law. -/
theorem parameterizedNextObservationJoint_fst
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    (P.parameterizedNextObservationJoint e iota n).fst =
      P.parameterizedDenseTimePrefixKernel e iota n := by
  rw [parameterizedNextObservationJoint, Kernel.mapOfMeasurable_eq_map, Kernel.fst_eq,
    ← Kernel.map_comp_right]
  · change
      (P.parameterizedDenseTimePrefixKernel e iota n.succ).map
          (Prod.fst ∘ DenseTimeHistory.splitLast n) =
        P.parameterizedDenseTimePrefixKernel e iota n
    calc
      (P.parameterizedDenseTimePrefixKernel e iota n.succ).map
          (Prod.fst ∘ DenseTimeHistory.splitLast n) =
          (P.parameterizedDenseTimePrefixKernel e iota n.succ).map
            (FiniteOrderedTimes.restrictPath
              (Fin.castLEOrderEmb (Nat.le_succ n))) := by
        congr 1
        funext path i
        exact DenseTimeHistory.splitLast_fst_apply n path i
      _ = P.parameterizedDenseTimePrefixKernel e iota n :=
        (P.parameterizedDenseTimePrefixKernel_map_restrictPath
          hP e iota (Nat.le_succ n)).symm
  · exact (DenseTimeHistory.splitLast n).measurable
  · exact measurable_fst

/-- One jointly measurable conditional law of the next observation given the parameter, start,
and preceding prefix. -/
def parameterizedObservationCondKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    Kernel ((Theta × alpha) × (Fin n → alpha)) alpha := by
  letI : IsMarkovKernel (P.parameterizedNextObservationJoint e iota n) := by
    rw [parameterizedNextObservationJoint, Kernel.mapOfMeasurable_eq_map]
    let : IsMarkovKernel (P.parameterizedDenseTimePrefixKernel e iota (n + 1)) :=
      P.isMarkovKernel_parameterizedDenseTimePrefixKernel hP e iota (n + 1)
    exact Kernel.IsMarkovKernel.map _ (DenseTimeHistory.splitLast n).measurable
  exact (P.parameterizedNextObservationJoint e iota n).condKernel

/-- The jointly parameterized conditional next-observation law is Markov. -/
theorem isMarkovKernel_parameterizedObservationCondKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    IsMarkovKernel (P.parameterizedObservationCondKernel hP e iota n) := by
  rw [parameterizedObservationCondKernel]
  infer_instance

/-- Disintegration reconstructs the jointly parameterized next-observation law. -/
theorem compProd_parameterizedObservationCondKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    P.parameterizedDenseTimePrefixKernel e iota n ⊗ₖ
        P.parameterizedObservationCondKernel hP e iota n =
      P.parameterizedNextObservationJoint e iota n := by
  rw [← P.parameterizedNextObservationJoint_fst hP e iota n]
  rw [parameterizedObservationCondKernel]
  exact Kernel.disintegrate _ _

end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess

end PortComputability
