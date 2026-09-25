/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Kernel.KernelSemigroup


/-!
# Measurably parameterized sub-Markov kernel semigroups

This file packages sub-Markov kernel semigroups depending measurably on a parameter. The
measurability field is joint in parameter, time, and starting state, with carrier ordering
`Theta × (NNReal × alpha)`. Each fixed-parameter slice is an ordinary
`SubMarkovKernelSemigroup`.

No parameter family is selected here, and no concrete coefficient, domain, Feller, conservativity,
or stochastic-process assertion is made.
-/

@[expose] public section

noncomputable section PortComputability

open Set
open scoped ENNReal ProbabilityTheory

section

namespace MarkovProcess

open MeasureTheory ProbabilityTheory

/-- A jointly measurable parameter family of sub-Markov transition-kernel semigroups.

The kernel is jointly measurable on `Θ × (NNReal × α)`. Mathlib writes `η.comp κ` for
first applying `κ` and then `η`, so the Chapman--Kolmogorov field has the orientation
`K θ (s + t) = (K θ t).comp (K θ s)`.
-/
structure ParameterizedSubMarkovKernelSemigroup (Theta alpha : Type*)
    [MeasurableSpace Theta] [MeasurableSpace alpha] where
  /-- The transition kernel at a parameter and nonnegative time. -/
  kernel : Theta → NNReal → Kernel alpha alpha
  /-- Joint measurability in parameter, time, and starting state. -/
  measurable_kernel : Measurable fun q : Theta × (NNReal × alpha) ↦
    kernel q.1 q.2.1 q.2.2
  /-- At time zero every parameter slice is the identity kernel. -/
  kernel_zero : ∀ theta, kernel theta 0 = Kernel.id
  /-- The Chapman--Kolmogorov law, in Mathlib's kernel-composition orientation. -/
  kernel_add : ∀ theta s t, kernel theta (s + t) = (kernel theta t).comp (kernel theta s)
  /-- Every transition measure has mass at most one. -/
  isSubMarkovKernel : ∀ theta t, IsSubMarkovKernel (kernel theta t)

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

instance : CoeFun (ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (fun _ ↦ Theta → NNReal → Kernel alpha alpha) where
  coe P := P.kernel

/-- Two parameterized semigroups are equal when all their kernel slices are equal. -/
@[ext]
theorem ext {P Q : ParameterizedSubMarkovKernelSemigroup Theta alpha}
    (h : ∀ theta t, P theta t = Q theta t) : P = Q := by
  cases P with
  | mk P _ _ _ _ =>
    cases Q with
    | mk Q _ _ _ _ =>
      have hPQ : P = Q := funext fun theta ↦ funext fun t ↦ h theta t
      cases hPQ
      rfl

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)

/-- The jointly measurable kernel with input ordered as parameter, then time and state. -/
def jointKernel : Kernel (Theta × (NNReal × alpha)) alpha where
  toFun q := P q.1 q.2.1 q.2.2
  measurable' := P.measurable_kernel

/-- Evaluation of the joint kernel is evaluation of the original parameter family. -/
@[simp]
theorem jointKernel_apply (q : Theta × (NNReal × alpha)) :
    P.jointKernel q = P q.1 q.2.1 q.2.2 :=
  rfl

/-- Evaluation of the joint kernel at an explicit parameter, time, and state. -/
@[simp]
theorem jointKernel_apply' (theta : Theta) (t : NNReal) (x : alpha) :
    P.jointKernel (theta, (t, x)) = P theta t x :=
  rfl

/-- Evaluation of the parameterized kernel on a measurable set is jointly measurable. -/
theorem measurable_measure {s : Set alpha} (hs : MeasurableSet s) :
    Measurable fun q : Theta × (NNReal × alpha) ↦ P q.1 q.2.1 q.2.2 s :=
  (Measure.measurable_coe hs).comp P.measurable_kernel

/-- The ordinary sub-Markov kernel semigroup at one fixed parameter. -/
def toSubMarkovKernelSemigroup (theta : Theta) : SubMarkovKernelSemigroup alpha where
  kernel := P theta
  measurable_kernel := by
    have hPair : Measurable fun p : NNReal × alpha ↦ (theta, p) :=
      (measurable_const : Measurable fun _ : NNReal × alpha ↦ theta).prod measurable_id
    exact P.measurable_kernel.comp hPair
  kernel_zero := P.kernel_zero theta
  kernel_add := P.kernel_add theta
  isSubMarkovKernel := P.isSubMarkovKernel theta

/-- A fixed-parameter slice evaluates to the original parameterized kernel. -/
@[simp]
theorem toSubMarkovKernelSemigroup_apply (theta : Theta) (t : NNReal) :
    toSubMarkovKernelSemigroup (P := P) theta t = P theta t :=
  rfl

/-- Every parameter slice is the identity kernel at time zero. -/
@[simp]
theorem zero (theta : Theta) : P theta 0 = Kernel.id :=
  P.kernel_zero theta

/-- The parameterwise Chapman--Kolmogorov law. -/
@[simp]
theorem add (theta : Theta) (s t : NNReal) :
    P theta (s + t) = (P theta t).comp (P theta s) :=
  P.kernel_add theta s t

/-- Transition kernels commute under composition at each fixed parameter. -/
theorem comp_comm (theta : Theta) (s t : NNReal) :
    (P theta t).comp (P theta s) = (P theta s).comp (P theta t) := by
  rw [← P.add theta s t, ← P.add theta t s, add_comm]

/-- Chapman--Kolmogorov as equality of parameterized transition measures. -/
theorem add_apply (theta : Theta) (s t : NNReal) (x : alpha) :
    P theta (s + t) x = (P theta s x).bind (P theta t) := by
  rw [P.add, Kernel.comp_apply]

/-- Chapman--Kolmogorov evaluated on a measurable set. -/
theorem add_apply' (theta : Theta) (s t : NNReal) (x : alpha)
    {u : Set alpha} (hu : MeasurableSet u) :
    P theta (s + t) x u = ∫⁻ y, P theta t y u ∂P theta s x := by
  rw [P.add, Kernel.comp_apply' _ _ _ hu]

/-- The tower form of Chapman--Kolmogorov for nonnegative measurable functions. -/
theorem lintegral_add (theta : Theta) (s t : NNReal) (x : alpha)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂P theta (s + t) x =
      ∫⁻ y, ∫⁻ z, f z ∂P theta t y ∂P theta s x := by
  rw [P.add, Kernel.lintegral_comp _ _ _ hf]

/-- Every parameterized transition measure has mass at most one. -/
theorem measure_univ_le_one (theta : Theta) (t : NNReal) (x : alpha) :
    P theta t x univ ≤ 1 :=
  P.isSubMarkovKernel theta t x

/-- Every parameterized transition measure assigns mass at most one to every set. -/
theorem measure_le_one (theta : Theta) (t : NNReal) (x : alpha) (s : Set alpha) :
    P theta t x s ≤ 1 :=
  (P.isSubMarkovKernel theta t).measure_le_one x s

end ParameterizedSubMarkovKernelSemigroup

end MarkovProcess

end

end PortComputability
