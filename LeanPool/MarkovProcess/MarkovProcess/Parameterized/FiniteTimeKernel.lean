/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.Kernel
import LeanPool.MarkovProcess.MarkovProcess.Parameterized.OrderedGrid

/-!
# Parameterized finite-time kernels

This file constructs the finite-dimensional kernel at a fixed strictly ordered time family for a
measurably parameterized sub-Markov semigroup. The construction recursively carries the parameter
through the augmented state kernel. Fiberwise conservativity is used only for the Markov-kernel
property.

The slice theorem identifies evaluation at a parameter and start with the existing
nonparameterized finite-time kernel of the fixed-parameter semigroup. No path-space or
stochastic-process existence claim is made here.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MarkovProcess

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

private theorem measurable_finCons_snd {n : ℕ} :
    Measurable (fun z : (Theta × alpha) × (Fin n → alpha) ↦
      @Fin.cons n (fun _ : Fin (n + 1) ↦ alpha) z.1.2 z.2) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.cons_zero] using!
      (measurable_snd.comp measurable_fst :
        Measurable (fun z : (Theta × alpha) × (Fin n → alpha) ↦ z.1.2))
  · simpa only [Fin.cons_succ] using!
      (measurable_pi_apply j).comp
        (measurable_snd : Measurable (Prod.snd :
          (Theta × alpha) × (Fin n → alpha) → Fin n → alpha))

/-- The jointly measurable finite-time kernel for a parameterized semigroup. -/
noncomputable def parameterizedFiniteTimeKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) :
    {n : ℕ} → FiniteOrderedTimes n → Kernel (Theta × alpha) (Fin n → alpha)
  | 0, _ => Kernel.const (Theta × alpha) (Measure.dirac (FiniteOrderedTimes.emptyPath alpha))
  | n + 1, times =>
      Kernel.mapOfMeasurable
        (P.augmentedKernel (times 0) ⊗ₖ
          Kernel.prodMkLeft (Theta × alpha)
            (parameterizedFiniteTimeKernel P times.relativeTail))
        (fun z ↦ @Fin.cons n (fun _ : Fin (n + 1) ↦ alpha) z.1.2 z.2)
        measurable_finCons_snd

@[simp]
theorem parameterizedFiniteTimeKernel_zero
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (times : FiniteOrderedTimes 0) :
    P.parameterizedFiniteTimeKernel times =
      Kernel.const (Theta × alpha) (Measure.dirac (FiniteOrderedTimes.emptyPath alpha)) :=
  rfl

@[simp]
theorem parameterizedFiniteTimeKernel_succ
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) {n : ℕ}
    (times : FiniteOrderedTimes (n + 1)) :
    P.parameterizedFiniteTimeKernel times =
      Kernel.mapOfMeasurable
        (P.augmentedKernel (times 0) ⊗ₖ
          Kernel.prodMkLeft (Theta × alpha)
            (P.parameterizedFiniteTimeKernel times.relativeTail))
        (fun z ↦ @Fin.cons n (fun _ : Fin (n + 1) ↦ alpha) z.1.2 z.2)
        measurable_finCons_snd :=
  rfl

theorem isMarkovKernel_parameterizedFiniteTimeKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    {n : ℕ} (times : FiniteOrderedTimes n) :
    IsMarkovKernel (P.parameterizedFiniteTimeKernel times) := by
  induction n with
  | zero =>
      rw [parameterizedFiniteTimeKernel_zero]
      infer_instance
  | succ n ih =>
      let : IsMarkovKernel (P.augmentedKernel (times 0)) :=
        P.isMarkovKernel_augmentedKernel hP (times 0)
      let : IsMarkovKernel (P.parameterizedFiniteTimeKernel times.relativeTail) :=
        ih times.relativeTail
      rw [parameterizedFiniteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map]
      exact Kernel.IsMarkovKernel.map _ measurable_finCons_snd

private theorem isFiniteKernel_parameterizedFiniteTimeKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    {n : ℕ} (times : FiniteOrderedTimes n) :
    IsFiniteKernel (P.parameterizedFiniteTimeKernel times) := by
  induction n with
  | zero =>
      rw [parameterizedFiniteTimeKernel_zero]
      infer_instance
  | succ n ih =>
      have hParameterState : IsSubMarkovKernel (P.parameterStateKernel (times 0)) :=
        fun q ↦ by
          rw [parameterStateKernel_apply]
          exact P.isSubMarkovKernel q.1 (times 0) q.2
      let : IsFiniteKernel (P.parameterStateKernel (times 0)) :=
        hParameterState.isFiniteKernel
      let : IsFiniteKernel (P.augmentedKernel (times 0)) := by
        rw [augmentedKernel]
        infer_instance
      let : IsFiniteKernel (P.parameterizedFiniteTimeKernel times.relativeTail) :=
        ih times.relativeTail
      rw [parameterizedFiniteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map]
      infer_instance

private theorem isFiniteKernel_finiteTimeKernel
    (Q : SubMarkovKernelSemigroup alpha)
    {n : ℕ} (times : FiniteOrderedTimes n) :
    IsFiniteKernel (Q.finiteTimeKernel times) := by
  induction n with
  | zero =>
      rw [SubMarkovKernelSemigroup.finiteTimeKernel_zero]
      infer_instance
  | succ n ih =>
      let : IsFiniteKernel (Q (times 0)) :=
        (Q.isSubMarkovKernel (times 0)).isFiniteKernel
      let : IsFiniteKernel (Q.finiteTimeKernel times.relativeTail) :=
        ih times.relativeTail
      rw [SubMarkovKernelSemigroup.finiteTimeKernel_succ,
        Kernel.mapOfMeasurable_eq_map]
      infer_instance

private theorem augmentedKernel_apply_eq_map
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (theta : Theta) (t : NNReal) (x : alpha) :
    P.augmentedKernel t (theta, x) = (P theta t x).map (Prod.mk theta) := by
  have hParameterState : IsSubMarkovKernel (P.parameterStateKernel t) := fun q ↦ by
    rw [parameterStateKernel_apply]
    exact P.isSubMarkovKernel q.1 t q.2
  let : IsFiniteKernel (P.parameterStateKernel t) := hParameterState.isFiniteKernel
  let : IsFiniteKernel (P theta t) := (P.isSubMarkovKernel theta t).isFiniteKernel
  rw [augmentedKernel, Kernel.prod_apply, Kernel.deterministic_apply,
    parameterStateKernel_apply, Measure.dirac_prod]

/-- A fixed-parameter slice is the ordinary finite-time kernel of that semigroup slice. -/
theorem parameterizedFiniteTimeKernel_apply
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    {n : ℕ} (times : FiniteOrderedTimes n) (theta : Theta) (x : alpha) :
    P.parameterizedFiniteTimeKernel times (theta, x) =
      SubMarkovKernelSemigroup.finiteTimeKernel
        (P.toSubMarkovKernelSemigroup theta) times x := by
  induction n generalizing theta x with
  | zero =>
      rw [parameterizedFiniteTimeKernel_zero,
        SubMarkovKernelSemigroup.finiteTimeKernel_zero,
        Kernel.const_apply, Kernel.const_apply]
  | succ n ih =>
      let Q := P.toSubMarkovKernelSemigroup theta
      let : IsFiniteKernel (P.augmentedKernel (times 0)) := by
        have hParameterState : IsSubMarkovKernel (P.parameterStateKernel (times 0)) :=
          fun q ↦ by
            rw [parameterStateKernel_apply]
            exact P.isSubMarkovKernel q.1 (times 0) q.2
        let : IsFiniteKernel (P.parameterStateKernel (times 0)) :=
          hParameterState.isFiniteKernel
        rw [augmentedKernel]
        infer_instance
      let : IsFiniteKernel (P.parameterizedFiniteTimeKernel times.relativeTail) :=
        isFiniteKernel_parameterizedFiniteTimeKernel P times.relativeTail
      let : IsFiniteKernel (Q (times 0)) := Q.isSubMarkovKernel (times 0) |>.isFiniteKernel
      let : IsFiniteKernel
          (SubMarkovKernelSemigroup.finiteTimeKernel Q times.relativeTail) :=
        isFiniteKernel_finiteTimeKernel Q times.relativeTail
      ext s hs
      rw [parameterizedFiniteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
        Kernel.map_apply' _ measurable_finCons_snd _ hs,
        Kernel.compProd_apply (hs.preimage measurable_finCons_snd),
        augmentedKernel_apply_eq_map, MeasureTheory.lintegral_map]
      · rw [SubMarkovKernelSemigroup.finiteTimeKernel_succ,
          Kernel.mapOfMeasurable_eq_map]
        rw [Kernel.map_apply' _ measurable_finCons _ hs,
          Kernel.compProd_apply (hs.preimage measurable_finCons)]
        simp_rw [Kernel.prodMkLeft_apply', ih times.relativeTail theta]
        rfl
      · exact Kernel.measurable_kernel_prodMk_left'
          (hs.preimage measurable_finCons_snd) (theta, x)
      · exact measurable_const.prodMk measurable_id

end ParameterizedSubMarkovKernelSemigroup

end MarkovProcess
