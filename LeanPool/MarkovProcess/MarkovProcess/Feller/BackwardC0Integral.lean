/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Feller.BackwardC0Recursion
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Finite-time integral represented by the backward `C₀` recursion

The backward Feller-semigroup recursion for a nonempty ordered family of `C₀` factors evaluates
to the integral of their coordinate product against the corresponding finite-time kernel.  The
proof follows the recursive kernel construction and uses composition-product integration.

No conservativity assumption is needed: sub-Markov finite-time kernels already give finite
measures, which suffice for bounded integrability.  This is an analytic identification only; no
statement about path space is proved here, and the process itself is built in `Trajectory/`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem integrable_coordinateProduct
    {Omega : Type*} [MeasurableSpace Omega] {n : ℕ}
    (factors : Fin n → C₀(alpha, ℝ)) (eval : Omega → Fin n → alpha)
    (heval : Measurable eval) (mu : Measure Omega) [IsFiniteMeasure mu] :
    Integrable (fun omega ↦ ∏ i, factors i (eval omega i)) mu := by
  refine Integrable.of_bound ?_ (∏ i, ‖factors i‖) ?_
  · exact
    (Finset.stronglyMeasurable_fun_prod Finset.univ fun i _ ↦
      ((factors i).measurable.comp
        ((measurable_pi_apply i).comp heval)).stronglyMeasurable).aestronglyMeasurable
  · filter_upwards [] with omega
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
    intro i _
    simpa only [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using!
      (factors i).toBCF.norm_coe_le_norm (eval omega i)

omit [TopologicalSpace alpha] [BorelSpace alpha] [LocallyCompactSpace alpha]
  [T2Space alpha] in
private theorem isFiniteKernel_finiteTimeKernel
    (P : SubMarkovKernelSemigroup alpha) {n : ℕ}
    (times : FiniteOrderedTimes n) : IsFiniteKernel (finiteTimeKernel P times) := by
  induction n with
  | zero =>
      rw [finiteTimeKernel_zero]
      infer_instance
  | succ n ih =>
      let : IsFiniteKernel (P (times 0)) :=
        (P.isSubMarkovKernel (times 0)).isFiniteKernel
      let : IsFiniteKernel (finiteTimeKernel P times.relativeTail) :=
        ih times.relativeTail
      rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map]
      infer_instance

omit [LocallyCompactSpace alpha] [T2Space alpha] in
/-- Evaluation of the backward `C₀` recursion is the coordinate-product integral against the
finite-time kernel. -/
theorem IsFellerKernelSemigroup.backwardC0_apply_eq_integral_finiteTimeKernel
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {n : ℕ} (times : FiniteOrderedTimes (n + 1))
    (factors : Fin (n + 1) → C₀(alpha, ℝ)) (x : alpha) :
    hP.backwardC0 times factors x =
      ∫ path, ∏ i, factors i (path i) ∂finiteTimeKernel P times x := by
  induction n generalizing x with
  | zero =>
      rw [hP.backwardC0_zero, hP.c0Semigroup_apply_apply]
      rw [← finiteTimeKernel_one_map_eval P times]
      unfold kernelIntegral
      rw [Kernel.map_apply _ (measurable_pi_apply 0)]
      rw [integral_map (measurable_pi_apply 0).aemeasurable
        (factors 0).measurable.stronglyMeasurable.aestronglyMeasurable]
      congr 1
      funext path
      rw [Fin.prod_univ_one]
  | succ n ih =>
      let : IsFiniteKernel (P (times 0)) :=
        (P.isSubMarkovKernel (times 0)).isFiniteKernel
      let : IsFiniteKernel (finiteTimeKernel P times.relativeTail) :=
        isFiniteKernel_finiteTimeKernel P times.relativeTail
      let productTest : (Fin (n + 2) → alpha) → ℝ :=
        fun path ↦ ∏ i, factors i (path i)
      have hProductTest : StronglyMeasurable productTest := by
        exact Finset.stronglyMeasurable_fun_prod Finset.univ fun i _ ↦
          ((factors i).measurable.comp (measurable_pi_apply i)).stronglyMeasurable
      rw [hP.backwardC0_succ, hP.c0Semigroup_apply_apply]
      rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map]
      unfold kernelIntegral
      change (∫ y, _ ∂P (times 0) x) =
        ∫ path, productTest path ∂(Kernel.map
          (P (times 0) ⊗ₖ Kernel.prodMkLeft alpha
            (finiteTimeKernel P times.relativeTail))
          (fun z ↦ Fin.cons z.1 z.2)) x
      rw [Kernel.map_apply _ measurable_finCons]
      rw [integral_map measurable_finCons.aemeasurable
        hProductTest.aestronglyMeasurable]
      dsimp only [productTest]
      rw [integral_compProd (integrable_coordinateProduct factors
        (fun z ↦ Fin.cons z.1 z.2) measurable_finCons _)]
      have heta : ∀ a, Kernel.prodMkLeft alpha
          (finiteTimeKernel P times.relativeTail) (x, a) =
            finiteTimeKernel P times.relativeTail a := by
        intro a
        ext s hs
        rw [Kernel.prodMkLeft_apply']
      simp_rw [heta]
      apply integral_congr_ae
      filter_upwards [] with a
      change factors 0 a * hP.backwardC0 times.relativeTail (Fin.tail factors) a = _
      have hprod : (fun b : Fin (n + 1) → alpha ↦
          ∏ i, factors i
            (@Fin.cons (n + 1) (fun _ : Fin (n + 2) ↦ alpha) a b i)) =
          fun b ↦ factors 0 a * ∏ i, (Fin.tail factors) i (b i) := by
        funext b
        rw [Fin.prod_univ_succ]
        rfl
      rw [hprod, integral_const_mul,
        ih times.relativeTail (Fin.tail factors) a]

end MarkovProcess.SubMarkovKernelSemigroup
