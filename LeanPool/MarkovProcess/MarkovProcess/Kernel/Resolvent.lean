/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import LeanPool.MarkovProcess.MarkovProcess.Kernel.Operator

/-!
# Resolvents of kernel semigroups

This file defines the resolvent of a sub-Markov kernel semigroup on nonnegative extended-real
observables by Laplace transformation of its transition kernels.

Main definitions: `SubMarkovKernelSemigroup.kernelResolvent` and
`SubMarkovKernelSemigroup.kernelResolventReal`.

No conservativity, topology, or finiteness of the resolvent is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MeasurableSpace alpha]

/-- The kernel resolvent on nonnegative extended-real observables. -/
noncomputable def kernelResolvent (P : SubMarkovKernelSemigroup alpha) (lam : ℝ)
    (f : alpha → ℝ≥0∞) (x : alpha) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
    ∫⁻ y, f y ∂(P (Real.toNNReal t) x)

/-- The kernel resolvent on real-valued observables.  Finiteness is established separately for
bounded observables at positive shifts. -/
noncomputable def kernelResolventReal (P : SubMarkovKernelSemigroup alpha) (lam : ℝ)
    (f : alpha → ℝ) (x : alpha) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
    kernelIntegral (P (Real.toNNReal t)) f x

private theorem norm_kernelIntegral_le_of_bound (P : SubMarkovKernelSemigroup alpha)
    {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (t : NNReal) (x : alpha) :
    |kernelIntegral (P t) f x| ≤ D := by
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  rw [← Real.norm_eq_abs]
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  calc
    ‖kernelIntegral (P t) f x‖ ≤ ∫ _y, D ∂(P t x) := by
      apply norm_integral_le_of_norm_le (integrable_const D)
      exact Eventually.of_forall hfD
    _ ≤ D := by
      rw [integral_const, smul_eq_mul]
      apply mul_le_of_le_one_left hD0
      rw [measureReal_def, ← ENNReal.toReal_one]
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
      exact (P.isSubMarkovKernel t).measure_le_one x Set.univ

private theorem integrableOn_kernelResolventReal_integrand
    (P : SubMarkovKernelSemigroup alpha) {lam : ℝ} (hlam : 0 < lam)
    {f : alpha → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) f x) (Ioi 0) := by
  apply Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
  · exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
      ((P.measurable_kernelIntegral hf).comp
        (measurable_real_toNNReal.prodMk measurable_const))).stronglyMeasurable
      ).aestronglyMeasurable.restrict
  · exact Eventually.of_forall fun t ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (norm_kernelIntegral_le_of_bound P hfD (Real.toNNReal t) x) (Real.exp_pos _).le

/-- The real kernel resolvent is additive on bounded measurable observables. -/
theorem kernelResolventReal_add (P : SubMarkovKernelSemigroup alpha)
    {lam : ℝ} (hlam : 0 < lam) {f g : alpha → ℝ}
    (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E) :
    P.kernelResolventReal lam (f + g) =
      P.kernelResolventReal lam f + P.kernelResolventReal lam g := by
  funext x
  unfold kernelResolventReal
  change (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) (f + g) x) =
    (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) f x) +
    ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) g x
  rw [← integral_add
    (integrableOn_kernelResolventReal_integrand P hlam hf hfD x)
    (integrableOn_kernelResolventReal_integrand P hlam hg hgE x)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  let : IsFiniteKernel (P (Real.toNNReal t)) :=
    (P.isSubMarkovKernel (Real.toNNReal t)).isFiniteKernel
  have hfint : Integrable f (P (Real.toNNReal t) x) :=
    Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable D
      (Eventually.of_forall hfD)
  have hgint : Integrable g (P (Real.toNNReal t) x) :=
    Integrable.of_bound hg.stronglyMeasurable.aestronglyMeasurable E
      (Eventually.of_forall hgE)
  have hinner : kernelIntegral (P (Real.toNNReal t)) (f + g) x =
      kernelIntegral (P (Real.toNNReal t)) f x +
        kernelIntegral (P (Real.toNNReal t)) g x := by
    unfold kernelIntegral
    simpa only [Pi.add_apply] using integral_add hfint hgint
  dsimp only
  rw [hinner]
  ring

/-- The real kernel resolvent is real homogeneous. -/
theorem kernelResolventReal_smul (P : SubMarkovKernelSemigroup alpha)
    (lam a : ℝ) (f : alpha → ℝ) :
    P.kernelResolventReal lam (a • f) = a • P.kernelResolventReal lam f := by
  funext x
  unfold kernelResolventReal
  change (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) (a • f) x) =
    a * ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) f x
  rw [← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  have hinner : kernelIntegral (P (Real.toNNReal t)) (a • f) x =
      a * kernelIntegral (P (Real.toNNReal t)) f x := by
    unfold kernelIntegral
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [MeasureTheory.integral_const_mul]
  dsimp only
  rw [hinner]
  ring

/-- The uniform bound for the real kernel resolvent of a bounded observable at a positive
shift. -/
theorem norm_kernelResolventReal_le (P : SubMarkovKernelSemigroup alpha)
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} {D : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    |P.kernelResolventReal lam f x| ≤ D / lam := by
  rw [← Real.norm_eq_abs]
  unfold kernelResolventReal
  calc
    ‖∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
        kernelIntegral (P (Real.toNNReal t)) f x‖ ≤
        ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * D := by
      apply norm_integral_le_of_norm_le
        ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (norm_kernelIntegral_le_of_bound P hfD (Real.toNNReal t) x) (Real.exp_pos _).le
    _ = D / lam := by
      rw [integral_mul_const, integral_exp_mul_Ioi (neg_neg_of_pos hlam) 0]
      simp only [mul_zero, Real.exp_zero]
      field_simp

end MarkovProcess.SubMarkovKernelSemigroup
