/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Feller.Semigroup
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.C0SemigroupJoint


/-!
# Continuity tools for finite-time Feller kernels

This file records the analytic continuity mechanism needed in a recursive proof of continuity of
finite-time laws.  In particular, strong continuity and contractivity imply joint continuity in
the time and in a varying `C₀` test function.  After evaluation, this gives convergence of kernel
integrals when both the transition time and the test function vary.

The extension from product tests to arbitrary compactly supported tests on a finite product is
not asserted here.
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess

namespace Semigroup.StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A strongly continuous contraction semigroup acts continuously when both time and the vector
vary.  Strong continuity alone only states this for a fixed vector; contractivity makes the
dependence on the vector uniform in time. -/
theorem tendsto_apply_of_tendsto
    (S : StronglyContinuousContractionSemigroup E) {X : Type*} {l : Filter X}
    {t : X → NNReal} {t₀ : NNReal} {f : X → E} {f₀ : E}
    (ht : Tendsto t l (nhds t₀)) (hf : Tendsto f l (nhds f₀)) :
    Tendsto (fun x ↦ S (t x) (f x)) l (nhds (S t₀ f₀)) := by
  rw [Metric.tendsto_nhds] at hf ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have htime : ∀ᶠ x in l, dist (S (t x) f₀) (S t₀ f₀) < ε / 2 :=
    ((S.continuous f₀).tendsto t₀ |>.comp ht) (Metric.ball_mem_nhds _ hhalf)
  filter_upwards [hf (ε / 2) hhalf, htime] with x hx htx
  calc
    dist (S (t x) (f x)) (S t₀ f₀)
        ≤ dist (S (t x) (f x)) (S (t x) f₀) +
            dist (S (t x) f₀) (S t₀ f₀) := dist_triangle _ _ _
    _ ≤ dist (f x) f₀ + dist (S (t x) f₀) (S t₀ f₀) :=
      by
        simpa only [add_comm] using
          add_le_add_right (S.dist_apply_le (t x) (f x) f₀)
            (dist (S (t x) f₀) (S t₀ f₀))
    _ < ε / 2 + ε / 2 := add_lt_add hx htx
    _ = ε := add_halves ε

/-- Joint continuity of the semigroup action in time and the evolving vector. -/
theorem continuous_apply
    (S : StronglyContinuousContractionSemigroup E) :
    Continuous fun tf : NNReal × E ↦ S tf.1 tf.2 := by
  rw [continuous_iff_continuousAt]
  intro tf
  exact S.tendsto_apply_of_tendsto continuousAt_fst continuousAt_snd

end Semigroup.StronglyContinuousContractionSemigroup

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

omit [LocallyCompactSpace alpha] [T2Space alpha] in
/-- Feller continuity permits both the time and the `C₀` integrand to vary. -/
theorem IsFellerKernelSemigroup.tendsto_kernelIntegral_c0
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {X : Type*} {l : Filter X} {t : X → NNReal} {t₀ : NNReal}
    {f : X → C₀(alpha, ℝ)} {f₀ : C₀(alpha, ℝ)}
    (ht : Tendsto t l (nhds t₀)) (hf : Tendsto f l (nhds f₀)) (x : alpha) :
    Tendsto (fun a ↦ kernelIntegral (P (t a)) (f a) x) l
      (nhds (kernelIntegral (P t₀) f₀ x)) := by
  have haction := hP.c0Semigroup.tendsto_apply_of_tendsto ht hf
  have heval : Continuous fun g : C₀(alpha, ℝ) ↦ g x :=
    (ZeroAtInftyContinuousMap.isometry_toBCF (α := alpha) (β := ℝ)).continuous.eval
      continuous_const
  simpa only [IsFellerKernelSemigroup.c0Semigroup_apply_apply] using!
    heval.continuousAt.tendsto.comp haction

omit [LocallyCompactSpace alpha] [T2Space alpha] in
/-- The two-transition backward recursion is continuous for product `C₀` tests.  The inner
transition acts on `g`; multiplication by the first-coordinate test `f` gives the varying `C₀`
test seen by the outer transition.  This is the successor-step analytic mechanism in the
finite-time argument. -/
theorem IsFellerKernelSemigroup.tendsto_twoStepProduct_c0
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {X : Type*} {l : Filter X}
    {t s : X → NNReal} {t₀ s₀ : NNReal}
    {f g : X → C₀(alpha, ℝ)} {f₀ g₀ : C₀(alpha, ℝ)}
    (ht : Tendsto t l (nhds t₀)) (hs : Tendsto s l (nhds s₀))
    (hf : Tendsto f l (nhds f₀)) (hg : Tendsto g l (nhds g₀)) (x : alpha) :
    Tendsto
      (fun a ↦ kernelIntegral (P (t a))
        (f a * hP.c0Semigroup (s a) (g a)) x)
      l
      (nhds (kernelIntegral (P t₀)
        (f₀ * hP.c0Semigroup s₀ g₀) x)) := by
  have hinner : Tendsto (fun a ↦ hP.c0Semigroup (s a) (g a)) l
      (nhds (hP.c0Semigroup s₀ g₀)) :=
    hP.c0Semigroup.tendsto_apply_of_tendsto hs hg
  exact hP.tendsto_kernelIntegral_c0 ht (hf.mul hinner) x

end SubMarkovKernelSemigroup

end MarkovProcess
