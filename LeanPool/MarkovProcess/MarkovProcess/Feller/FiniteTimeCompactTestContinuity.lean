/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Feller.CoordinatePolynomialContinuity
public import Mathlib.MeasureTheory.Integral.CompactlySupported


/-!
# Continuity of finite-time integrals of compactly supported tests

This file extends finite coordinate-polynomial continuity to arbitrary compactly supported
continuous tests by uniform approximation. Conservativity makes every finite-time law a
probability measure, so the approximation error is uniform in the ordered time family.

The measurable structure on a finite product need not expose an `OpensMeasurableSpace` instance
under the standing assumptions. We therefore derive strong measurability of the test from its
coordinate-polynomial approximants instead of adding that extra assumption. This is
finite-dimensional analytic infrastructure; no statement about path space is proved here.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

/-- Finite-time integrals of compactly supported continuous tests vary continuously under
coordinatewise convergence of the ordered observation times. -/
theorem IsFellerKernelSemigroup.tendsto_integral_compactlySupported_finiteTimeKernel
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes n} {times0 : FiniteOrderedTimes n}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times0 i)))
    (f : C_c(Fin n → alpha, ℝ)) (x : alpha) :
    Tendsto (fun a ↦ ∫ path, f path ∂finiteTimeKernel P (times a) x) l
      (nhds (∫ path, f path ∂finiteTimeKernel P times0 x)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  obtain ⟨terms, hterms⟩ :=
    PiContinuousMap.exists_coordinateProductTerms_near_compactlySupported f
      (div_pos hepsilon (by norm_num : (0 : ℝ) < 3))
  let polynomial := PiContinuousMap.coordinatePolynomial terms
  have hnear (path : Fin n → alpha) : ‖polynomial path - f path‖ < epsilon / 3 := by
    rw [PiContinuousMap.coordinatePolynomial_apply]
    exact hterms path
  have hApprox (u : FiniteOrderedTimes n) :
      dist (∫ path, polynomial path ∂finiteTimeKernel P u x)
          (∫ path, f path ∂finiteTimeKernel P u x) ≤ epsilon / 3 := by
    let : IsProbabilityMeasure (finiteTimeKernel P u x) :=
      hP.isProbabilityMeasure_finiteTimeLaw P u x
    have hdiff : Integrable (fun path ↦ polynomial path - f path)
        (finiteTimeKernel P u x) := by
      apply Integrable.of_bound (C := epsilon / 3)
      · exact (stronglyMeasurable_coordinatePolynomial terms).sub
          (stronglyMeasurable_compactlySupported_pi f) |>.aestronglyMeasurable
      · exact ae_of_all _ fun path ↦ (hnear path).le
    have hp : Integrable polynomial (finiteTimeKernel P u x) :=
      integrable_coordinatePolynomial terms _
    have hf : Integrable f (finiteTimeKernel P u x) := by
      have hsub := hp.sub hdiff
      apply hsub.congr
      exact ae_of_all _ fun path ↦ by simp only [Pi.sub_apply, sub_sub_cancel]
    rw [Real.dist_eq, ← MeasureTheory.integral_sub hp hf]
    calc
      ‖∫ path, polynomial path - f path ∂finiteTimeKernel P u x‖ ≤
          (epsilon / 3) * (finiteTimeKernel P u x).real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const
          (ae_of_all _ fun path ↦ (hnear path).le)
      _ = epsilon / 3 := by
        simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]
  have hPolynomial :=
    hFeller.tendsto_integral_coordinatePolynomial_finiteTimeKernel hP ht terms x
  rw [Metric.tendsto_nhds] at hPolynomial
  filter_upwards [hPolynomial (epsilon / 3)
    (div_pos hepsilon (by norm_num : (0 : ℝ) < 3))] with a ha
  calc
    dist (∫ path, f path ∂finiteTimeKernel P (times a) x)
        (∫ path, f path ∂finiteTimeKernel P times0 x) ≤
      dist (∫ path, f path ∂finiteTimeKernel P (times a) x)
          (∫ path, polynomial path ∂finiteTimeKernel P (times a) x) +
        dist (∫ path, polynomial path ∂finiteTimeKernel P (times a) x)
          (∫ path, f path ∂finiteTimeKernel P times0 x) := dist_triangle _ _ _
    _ ≤ dist (∫ path, f path ∂finiteTimeKernel P (times a) x)
          (∫ path, polynomial path ∂finiteTimeKernel P (times a) x) +
        (dist (∫ path, polynomial path ∂finiteTimeKernel P (times a) x)
            (∫ path, polynomial path ∂finiteTimeKernel P times0 x) +
          dist (∫ path, polynomial path ∂finiteTimeKernel P times0 x)
            (∫ path, f path ∂finiteTimeKernel P times0 x)) := by
      apply add_le_add_right
      exact dist_triangle _ _ _
    _ < epsilon := by
      have hleft := hApprox (times a)
      rw [dist_comm] at hleft
      have hright := hApprox times0
      linarith only [hleft, ha, hright]

end MarkovProcess.SubMarkovKernelSemigroup
