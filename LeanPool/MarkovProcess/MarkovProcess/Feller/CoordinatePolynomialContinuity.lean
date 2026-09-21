/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Feller.CoordinateProductContinuity

/-!
# Continuity of finite coordinate polynomials

Continuity of finite-time integrals for one coordinate-product term extends to every finite sum
of such terms.  The proof supplies explicit bounded integrability for the individual terms and
their coordinate polynomials before applying linearity of the integral.

This file handles only explicit finite coordinate polynomials.  The passage to arbitrary
compactly supported continuous tests is in `Feller/FiniteTimeCompactTestContinuity.lean`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem integrable_coordinateProductTerm
    {n : ℕ} (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha)
    (mu : Measure (Fin n → alpha)) [IsFiniteMeasure mu] :
    Integrable term.toContinuousMap mu := by
  have hprod : StronglyMeasurable (fun path : Fin n → alpha ↦
      (term.factors.map fun p ↦ p.2 (path p.1)).prod) := by
    induction term.factors with
    | nil => exact stronglyMeasurable_const
    | cons p factors ih =>
        simp only [List.map_cons, List.prod_cons]
        exact ((p.2.measurable.comp (measurable_pi_apply p.1)).stronglyMeasurable).mul ih
  have hfun : (term.toContinuousMap : (Fin n → alpha) → ℝ) = fun path ↦
      term.coefficient * (term.factors.map fun p ↦ p.2 (path p.1)).prod := by
    funext path
    exact PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply term path
  rw [hfun]
  refine Integrable.of_bound (hprod.const_mul term.coefficient).aestronglyMeasurable
    (‖term.coefficient‖ * (term.factors.map fun p ↦ ‖p.2‖).prod) ?_
  filter_upwards [] with path
  rw [norm_mul, List.norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  induction term.factors with
  | nil =>
      simp only [List.map_nil, List.prod_nil]
      exact le_rfl
  | cons p factors ih =>
      simp only [List.map_cons, List.prod_cons]
      have all_nonneg : ∀ fs : List (Fin n × C₀(alpha, ℝ)),
          0 ≤ (fs.map fun q ↦ ‖q.2 (path q.1)‖).prod := by
        intro fs
        induction fs with
        | nil => simp only [List.map_nil, List.prod_nil, zero_le_one]
        | cons q fs ih_nonneg =>
            simp only [List.map_cons, List.prod_cons]
            exact mul_nonneg (norm_nonneg _) ih_nonneg
      have hnonneg : 0 ≤
          ((factors.map fun p ↦ p.2 (path p.1)).map norm).prod := by
        simpa only [List.map_map, Function.comp_apply] using! all_nonneg factors
      exact mul_le_mul (p.2.toBCF.norm_coe_le_norm (path p.1)) ih
        hnonneg (norm_nonneg _)

omit [LocallyCompactSpace alpha] [T2Space alpha] in
private theorem integrable_coordinatePolynomial
    {n : ℕ} (terms : List (PiContinuousMap.CoordinateProductTerm (Fin n) alpha))
    (mu : Measure (Fin n → alpha)) [IsFiniteMeasure mu] :
    Integrable (PiContinuousMap.coordinatePolynomial terms) mu := by
  induction terms with
  | nil =>
      simp only [PiContinuousMap.coordinatePolynomial_nil]
      change Integrable (fun _ : Fin n → alpha ↦ (0 : ℝ)) mu
      refine Integrable.of_bound stronglyMeasurable_const.aestronglyMeasurable 0 ?_
      exact ae_of_all _ fun _ ↦ by
        simpa only [norm_zero] using (le_refl (0 : ℝ))
  | cons term terms ih =>
      rw [PiContinuousMap.coordinatePolynomial_cons]
      exact (integrable_coordinateProductTerm term mu).add ih

omit [LocallyCompactSpace alpha] [T2Space alpha] in
/-- Finite-time integrals of an explicit coordinate polynomial vary continuously under
coordinatewise convergence of the ordered observation times. -/
theorem IsFellerKernelSemigroup.tendsto_integral_coordinatePolynomial_finiteTimeKernel
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes n} {times0 : FiniteOrderedTimes n}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times0 i)))
    (terms : List (PiContinuousMap.CoordinateProductTerm (Fin n) alpha)) (x : alpha) :
    Tendsto (fun a ↦ ∫ path, PiContinuousMap.coordinatePolynomial terms path
        ∂finiteTimeKernel P (times a) x) l
      (nhds (∫ path, PiContinuousMap.coordinatePolynomial terms path
        ∂finiteTimeKernel P times0 x)) := by
  induction terms with
  | nil =>
      simp only [PiContinuousMap.coordinatePolynomial_nil, ContinuousMap.zero_apply,
        integral_zero]
      exact tendsto_const_nhds
  | cons term terms ih =>
      have hIntegral (u : FiniteOrderedTimes n) :
          ∫ path, PiContinuousMap.coordinatePolynomial (term :: terms) path
              ∂finiteTimeKernel P u x =
            (∫ path, term.toContinuousMap path ∂finiteTimeKernel P u x) +
              ∫ path, PiContinuousMap.coordinatePolynomial terms path
                ∂finiteTimeKernel P u x := by
        let : IsProbabilityMeasure (finiteTimeKernel P u x) :=
          hP.isProbabilityMeasure_finiteTimeLaw P u x
        rw [PiContinuousMap.coordinatePolynomial_cons]
        apply integral_add
        · exact integrable_coordinateProductTerm term _
        · exact integrable_coordinatePolynomial terms _
      simp_rw [hIntegral]
      exact (hFeller.tendsto_integral_coordinateProductTerm_finiteTimeKernel
        hP ht term x).add ih

end MarkovProcess.SubMarkovKernelSemigroup
