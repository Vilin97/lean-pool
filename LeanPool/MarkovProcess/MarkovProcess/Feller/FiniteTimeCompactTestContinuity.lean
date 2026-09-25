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
  rw [show (term.toContinuousMap : (Fin n → alpha) → ℝ) = fun path ↦
      term.coefficient * (term.factors.map fun p ↦ p.2 (path p.1)).prod by
    funext path
    exact PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply term path]
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
private theorem stronglyMeasurable_coordinatePolynomial
    {n : ℕ} (terms : List (PiContinuousMap.CoordinateProductTerm (Fin n) alpha)) :
    StronglyMeasurable (PiContinuousMap.coordinatePolynomial terms) := by
  induction terms with
  | nil =>
      simp only [PiContinuousMap.coordinatePolynomial_nil]
      exact stronglyMeasurable_const
  | cons term terms ih =>
      rw [PiContinuousMap.coordinatePolynomial_cons]
      apply StronglyMeasurable.add _ ih
      have hprod : StronglyMeasurable (fun path : Fin n → alpha ↦
          (term.factors.map fun p ↦ p.2 (path p.1)).prod) := by
        induction term.factors with
        | nil => exact stronglyMeasurable_const
        | cons p factors ihFactors =>
            simp only [List.map_cons, List.prod_cons]
            exact ((p.2.measurable.comp (measurable_pi_apply p.1)).stronglyMeasurable).mul
              ihFactors
      rw [show (term.toContinuousMap : (Fin n → alpha) → ℝ) = fun path ↦
          term.coefficient * (term.factors.map fun p ↦ p.2 (path p.1)).prod by
        funext path
        exact PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply term path]
      exact hprod.const_mul term.coefficient

-- This approximation argument avoids assuming `OpensMeasurableSpace (Fin n → alpha)`.
private theorem stronglyMeasurable_compactlySupported_fin
    {n : ℕ} (f : C_c(Fin n → alpha, ℝ)) : StronglyMeasurable f := by
  have hexists (m : ℕ) :
      ∃ terms : List (PiContinuousMap.CoordinateProductTerm (Fin n) alpha),
        ∀ x, ‖PiContinuousMap.coordinatePolynomial terms x - f x‖ <
          1 / ((m : ℝ) + 1) := by
    have hpositive : 0 < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨terms, hterms⟩ :=
      PiContinuousMap.exists_coordinateProductTerms_near_compactlySupported f hpositive
    exact ⟨terms, fun x ↦ by
      rw [PiContinuousMap.coordinatePolynomial_apply]
      exact hterms x⟩
  choose terms hterms using hexists
  apply stronglyMeasurable_of_tendsto atTop
    (fun m ↦ stronglyMeasurable_coordinatePolynomial (terms m))
  rw [tendsto_pi_nhds]
  intro x
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hscalar : Tendsto (fun m : ℕ ↦ (1 : ℝ) / ((m : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Metric.tendsto_nhds] at hscalar
  filter_upwards [hscalar epsilon hepsilon] with m hm
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at hm
  exact (hterms m x).trans_le hm.le

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
          (stronglyMeasurable_compactlySupported_fin f) |>.aestronglyMeasurable
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
