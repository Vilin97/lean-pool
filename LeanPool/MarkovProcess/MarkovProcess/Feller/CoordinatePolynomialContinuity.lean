/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.CoordinatePolynomialMeasure
public import LeanPool.MarkovProcess.MarkovProcess.Feller.CoordinateProductContinuity


/-!
# Continuity of finite coordinate polynomials

Continuity of finite-time integrals for one coordinate-product term extends to every finite sum
of such terms.  The proof supplies explicit bounded integrability for the individual terms and
their coordinate polynomials before applying linearity of the integral.

This file handles only explicit finite coordinate polynomials.  The passage to arbitrary
compactly supported continuous tests is in `Feller/FiniteTimeCompactTestContinuity.lean`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

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
