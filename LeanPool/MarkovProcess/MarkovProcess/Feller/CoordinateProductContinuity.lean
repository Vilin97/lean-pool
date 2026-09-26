/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.CoordinateProductActiveReduction
public import LeanPool.MarkovProcess.MarkovProcess.Feller.BackwardC0Integral
public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.KernelRestriction


/-!
# Continuity of finite-time integrals of coordinate-product terms

This file proves continuity, under coordinatewise convergence of ordered times, of the
finite-time-kernel integral of one `PiContinuousMap.CoordinateProductTerm`.  The proof reduces
to the coordinates on which the term has factors and applies the backward `C₀` recursion.

When there are no active coordinates, the integrand is its scalar coefficient.  That branch
uses conservativity to identify the finite-time law as a probability measure; in particular,
it never attempts to construct a constant-one element of `C₀`.  This is finite-dimensional
analytic infrastructure; no statement about path space is proved here.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

omit [LocallyCompactSpace alpha] [T2Space alpha] in
/-- The finite-time integral of a coordinate-product term varies continuously when every
ordered time coordinate varies continuously. -/
theorem IsFellerKernelSemigroup.tendsto_integral_coordinateProductTerm_finiteTimeKernel
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes n} {times0 : FiniteOrderedTimes n}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times0 i)))
    (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha) (x : alpha) :
    Tendsto (fun a ↦ ∫ path, term.toContinuousMap path ∂finiteTimeKernel P (times a) x) l
      (nhds (∫ path, term.toContinuousMap path ∂finiteTimeKernel P times0 x)) := by
  let A := PiContinuousMap.activeCoordinates term.factors
  by_cases hA : A.card = 0
  · have hActive : PiContinuousMap.activeCoordinates term.factors = ∅ := by
      exact Finset.card_eq_zero.mp hA
    have hTerm (path : Fin n → alpha) :
        term.toContinuousMap path = term.coefficient := by
      rw [PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply_active]
      simp only [PiContinuousMap.CoordinateProductTerm.activeEvaluation, hActive,
        Finset.card_empty, Finset.prod_fin_eq_prod_range, Finset.prod_range_zero, mul_one]
    have hIntegral (u : FiniteOrderedTimes n) :
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel P u x = term.coefficient := by
      let : IsProbabilityMeasure (finiteTimeKernel P u x) :=
        hP.isProbabilityMeasure_finiteTimeLaw P u x
      rw [integral_congr_ae (ae_of_all _ hTerm)]
      simp only [integral_const, probReal_univ, one_smul]
    simp_rw [hIntegral]
    exact tendsto_const_nhds
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hA
    let e := PiContinuousMap.activeOrderEmbedding term.factors
    let ec : Fin (k + 1) ↪o Fin n :=
      (Fin.castOrderIso hk.symm).toOrderEmbedding.trans e
    let factors : Fin (k + 1) → C₀(alpha, ℝ) := fun j ↦
      PiContinuousMap.activeNormalizedFactor term.factors (Fin.cast hk.symm j)
    have htimes : ∀ i, Tendsto (fun a ↦ (times a).restrict ec i) l
        (nhds (times0.restrict ec i)) := by
      intro i
      exact ht (ec i)
    have hIntegral (u : FiniteOrderedTimes n) :
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel P u x =
          term.coefficient * hFeller.backwardC0
            (u.restrict ec) factors x := by
      let g : (Fin (k + 1) → alpha) → ℝ :=
        fun path ↦ ∏ i, factors i (path i)
      have hg : StronglyMeasurable g := by
        exact Finset.stronglyMeasurable_fun_prod Finset.univ fun i _ ↦
          ((factors i).measurable.comp (measurable_pi_apply i)).stronglyMeasurable
      have hpoint : ∀ path : Fin n → alpha,
          term.toContinuousMap path =
            term.coefficient * g (FiniteOrderedTimes.restrictPath ec path) := by
        intro path
        rw [PiContinuousMap.CoordinateProductTerm.toContinuousMap_apply_active]
        simp only [PiContinuousMap.CoordinateProductTerm.activeEvaluation, g,
          factors, FiniteOrderedTimes.restrictPath, ec, e,
          RelEmbedding.coe_trans, Function.comp_apply,
          OrderIso.coe_toOrderEmbedding]
        congr 1
        exact ((Fin.castOrderIso hk.symm).toEquiv.prod_comp
          (fun j ↦ PiContinuousMap.activeNormalizedFactor term.factors j
            (path (PiContinuousMap.activeOrderEmbedding term.factors j)))).symm
      calc
        ∫ path, term.toContinuousMap path ∂finiteTimeKernel P u x =
            ∫ path, term.coefficient *
              g (FiniteOrderedTimes.restrictPath ec path) ∂finiteTimeKernel P u x := by
              apply integral_congr_ae
              exact ae_of_all _ hpoint
        _ = term.coefficient * ∫ path,
              g (FiniteOrderedTimes.restrictPath ec path) ∂finiteTimeKernel P u x := by
              rw [integral_const_mul]
        _ = term.coefficient * ∫ path, g path ∂
              (finiteTimeKernel P u).map (FiniteOrderedTimes.restrictPath ec) x := by
              rw [Kernel.map_apply _ (FiniteOrderedTimes.measurable_restrictPath ec)]
              rw [integral_map
                (FiniteOrderedTimes.measurable_restrictPath ec).aemeasurable
                hg.aestronglyMeasurable]
        _ = term.coefficient * ∫ path, g path ∂
              finiteTimeKernel P (u.restrict ec) x := by
              rw [hP.finiteTimeKernel_map_restrictPath P u ec]
        _ = term.coefficient * hFeller.backwardC0 (u.restrict ec) factors x := by
              rw [hFeller.backwardC0_apply_eq_integral_finiteTimeKernel]
    simp_rw [hIntegral]
    apply tendsto_const_nhds.mul
    have hb := hFeller.tendsto_backwardC0 htimes factors
    have heval : Continuous fun f : C₀(alpha, ℝ) ↦ f x :=
      (ZeroAtInftyContinuousMap.isometry_toBCF (α := alpha) (β := ℝ)).continuous.eval
        continuous_const
    exact heval.continuousAt.tendsto.comp hb
end MarkovProcess.SubMarkovKernelSemigroup
