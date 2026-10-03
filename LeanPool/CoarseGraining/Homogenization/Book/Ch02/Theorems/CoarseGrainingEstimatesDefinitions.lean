/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MagicIdentitiesDefinitions

/-! # Coarse Graining Estimates Definitions -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- Public theorem package for `l.cg.response.estimates.basic.definitions`.

The canonical public theorem proving this package is
`responseCoarseGrainingEstimatesTheory` in `CoarseGrainingEstimates.lean`. -/
structure ResponseCoarseGrainingEstimatesTheory {d : ℕ} (U : Domain d)
    (a : CoeffOn U) : Prop where
  linear_response :
    ∀ p q : Vec d, ∀ w : Solution U a,
      |average U
        (fun x =>
          vecDot p (matVecMul (a.toCoeffField x) (w.toH1.grad x)) -
            vecDot q (w.toH1.grad x))| ≤
        Real.sqrt (variationEnergyValue U a w) *
          Real.sqrt ((2 : ℝ) * responseJ U a p q)
  coarse_graining :
    ∀ p : Vec d, ∀ w : Solution U a,
      |vecDot p
        (matVecMul (aStarCoarse U a) (averageGradient U a w) -
          averageFlux U a w)| ≤
        Real.sqrt (2 : ℝ) *
          Real.sqrt
            (vecDot p
              (matVecMul (sigmaCoarse U a - sigmaStarCoarse U a) p)) *
          Real.sqrt (variationEnergyValue U a w)
  average_gradient_energy :
    ∀ w : Solution U a,
      (1 / 2 : ℝ) *
          vecDot (averageGradient U a w)
            (matVecMul (sigmaStarCoarse U a) (averageGradient U a w)) ≤
        (1 / 2 : ℝ) * variationEnergyValue U a w
  average_flux_energy :
    ∀ w : Solution U a,
      (1 / 2 : ℝ) *
          vecDot (averageFlux U a w)
            (matVecMul ((bCoarse U a)⁻¹) (averageFlux U a w)) ≤
        (1 / 2 : ℝ) * variationEnergyValue U a w

namespace ResponseCoarseGrainingEstimatesTheory

/-- The coarse-graining estimates depend only on the public coefficient
representative up to a.e. equality on the domain. -/
theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b)
    (hTheory : ResponseCoarseGrainingEstimatesTheory U a) :
    ResponseCoarseGrainingEstimatesTheory U b where
  linear_response := by
    intro p q w
    let wa : Solution U a := Solution.ofAEEq h.symm w
    have hAvg :
        average U
            (fun x =>
              vecDot p (matVecMul (b.toCoeffField x) (w.toH1.grad x)) -
                vecDot q (w.toH1.grad x)) =
          average U
            (fun x =>
              vecDot p (matVecMul (a.toCoeffField x) (wa.toH1.grad x)) -
                vecDot q (wa.toH1.grad x)) := by
      unfold average
      congr 1
      exact MeasureTheory.integral_congr_ae <| h.symm.mono fun x hx => by
        simp [wa, hx]
    have hOld := hTheory.linear_response p q wa
    simpa [wa, hAvg, variationEnergyValue_ofAEEq h.symm w,
      responseJ_eq_ofAEEq h p q] using hOld
  coarse_graining := by
    intro p w
    let wa : Solution U a := Solution.ofAEEq h.symm w
    have hOld := hTheory.coarse_graining p wa
    simpa [wa, aStarCoarse_eq_ofAEEq h, sigmaCoarse_eq_ofAEEq h,
      sigmaStarCoarse_eq_ofAEEq h, averageGradient_ofAEEq h.symm w,
      averageFlux_ofAEEq h.symm w, variationEnergyValue_ofAEEq h.symm w]
      using hOld
  average_gradient_energy := by
    intro w
    let wa : Solution U a := Solution.ofAEEq h.symm w
    have hOld := hTheory.average_gradient_energy wa
    simpa [wa, sigmaStarCoarse_eq_ofAEEq h,
      averageGradient_ofAEEq h.symm w,
      variationEnergyValue_ofAEEq h.symm w] using hOld
  average_flux_energy := by
    intro w
    let wa : Solution U a := Solution.ofAEEq h.symm w
    have hOld := hTheory.average_flux_energy wa
    simpa [wa, bCoarse_eq_ofAEEq h, averageFlux_ofAEEq h.symm w,
      variationEnergyValue_ofAEEq h.symm w] using hOld

/-- A.e.-equivalent coefficient representatives satisfy the same
coarse-graining estimate package. -/
theorem iff_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    ResponseCoarseGrainingEstimatesTheory U a ↔
      ResponseCoarseGrainingEstimatesTheory U b :=
  ⟨ofAEEq h, ofAEEq h.symm⟩

end ResponseCoarseGrainingEstimatesTheory

end

end Ch02
end Book
end Homogenization
