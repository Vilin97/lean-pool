/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ScalarPoissonHessianBelowTwo
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ScalarPoissonHessianAboveTwo
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ScalarPoissonHessianTwo

/-!
# Finite-exponent scalar Poisson Hessian estimates

This module provides the common centered-cube scalar Poisson Hessian
Calderón--Zygmund estimate for every finite exponent.

## Main results

- `exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le`: the
  normalized Hilbert-matrix Hessian estimate for scalar Dirichlet Poisson
  solutions with data in `L² ∩ L^q`.

## Implementation notes

The proof selects the below-energy duality theorem, the energy theorem, or the
above-energy good-`λ` theorem according to the exponent.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

/-- The normalized finite-exponent Calderón--Zygmund Hessian estimate for
zero-trace scalar Poisson solutions on centered triadic cubes. -/
theorem exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (F : Vec d → ℝ),
      MemLp F 2 (normalizedCubeMeasure (originCube d m)) →
      MemLp F q.exponent (normalizedCubeMeasure (originCube d m)) →
      ∀ u : H10Function (openCubeSet (originCube d m)),
        CubeDirichletWeakPoissonProblem (originCube d m) u F →
        ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function,
          MemLp (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) q.exponent
            (normalizedCubeMeasure (originCube d m)) ∧
          eLpNorm (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) q.exponent
            (normalizedCubeMeasure (originCube d m)) ≤
            C * eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) := by
  by_cases hlt : q.exponent.toReal < 2
  · exact exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_of_lt_two d q hlt
  by_cases hgt : 2 < q.exponent.toReal
  · exact exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_of_two_lt d q hgt
  have hreal : q.exponent.toReal = 2 :=
    le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
  have hexp : q.exponent = 2 := by
    apply (ENNReal.toReal_eq_toReal_iff' q.lt_top.ne (by norm_num)).mp
    simpa only [ENNReal.toReal_ofNat] using hreal
  have hq : q = FiniteLpExponent.two := by
    cases q
    simp only [FiniteLpExponent.two] at hexp ⊢
    cases hexp
    rfl
  subst q
  obtain ⟨C, hCtop, hC⟩ :=
    exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_two d
  refine ⟨C, hCtop, ?_⟩
  intro m F hF2 _ u hweak
  simpa only [FiniteLpExponent.two_exponent] using hC m F hF2 u hweak

end CubeCalderonZygmund

end
end Homogenization
