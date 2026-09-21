/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.Residue
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupport
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType
public import Mathlib.Data.Real.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DegreeValuation
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportResidue
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrderTypeMultiplicativity

/-!
# LM24 degree-residue statement

This module states LM24, Proposition 5.1.1 in the grade-zero-component presentation of the
residue ring. The degree valuation is exhibited together with its exact value function, its
finite-support nonpositive subring, its zero negative ideal, and the bijective residue map.

The construction uses LM24's reduction of degree multiplicativity to Berarducci, Corollary 9.9.
The residue identifications are proved in
`ConwayRefinement.HahnSeries.FiniteSupportResidue`.
-/

universe v

public noncomputable section

open scoped DirectSum HahnSeries

namespace HahnSeries.Nonpositive

variable {K : Type v} [Field K] [CharZero K]

/-- LM24, Proposition 5.1.1: the degree-zero residue ring of the multiplicative degree valuation
is the finite-support ring. -/
theorem real_hahn_series_finite_support_residue :
    ∃ w : MaxAddDegree (Nonpositive ℝ K) NatOrdinal, w.IsMultiplicative ∧
      (∀ b, w b = (b : K⟦ℝ⟧).degree) ∧
        w.nonpositiveSubring = finiteSupportSubring ∧
        w.negativeIdeal = ⊥ ∧ Function.Bijective w.residueMap := by
  let hmul : ∀ b c : Nonpositive ℝ K,
      ((b * c : Nonpositive ℝ K) : K⟦ℝ⟧).degree =
        (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree :=
    degree_mul_of_orderTypeMultiplicativeOnWeaklyPrincipal
      orderTypeMultiplicativeOnWeaklyPrincipal
  let w := degreeValuation K
  have hvalue : ∀ b, w b = (b : K⟦ℝ⟧).degree := degreeValuation_apply
  have hwmul : w.IsMultiplicative := ⟨fun b c ↦ by rw [hvalue, hvalue, hvalue]; exact hmul b c⟩
  refine ⟨w, hwmul, hvalue,
    nonpositiveSubring_eq_finiteSupportSubring_of_value_eq_degree w hvalue,
    negativeIdeal_eq_bot_of_value_eq_degree w hvalue, ?_, w.residueMap_surjective⟩
  exact residueMap_injective_of_value_eq_degree w hvalue

end HahnSeries.Nonpositive
