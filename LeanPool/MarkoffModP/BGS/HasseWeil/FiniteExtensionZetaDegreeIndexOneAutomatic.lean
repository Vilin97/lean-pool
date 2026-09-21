/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionClosedPlaceSplittingFormula
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZetaDegreeIndexOneFromAllCounts
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionStandardZetaRationality

/-!
# Automatic divisor-degree index one

The exact constant-extension splitting formula supplies the sole geometric
hypothesis of the noncircular F. K. Schmidt argument.  Consequently a finite
separable function field with exact constants has divisor-degree index one.
-/

open scoped Polynomial

namespace BGS.HasseWeil

noncomputable section

variable (C N : Type*) [Field C] [Fintype C]
  [DecidableEq C] [DecidableEq (RatFunc C)]
  [Field N] [Algebra (RatFunc C) N]
  [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]

local instance automaticIndexOneBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance automaticIndexOneBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- F. K. Schmidt's divisor-index-one theorem, with the constant-extension
closed-place identity discharged internally. -/
theorem finiteExtensionDivisorDegreeIndex_eq_one_of_exactConstants
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) :
    finiteExtensionDivisorDegreeIndex C N = 1 := by
  apply
    finiteExtensionDivisorDegreeIndex_eq_one_of_all_exactConstantExtension_closedPlaceCount
      C N hExact
  intro S _ _ _ _ _ level
  rw [exactConstantExtensionClosedPlaceExtensionCount_eq_classical_decidableEq]
  have hcount := exactConstantExtensionClosedPlaceExtensionCount_eq
    C S N hExact level
  convert hcount using 1 <;> congr 1

/-- Exact constants now give the standard curve zeta form without a separate
divisor-index hypothesis. -/
theorem exists_finiteExtensionClosedPlaceZeta_rational_with_genus_degree_bound_of_exactConstants
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧
        P.eval 1 ≠ 0 ∧
        P.natDegree < 2 * FunctionField.genus C N + 2 ∧
        HasCurveZetaRationalForm
          (formalPointCountZeta
            (finiteExtensionClosedPlaceExtensionCount C N))
          (Nat.card C) P := by
  exact exists_finiteExtensionClosedPlaceZeta_rational_with_genus_degree_bound
    C N hExact
      (finiteExtensionDivisorDegreeIndex_eq_one_of_exactConstants
        C N hExact)

/-- Exact constants and an intrinsic genus budget give the standard zeta
trace package with no remaining degree-index premise. -/
theorem exists_finiteExtensionClosedPlaceZeta_trace_with_degree_budget_of_exactConstants
    (budget : ℕ)
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hgenus : FunctionField.genus C N ≤ budget) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧
        P.eval 1 ≠ 0 ∧
        P.natDegree ≤ 2 * budget + 1 ∧
        HasCurveZetaRationalForm
          (formalPointCountZeta
            (finiteExtensionClosedPlaceExtensionCount C N))
          (Nat.card C) P ∧
        HasZetaNumeratorPointCountFormula
          (Nat.card C)
          (finiteExtensionClosedPlaceExtensionCount C N) P := by
  exact exists_finiteExtensionClosedPlaceZeta_trace_with_degree_budget
    C N budget hExact
      (finiteExtensionDivisorDegreeIndex_eq_one_of_exactConstants
        C N hExact)
      hgenus

end

end BGS.HasseWeil
