/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Internal.NormalForm

/-!
# Polynomial-time normal forms

`P` and `FP` membership can be witnessed by deterministic machines whose
running-time bounds are evaluations of polynomials with natural coefficients.
Unlike the arbitrary asymptotic witnesses in the class definitions, these
normalized bounds are valid on every input length and are monotone.

## Main result

- `mem_P_iff_decidesInTime_polynomial` — polynomial-evaluation normal form for `P`
- `mem_FP_iff_computesInTime_polynomial` — polynomial-evaluation normal form for `FP`
-/


public section

namespace Complexity

/-- A language belongs to `P` exactly when some deterministic machine decides
it within the evaluation of a natural-coefficient polynomial. -/
theorem mem_P_iff_decidesInTime_polynomial {L : Language} :
    L ∈ P ↔ ∃ (k : ℕ) (tm : TM k) (p : Polynomial ℕ),
      tm.DecidesInTime L p.eval := by
  exact mem_P_iff_decidesInTime_polynomial_internal

/-- A function belongs to `FP` exactly when some deterministic machine
computes it within the evaluation of a natural-coefficient polynomial. -/
theorem mem_FP_iff_computesInTime_polynomial {f : List Bool → List Bool} :
    f ∈ FP ↔ ∃ (k : ℕ) (tm : TM k) (p : Polynomial ℕ),
      tm.ComputesInTime f p.eval := by
  exact mem_FP_iff_computesInTime_polynomial_internal

end Complexity
