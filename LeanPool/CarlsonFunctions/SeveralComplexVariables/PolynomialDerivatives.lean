/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.SeveralComplexVariables.Derivatives
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Analytic.Polynomial

/-! # Formal and analytic coordinate derivatives of complex polynomials -/

@[expose] public noncomputable section
namespace MvPolynomial
variable {ι : Type*}

open scoped Classical in
/-- Formal partial differentiation agrees with differentiating a coordinate slice.
No finiteness assumption on the variable type is needed. -/
theorem hasDerivAt_eval_update (p : MvPolynomial ι ℂ) (z : ι → ℂ) (i : ι) (x : ℂ) :
    HasDerivAt (fun w => p.eval (Function.update z i w))
      ((pderiv i p).eval (Function.update z i x)) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const x c
  | add p q hp hq => simpa using! hp.add hq
  | mul_X p j hp =>
    by_cases h : j = i
    · subst j
      simpa [pderiv_mul, mul_comm, add_comm] using! hp.mul (hasDerivAt_id x)
    · simpa [pderiv_mul, h, Ne.symm h, mul_comm] using! hp.mul (hasDerivAt_const x (z j))

/-- Coordinate differentiation of a polynomial is evaluation of its formal derivative. -/
theorem partialDeriv_eval  (p : MvPolynomial ι ℂ) (z : ι → ℂ) (i : ι) :
    SeveralComplexVariables.partialDeriv i (fun w => p.eval w) z = (pderiv i p).eval z := by
  simpa [SeveralComplexVariables.partialDeriv] using (p.hasDerivAt_eval_update z i (z i)).deriv

end MvPolynomial
