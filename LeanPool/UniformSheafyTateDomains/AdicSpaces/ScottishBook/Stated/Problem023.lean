/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.CompletedAlgClosure

/-!
# Nonarchimedean Scottish Book — Problem 23

**Proposer:** Kiran Kedlaya
**Date:** 28 April 2016

## Problem Statement

Let K = completed algebraic closure of F_p((t)). Let f: K → K be a
continuous endomorphism. If f(t) is not integral over the maximal
tamely ramified extension, is f non-surjective?

## Notes

None.

## Status

Open.

## Mathematical Background

Let `K` denote the completed algebraic closure of `F_p((t))`, i.e.,
the completion of `AlgebraicClosure(F_p((t)))` with respect to the
unique extension of the `t`-adic valuation.  This is a complete,
algebraically closed nonarchimedean field of characteristic `p`.

A continuous endomorphism `f : K → K` is a ring homomorphism that is
continuous with respect to the nonarchimedean topology on `K`.  Such
endomorphisms are determined by the image `f(t)` of the uniformizer
`t`, but not every element of `K` arises as `f(t)` for a continuous
endomorphism.

The **maximal tamely ramified extension** of `F_p((t))` is the largest
algebraic extension whose ramification indices are all coprime to `p`.
An element `x ∈ K` is **integral over the maximal tamely ramified
extension** if it satisfies a monic polynomial with coefficients in this
subfield.

The problem conjectures that if `f(t)` is sufficiently "wild" (not
integral over the tame closure), then `f` cannot be surjective.

## Definitions formalized

1. `CompletedAlgClosure p` — the completed algebraic closure of F_p((t))
   (from `CompletedAlgClosure.lean`)
2. `CompletedAlgClosure.ContinuousEnd p` — continuous endomorphisms
3. `CompletedAlgClosure.IsIntegralOverMaxTame` — integrality over the
   maximal tamely ramified extension
4. `problem23` — the open problem statement

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 23
-/

open ScottishBook

namespace ScottishBook

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- **Scottish Book Problem 23** (Kedlaya, 28 Apr 2016, open):

*Let `K` be the completed algebraic closure of `F_p((t))`, and let
`f : K → K` be a continuous endomorphism.  If `f(t)` is not integral
over the maximal tamely ramified extension of `F_p((t))`, then `f` is
not surjective.*

The hypothesis `hnt` asserts that `f(t)` does not lie in the integral
closure of the maximal tamely ramified subfield of `K`.  The conclusion
is that `f` (viewed as a ring homomorphism `K →+* K`) fails to be
surjective.

This is an **open problem** — the `sorry` is intentional. -/
theorem problem23
    (f : CompletedAlgClosure.ContinuousEnd p)
    (hnt : ¬ CompletedAlgClosure.IsIntegralOverMaxTame p
      (f.toRingHom (CompletedAlgClosure.t p))) :
    ¬ Function.Surjective f.toRingHom := by
  sorry

end ScottishBook
