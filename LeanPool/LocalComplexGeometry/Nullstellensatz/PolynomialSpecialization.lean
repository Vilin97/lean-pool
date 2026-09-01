/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Germs.Representatives
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Order.Filter.Finite

/-!
# Specializing polynomial identities of function germs

A polynomial identity between germs has only finitely many nonzero
coefficients.  Consequently representatives of its coefficients satisfy the
corresponding pointwise complex-polynomial identity on one common
neighborhood.  This is the finite-uniformity step needed when cleared generic
fiber identities are specialized over the analytic base.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

/-- The ring homomorphism sending a function to its germ at the origin. -/
def functionToGermRingHom (n : ℕ) :
    (ComplexEuclidean n → ℂ) →+* FunctionGerm n :=
  Filter.Germ.coeRingHom (𝓝 (0 : ComplexEuclidean n))

/-- A polynomial identity after passing from coefficient functions to their
germs holds pointwise after specializing the coefficient functions on a
single neighborhood of the origin. -/
theorem eventually_polynomial_map_eval_eq_of_map_germ_eq {n : ℕ}
    (p q : Polynomial (ComplexEuclidean n → ℂ))
    (hmap : p.map (functionToGermRingHom n) =
      q.map (functionToGermRingHom n)) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      p.map (Pi.evalRingHom (fun _ : ComplexEuclidean n ↦ ℂ) z) =
        q.map (Pi.evalRingHom (fun _ : ComplexEuclidean n ↦ ℂ) z) := by
  classical
  let S : Finset ℕ := p.support ∪ q.support
  have hcoeff (k : ℕ) :
      (p.coeff k : FunctionGerm n) = (q.coeff k : FunctionGerm n) := by
    have hk := congrArg (fun r : Polynomial (FunctionGerm n) ↦ r.coeff k) hmap
    simpa [functionToGermRingHom] using hk
  have hevent (k : ℕ) :
      ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n), p.coeff k z = q.coeff k z :=
    Filter.Germ.coe_eq.mp (hcoeff k)
  have hall :
      ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
        ∀ k ∈ S, p.coeff k z = q.coeff k z :=
    S.eventually_all.2 fun k hk ↦ hevent k
  filter_upwards [hall] with z hz
  apply Polynomial.ext
  intro k
  simp only [Polynomial.coeff_map]
  by_cases hk : k ∈ S
  · exact hz k hk
  · have hkp : k ∉ p.support := fun h ↦ hk (Finset.mem_union_left _ h)
    have hkq : k ∉ q.support := fun h ↦ hk (Finset.mem_union_right _ h)
    rw [Polynomial.notMem_support_iff.mp hkp,
      Polynomial.notMem_support_iff.mp hkq]

/-- Eventual equality of coefficient functions gives eventual equality of
their fixed polynomial evaluations at every last-coordinate value. -/
theorem eventually_polynomial_eval_eq_of_map_germ_eq {n : ℕ}
    (p q : Polynomial (ComplexEuclidean n → ℂ))
    (hmap : p.map (functionToGermRingHom n) =
      q.map (functionToGermRingHom n)) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n), ∀ w : ℂ,
      (p.map (Pi.evalRingHom (fun _ : ComplexEuclidean n ↦ ℂ) z)).eval w =
        (q.map (Pi.evalRingHom (fun _ : ComplexEuclidean n ↦ ℂ) z)).eval w := by
  filter_upwards [eventually_polynomial_map_eval_eq_of_map_germ_eq p q hmap]
    with z hz
  intro w
  rw [hz]

end

end LocalComplexGeometry
