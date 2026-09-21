/-
Copyright (c) 2026 the authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira
-/
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Examples

Supporting results for Nagata’s factoriality theorem.
-/

namespace NagataFactoriality

open Polynomial

theorem int_uniqueFactorizationMonoid : UniqueFactorizationMonoid ℤ := by
  infer_instance

theorem int_polynomial_uniqueFactorizationMonoid : UniqueFactorizationMonoid ℤ[X] := by
  infer_instance

theorem mvPolynomial_uniqueFactorizationMonoid (n : ℕ) (k : Type*) [Field k] :
    UniqueFactorizationMonoid (MvPolynomial (Fin n) k) := by
  infer_instance

theorem iterated_polynomial_uniqueFactorizationMonoid (k : Type*) [Field k] :
    UniqueFactorizationMonoid (Polynomial (Polynomial k)) := by
  infer_instance

end NagataFactoriality
