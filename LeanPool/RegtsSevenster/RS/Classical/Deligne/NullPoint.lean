/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Complex points of finite-type algebras

Every nonzero commutative ℂ-algebra of finite type admits a
ℂ-point: quotient by a maximal ideal, apply Zariski's lemma over
the Jacobson ring ℂ, and lift to the algebraically closed base.
This is the Nullstellensatz input of the descent's final step.
-/

namespace RS

/-- **The ℂ-point**: a nonzero finite-type commutative ℂ-algebra
maps onto ℂ. -/
theorem exists_algHom_complex (R : Type*) [CommRing R]
    [Algebra ℂ R] [Nontrivial R] [Algebra.FiniteType ℂ R] :
    Nonempty (R →ₐ[ℂ] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  haveI := hm
  letI := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (R ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing ℂ (R ⧸ m)
  haveI : Algebra.IsAlgebraic ℂ (R ⧸ m) :=
    Algebra.IsAlgebraic.of_finite ℂ (R ⧸ m)
  exact ⟨(IsAlgClosed.lift (M := ℂ)).comp (Ideal.Quotient.mkₐ ℂ m)⟩

end RS
