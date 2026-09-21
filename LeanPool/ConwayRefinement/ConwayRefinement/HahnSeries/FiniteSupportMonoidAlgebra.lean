/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupport
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Finite-support Hahn series as an additive monoid algebra

Finite-support nonpositive Hahn series are canonically the additive monoid algebra on the monoid
of nonpositive exponents. The equivalence is defined without a choice of basis: its inverse sends
each formal monomial to the corresponding Hahn monomial, and its forward map reads coefficients.

This algebra equivalence is the multiplicative strengthening of `finiteSupportFinsuppEquiv`.
-/

open scoped HahnSeries

universe u v

namespace HahnSeries.Nonpositive

public noncomputable section

variable {G : Type u} {K : Type v}
  [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [CommRing K]

/-- The monoid homomorphism sending a formal nonpositive exponent to its Hahn monomial. -/
def finiteSupportMonomialHom :
    Multiplicative (exponentMonoid G) →* FiniteSupportRing (G := G) (K := K) where
  toFun g := finiteSupportMonomial (K := K) g.toAdd
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_finiteSupportMonomial]
    exact HahnSeries.single_zero_one
  map_mul' g h := by
    rw [finiteSupportMonomial_mul]
    apply congrArg (finiteSupportMonomial (K := K))
    apply Subtype.ext
    rfl

/-- Evaluate a finite formal sum of monomials as a finite-support Hahn series. -/
def finiteSupportAddMonoidAlgebraToSeries :
    AddMonoidAlgebra K (exponentMonoid G) →ₐ[K]
      FiniteSupportRing (G := G) (K := K) :=
  AddMonoidAlgebra.lift K _ _ finiteSupportMonomialHom

/-- Reading coefficients after evaluating a formal sum returns the original coefficient
function. -/
@[simp]
theorem finiteSupportCoefficients_toSeries
    (f : AddMonoidAlgebra K (exponentMonoid G)) :
    finiteSupportCoefficients (finiteSupportAddMonoidAlgebraToSeries f) =
      AddMonoidAlgebra.coeff f := by
  induction f using AddMonoidAlgebra.induction_on with
  | of g =>
      rw [AddMonoidAlgebra.of_apply]
      rw [finiteSupportAddMonoidAlgebraToSeries, AddMonoidAlgebra.lift_single]
      rw [one_smul]
      change finiteSupportCoefficients
        (finiteSupportMonomialHom (Multiplicative.ofAdd g)) =
          AddMonoidAlgebra.coeff (AddMonoidAlgebra.single g 1)
      rw [show finiteSupportMonomialHom (Multiplicative.ofAdd g) =
        finiteSupportMonomial (K := K) g from rfl]
      rw [finiteSupportCoefficients_monomial]
      rfl
  | add f g hf hg =>
      rw [map_add, map_add, hf, hg]
      exact (AddMonoidAlgebra.coeff_add f g).symm
  | smul k f hf =>
      rw [map_smul, map_smul, hf]
      exact (AddMonoidAlgebra.coeff_smul k f).symm

theorem finiteSupportAddMonoidAlgebraToSeries_bijective :
    Function.Bijective (finiteSupportAddMonoidAlgebraToSeries (G := G) (K := K)) := by
  constructor
  · intro f g hfg
    apply AddMonoidAlgebra.coeff_injective
    rw [← finiteSupportCoefficients_toSeries f,
      ← finiteSupportCoefficients_toSeries g, hfg]
  · intro b
    refine ⟨AddMonoidAlgebra.ofCoeff (finiteSupportFinsuppEquiv b), ?_⟩
    apply finiteSupportFinsuppEquiv.injective
    rw [finiteSupportFinsuppEquiv_apply, finiteSupportFinsuppEquiv_apply,
      finiteSupportCoefficients_toSeries, AddMonoidAlgebra.coeff_ofCoeff]

/-- The canonical algebra equivalence between finite-support nonpositive Hahn series and the
additive monoid algebra on nonpositive exponents. -/
def finiteSupportAddMonoidAlgebraEquiv :
    FiniteSupportRing (G := G) (K := K) ≃ₐ[K]
      AddMonoidAlgebra K (exponentMonoid G) :=
  (AlgEquiv.ofBijective finiteSupportAddMonoidAlgebraToSeries
    finiteSupportAddMonoidAlgebraToSeries_bijective).symm

/-- The inverse algebra equivalence evaluates formal sums as Hahn series. -/
@[simp]
theorem finiteSupportAddMonoidAlgebraEquiv_symm_apply
    (f : AddMonoidAlgebra K (exponentMonoid G)) :
    finiteSupportAddMonoidAlgebraEquiv.symm f =
      finiteSupportAddMonoidAlgebraToSeries f :=
  (rfl)

/-- The forward algebra equivalence reads the Hahn-series coefficient function. -/
@[simp]
theorem coeff_finiteSupportAddMonoidAlgebraEquiv
    (b : FiniteSupportRing (G := G) (K := K)) :
    AddMonoidAlgebra.coeff (finiteSupportAddMonoidAlgebraEquiv b) =
      finiteSupportCoefficients b := by
  have h := congrArg finiteSupportCoefficients
    (finiteSupportAddMonoidAlgebraEquiv.symm_apply_apply b)
  rw [finiteSupportAddMonoidAlgebraEquiv_symm_apply,
    finiteSupportCoefficients_toSeries] at h
  exact h

/-- A Hahn monomial corresponds to the formal monomial with coefficient one. -/
@[simp]
theorem finiteSupportAddMonoidAlgebraEquiv_monomial
    (g : exponentMonoid G) :
    finiteSupportAddMonoidAlgebraEquiv (finiteSupportMonomial (K := K) g) =
      AddMonoidAlgebra.single g 1 := by
  apply AddMonoidAlgebra.coeff_injective
  rw [coeff_finiteSupportAddMonoidAlgebraEquiv,
    finiteSupportCoefficients_monomial]
  rfl

end

end HahnSeries.Nonpositive
