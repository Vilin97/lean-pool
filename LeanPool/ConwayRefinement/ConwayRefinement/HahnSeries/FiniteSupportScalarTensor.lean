/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportScalarExtension
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# Scalar extension as a tensor product for finite-support Hahn series

For commutative rings `K` and `L` with a `K`-algebra structure on `L`, finite-support
nonpositive Hahn series over `L` are the scalar extension of the corresponding ring over `K`.
The equivalence is transported through the canonical additive-monoid-algebra presentation, so it
does not choose a basis or enumerate the support.

This is the generic base-change identification used for the localization of the principal graded
ring in LM24, Section 6.3.
-/

open scoped HahnSeries TensorProduct

universe u v w

namespace HahnSeries.Nonpositive

public noncomputable section

variable {G : Type u} {K : Type v} {L : Type w}
  [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
  [CommRing K] [CommRing L] [Algebra K L]

/-- Base change of finite-support nonpositive Hahn series along a commutative-ring algebra. -/
def finiteSupportScalarTensorEquiv :
    L ⊗[K] FiniteSupportRing (G := G) (K := K) ≃ₐ[L]
      FiniteSupportRing (G := G) (K := L) :=
  (Algebra.TensorProduct.congr
      (AlgEquiv.refl : L ≃ₐ[L] L)
      (finiteSupportAddMonoidAlgebraEquiv (G := G) (K := K))).trans
    ((AddMonoidAlgebra.scalarTensorEquiv K L).trans
      (finiteSupportAddMonoidAlgebraEquiv (G := G) (K := L)).symm)

/-- On a pure tensor, finite-support scalar base change multiplies the constant series by the
coefficientwise scalar extension. -/
theorem finiteSupportScalarTensorEquiv_tmul
    (l : L) (p : FiniteSupportRing (G := G) (K := K)) :
    finiteSupportScalarTensorEquiv (G := G) (K := K) (L := L) (l ⊗ₜ p) =
      finiteSupportScalarHom (G := G) l * finiteSupportScalarExtension p := by
  have hscalar :
      finiteSupportAddMonoidAlgebraEquiv
          (finiteSupportScalarHom (G := G) l) =
        AddMonoidAlgebra.single 0 l := by
    change finiteSupportAddMonoidAlgebraEquiv
        (algebraMap L (FiniteSupportRing (G := G) (K := L)) l) = _
    rw [AlgEquiv.commutes]
    rfl
  rw [finiteSupportScalarTensorEquiv]
  simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  rw [AddMonoidAlgebra.scalarTensorEquiv_tmul]
  apply finiteSupportAddMonoidAlgebraEquiv.injective
  rw [finiteSupportAddMonoidAlgebraEquiv.apply_symm_apply, map_mul, hscalar]
  rw [finiteSupportAddMonoidAlgebraEquiv_scalarExtension]
  simp only [Algebra.smul_def]
  congr 1

end

end HahnSeries.Nonpositive
