/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Normalization after finite constant extension

Smooth base change commutes with integral closure.  Applied to the coefficient
extension `C[X] → S[X]`, this identifies the base change of the normalization
of a `C[X]`-algebra with the normalization of its polynomial base change.

The first declaration records the general smooth statement.  The second
specializes it to finite fields: finiteness makes `S / C` finite type, while
the perfectness of `C` supplies formal smoothness.
-/

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

variable (C S N : Type*) [Field C] [Field S] [Algebra C S]
  [CommRing N] [Algebra C[X] N]

local instance finiteFieldNormalizationPolynomialCoefficientAlgebra :
    Algebra C[X] S[X] :=
  Polynomial.algebra C S

/-- Smooth coefficient extension commutes with normalization over the
polynomial base. -/
noncomputable def polynomialIntegralClosureBaseChangeAlgEquiv
    [Algebra.Smooth C S] :
    S[X] ⊗[C[X]] integralClosure C[X] N ≃ₐ[S[X]]
      integralClosure S[X] (S[X] ⊗[C[X]] N) := by
  letI : Algebra.Smooth C[X] (C[X] ⊗[C] S) := inferInstance
  letI : Algebra.Smooth C[X] S[X] :=
    Algebra.Smooth.of_equiv (Algebra.IsPushout.equiv C C[X] S S[X])
  exact AlgEquiv.ofBijective
    (TensorProduct.toIntegralClosure C[X] S[X] N)
    TensorProduct.toIntegralClosure_bijective_of_smooth

/-- For an extension of finite fields, coefficient extension commutes with
normalization over the polynomial base. -/
noncomputable def finiteFieldPolynomialIntegralClosureBaseChangeAlgEquiv
    [Fintype C] [Finite S] :
    S[X] ⊗[C[X]] integralClosure C[X] N ≃ₐ[S[X]]
      integralClosure S[X] (S[X] ⊗[C[X]] N) := by
  letI : Algebra.Smooth C S :=
    { formallySmooth := inferInstance
      finitePresentation :=
        Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  exact polynomialIntegralClosureBaseChangeAlgEquiv C S N

end


end BGS.HasseWeil
