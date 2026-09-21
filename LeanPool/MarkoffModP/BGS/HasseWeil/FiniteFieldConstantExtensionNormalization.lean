/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteFieldPolynomialNormalization
import LeanPool.MarkoffModP.BGS.HasseWeil.PolynomialTensorCancel

/-!
# Normalization in a finite constant extension

Let `N` be a `C[X]`-algebra and let `S / C` be a finite extension of finite
fields.  Combining smooth base change for integral closure with explicit
polynomial tensor cancellation gives

`S ⊗[C] integralClosure C[X] N ≃ integralClosure S[X] (S ⊗[C] N)`.

The normalization comparison is first kept over `S[X]`, so it transports
contractions of height-one primes to the polynomial base.  Its restriction
to `S` is retained for residue-field dimension calculations.  The values of
both equivalences on pure tensors are recorded explicitly.
-/

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

variable (C S N : Type*) [Field C] [Field S] [Algebra C S]
  [CommRing N] [Algebra C[X] N]

local instance normalizationBaseConstantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap C[X] N).comp (algebraMap C C[X]))

local instance normalizationBaseConstantPolynomialTower :
    IsScalarTower C C[X] N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance normalizationCoefficientPolynomialAlgebra :
    Algebra C[X] S[X] :=
  Polynomial.algebra C S

/-- The polynomial algebra structure on the constant-extended ambient ring.
It sends `X` to `1 ⊗ algebraMap C[X] N X`.  This public name lets downstream
function-field constructions install exactly the same algebra structure. -/
@[reducible]
noncomputable def constantExtensionTensorPolynomialAlgebra :
    Algebra S[X] (S ⊗[C] N) :=
  polynomialTensorCancelTargetPolynomialExtensionAlgebra C S N

/-- The matching polynomial algebra structure on the constant tensor of the
original normalization. -/
@[reducible]
noncomputable def constantExtensionNormalizationTensorPolynomialAlgebra :
    Algebra S[X] (S ⊗[C] integralClosure C[X] N) :=
  polynomialTensorCancelTargetPolynomialExtensionAlgebra C S
    (integralClosure C[X] N)

local instance normalizationTargetPolynomialAlgebra :
    Algebra S[X] (S ⊗[C] N) :=
  constantExtensionTensorPolynomialAlgebra C S N

local instance normalizationSourcePolynomialAlgebra :
    Algebra S[X] (S ⊗[C] integralClosure C[X] N) :=
  constantExtensionNormalizationTensorPolynomialAlgebra C S N

local instance normalizationTargetConstantAlgebra : Algebra S (S ⊗[C] N) :=
  Algebra.TensorProduct.leftAlgebra

local instance normalizationTargetConstantPolynomialTower :
    IsScalarTower S S[X] (S ⊗[C] N) :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro s
    change s ⊗ₜ[C] (1 : N) =
      Polynomial.aeval
        (polynomialTensorCancelEvaluationPoint C S N) (Polynomial.C s)
    simp)

local instance normalizationTargetIntegralClosureConstantAlgebra :
    Algebra S (integralClosure S[X] (S ⊗[C] N)) :=
  RingHom.toAlgebra
    ((algebraMap S[X] (integralClosure S[X] (S ⊗[C] N))).comp
      (algebraMap S S[X]))

/-- After a finite extension of finite constants, normalization commutes with
constant extension as an equivalence over the polynomial ring `S[X]`. -/
noncomputable def finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv
    [Fintype C] [Finite S] :
    S ⊗[C] integralClosure C[X] N ≃ₐ[S[X]]
      integralClosure S[X] (S ⊗[C] N) :=
  (polynomialTensorCancelOverCoefficientPolynomial C S
      (integralClosure C[X] N)).symm |>.trans
    (finiteFieldPolynomialIntegralClosureBaseChangeAlgEquiv C S N) |>.trans
    (polynomialTensorCancelOverCoefficientPolynomial C S N).mapIntegralClosure

/-- The polynomial-algebra normalization equivalence sends a pure tensor to
the corresponding pure tensor in the extended ambient algebra. -/
@[simp]
theorem finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv_tmul
    [Fintype C] [Finite S]
    (s : S) (a : integralClosure C[X] N) :
    (((finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv C S N)
        (s ⊗ₜ[C] a) : integralClosure S[X] (S ⊗[C] N)) :
      S ⊗[C] N) =
      s ⊗ₜ[C] (a : N) := by
  simp [finiteFieldConstantExtensionIntegralClosurePolynomialAlgEquiv,
    finiteFieldPolynomialIntegralClosureBaseChangeAlgEquiv,
    polynomialIntegralClosureBaseChangeAlgEquiv,
    TensorProduct.toIntegralClosure]

/-- After a finite extension of finite constants, the normalization is the
constant tensor extension of the original normalization. -/
noncomputable def finiteFieldConstantExtensionIntegralClosureAlgEquiv
    [Fintype C] [Finite S] :
    S ⊗[C] integralClosure C[X] N ≃ₐ[S]
      integralClosure S[X] (S ⊗[C] N) := by
  letI : Algebra S[X] (S[X] ⊗[C[X]] N) :=
    Algebra.TensorProduct.leftAlgebra
  letI : Algebra S (S[X] ⊗[C[X]] integralClosure C[X] N) :=
    Algebra.TensorProduct.leftAlgebra
  let e : S[X] ⊗[C[X]] integralClosure C[X] N ≃+*
      integralClosure S[X] (S ⊗[C] N) :=
    (finiteFieldPolynomialIntegralClosureBaseChangeAlgEquiv C S N).toRingEquiv.trans
      (polynomialTensorCancelOverCoefficientPolynomial C S N).mapIntegralClosure.toRingEquiv
  exact
    { (polynomialTensorCancel C S
        (integralClosure C[X] N)).symm.toRingEquiv.trans e with
      commutes' := fun s => by
        apply Subtype.ext
        simp [e, finiteFieldPolynomialIntegralClosureBaseChangeAlgEquiv,
          polynomialIntegralClosureBaseChangeAlgEquiv,
          TensorProduct.toIntegralClosure]
        change s ⊗ₜ[C] (1 : N) =
          algebraMap S[X] (S ⊗[C] N) (Polynomial.C s)
        change s ⊗ₜ[C] (1 : N) =
          Polynomial.aeval
            (polynomialTensorCancelEvaluationPoint C S N) (Polynomial.C s)
        simp }

/-- The normalization equivalence sends a pure tensor to the corresponding
pure tensor in the extended function algebra. -/
@[simp]
theorem finiteFieldConstantExtensionIntegralClosureAlgEquiv_tmul
    [Fintype C] [Finite S]
    (s : S) (a : integralClosure C[X] N) :
    (((finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N)
        (s ⊗ₜ[C] a) : integralClosure S[X] (S ⊗[C] N)) :
      S ⊗[C] N) =
      s ⊗ₜ[C] (a : N) := by
  simp [finiteFieldConstantExtensionIntegralClosureAlgEquiv,
    finiteFieldPolynomialIntegralClosureBaseChangeAlgEquiv,
    polynomialIntegralClosureBaseChangeAlgEquiv,
    TensorProduct.toIntegralClosure]

/-- The normalization comparison with its constant-algebra structures erased.
This is the stable interface for constructions that only need the underlying
ring map and should not depend on the particular `S`-algebra instances used to
build the comparison. -/
noncomputable def finiteFieldConstantExtensionIntegralClosureRingEquiv
    [Fintype C] [Finite S] :
    S ⊗[C] integralClosure C[X] N ≃+*
      integralClosure S[X] (S ⊗[C] N) :=
  (finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N).toRingEquiv

/-- The instance-free normalization comparison has the expected value on a
pure tensor. -/
@[simp]
theorem finiteFieldConstantExtensionIntegralClosureRingEquiv_tmul
    [Fintype C] [Finite S]
    (s : S) (a : integralClosure C[X] N) :
    (((finiteFieldConstantExtensionIntegralClosureRingEquiv C S N)
        (s ⊗ₜ[C] a) : integralClosure S[X] (S ⊗[C] N)) :
      S ⊗[C] N) =
      s ⊗ₜ[C] (a : N) :=
  finiteFieldConstantExtensionIntegralClosureAlgEquiv_tmul C S N s a

end


end BGS.HasseWeil
