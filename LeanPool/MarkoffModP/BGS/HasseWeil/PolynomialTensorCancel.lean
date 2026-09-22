/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Cancelling a polynomial ring in a tensor product

If the `C[X]`-algebra structure on `A` extends its `C`-algebra structure, then
base change from `C[X]` to `S[X]` is canonically the same as base change from
`C` to `S`.  This file constructs the resulting explicit `S`-algebra
equivalence

`S[X] ⊗[C[X]] A ≃ₐ[S] S ⊗[C] A`

and records its values on pure tensors in both directions.
-/

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

variable (C S A : Type*)
  [CommRing C] [CommRing S] [CommRing A]
  [Algebra C S] [Algebra C A] [Algebra C[X] A]
  [IsScalarTower C C[X] A]

private noncomputable def coefficientPolynomialAlgHom :
    C[X] →ₐ[C] S[X] :=
  Polynomial.mapAlgHom (Algebra.ofId C S)

local instance coefficientPolynomialAlgebra : Algebra C[X] S[X] :=
  Polynomial.algebra C S

local instance coefficientPolynomialTower : IsScalarTower C C[X] S[X] :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro c
    simp [Polynomial.algebraMap_def])

private abbrev PolynomialTensor := TensorProduct C[X] S[X] A
private abbrev ConstantTensor := TensorProduct C S A

/-- The image of the polynomial variable in the constant tensor product. -/
noncomputable def polynomialTensorCancelEvaluationPoint :
    TensorProduct C S A :=
  Algebra.TensorProduct.includeRight (algebraMap C[X] A Polynomial.X)

private noncomputable def constantTensorPolynomialAlgHom :
    C[X] →ₐ[C] ConstantTensor C S A :=
  Polynomial.aeval (polynomialTensorCancelEvaluationPoint C S A)

/-- The `C[X]`-algebra structure on `S ⊗[C] A` obtained by evaluating `X`
at `1 ⊗ algebraMap C[X] A X`. -/
@[reducible]
noncomputable def polynomialTensorCancelTargetPolynomialAlgebra :
    Algebra C[X] (TensorProduct C S A) :=
  (constantTensorPolynomialAlgHom C S A).toAlgebra

local instance constantTensorPolynomialAlgebra :
    Algebra C[X] (ConstantTensor C S A) :=
  polynomialTensorCancelTargetPolynomialAlgebra C S A

/-- The `S[X]`-algebra structure on `S ⊗[C] A` obtained by evaluating `X`
at `1 ⊗ algebraMap C[X] A X`. -/
@[reducible]
noncomputable def polynomialTensorCancelTargetPolynomialExtensionAlgebra :
    Algebra S[X] (TensorProduct C S A) :=
  (Polynomial.aeval
    (polynomialTensorCancelEvaluationPoint C S A)).toAlgebra

local instance constantTensorPolynomialExtensionAlgebra :
    Algebra S[X] (ConstantTensor C S A) :=
  polynomialTensorCancelTargetPolynomialExtensionAlgebra C S A

local instance constantTensorPolynomialTower :
    IsScalarTower C C[X] (ConstantTensor C S A) :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro c
    change (algebraMap C S c ⊗ₜ[C] (1 : A)) =
      constantTensorPolynomialAlgHom C S A (Polynomial.C c)
    simp [constantTensorPolynomialAlgHom])

private theorem includeRight_algebraMap_polynomial (p : C[X]) :
    (Algebra.TensorProduct.includeRight :
      A →ₐ[C] ConstantTensor C S A) (algebraMap C[X] A p) =
      constantTensorPolynomialAlgHom C S A p := by
  have h :
      (Algebra.TensorProduct.includeRight :
          A →ₐ[C] ConstantTensor C S A).comp
          (IsScalarTower.toAlgHom C C[X] A) =
        constantTensorPolynomialAlgHom C S A := by
    ext
    simp [constantTensorPolynomialAlgHom,
      polynomialTensorCancelEvaluationPoint]
  simpa [Polynomial.algebraMap_def, coefficientPolynomialAlgHom] using
    DFunLike.congr_fun h p

private noncomputable def rightFactorToConstantTensor :
    A →ₐ[C[X]] ConstantTensor C S A where
  __ := (Algebra.TensorProduct.includeRight :
    A →ₐ[C] ConstantTensor C S A).toRingHom
  commutes' := includeRight_algebraMap_polynomial C S A

private noncomputable def leftFactorToConstantTensorOverS :
    S[X] →ₐ[S] ConstantTensor C S A :=
  Polynomial.aeval (polynomialTensorCancelEvaluationPoint C S A)

omit [IsScalarTower C C[X] A] in
private theorem leftFactorToConstantTensor_compatible (p : C[X]) :
    leftFactorToConstantTensorOverS C S A (algebraMap C[X] S[X] p) =
      constantTensorPolynomialAlgHom C S A p := by
  have h :
      ((leftFactorToConstantTensorOverS C S A).restrictScalars C).comp
          (coefficientPolynomialAlgHom C S) =
        constantTensorPolynomialAlgHom C S A := by
    ext
    simp [leftFactorToConstantTensorOverS,
      constantTensorPolynomialAlgHom,
      polynomialTensorCancelEvaluationPoint, coefficientPolynomialAlgHom]
  exact DFunLike.congr_fun h p

private noncomputable def leftFactorToConstantTensor :
    S[X] →ₐ[C[X]] ConstantTensor C S A where
  __ := (leftFactorToConstantTensorOverS C S A).toRingHom
  commutes' := leftFactorToConstantTensor_compatible C S A

private noncomputable def polynomialTensorToConstantTensorOverPolynomial :
    PolynomialTensor C S A →ₐ[C[X]] ConstantTensor C S A :=
  Algebra.TensorProduct.lift
    (leftFactorToConstantTensor C S A)
    (rightFactorToConstantTensor C S A)
    (fun _ _ ↦ Commute.all _ _)

private noncomputable def polynomialTensorToConstantTensor :
    PolynomialTensor C S A →ₐ[S] ConstantTensor C S A where
  __ := (polynomialTensorToConstantTensorOverPolynomial C S A).toRingHom
  commutes' s := by
    change polynomialTensorToConstantTensorOverPolynomial C S A
        ((Algebra.TensorProduct.includeLeft :
          S[X] →ₐ[S] PolynomialTensor C S A) (Polynomial.C s)) =
      algebraMap S (ConstantTensor C S A) s
    simp [polynomialTensorToConstantTensorOverPolynomial,
      leftFactorToConstantTensor, leftFactorToConstantTensorOverS]

private noncomputable def constantsToPolynomialTensor :
    S →ₐ[S] PolynomialTensor C S A :=
  (Algebra.TensorProduct.includeLeft :
      S[X] →ₐ[S] PolynomialTensor C S A).comp Polynomial.CAlgHom

private noncomputable def rightFactorToPolynomialTensor :
    A →ₐ[C] PolynomialTensor C S A :=
  (Algebra.TensorProduct.includeRight :
      A →ₐ[C[X]] PolynomialTensor C S A).restrictScalars C

private noncomputable def constantTensorToPolynomialTensor :
    ConstantTensor C S A →ₐ[S] PolynomialTensor C S A :=
  Algebra.TensorProduct.lift
    (constantsToPolynomialTensor C S A)
    (rightFactorToPolynomialTensor C S A)
    (fun _ _ ↦ Commute.all _ _)

private theorem constantTensorToPolynomialTensor_comp_leftFactor :
    (constantTensorToPolynomialTensor C S A).comp
        (leftFactorToConstantTensorOverS C S A) =
      (Algebra.TensorProduct.includeLeft :
        S[X] →ₐ[S] PolynomialTensor C S A) := by
  ext
  simp [constantTensorToPolynomialTensor,
    leftFactorToConstantTensorOverS,
    polynomialTensorCancelEvaluationPoint, rightFactorToPolynomialTensor]

private theorem constantTensorToPolynomialTensor_commutes_polynomial
    (p : C[X]) :
    constantTensorToPolynomialTensor C S A
        (algebraMap C[X] (ConstantTensor C S A) p) =
      algebraMap C[X] (PolynomialTensor C S A) p := by
  rw [show algebraMap C[X] (ConstantTensor C S A) p =
      leftFactorToConstantTensorOverS C S A
        (algebraMap C[X] S[X] p) by
    exact (leftFactorToConstantTensor_compatible C S A p).symm]
  have hp := AlgHom.congr_fun
    (constantTensorToPolynomialTensor_comp_leftFactor C S A)
      (algebraMap C[X] S[X] p)
  change constantTensorToPolynomialTensor C S A
      (leftFactorToConstantTensorOverS C S A
        (algebraMap C[X] S[X] p)) =
    Algebra.TensorProduct.includeLeft (algebraMap C[X] S[X] p) at hp
  rw [hp]
  rfl

private noncomputable def constantTensorToPolynomialTensorOverPolynomial :
    ConstantTensor C S A →ₐ[C[X]] PolynomialTensor C S A where
  __ := (constantTensorToPolynomialTensor C S A).toRingHom
  commutes' := constantTensorToPolynomialTensor_commutes_polynomial C S A

private noncomputable def polynomialTensorToConstantTensorOverCoefficientPolynomial :
    PolynomialTensor C S A →ₐ[S[X]] ConstantTensor C S A where
  __ := (polynomialTensorToConstantTensor C S A).toRingHom
  commutes' p := by
    change polynomialTensorToConstantTensor C S A
        ((Algebra.TensorProduct.includeLeft :
          S[X] →ₐ[S[X]] PolynomialTensor C S A) p) =
      leftFactorToConstantTensorOverS C S A p
    simp [polynomialTensorToConstantTensor,
      polynomialTensorToConstantTensorOverPolynomial,
      leftFactorToConstantTensor]

private noncomputable def constantTensorToPolynomialTensorOverCoefficientPolynomial :
    ConstantTensor C S A →ₐ[S[X]] PolynomialTensor C S A where
  __ := (constantTensorToPolynomialTensor C S A).toRingHom
  commutes' p := by
    have hp := AlgHom.congr_fun
      (constantTensorToPolynomialTensor_comp_leftFactor C S A) p
    change constantTensorToPolynomialTensor C S A
        (leftFactorToConstantTensorOverS C S A p) =
      (Algebra.TensorProduct.includeLeft :
        S[X] →ₐ[S[X]] PolynomialTensor C S A) p
    exact hp

private theorem constantTensorToPolynomialTensor_leftInverse :
    (constantTensorToPolynomialTensor C S A).comp
        (polynomialTensorToConstantTensor C S A) =
      AlgHom.id S (PolynomialTensor C S A) := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p a =>
      change constantTensorToPolynomialTensor C S A
          (leftFactorToConstantTensorOverS C S A p *
            rightFactorToConstantTensor C S A a) =
        p ⊗ₜ[C[X]] a
      rw [map_mul]
      have hp := AlgHom.congr_fun
        (constantTensorToPolynomialTensor_comp_leftFactor C S A) p
      change constantTensorToPolynomialTensor C S A
          (leftFactorToConstantTensorOverS C S A p) =
        Algebra.TensorProduct.includeLeft p at hp
      rw [hp]
      simp [constantTensorToPolynomialTensor,
        rightFactorToConstantTensor, rightFactorToPolynomialTensor]

private theorem constantTensorToPolynomialTensor_rightInverse :
    (polynomialTensorToConstantTensor C S A).comp
        (constantTensorToPolynomialTensor C S A) =
      AlgHom.id S (ConstantTensor C S A) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro s
    simpa [constantTensorToPolynomialTensor, constantsToPolynomialTensor] using
      (polynomialTensorToConstantTensor C S A).commutes s
  · apply AlgHom.ext
    intro a
    simp [constantTensorToPolynomialTensor,
      polynomialTensorToConstantTensor,
      polynomialTensorToConstantTensorOverPolynomial,
      rightFactorToConstantTensor, rightFactorToPolynomialTensor]

private theorem constantTensorToPolynomialTensorOverPolynomial_leftInverse :
    (constantTensorToPolynomialTensorOverPolynomial C S A).comp
        (polynomialTensorToConstantTensorOverPolynomial C S A) =
      AlgHom.id C[X] (PolynomialTensor C S A) := by
  apply AlgHom.ext
  intro z
  exact DFunLike.congr_fun
    (constantTensorToPolynomialTensor_leftInverse C S A) z

private theorem constantTensorToPolynomialTensorOverPolynomial_rightInverse :
    (polynomialTensorToConstantTensorOverPolynomial C S A).comp
        (constantTensorToPolynomialTensorOverPolynomial C S A) =
      AlgHom.id C[X] (ConstantTensor C S A) := by
  apply AlgHom.ext
  intro z
  exact DFunLike.congr_fun
    (constantTensorToPolynomialTensor_rightInverse C S A) z

private theorem
    constantTensorToPolynomialTensorOverCoefficientPolynomial_leftInverse :
    (constantTensorToPolynomialTensorOverCoefficientPolynomial C S A).comp
        (polynomialTensorToConstantTensorOverCoefficientPolynomial C S A) =
      AlgHom.id S[X] (PolynomialTensor C S A) := by
  apply AlgHom.ext
  intro z
  exact DFunLike.congr_fun
    (constantTensorToPolynomialTensor_leftInverse C S A) z

private theorem
    constantTensorToPolynomialTensorOverCoefficientPolynomial_rightInverse :
    (polynomialTensorToConstantTensorOverCoefficientPolynomial C S A).comp
        (constantTensorToPolynomialTensorOverCoefficientPolynomial C S A) =
      AlgHom.id S[X] (ConstantTensor C S A) := by
  apply AlgHom.ext
  intro z
  exact DFunLike.congr_fun
    (constantTensorToPolynomialTensor_rightInverse C S A) z

/-- Polynomial tensor cancellation as a `C[X]`-algebra equivalence, where the
target uses `polynomialTensorCancelTargetPolynomialAlgebra`. -/
noncomputable def polynomialTensorCancelOverPolynomial :
    TensorProduct C[X] S[X] A ≃ₐ[C[X]] TensorProduct C S A :=
  AlgEquiv.ofAlgHom
    (polynomialTensorToConstantTensorOverPolynomial C S A)
    (constantTensorToPolynomialTensorOverPolynomial C S A)
    (constantTensorToPolynomialTensorOverPolynomial_rightInverse C S A)
    (constantTensorToPolynomialTensorOverPolynomial_leftInverse C S A)

/-- Polynomial tensor cancellation as an `S[X]`-algebra equivalence, where
the target uses `polynomialTensorCancelTargetPolynomialExtensionAlgebra`. -/
noncomputable def polynomialTensorCancelOverCoefficientPolynomial :
    TensorProduct C[X] S[X] A ≃ₐ[S[X]] TensorProduct C S A :=
  AlgEquiv.ofAlgHom
    (polynomialTensorToConstantTensorOverCoefficientPolynomial C S A)
    (constantTensorToPolynomialTensorOverCoefficientPolynomial C S A)
    (constantTensorToPolynomialTensorOverCoefficientPolynomial_rightInverse
      C S A)
    (constantTensorToPolynomialTensorOverCoefficientPolynomial_leftInverse
      C S A)

/-- Cancelling the polynomial base change in a tensor product. -/
noncomputable def polynomialTensorCancel :
    TensorProduct C[X] S[X] A ≃ₐ[S] TensorProduct C S A :=
  AlgEquiv.ofAlgHom
    (polynomialTensorToConstantTensor C S A)
    (constantTensorToPolynomialTensor C S A)
    (constantTensorToPolynomialTensor_rightInverse C S A)
    (constantTensorToPolynomialTensor_leftInverse C S A)

@[simp]
theorem polynomialTensorCancelOverPolynomial_apply
    (z : TensorProduct C[X] S[X] A) :
    polynomialTensorCancelOverPolynomial C S A z =
      polynomialTensorCancel C S A z := by
  rfl

@[simp]
theorem polynomialTensorCancelOverPolynomial_symm_apply
    (z : TensorProduct C S A) :
    (polynomialTensorCancelOverPolynomial C S A).symm z =
      (polynomialTensorCancel C S A).symm z := by
  rfl

@[simp]
theorem polynomialTensorCancelOverCoefficientPolynomial_apply
    (z : TensorProduct C[X] S[X] A) :
    polynomialTensorCancelOverCoefficientPolynomial C S A z =
      polynomialTensorCancel C S A z := by
  rfl

@[simp]
theorem polynomialTensorCancelOverCoefficientPolynomial_symm_apply
    (z : TensorProduct C S A) :
    (polynomialTensorCancelOverCoefficientPolynomial C S A).symm z =
      (polynomialTensorCancel C S A).symm z := by
  rfl

@[simp]
theorem polynomialTensorCancel_tmul (p : S[X]) (a : A) :
    polynomialTensorCancel C S A (p ⊗ₜ[C[X]] a) =
      Polynomial.aeval (polynomialTensorCancelEvaluationPoint C S A) p *
        (1 ⊗ₜ[C] a) := by
  rfl

@[simp]
theorem polynomialTensorCancel_symm_tmul (s : S) (a : A) :
    (polynomialTensorCancel C S A).symm (s ⊗ₜ[C] a) =
      Polynomial.C s ⊗ₜ[C[X]] a := by
  simp [polynomialTensorCancel, constantTensorToPolynomialTensor,
    constantsToPolynomialTensor, rightFactorToPolynomialTensor]

end

end BGS.HasseWeil
