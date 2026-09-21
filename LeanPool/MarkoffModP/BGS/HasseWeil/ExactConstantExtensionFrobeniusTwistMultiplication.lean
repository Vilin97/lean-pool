/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistConstants
import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionFrobeniusTwistDegree

/-!
# Multiplication presentation of Frobenius-twist constant extensions

Let `T = S ⊗[C] N`, and let `F_g` be a Frobenius-twist fixed field in
`T`.  The multiplication map from `S ⊗[C] F_g` to `T` is an equivalence
over the original function-field base.  Thus every twist becomes the same
top field after extending constants from `C` to `S`.

This is the field-level transport needed to compare the differents, genera,
and Riemann budgets of all twists without identifying the twist fields over
`C(X)` themselves.
-/

open scoped TensorProduct

namespace BGS.HasseWeil

noncomputable section


variable (C L N S : Type*) [Field C] [Field L] [Field N] [Field S]
  [Algebra C L] [Algebra L N] [Algebra C N] [IsScalarTower C L N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
  [FiniteDimensional L N] [IsGalois L N]
  [Fintype C] [Finite S]

/-- Multiplication identifies the constant extension of a Frobenius-twist
field with the common exact constant extension. -/
noncomputable def exactConstantExtensionFrobeniusTwistMultiplicationAlgEquiv
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[L] N)
    (hdiv : Nat.card (N ≃ₐ[L] N) ∣ Module.finrank C S) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C L N S
    let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
    letI : Algebra C F := Algebra.restrictScalars C L F
    let hExactF :=
      exactConstantExtensionFrobeniusTwistField_algebraicClosure_eq_bot
        C L N S hExact g
    letI := exactConstantExtensionField C F S hExactF
    letI := exactConstantExtensionBaseAlgebra C L F S
    ExactConstantExtension C F S ≃ₐ[L] ExactConstantExtension C N S := by
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  have hCLT : algebraMap C T =
      (algebraMap L T).comp (algebraMap C L) := by
    ext c
    change algebraMap C S c ⊗ₜ[C] (1 : N) =
      (1 : S) ⊗ₜ[C] algebraMap L N (algebraMap C L c)
    rw [← IsScalarTower.algebraMap_apply C L N]
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul c
  letI : IsScalarTower C L T := IsScalarTower.of_algebraMap_eq' hCLT
  let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
  letI : Algebra C F := Algebra.restrictScalars C L F
  letI : SMul C F := Algebra.toSMul
  letI : Module C F := Algebra.toModule
  letI : IsScalarTower C L F := IsScalarTower.of_algebraMap_eq' rfl
  have hExactF : algebraicClosure C F =
      (⊥ : IntermediateField C F) :=
    exactConstantExtensionFrobeniusTwistField_algebraicClosure_eq_bot
      C L N S hExact g
  let U := ExactConstantExtension C F S
  letI : Field U := exactConstantExtensionField C F S hExactF
  letI : Algebra L U := exactConstantExtensionBaseAlgebra C L F S
  let fS : S →ₐ[C] T := Algebra.TensorProduct.includeLeft
  let fF : F →ₐ[C] T := F.val.restrictScalars C
  let fC : U →ₐ[C] T := Algebra.TensorProduct.productMap fS fF
  let f : U →ₐ[L] T :=
    { fC.toRingHom with
      commutes' := fun l => by
        change fC ((1 : S) ⊗ₜ[C] algebraMap L F l) =
          (1 : S) ⊗ₜ[C] algebraMap L N l
        rw [Algebra.TensorProduct.productMap_right_apply]
        rfl }
  letI : Algebra N T := exactConstantExtensionAlgebra C N S
  letI : IsScalarTower L N T := exactConstantExtensionBaseTower C L N S
  let eT := exactConstantExtensionLinearEquiv C N S
  letI : Module.Finite N (N ⊗[C] S) := Module.Finite.base_change C N S
  letI : Module.Finite N T := Module.Finite.equiv eT
  letI : Module.Finite L T := Module.Finite.trans N T
  letI : Module.Finite L F := Module.Finite.left L F T
  letI : Algebra F U := exactConstantExtensionAlgebra C F S
  letI : IsScalarTower L F U := exactConstantExtensionBaseTower C L F S
  let eU := exactConstantExtensionLinearEquiv C F S
  letI : Module.Finite F (F ⊗[C] S) := Module.Finite.base_change C F S
  letI : Module.Finite F U := Module.Finite.equiv eU
  letI : Module.Finite L U := Module.Finite.trans F U
  have hdim : Module.finrank L U = Module.finrank L T := by
    calc
      Module.finrank L U = Module.finrank L F * Module.finrank C S :=
        exactConstantExtension_finrank_over_base C L F S
      _ = Module.finrank L N * Module.finrank C S := by
        rw [finrank_frobeniusTwistField_over_base
          C L N S hExact g hdiv]
      _ = Module.finrank L T :=
        (exactConstantExtension_finrank_over_base C L N S).symm
  have hinj : Function.Injective f := f.injective
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mp hinj
  exact AlgEquiv.ofBijective f ⟨hinj, hsurj⟩

/-- Multiplication also identifies the constant extension of a
Frobenius-twist field with the common top field as an algebra over the
enlarged constant field `S`.  This is the scalar structure used to transport
the intrinsic genus. -/
noncomputable def
    exactConstantExtensionFrobeniusTwistMultiplicationAlgEquivOverConstants
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (g : N ≃ₐ[L] N)
    (hdiv : Nat.card (N ≃ₐ[L] N) ∣ Module.finrank C S) :
    letI := exactConstantExtensionField C N S hExact
    letI := exactConstantExtensionBaseAlgebra C L N S
    let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
    letI : Algebra C F := Algebra.restrictScalars C L F
    let hExactF :=
      exactConstantExtensionFrobeniusTwistField_algebraicClosure_eq_bot
        C L N S hExact g
    letI := exactConstantExtensionField C F S hExactF
    letI : Algebra S (ExactConstantExtension C F S) :=
      Algebra.TensorProduct.leftAlgebra
    letI : Algebra S (ExactConstantExtension C N S) :=
      Algebra.TensorProduct.leftAlgebra
    ExactConstantExtension C F S ≃ₐ[S] ExactConstantExtension C N S := by
  let T := ExactConstantExtension C N S
  letI : Field T := exactConstantExtensionField C N S hExact
  letI : Algebra L T := exactConstantExtensionBaseAlgebra C L N S
  have hCLT : algebraMap C T =
      (algebraMap L T).comp (algebraMap C L) := by
    ext c
    change algebraMap C S c ⊗ₜ[C] (1 : N) =
      (1 : S) ⊗ₜ[C] algebraMap L N (algebraMap C L c)
    rw [← IsScalarTower.algebraMap_apply C L N]
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul c
  letI : IsScalarTower C L T := IsScalarTower.of_algebraMap_eq' hCLT
  let F := exactConstantExtensionFrobeniusTwistField C L N S hExact g
  letI : Algebra C F := Algebra.restrictScalars C L F
  letI : SMul C F := Algebra.toSMul
  letI : Module C F := Algebra.toModule
  letI : IsScalarTower C L F := IsScalarTower.of_algebraMap_eq' rfl
  have hExactF : algebraicClosure C F =
      (⊥ : IntermediateField C F) :=
    exactConstantExtensionFrobeniusTwistField_algebraicClosure_eq_bot
      C L N S hExact g
  let U := ExactConstantExtension C F S
  letI : Field U := exactConstantExtensionField C F S hExactF
  letI : Algebra L U := exactConstantExtensionBaseAlgebra C L F S
  let fConst : S →ₐ[C] T := Algebra.TensorProduct.includeLeft
  let fTwist : F →ₐ[C] T := F.val.restrictScalars C
  let fC : U →ₐ[C] T :=
    Algebra.TensorProduct.productMap fConst fTwist
  let fL : U →ₐ[L] T :=
    { fC.toRingHom with
      commutes' := fun l => by
        change fC ((1 : S) ⊗ₜ[C] algebraMap L F l) =
          (1 : S) ⊗ₜ[C] algebraMap L N l
        rw [Algebra.TensorProduct.productMap_right_apply]
        rfl }
  letI : Algebra S U := Algebra.TensorProduct.leftAlgebra
  letI : Algebra S T := Algebra.TensorProduct.leftAlgebra
  let fS : U →ₐ[S] T :=
    { fC.toRingHom with
      commutes' := fun s => by
        change fC (s ⊗ₜ[C] (1 : F)) = s ⊗ₜ[C] (1 : N)
        rw [Algebra.TensorProduct.productMap_left_apply]
        rfl }
  letI : Algebra N T := exactConstantExtensionAlgebra C N S
  letI : IsScalarTower L N T := exactConstantExtensionBaseTower C L N S
  let eT := exactConstantExtensionLinearEquiv C N S
  letI : Module.Finite N (N ⊗[C] S) := Module.Finite.base_change C N S
  letI : Module.Finite N T := Module.Finite.equiv eT
  letI : Module.Finite L T := Module.Finite.trans N T
  letI : Module.Finite L F := Module.Finite.left L F T
  letI : Algebra F U := exactConstantExtensionAlgebra C F S
  letI : IsScalarTower L F U := exactConstantExtensionBaseTower C L F S
  let eU := exactConstantExtensionLinearEquiv C F S
  letI : Module.Finite F (F ⊗[C] S) := Module.Finite.base_change C F S
  letI : Module.Finite F U := Module.Finite.equiv eU
  letI : Module.Finite L U := Module.Finite.trans F U
  have hdim : Module.finrank L U = Module.finrank L T := by
    calc
      Module.finrank L U = Module.finrank L F * Module.finrank C S :=
        exactConstantExtension_finrank_over_base C L F S
      _ = Module.finrank L N * Module.finrank C S := by
        rw [finrank_frobeniusTwistField_over_base
          C L N S hExact g hdiv]
      _ = Module.finrank L T :=
        (exactConstantExtension_finrank_over_base C L N S).symm
  have hinjL : Function.Injective fL := fL.injective
  have hsurjL : Function.Surjective fL :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := fL.toLinearMap) hdim).mp hinjL
  have hinjS : Function.Injective fS := by
    intro x y hxy
    apply hinjL
    exact hxy
  have hsurjS : Function.Surjective fS := by
    intro y
    obtain ⟨x, hx⟩ := hsurjL y
    exact ⟨x, hx⟩
  exact AlgEquiv.ofBijective fS ⟨hinjS, hsurjS⟩

end

end BGS.HasseWeil
