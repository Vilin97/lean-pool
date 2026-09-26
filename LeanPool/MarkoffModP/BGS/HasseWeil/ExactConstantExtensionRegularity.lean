/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FunctionFieldNormalClosureConstantBase

/-!
# Regular constant extensions

An exact constant field makes finite Galois extensions of the constants
linearly disjoint from the function field.  The existing tensor-product
construction therefore remains a field and its full Galois group is a direct
product.  This file records the corresponding intrinsic statement: the
original function-field Galois group is exactly the subgroup acting trivially
on the enlarged constants.

The final declarations specialize these facts to the normal closure used in
the Hasse--Weil development.  They concern the proved constant base `C(t)`;
they do not assert compatibility with the not-yet-defined compositum `C F` of
an arbitrary intermediate function field `F`.
-/

@[expose] public section

open scoped TensorProduct

namespace BGS.HasseWeil

noncomputable section

variable (C L N S : Type*) [Field C] [Field L] [Field N] [Field S]
  [Algebra C L] [Algebra L N] [Algebra C N] [IsScalarTower C L N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
  [FiniteDimensional L N] [IsGalois L N]

/-- The action of the original function-field Galois group, regarded as an
automorphism of the constant extension that acts trivially on the enlarged
constants. -/
noncomputable def exactConstantExtensionFunctionAutHomToConstantKernel
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    let := exactConstantExtensionField C N S hExact
    let := exactConstantExtensionBaseAlgebra C L N S
    (N ≃ₐ[L] N) →*
      (exactConstantExtensionConstantQuotient C L N S hExact).ker := by
  intro fieldModel algebraModel
  let f := exactConstantExtensionFunctionAutHom C L N S
  exact
    { toFun := fun g => ⟨f g, by
          rw [exactConstantExtensionConstantQuotient_ker C L N S hExact]
          exact ⟨g, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        exact map_one f
      map_mul' := by
        intro g h
        apply Subtype.ext
        exact map_mul f g h }

theorem exactConstantExtensionFunctionAutHomToConstantKernel_injective
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    let := exactConstantExtensionField C N S hExact
    let := exactConstantExtensionBaseAlgebra C L N S
    Function.Injective
      (exactConstantExtensionFunctionAutHomToConstantKernel C L N S hExact) := by
  intro fieldModel algebraModel
  intro g h hgh
  have hfun : exactConstantExtensionFunctionAutHom C L N S g =
      exactConstantExtensionFunctionAutHom C L N S h :=
    congrArg Subtype.val hgh
  have hp := exactConstantExtensionCombinedAutHom_injective C L N S
    (show exactConstantExtensionCombinedAutHom C L N S (1, g) =
        exactConstantExtensionCombinedAutHom C L N S (1, h) by
      simpa [exactConstantExtensionCombinedAutHom] using hfun)
  exact congrArg Prod.snd hp

theorem exactConstantExtensionFunctionAutHomToConstantKernel_surjective
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    let := exactConstantExtensionField C N S hExact
    let := exactConstantExtensionBaseAlgebra C L N S
    Function.Surjective
      (exactConstantExtensionFunctionAutHomToConstantKernel C L N S hExact) := by
  intro fieldModel algebraModel
  intro x
  have hx : x.1 ∈ (exactConstantExtensionFunctionAutHom C L N S).range := by
    rw [← exactConstantExtensionConstantQuotient_ker C L N S hExact]
    exact x.property
  obtain ⟨g, hg⟩ := hx
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact hg

/-- Exact finite constant extension preserves the function-field Galois group:
it is canonically the kernel of restriction from the full extended Galois
group to the Galois group of the enlarged constants. -/
noncomputable def exactConstantExtensionFunctionAutMulEquiv
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    let := exactConstantExtensionField C N S hExact
    let := exactConstantExtensionBaseAlgebra C L N S
    (N ≃ₐ[L] N) ≃*
      (exactConstantExtensionConstantQuotient C L N S hExact).ker := by
  intro fieldModel algebraModel
  exact MulEquiv.ofBijective
    (exactConstantExtensionFunctionAutHomToConstantKernel C L N S hExact)
    ⟨exactConstantExtensionFunctionAutHomToConstantKernel_injective
        C L N S hExact,
      exactConstantExtensionFunctionAutHomToConstantKernel_surjective
        C L N S hExact⟩

section NormalClosure

variable (K F S : Type*) [Field K] [Field F] [Field S]
  [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)]
  [Algebra (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
  [Algebra.IsSeparable (RatFunc K) F]
  [Algebra (FunctionFieldNormalClosureConstantField K F) S]
  [FiniteDimensional (FunctionFieldNormalClosureConstantField K F) S]
  [IsGalois (FunctionFieldNormalClosureConstantField K F) S]

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] [FiniteDimensional (RatFunc K) F] in
/-- A finite Galois extension of the exact constants has field-valued tensor
product with the function-field normal closure. -/
theorem functionFieldNormalClosureConstantExtensionTensor_isField :
    IsField (ExactConstantExtension
      (FunctionFieldNormalClosureConstantField K F)
      (FunctionFieldNormalClosure K F) S) :=
  exactConstantExtensionTensor_isField
    (FunctionFieldNormalClosureConstantField K F)
    (FunctionFieldNormalClosure K F) S
    (functionFieldNormalClosureConstantField_isExact K F)

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] [FiniteDimensional (RatFunc K) F]
  [FiniteDimensional (↥(FunctionFieldNormalClosureConstantField K F)) S]
  [IsGalois (↥(FunctionFieldNormalClosureConstantField K F)) S] in
/-- The constant extension has the expected degree over the original normal
closure. -/
theorem functionFieldNormalClosureConstantExtension_finrank_over_normalClosure :
    let := exactConstantExtensionAlgebra
      (FunctionFieldNormalClosureConstantField K F)
      (FunctionFieldNormalClosure K F) S
    let : SMul (FunctionFieldNormalClosure K F)
        (ExactConstantExtension (FunctionFieldNormalClosureConstantField K F)
          (FunctionFieldNormalClosure K F) S) := Algebra.toSMul
    let : Module (FunctionFieldNormalClosure K F)
        (ExactConstantExtension (FunctionFieldNormalClosureConstantField K F)
          (FunctionFieldNormalClosure K F) S) := Algebra.toModule
    Module.finrank (FunctionFieldNormalClosure K F)
      (ExactConstantExtension
        (FunctionFieldNormalClosureConstantField K F)
        (FunctionFieldNormalClosure K F) S) =
      Module.finrank (FunctionFieldNormalClosureConstantField K F) S := by
  exact exactConstantExtension_finrank
    (FunctionFieldNormalClosureConstantField K F)
    (FunctionFieldNormalClosure K F) S

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- The normal closure remains Galois over its proved constant base after a
finite Galois extension of the exact constants. -/
theorem functionFieldNormalClosureConstantExtension_isGalois_over_constantBase :
    let C := FunctionFieldNormalClosureConstantField K F
    let B := FunctionFieldNormalClosureConstantBase K F
    let N := FunctionFieldNormalClosure K F
    let hExact := functionFieldNormalClosureConstantField_isExact K F
    let := exactConstantExtensionField C N S hExact
    let := exactConstantExtensionBaseAlgebra C B N S
    IsGalois B (ExactConstantExtension C N S) := by
  exact exactConstantExtension_isGalois
    (FunctionFieldNormalClosureConstantField K F)
    (FunctionFieldNormalClosureConstantBase K F)
    (FunctionFieldNormalClosure K F) S
    (functionFieldNormalClosureConstantField_isExact K F)

/-- In the normal-closure setting, the original geometric Galois group is the
kernel of restriction to the enlarged constants. -/
noncomputable def
    functionFieldNormalClosureConstantExtensionFunctionAutMulEquiv :
    let C := FunctionFieldNormalClosureConstantField K F
    let B := FunctionFieldNormalClosureConstantBase K F
    let N := FunctionFieldNormalClosure K F
    let hExact := functionFieldNormalClosureConstantField_isExact K F
    let := exactConstantExtensionField C N S hExact
    let := exactConstantExtensionBaseAlgebra C B N S
    (N ≃ₐ[B] N) ≃*
      (exactConstantExtensionConstantQuotient C B N S hExact).ker := by
  exact exactConstantExtensionFunctionAutMulEquiv
    (FunctionFieldNormalClosureConstantField K F)
    (FunctionFieldNormalClosureConstantBase K F)
    (FunctionFieldNormalClosure K F) S
    (functionFieldNormalClosureConstantField_isExact K F)

end NormalClosure

end

end BGS.HasseWeil
