/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FunctionFieldNormalClosureConstants
public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionQuotient

/-!
# The constant-base field inside the function-field normal closure

Let `N / K(t)` be the chosen function-field normal closure and let `C` be its
algebraic constant field.  The restriction map

`Gal(N/K(t)) → Gal(C/K)`

is already known to be onto.  This file defines the fixed field of its kernel.
Every element of `C` lies in that fixed field, so it gives a genuine tower
`C ⊆ L_C ⊆ N`; moreover `N / L_C` is finite Galois.  The general exact
constant-extension and Frobenius-quotient theorems can therefore be applied
directly to the normal closure used by the Hasse--Weil proof.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section


variable (K L : Type*) [Field K] [Field L]
  [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)]
  [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- The fixed field of the automorphisms of the normal closure that act
trivially on all algebraic constants. -/
abbrev FunctionFieldNormalClosureConstantBase :=
  IntermediateField.fixedField
    (functionFieldNormalClosureConstantRestriction K L).ker

/-- Algebraic constants embed into the fixed field of the restriction
kernel. -/
def functionFieldNormalClosureConstantToBase :
    FunctionFieldNormalClosureConstantField K L →ₐ[K]
      FunctionFieldNormalClosureConstantBase K L where
  toFun c := ⟨c.1, by
    apply (IntermediateField.mem_fixedField_iff
      (H := (functionFieldNormalClosureConstantRestriction K L).ker) c.1).mpr
    intro g hg
    exact (mem_functionFieldNormalClosureConstantRestriction_ker_iff
      K L g).mp hg c⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The induced algebra structure of the kernel fixed field over the full
constant field. -/
@[reducible] noncomputable instance functionFieldNormalClosureConstantBaseAlgebra :
    Algebra (FunctionFieldNormalClosureConstantField K L)
      (FunctionFieldNormalClosureConstantBase K L) :=
  (functionFieldNormalClosureConstantToBase K L).toAlgebra

local instance normalClosureConstantBaseSMul :
    SMul (FunctionFieldNormalClosureConstantField K L)
      (FunctionFieldNormalClosureConstantBase K L) := Algebra.toSMul

local instance normalClosureConstantBaseModule :
    Module (FunctionFieldNormalClosureConstantField K L)
      (FunctionFieldNormalClosureConstantBase K L) := Algebra.toModule

/-- The embeddings of the constants into the fixed field and into the normal
closure form a scalar tower. -/
noncomputable instance functionFieldNormalClosureConstantBase_isScalarTower :
    IsScalarTower (FunctionFieldNormalClosureConstantField K L)
      (FunctionFieldNormalClosureConstantBase K L)
      (FunctionFieldNormalClosure K L) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext c
  rfl

/-- The normal closure is finite over the kernel fixed field. -/
noncomputable instance
    functionFieldNormalClosure_finiteDimensional_over_constantBase :
    FiniteDimensional (FunctionFieldNormalClosureConstantBase K L)
      (FunctionFieldNormalClosure K L) := by
  infer_instance

/-- The normal closure is Galois over the kernel fixed field. -/
noncomputable instance functionFieldNormalClosure_isGalois_over_constantBase :
    IsGalois (FunctionFieldNormalClosureConstantBase K L)
      (FunctionFieldNormalClosure K L) := by
  infer_instance

section Extension

variable (S : Type*) [Field S]
  [Algebra (FunctionFieldNormalClosureConstantField K L) S]
  [FiniteDimensional (FunctionFieldNormalClosureConstantField K L) S]
  [IsGalois (FunctionFieldNormalClosureConstantField K L) S]

/-- The generic exact-constant field structure specializes to the chosen
function-field normal closure. -/
@[reducible] noncomputable instance
    functionFieldNormalClosureExactConstantExtensionField :
    Field (ExactConstantExtension
      (FunctionFieldNormalClosureConstantField K L)
      (FunctionFieldNormalClosure K L) S) :=
  exactConstantExtensionField
    (FunctionFieldNormalClosureConstantField K L)
    (FunctionFieldNormalClosure K L) S
    (functionFieldNormalClosureConstantField_isExact K L)

/-- The Galois group of the specialized constant extension is the product of
the new constant Galois group and the kernel-fixed-field Galois group. -/
noncomputable def functionFieldNormalClosureConstantExtensionAutMulEquiv :
    let := exactConstantExtensionBaseAlgebra
      (FunctionFieldNormalClosureConstantField K L)
      (FunctionFieldNormalClosureConstantBase K L)
      (FunctionFieldNormalClosure K L) S
    (S ≃ₐ[FunctionFieldNormalClosureConstantField K L] S) ×
        (FunctionFieldNormalClosure K L ≃ₐ[
          FunctionFieldNormalClosureConstantBase K L]
          FunctionFieldNormalClosure K L) ≃*
      (ExactConstantExtension
          (FunctionFieldNormalClosureConstantField K L)
          (FunctionFieldNormalClosure K L) S ≃ₐ[
            FunctionFieldNormalClosureConstantBase K L]
        ExactConstantExtension
          (FunctionFieldNormalClosureConstantField K L)
          (FunctionFieldNormalClosure K L) S) := by
  let := exactConstantExtensionBaseAlgebra
    (FunctionFieldNormalClosureConstantField K L)
    (FunctionFieldNormalClosureConstantBase K L)
    (FunctionFieldNormalClosure K L) S
  exact exactConstantExtensionAutMulEquiv
    (FunctionFieldNormalClosureConstantField K L)
    (FunctionFieldNormalClosureConstantBase K L)
    (FunctionFieldNormalClosure K L) S
    (functionFieldNormalClosureConstantField_isExact K L)

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] in
/-- The specialized constant quotient is onto. -/
theorem functionFieldNormalClosureConstantExtensionQuotient_surjective :
    let := exactConstantExtensionBaseAlgebra
      (FunctionFieldNormalClosureConstantField K L)
      (FunctionFieldNormalClosureConstantBase K L)
      (FunctionFieldNormalClosure K L) S
    Function.Surjective (exactConstantExtensionConstantQuotient
      (FunctionFieldNormalClosureConstantField K L)
      (FunctionFieldNormalClosureConstantBase K L)
      (FunctionFieldNormalClosure K L) S
      (functionFieldNormalClosureConstantField_isExact K L)) := by
  let := exactConstantExtensionBaseAlgebra
    (FunctionFieldNormalClosureConstantField K L)
    (FunctionFieldNormalClosureConstantBase K L)
    (FunctionFieldNormalClosure K L) S
  exact exactConstantExtensionConstantQuotient_surjective
    (FunctionFieldNormalClosureConstantField K L)
    (FunctionFieldNormalClosureConstantBase K L)
    (FunctionFieldNormalClosure K L) S
    (functionFieldNormalClosureConstantField_isExact K L)

end Extension

end

end BGS.HasseWeil
