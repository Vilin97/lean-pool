/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionPlaceTower
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.FieldTheory.IsSepClosed

/-!
# A finite Galois closure for a one-variable function field

For a finite separable extension `L / K(t)`, choose an embedding of `L` into
the absolute separable closure of `K(t)` and take its normal closure there.
The result is a finite Galois extension of `K(t)` containing an embedded copy
of `L`.

This is the field-theoretic Galois-closure layer required by the twisted
fixed-field argument.  It does not identify the algebraic constant field of
the closure or construct any Frobenius complements.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

variable (K L : Type*) [Field K] [Field L]
  [Algebra (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

/-- A chosen `K(t)`-embedding of the function field into the absolute
separable closure of `K(t)`. -/
def functionFieldSeparableClosureEmbedding :
    L →ₐ[RatFunc K] SeparableClosure (RatFunc K) :=
  IsSepClosed.lift

/-- The normal closure of the chosen embedded copy of `L` inside the absolute
separable closure of `K(t)`. -/
def FunctionFieldNormalClosure :
    IntermediateField (RatFunc K) (SeparableClosure (RatFunc K)) :=
  IntermediateField.normalClosure (RatFunc K)
    (functionFieldSeparableClosureEmbedding K L).fieldRange
    (SeparableClosure (RatFunc K))

/-- The original function field embeds into its chosen normal closure. -/
def functionFieldToNormalClosure :
    L →ₐ[RatFunc K] FunctionFieldNormalClosure K L :=
  (functionFieldSeparableClosureEmbedding K L).codRestrict
    (FunctionFieldNormalClosure K L).toSubalgebra (fun x => by
      exact IntermediateField.le_normalClosure
        (functionFieldSeparableClosureEmbedding K L).fieldRange
        ⟨x, rfl⟩)

theorem functionFieldToNormalClosure_injective :
    Function.Injective (functionFieldToNormalClosure K L) :=
  (functionFieldToNormalClosure K L).injective

variable [FiniteDimensional (RatFunc K) L]

/-- The chosen normal closure remains finite over `K(t)`. -/
noncomputable instance functionFieldNormalClosure_finiteDimensional :
    FiniteDimensional (RatFunc K) (FunctionFieldNormalClosure K L) := by
  let : FiniteDimensional (RatFunc K)
      (functionFieldSeparableClosureEmbedding K L).fieldRange :=
    (functionFieldSeparableClosureEmbedding K L).toLinearMap.finiteDimensional_range
  change FiniteDimensional (RatFunc K)
    (IntermediateField.normalClosure (RatFunc K)
      (functionFieldSeparableClosureEmbedding K L).fieldRange
      (SeparableClosure (RatFunc K)))
  infer_instance

/-- The chosen normal closure is Galois over `K(t)`. -/
noncomputable instance functionFieldNormalClosure_isGalois :
    IsGalois (RatFunc K) (FunctionFieldNormalClosure K L) :=
  IsGalois.normalClosure (RatFunc K)
    (functionFieldSeparableClosureEmbedding K L).fieldRange
    (SeparableClosure (RatFunc K))

end

end BGS.HasseWeil
