/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.GeneralFiniteExtensionRiemannLower
public import LeanPool.MarkoffModP.BGS.HasseWeil.GeneralSquareFieldStepanovCount

/-!
# Automatic intrinsic Stepanov bounds

The arbitrary-function-field Stepanov theorem asks only for a finite-place
Riemann budget.  The primitive-element construction supplies such a budget
for every finite separable function field.  This file composes those results,
leaving only the explicit large-square-field inequality for the constructed
budget.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section


variable (K S : Type*) [Field K] [Fintype K]
  [Field S] [Fintype S] [DecidableEq S] [Algebra K S]
  [DecidableEq (RatFunc S)]
variable (L : Type*) [Field L] [Algebra (RatFunc S) L]
  [FiniteDimensional (RatFunc S) L]
  [Algebra.IsSeparable (RatFunc S) L]

local instance automaticSquareFieldConstantAlgebra : Algebra S L :=
  RingHom.toAlgebra ((algebraMap (RatFunc S) L).comp
    (algebraMap S (RatFunc S)))

local instance automaticSquareFieldConstantTower :
    IsScalarTower S (RatFunc S) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Every finite separable function field with exact constants has an
intrinsic Stepanov budget.  Once the half-sized field is large relative to
that constructed budget, its complete degree-one place count satisfies the
square-field upper bound. -/
theorem exists_squareFieldStepanov_budget
    (hcard : Fintype.card S = (Fintype.card K) ^ 2)
    (hconstants : algebraicClosure S L = ⊥) :
    ∃ g : ℕ,
      (g + 1) * (g + 2) ≤ Fintype.card K →
        finiteExtensionRationalPlaceCount S L ≤
          Fintype.card S + (2 * g + 1) * Fintype.card K +
            Module.finrank (RatFunc S) L := by
  obtain ⟨g, hriemann⟩ := exists_finitePlace_riemann_lower_budget S L
  refine ⟨g, fun hlarge => ?_⟩
  apply
    finiteExtensionRationalPlaceCount_le_squareFieldStepanov_of_finitePlaceRiemann
      K S L g hcard hconstants _ hlarge
  intro Q N
  have h := hriemann Q.1 N
  simpa only [Q.2, Nat.mul_one] using h

end

end BGS.HasseWeil
