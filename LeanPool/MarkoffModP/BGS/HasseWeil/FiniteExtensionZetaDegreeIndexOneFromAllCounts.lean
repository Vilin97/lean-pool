/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZetaDegreeIndexOne
import Mathlib.FieldTheory.Finite.Extension

/-!
# Choosing the constant extension of divisor-index degree

The geometric F. K. Schmidt composition in
`FiniteExtensionZetaDegreeIndexOne` accepts a finite constant extension whose
degree is the divisor-degree index.  Finite-field theory supplies such an
extension in every positive degree.  This file isolates that final choice:
if the closed-place splitting identity is available for every finite Galois
constant extension, then the divisor-degree index is one.
-/

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (C N : Type*) [Field C] [Fintype C] [DecidableEq C]
  [DecidableEq (RatFunc C)]
  [Field N] [Algebra (RatFunc C) N]
  [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]

local instance selectedExtensionBaseConstantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C (RatFunc C)))

local instance selectedExtensionBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- It suffices to prove the exact constant-extension closed-place identity
uniformly for finite Galois extensions of the constant field.  The required
extension of degree equal to the divisor-degree index is the standard finite
field extension `FiniteField.Extension`. -/
theorem finiteExtensionDivisorDegreeIndex_eq_one_of_all_exactConstantExtension_closedPlaceCount
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N))
    (hcount : ∀ (S : Type) [Field S] [Fintype S] [Algebra C S]
      [FiniteDimensional C S] [IsGalois C S], ∀ r,
      exactConstantExtensionClosedPlaceExtensionCount C S N hExact r =
        finiteExtensionClosedPlaceExtensionCount C N
          (Module.finrank C S * r)) :
    finiteExtensionDivisorDegreeIndex C N = 1 := by
  let d := finiteExtensionDivisorDegreeIndex C N
  have hd : 0 < d := finiteExtensionDivisorDegreeIndex_pos C N
  let p := ringChar C
  letI : Fact p.Prime := ⟨CharP.char_is_prime C p⟩
  letI : NeZero d := ⟨hd.ne'⟩
  letI : Fintype (FiniteField.Extension C p d) :=
    Fintype.ofFinite (FiniteField.Extension C p d)
  apply finiteExtensionDivisorDegreeIndex_eq_one_of_exactConstantExtension_closedPlaceCount
    C (FiniteField.Extension C p d) N hExact
  · simpa [d] using FiniteField.finrank_extension C p d
  · intro r
    simpa [d, FiniteField.finrank_extension] using
      hcount (FiniteField.Extension C p d) r

end

end BGS.HasseWeil
