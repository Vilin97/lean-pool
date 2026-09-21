/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
import Mathlib.RingTheory.OreLocalization.Ring

/-!
# Localization interface for derivation-Ore extensions

The proposition below is the exact output expected from a theorem saying that
localizing a derivation-Ore extension at coefficients gives the derivation-Ore
extension of the localized coefficient ring.  It packages data and its
compatibility law; it does not assert that the data exist.
-/

namespace AlgebraicAnalysis
namespace OreLocalizationExtension

open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open OreLocalization

/-- Existence of data identifying the localization of `NormalOre D` along coefficient
denominators with a derivation-Ore extension of the localized coefficient
ring.  Ore-ness of both denominator sets remains an explicit hypothesis. -/
def IsDerivationOreLocalization
    {B : Type*} [Ring B]
    (D : OreDivisionDerivation B) (S : Submonoid B)
    [OreSet S]
    [OreSet (S.map (normalCoefficient D).toMonoidHom)] : Prop :=
  ∃ (D' : OreDivisionDerivation (B[S⁻¹]))
    (e : (NormalOre D)[(S.map (normalCoefficient D).toMonoidHom)⁻¹] ≃+*
      NormalOre D'),
    ∀ b : B,
      e (numeratorHom (normalCoefficient D b)) =
        normalCoefficient D' (numeratorHom b)

end OreLocalizationExtension
end AlgebraicAnalysis
