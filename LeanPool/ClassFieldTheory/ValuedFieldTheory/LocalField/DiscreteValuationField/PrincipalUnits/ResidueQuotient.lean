/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismTransport

/-! # Residue Quotient -/

@[expose] public section
namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

/-!
# The first principal-unit quotient

Identifies valuation-ring units modulo first principal units with residue-field units and
records compatibility with valuation-preserving automorphisms.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- The kernel of the residue map on valuation-ring units is the first
principal-unit subgroup. -/
theorem residueUnitHom_ker_eq :
    (higherPrincipalUnitGroup.residueUnitHom F).ker =
      higherPrincipalUnitGroup F 1 := by
  ext u
  rw [MonoidHom.mem_ker, higherPrincipalUnitGroup.residueUnitHom_eq_one_iff]

/-- The first-isomorphism form of the residue map on valuation-ring units:
`O_K^* / U_K^1` is the unit group of the residue field. -/
noncomputable def unitsModOneEquivResidueFieldUnits :
    F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F 1 ≃* F.residueFieldˣ :=
  QuotientGroup.liftEquiv
    (higherPrincipalUnitGroup F 1)
    (by
      simpa [higherPrincipalUnitGroup.residueUnitHom] using
        (IsLocalRing.surjective_units_map_of_local_ringHom
          F.residueMap F.residue_surjective
          (inferInstanceAs (IsLocalHom F.residueMap))))
    (higherPrincipalUnitGroup.residueUnitHom_ker_eq F).symm

/--
Establishes the identity `higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits F
(QuotientGroup.mk' (higherPrincipalUnitGroup F 1) u) = higherPrincipalUnitGroup.residueUnitHom F
u`.
-/
theorem unitsModOneEquivResidueFieldUnits_mk
    (u : F.valuationSubringˣ) :
    higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits F
        (QuotientGroup.mk' (higherPrincipalUnitGroup F 1) u) =
      higherPrincipalUnitGroup.residueUnitHom F u := by
  rfl

/-- Compatibility of the induced action on `O^*/U^1` with the induced action
on residue-field units. -/
theorem unitsModOneEquivResidueFieldUnits_unitsModPrincipalUnitEquivOfPreserves_one
    (e : K ≃+* K)
    (hmem :
      ∀ x : K,
        x ∈ F.valuation.valuationSubring ↔
          e x ∈ F.valuation.valuationSubring)
    (q : F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F 1) :
    higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits F
        (higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves
          F e hmem 1 q) =
      Units.map
        (valuationSubringResidueFieldEquivOfPreserves F e hmem).toMonoidHom
        (higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits F q) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
    (higherPrincipalUnitGroup F 1) q
  rw [higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk,
    higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk,
    higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk,
    residueUnitHom_valuationSubringUnitEquivOfPreserves]
end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
