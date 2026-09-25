/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LaurentPrincipalUnitTransport
/-!
# Exact transported Lubin--Tate norm subgroup

The exact principal-unit transport upgrades the transported
equal-characteristic Lubin--Tate norm containment to the sharp standard
subgroup formula.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries ValuativeRel

namespace LubinTate
namespace EqualCharacteristic

open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The transported level-`m+1` Lubin--Tate norm subgroup is exactly
`⟨ϖ⟩ · U^(m+1)` in the target local field. -/
theorem
    equalCharacteristicTransportedLubinTateNormSubgroup_eq_uniformizerPrincipalSubgroup
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    equalCharacteristicTransportedLubinTateNormSubgroup
        K p ϖ hϖ m =
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let pi : Bˣ := (equalCharacteristicLaurentUniformizerUnit F)⁻¹
  let e := equalCharacteristicTargetLaurentUnitsEquiv K p ϖ hϖ
  have htransport :=
    equalCharacteristicLubinTateNormSubgroup_map_eq_transported
      K p ϖ hϖ m
  have hepi : e pi = ϖ := by
    change
      equalCharacteristicTargetLaurentUnitsEquiv K p ϖ hϖ
          (equalCharacteristicLaurentUniformizerUnit
            (equalCharacteristicTargetLocalField K))⁻¹ =
        ϖ
    exact
      equalCharacteristicTargetLaurentUnitsEquiv_uniformizer_inv
        K p ϖ hϖ
  have hprincipal :=
    equalCharacteristicTargetLaurent_fieldPrincipalUnits_map_eq
      K p ϖ hϖ m
  rw [← htransport]
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  rw [
    equalCharacteristicLubinTateNormSubgroup_eq_uniformizerPrincipalSubgroup]
  unfold LocalFieldTheory.uniformizerPrincipalSubgroup
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, map_pow]
  change
    Subgroup.zpowers ((e pi) ^ 1) ⊔
        (LocalFieldTheory.fieldPrincipalUnits B (m + 1)).map e.toMonoidHom =
      Subgroup.zpowers (ϖ ^ 1) ⊔ LocalFieldTheory.fieldPrincipalUnits K (m + 1)
  rw [hepi]
  rw [hprincipal]

end EqualCharacteristic
end LubinTate
