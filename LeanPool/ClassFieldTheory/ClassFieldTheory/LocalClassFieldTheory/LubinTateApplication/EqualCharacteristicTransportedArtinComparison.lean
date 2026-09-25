/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicTransportedUpperRestriction
public import LeanPool.ClassFieldTheory.GaloisCohomology.GroupTheory.RestrictionKernel
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.TransportedNormSubgroupExact
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
/-!
# Local Artin comparison on transported Lubin--Tate levels

The exact transported norm-subgroup formula and finite-tower naturality of
the local Artin map identify the image of a target-field principal-unit
group with the kernel of restriction to the corresponding lower transported
Lubin--Tate level.  The transported upper-ramification calculation identifies
the same kernel, giving integral filtered reciprocity over the target field.
-/

@[expose] public section

noncomputable
section

open scoped LaurentSeries ValuativeRel

namespace LocalClassFieldTheory

open RamificationTheory.LocalField
open LubinTate

open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate.EqualCharacteristic

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- In a tower of transported levels `m + 1 ≤ n + 1`, the target-field
local Artin image of `U^(m+1)` is the kernel of actual restriction to the
lower transported level. -/
theorem
    equalCharacteristicTransportedLubinTateArtinPrincipalUnitsImage_eq_restrictKer
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    {m n : ℕ} (hmn : m ≤ n) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F m
    let L := equalCharacteristicLubinTateLevelField F n
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F m
    letI : Algebra B L :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ m
    letI : Algebra K L :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    letI : FiniteDimensional K E :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K p ϖ hϖ m
    letI : FiniteDimensional K L :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K p ϖ hϖ n
    letI : IsAbelianGalois K E :=
      equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
        K p ϖ hϖ m
    letI : IsAbelianGalois K L :=
      equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
        K p ϖ hϖ n
    (LocalFieldTheory.fieldPrincipalUnits K (m + 1)).map
        (abelianLocalArtinMonoidHom K L) =
      (equalCharacteristicTransportedLubinTateRestrictNormalHom
        K p ϖ hϖ hmn).ker := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  let L := equalCharacteristicLubinTateLevelField F n
  let : Algebra B E :=
    equalCharacteristicLubinTateLevelAlgebra F m
  let : Algebra B L :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let hEL : E ≤ L :=
    equalCharacteristicLubinTateLevelField_mono F hmn
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ m
  let : Algebra K L :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  let : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ m
  let : FiniteDimensional K L :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ n
  let : IsAbelianGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ m
  let : IsAbelianGalois K L :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ n
  let ELAlgebra : Algebra E L :=
    RingHom.toAlgebra (IntermediateField.inclusion hEL).toRingHom
  let : SMul E L :=
    @Algebra.toSMul _ _ _ _ ELAlgebra
  let : IsScalarTower K E L :=
    IsScalarTower.of_algebraMap_eq' (R := K) (S := E) (A := L) (by
      apply RingHom.ext
      intro x
      apply L.val.injective
      rfl)
  let φ := abelianLocalArtinMonoidHom K L
  let ψ :=
    equalCharacteristicTransportedLubinTateRestrictNormalHom
      K p ϖ hϖ hmn
  have hrestrict :
      ψ.comp φ = abelianLocalArtinMonoidHom K E := by
    change
      (AlgEquiv.restrictNormalHom E).comp
          (abelianLocalArtinMonoidHom K L) =
        abelianLocalArtinMonoidHom K E
    exact abelianLocalArtinMonoidHom_restrict_tower K E L
  have hker :
      (ψ.comp φ).ker =
        Subgroup.zpowers ϖ ⊔ LocalFieldTheory.fieldPrincipalUnits K (m + 1) := by
    rw [hrestrict, abelianLocalArtinMonoidHom_ker]
    change
      equalCharacteristicTransportedLubinTateNormSubgroup
          K p ϖ hϖ m =
        Subgroup.zpowers ϖ ⊔ LocalFieldTheory.fieldPrincipalUnits K (m + 1)
    simpa [LocalFieldTheory.uniformizerPrincipalSubgroup] using
      equalCharacteristicTransportedLubinTateNormSubgroup_eq_uniformizerPrincipalSubgroup
        K p ϖ hϖ m
  have hZ : Subgroup.zpowers ϖ ≤ φ.ker := by
    rw [abelianLocalArtinMonoidHom_ker]
    change
      Subgroup.zpowers ϖ ≤
        equalCharacteristicTransportedLubinTateNormSubgroup
          K p ϖ hϖ n
    rw [
      equalCharacteristicTransportedLubinTateNormSubgroup_eq_uniformizerPrincipalSubgroup]
    simp [LocalFieldTheory.uniformizerPrincipalSubgroup]
  exact Subgroup.map_eq_ker_of_comp_ker_eq_sup_of_left_le_ker
    φ ψ (Subgroup.zpowers ϖ) (LocalFieldTheory.fieldPrincipalUnits K (m + 1))
    (abelianLocalArtinMonoidHom_surjective K L) hker hZ

/-- Integral filtered local reciprocity for a transported
equal-characteristic Lubin--Tate level. -/
theorem
    equalCharacteristicTransportedLubinTateArtinPrincipalUnitsImage_eq_localUpperRamificationGroup
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let L := equalCharacteristicLubinTateLevelField F n
    letI : Algebra B L :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : CharP K p := hKp
    letI : Algebra K L :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    letI : FiniteDimensional K L :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K p ϖ hϖ n
    letI : IsAbelianGalois K L :=
      equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
        K p ϖ hϖ n
    (LocalFieldTheory.fieldPrincipalUnits K k).map
        (abelianLocalArtinMonoidHom K L) =
      localUpperRamificationGroup K L (k : ℝ) := by
  let m := k - 1
  have hmn : m ≤ n := by
    dsimp only [m]
    omega
  have hArtin :=
    equalCharacteristicTransportedLubinTateArtinPrincipalUnitsImage_eq_restrictKer
      K p ϖ hϖ hmn
  have hUpper :=
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_eq_restrictKer
      K p ϖ hϖ n k hk hkn
  simpa [m, Nat.sub_add_cancel hk] using
    hArtin.trans hUpper.symm

end LocalClassFieldTheory
