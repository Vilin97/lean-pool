/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardArtinComparison
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicTransportedLevelTower
/-!
# Restriction kernels for transported upper ramification groups

At an integral upper index, the explicit Laurent Lubin--Tate upper group is
a restriction kernel.  The base-field transport equivalences commute with
level restriction, so the same kernel description holds for the
transported target-field algebra.
-/

noncomputable section

open scoped LaurentSeries ValuativeRel

namespace LocalClassFieldTheory

open RamificationTheory.LocalField
open LubinTate

open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate.EqualCharacteristic
open RamificationTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- For `1 ≤ k ≤ n + 1`, the `k`-th upper ramification group of the
transported level `n + 1` is the kernel of restriction to level `k`. -/
theorem
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_eq_restrictKer
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let m := k - 1
    let E := equalCharacteristicLubinTateLevelField F m
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F m
    letI : Algebra B L :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : IsGalois B E :=
      equalCharacteristicLubinTateLevelField_isGalois F m
    letI : IsGalois B L :=
      equalCharacteristicLubinTateLevelField_isGalois F n
    letI : FiniteDimensional B E :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F m
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p (hKp := hKp) ϖ hϖ m
    letI : Algebra K L :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p (hKp := hKp) ϖ hϖ n
    letI : IsGalois K E :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K p (hKp := hKp) ϖ hϖ m
    letI : IsGalois K L :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K p (hKp := hKp) ϖ hϖ n
    letI : FiniteDimensional K E :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K p (hKp := hKp) ϖ hϖ m
    letI : FiniteDimensional K L :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K p (hKp := hKp) ϖ hϖ n
    localUpperRamificationGroup K L (k : ℝ) =
      (equalCharacteristicTransportedLubinTateRestrictNormalHom
        K p (hKp := hKp) ϖ hϖ (by omega : m ≤ n)).ker := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let hKq : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let m := k - 1
  let E := equalCharacteristicLubinTateLevelField F m
  let L := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B :=
    equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let : FiniteDimensional B L :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let upperB := localUpperRamificationGroup B L
  let : Algebra B E :=
    equalCharacteristicLubinTateLevelAlgebra F m
  let : Algebra B L :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let : IsGalois B E :=
    equalCharacteristicLubinTateLevelField_isGalois F m
  let : IsGalois B L :=
    equalCharacteristicLubinTateLevelField_isGalois F n
  let : FiniteDimensional B E :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F m
  have hmn : m ≤ n := by
    dsimp only [m]
    omega
  let hEL : E ≤ L :=
    equalCharacteristicLubinTateLevelField_mono F hmn
  let rB := intermediateFieldRestrictNormalHom E L hEL
  have hRestrict :
      equalCharacteristicLubinTateRealUpperRamificationGroup
          F n (k : ℝ) =
        rB.ker := by
    simpa only [m, E, L, rB, hEL] using
      equalCharacteristicLubinTateRealUpperRamificationGroup_eq_restrictKer
        F n k hk hkn
  have hSource :
      upperB (k : ℝ) = rB.ker :=
    (equalCharacteristicLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
      F n (k : ℝ)).symm.trans hRestrict
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ m
  let : Algebra K L :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  let : Module K L := Algebra.toModule
  let : IsGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isGalois
      K p ϖ hϖ m
  let : IsGalois K L :=
    equalCharacteristicTransportedLubinTateLevel_isGalois
      K p ϖ hϖ n
  let : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ m
  let : FiniteDimensional K L :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ n
  let upperK := localUpperRamificationGroup K L
  let qE :=
    equalCharacteristicTransportedLubinTateGaloisEquiv
      K p ϖ hϖ m
  let qL :=
    equalCharacteristicTransportedLubinTateGaloisEquiv
      K p ϖ hϖ n
  let rK :=
    equalCharacteristicTransportedLubinTateRestrictNormalHom
      K p ϖ hϖ hmn
  have hcomm :
      rK.comp qL.toMonoidHom =
        qE.toMonoidHom.comp rB := by
    apply MonoidHom.ext
    intro σ
    exact
      equalCharacteristicTransportedLubinTateGaloisEquiv_restrict
        K p ϖ hϖ hmn σ
  have hkerMap :
      rB.ker.map qL.toMonoidHom = rK.ker :=
    (Subgroup.map_symm_eq_iff_map_eq rB.ker (e := qL)).mp <| by
      calc
        rK.ker.map qL.symm.toMonoidHom =
            (rK.comp qL.toMonoidHom).ker :=
          (MonoidHom.ker_comp_mulEquiv rK qL).symm
        _ = (qE.toMonoidHom.comp rB).ker :=
          congrArg MonoidHom.ker hcomm
        _ = rB.ker := MonoidHom.ker_mulEquiv_comp rB qE
  have hMap :
      Subgroup.map qL.toMonoidHom (upperB (k : ℝ)) =
        upperK (k : ℝ) := by
    exact
      equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq
        K p (hKp := hKp) ϖ hϖ n (k : ℝ)
  change upperK (k : ℝ) = rK.ker
  calc
    upperK (k : ℝ) =
        Subgroup.map qL.toMonoidHom (upperB (k : ℝ)) := hMap.symm
    _ = Subgroup.map qL.toMonoidHom rB.ker :=
      congrArg (Subgroup.map qL.toMonoidHom) hSource
    _ = rK.ker := hkerMap

end LocalClassFieldTheory
