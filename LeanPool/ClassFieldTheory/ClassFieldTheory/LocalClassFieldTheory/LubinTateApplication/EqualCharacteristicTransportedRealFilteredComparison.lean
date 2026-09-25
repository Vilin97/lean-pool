/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicRealFilteredComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicTransportedArtinComparison
/-!
# Real filtered reciprocity on transported Lubin--Tate levels

The integral target-field comparison is extended to every nonnegative real
index.  The upper filtration is transported from the Laurent model, while
the zeroth and terminal Artin groups use the exact transported norm subgroup.
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

/-- The target-field upper ramification group at index zero is full on a
transported Lubin--Tate level. -/
theorem
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_zero_eq_top
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : Algebra B L :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    letI : IsGalois B L :=
      equalCharacteristicLubinTateLevelField_isGalois F n
    letI : CharP K p := hKp
    letI : Algebra K L :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    letI : FiniteDimensional K L :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K p ϖ hϖ n
    letI : IsGalois K L :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K p ϖ hϖ n
    localUpperRamificationGroup K L 0 = ⊤ := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let L := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B :=
    equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let finBL : FiniteDimensional B L :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let upperB :=
    @localUpperRamificationGroup B L
      inferInstance inferInstance
      inferInstance finBL inferInstance
      inferInstance inferInstance inferInstance
  have hSource : upperB 0 = ⊤ := by
    simpa only [upperB, F, B, L] using
      equalCharacteristicLubinTateLocalUpperRamificationGroup_zero_eq_top
        F n
  let algBL : Algebra B L :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let : CharP K p := hKp
  let algKL : Algebra K L :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  let : Module K L := Algebra.toModule
  let galKL : IsGalois K L :=
    equalCharacteristicTransportedLubinTateLevel_isGalois
      K p ϖ hϖ n
  let finKL : FiniteDimensional K L :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ n
  let upperK :=
    @localUpperRamificationGroup K L
      inferInstance inferInstance
      algKL finKL galKL
      inferInstance inferInstance inferInstance
  let q :=
    equalCharacteristicTransportedLubinTateGaloisEquiv
      K p ϖ hϖ n
  have hMap :
      Subgroup.map q.toMonoidHom (upperB 0) = upperK 0 := by
    simpa only [upperB, upperK, q, F, B, L] using
      equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq
        K p (hKp := hKp) ϖ hϖ n 0
  change upperK 0 = ⊤
  calc
    upperK 0 = Subgroup.map q.toMonoidHom (upperB 0) := hMap.symm
    _ = _ := congrArg (Subgroup.map q.toMonoidHom) hSource
    _ = ⊤ := Subgroup.map_top_of_surjective q.toMonoidHom q.surjective

private theorem principalUnitsImage_zero_eq_top_of_uniformizer_zpowers_le_ker
    {G : Type} [Group G]
    (φ : Kˣ →* G)
    (hφ : Function.Surjective φ)
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (hϖKer :
      Subgroup.zpowers ϖ ≤
        φ.ker) :
    (LocalFieldTheory.fieldPrincipalUnits K 0).map
        φ = ⊤ := by
  apply top_unique
  intro σ _
  obtain ⟨x, hx⟩ := hφ σ
  obtain ⟨u, hdecomp⟩ :=
    exists_integerUnit_mul_uniformizer_zpow K ϖ hϖ x
  have hpowKer :
      ϖ ^ valuationMap K (Additive.ofMul x) ∈
        φ.ker :=
    hϖKer (Subgroup.zpow_mem_zpowers ϖ _)
  have hpow :
      φ (ϖ ^ valuationMap K (Additive.ofMul x)) = 1 :=
    MonoidHom.mem_ker.mp hpowKer
  refine ⟨integerUnitsToFieldUnits K u, ?_, ?_⟩
  · unfold LocalFieldTheory.fieldPrincipalUnits
    exact ⟨u, by simp, rfl⟩
  · rw [← hx, ← hdecomp, map_mul, hpow, mul_one]

/-- The target-field Artin image of the valuation-ring unit group `U^0` is
the full Galois group of a transported Lubin--Tate level. -/
theorem
    equalCharacteristicTransportedLubinTateArtinPrincipalUnitsImage_zero_eq_top
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let L := equalCharacteristicLubinTateLevelField F n
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
    (LocalFieldTheory.fieldPrincipalUnits K 0).map
        (abelianLocalArtinMonoidHom K L) = ⊤ := by
  let F := equalCharacteristicTargetLocalField K
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let L := equalCharacteristicLubinTateLevelField F n
  let : CharP K p := hKp
  let : Algebra K L :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  let : FiniteDimensional K L :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ n
  let : IsAbelianGalois K L :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ n
  let φ : Kˣ →* Gal(L/K) :=
    abelianLocalArtinMonoidHom K L
  have hφ : Function.Surjective φ := by
    change Function.Surjective (abelianLocalArtinMonoidHom K L)
    exact abelianLocalArtinMonoidHom_surjective K L
  have hNorm :
      Subgroup.zpowers ϖ ≤
        localNormSubgroup K L := by
    change
      Subgroup.zpowers ϖ ≤
        equalCharacteristicTransportedLubinTateNormSubgroup
          K p ϖ hϖ n
    rw [
      equalCharacteristicTransportedLubinTateNormSubgroup_eq_uniformizerPrincipalSubgroup]
    simp [LocalFieldTheory.uniformizerPrincipalSubgroup]
  have hφKer : φ.ker = localNormSubgroup K L := by
    change
      (abelianLocalArtinMonoidHom K L).ker =
        localNormSubgroup K L
    exact abelianLocalArtinMonoidHom_ker K L
  have hϖKer : Subgroup.zpowers ϖ ≤ φ.ker := by
    rw [hφKer]
    exact hNorm
  exact
    principalUnitsImage_zero_eq_top_of_uniformizer_zpowers_le_ker
      K φ hφ ϖ hϖ hϖKer

/-- The zeroth target-field Artin principal-unit group is full. -/
theorem
    equalCharacteristicTransportedLubinTateArtinPrincipalUnitGroup_zero_eq_top
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let L := equalCharacteristicLubinTateLevelField F n
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
    artinPrincipalUnitGroup K L 0 = ⊤ := by
  simpa only [artinPrincipalUnitGroup] using
    equalCharacteristicTransportedLubinTateArtinPrincipalUnitsImage_zero_eq_top
      K p ϖ hϖ n

/-- At the last visible integral index, the target-field upper
ramification group is trivial. -/
theorem
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_succ_eq_bot
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : Algebra B L :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    letI : IsGalois B L :=
      equalCharacteristicLubinTateLevelField_isGalois F n
    letI : CharP K p := hKp
    letI : Algebra K L :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    letI : FiniteDimensional K L :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K p ϖ hϖ n
    letI : IsGalois K L :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K p ϖ hϖ n
    localUpperRamificationGroup K L ((n + 1 : ℕ) : ℝ) = ⊥ := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let L := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B :=
    equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let finBL : FiniteDimensional B L :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let upperB :=
    @localUpperRamificationGroup B L
      inferInstance inferInstance
      inferInstance finBL inferInstance
      inferInstance inferInstance inferInstance
  have hSource : upperB ((n + 1 : ℕ) : ℝ) = ⊥ := by
    simpa only [upperB, F, B, L] using
      equalCharacteristicLubinTateLocalUpperRamificationGroup_succ_eq_bot
        F n
  let algBL : Algebra B L :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let : CharP K p := hKp
  let algKL : Algebra K L :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  let : Module K L := Algebra.toModule
  let galKL : IsGalois K L :=
    equalCharacteristicTransportedLubinTateLevel_isGalois
      K p ϖ hϖ n
  let finKL : FiniteDimensional K L :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ n
  let upperK :=
    @localUpperRamificationGroup K L
      inferInstance inferInstance
      algKL finKL galKL
      inferInstance inferInstance inferInstance
  let q :=
    equalCharacteristicTransportedLubinTateGaloisEquiv
      K p ϖ hϖ n
  have hMap :
      Subgroup.map q.toMonoidHom (upperB ((n + 1 : ℕ) : ℝ)) =
        upperK ((n + 1 : ℕ) : ℝ) := by
    simpa only [upperB, upperK, q, F, B, L] using
      equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq
        K p (hKp := hKp) ϖ hϖ n ((n + 1 : ℕ) : ℝ)
  change upperK ((n + 1 : ℕ) : ℝ) = ⊥
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  have hσ' :
      σ ∈ Subgroup.map q.toMonoidHom
        (upperB ((n + 1 : ℕ) : ℝ)) := by
    rw [hMap]
    exact hσ
  rcases hσ' with ⟨τ, hτ, rfl⟩
  have hτ' : τ = 1 := by
    rw [hSource] at hτ
    exact hτ
  rw [hτ', map_one]

/-- The target-field Artin principal-unit group at level `n+1` is
trivial. -/
theorem
    equalCharacteristicTransportedLubinTateArtinPrincipalUnitGroup_succ_eq_bot
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) :
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
    artinPrincipalUnitGroup K L (n + 1) = ⊥ := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let L := equalCharacteristicLubinTateLevelField F n
  let : Algebra B L :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let : CharP K p := hKp
  let : Algebra K L :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  let : FiniteDimensional K L :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ n
  let : IsAbelianGalois K L :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ n
  change
    (LocalFieldTheory.fieldPrincipalUnits K (n + 1)).map
        (abelianLocalArtinMonoidHom K L) = ⊥
  exact
    (equalCharacteristicTransportedLubinTateArtinPrincipalUnitsImage_eq_localUpperRamificationGroup
      K p ϖ hϖ n (n + 1) (by omega) (by omega)).trans
      (equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_succ_eq_bot
        K p ϖ hϖ n)

/-- On the visible positive range, the target-field upper filtration is the
natural-ceiling step extension of its integral values. -/
theorem
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_eq_natCeil
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (t : ℝ)
    (hk : 1 ≤ ⌈t⌉₊) (hkn : ⌈t⌉₊ ≤ n + 1) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let L := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : Algebra B L :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    letI : IsGalois B L :=
      equalCharacteristicLubinTateLevelField_isGalois F n
    letI : CharP K p := hKp
    letI : Algebra K L :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    letI : FiniteDimensional K L :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K p ϖ hϖ n
    letI : IsGalois K L :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K p ϖ hϖ n
    localUpperRamificationGroup K L t =
      localUpperRamificationGroup K L (⌈t⌉₊ : ℝ) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let L := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B :=
    equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let finBL : FiniteDimensional B L :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let upperB :=
    @localUpperRamificationGroup B L
      inferInstance inferInstance
      inferInstance finBL inferInstance
      inferInstance inferInstance inferInstance
  have hSource :
      upperB t = upperB (⌈t⌉₊ : ℝ) := by
    calc
      upperB t =
          equalCharacteristicLubinTateRealUpperRamificationGroup
            F n t := by
        simpa only [upperB, F, B, L] using
          (equalCharacteristicLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
            F n t).symm
      _ =
          equalCharacteristicLubinTateRealUpperRamificationGroup
            F n (⌈t⌉₊ : ℝ) :=
        equalCharacteristicLubinTateRealUpperRamificationGroup_eq_natCeil
          F n t hk hkn
      _ = upperB (⌈t⌉₊ : ℝ) := by
        simpa only [upperB, F, B, L] using
          equalCharacteristicLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
            F n (⌈t⌉₊ : ℝ)
  let algBL : Algebra B L :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let : CharP K p := hKp
  let algKL : Algebra K L :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  let : Module K L := Algebra.toModule
  let galKL : IsGalois K L :=
    equalCharacteristicTransportedLubinTateLevel_isGalois
      K p ϖ hϖ n
  let finKL : FiniteDimensional K L :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ n
  let upperK :=
    @localUpperRamificationGroup K L
      inferInstance inferInstance
      algKL finKL galKL
      inferInstance inferInstance inferInstance
  let q :=
    equalCharacteristicTransportedLubinTateGaloisEquiv
      K p ϖ hϖ n
  have hMap :
      Subgroup.map q.toMonoidHom (upperB t) = upperK t := by
    simpa only [upperB, upperK, q, F, B, L] using
      equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq
        K p (hKp := hKp) ϖ hϖ n t
  have hMapCeil :
      Subgroup.map q.toMonoidHom (upperB (⌈t⌉₊ : ℝ)) =
        upperK (⌈t⌉₊ : ℝ) := by
    simpa only [upperB, upperK, q, F, B, L] using
      equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq
        K p (hKp := hKp) ϖ hϖ n (⌈t⌉₊ : ℝ)
  change upperK t = upperK (⌈t⌉₊ : ℝ)
  calc
    upperK t = Subgroup.map q.toMonoidHom (upperB t) := hMap.symm
    _ = Subgroup.map q.toMonoidHom (upperB (⌈t⌉₊ : ℝ)) := by
      rw [hSource]
    _ = upperK (⌈t⌉₊ : ℝ) := hMapCeil

/-- Beyond the last visible level, the target-field Artin step group is
trivial. -/
theorem
    equalCharacteristicTransportedLubinTateArtinPrincipalUnitStepGroup_eq_bot_of_level_lt_ceil
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (t : ℝ) (hlevel : n + 1 < ⌈t⌉₊) :
    let F := equalCharacteristicTargetLocalField K
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let L := equalCharacteristicLubinTateLevelField F n
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
    artinPrincipalUnitStepGroup K L t = ⊥ := by
  let F := equalCharacteristicTargetLocalField K
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let L := equalCharacteristicLubinTateLevelField F n
  let : CharP K p := hKp
  let : Algebra K L :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  let : FiniteDimensional K L :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ n
  let : IsAbelianGalois K L :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ n
  unfold artinPrincipalUnitStepGroup
    RamificationTheory.natCeilStepFiltration
  apply le_antisymm
  · have hle :=
      artinPrincipalUnitGroup_antitone K L (Nat.le_of_lt hlevel)
    rw [
      equalCharacteristicTransportedLubinTateArtinPrincipalUnitGroup_succ_eq_bot
        K p ϖ hϖ n] at hle
    exact hle
  · exact bot_le

/-- Beyond the last visible level, the target-field upper ramification
group is trivial. -/
theorem
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_eq_bot_of_level_lt_ceil
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (t : ℝ) (hlevel : n + 1 < ⌈t⌉₊) :
    let F := equalCharacteristicTargetLocalField K
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let L := equalCharacteristicLubinTateLevelField F n
    letI : CharP K p := hKp
    letI : Algebra K L :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    letI : FiniteDimensional K L :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K p ϖ hϖ n
    letI : IsGalois K L :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K p ϖ hϖ n
    localUpperRamificationGroup K L t = ⊥ := by
  let F := equalCharacteristicTargetLocalField K
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let L := equalCharacteristicLubinTateLevelField F n
  let : CharP K p := hKp
  let : Algebra K L :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  let : FiniteDimensional K L :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ n
  let : IsGalois K L :=
    equalCharacteristicTransportedLubinTateLevel_isGalois
      K p ϖ hϖ n
  have ht : (((n + 1 : ℕ) : ℝ)) ≤ t := by
    have hsucc : n + 1 + 1 ≤ ⌈t⌉₊ := by
      omega
    exact (Nat.add_one_le_ceil_iff.mp hsucc).le
  apply le_antisymm
  · have hle := localUpperRamificationGroup_antitone K L ht
    rw [
      equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_succ_eq_bot
        K p ϖ hϖ n] at hle
    exact hle
  · exact bot_le

/-- Real filtered local reciprocity for every transported
equal-characteristic Lubin--Tate level. -/
theorem
    equalCharacteristicTransportedLubinTateArtinPrincipalUnitStepGroup_eq_localUpperRamificationGroup
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    let F := equalCharacteristicTargetLocalField K
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let L := equalCharacteristicLubinTateLevelField F n
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
    artinPrincipalUnitStepGroup K L t =
      localUpperRamificationGroup K L t := by
  let F := equalCharacteristicTargetLocalField K
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let L := equalCharacteristicLubinTateLevelField F n
  let k : ℕ := ⌈t⌉₊
  let : CharP K p := hKp
  let : Algebra K L :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  let : FiniteDimensional K L :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ n
  let : IsAbelianGalois K L :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ n
  by_cases hkzero : k = 0
  · have hceilzero : ⌈t⌉₊ = 0 := by
      simpa only [k] using hkzero
    have htzero : t = 0 :=
      le_antisymm (Nat.ceil_eq_zero.mp hceilzero) ht
    subst t
    calc
      artinPrincipalUnitStepGroup K L (0 : ℝ) = ⊤ := by
        simpa [artinPrincipalUnitStepGroup,
          RamificationTheory.natCeilStepFiltration] using
          equalCharacteristicTransportedLubinTateArtinPrincipalUnitGroup_zero_eq_top
            K p ϖ hϖ n
      _ = localUpperRamificationGroup K L 0 :=
        (equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_zero_eq_top
          K p ϖ hϖ n).symm
  · have hk : 1 ≤ k := by
      omega
    by_cases hkn : k ≤ n + 1
    · have hLocalStep :
          localUpperRamificationGroup K L t =
            localUpperRamificationGroup K L (k : ℝ) := by
        simpa only [k] using
          equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_eq_natCeil
            K p ϖ hϖ n t
              (by simpa only [k] using hk)
              (by simpa only [k] using hkn)
      change
        (LocalFieldTheory.fieldPrincipalUnits K k).map
            (abelianLocalArtinMonoidHom K L) =
          localUpperRamificationGroup K L t
      exact
        (equalCharacteristicTransportedLubinTateArtinPrincipalUnitsImage_eq_localUpperRamificationGroup
          K p ϖ hϖ n k hk hkn).trans hLocalStep.symm
    · have hlevel : n + 1 < ⌈t⌉₊ := by
        dsimp only [k] at hkn
        omega
      exact
        (equalCharacteristicTransportedLubinTateArtinPrincipalUnitStepGroup_eq_bot_of_level_lt_ceil
          K p ϖ hϖ n t hlevel).trans
          (equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_eq_bot_of_level_lt_ceil
            K p ϖ hϖ n t hlevel).symm

end LocalClassFieldTheory
