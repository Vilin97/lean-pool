/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LocalUpperRamification
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardNormSubgroupExact
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.Filtration
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction
/-!
# Filtered Artin comparison for standard Lubin--Tate levels

This module records the characteristic-independent part of the filtered
Artin comparison for the canonical standard Lubin--Tate tower.

The local Artin image of a lower level's norm subgroup is the kernel of
restriction from a higher level, and powers of the chosen base uniformizer
lie in the Artin kernel.  The source theorem
`standardLubinTateCanonicalUniformizerPrincipalSubgroup_eq_normSubgroup`
identifies the canonical norm subgroup with the canonical
uniformizer-principal subgroup.  Rewriting by this equality and cancelling
the uniformizer factor gives the positive integral Artin comparison;
`standardLubinTateRealUpperRamificationGroup_eq_restrictKer` identifies the
same restriction kernel with the upper ramification group.  Concretely, the
proof composes
`standardLubinTateNormSubgroup_map_artin_eq_restrictKer`,
`standardLubinTateBaseUniformizerUnit_zpowers_le_artinKer`, and
`standardLubinTateRealUpperRamificationGroup_eq_restrictKer`, using the exact
norm formula only as the source-produced rewrite between the first two steps.

No norm-subgroup equality or containment is accepted as a theorem
hypothesis here.  The imported equality is proved from the
changed-uniformizer construction, and the zero-index comparison needs only
the independently known uniformizer norm.
-/

@[expose] public section

noncomputable
section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open RamificationTheory RamificationTheory.LocalField

open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate
open RamificationTheory.HilbertRamification.Higher

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Mapping the kernel of a composite through a surjective first map gives
the kernel of the second map. -/
theorem map_composite_ker_eq_ker_of_surjective
    {A G H : Type*} [Group A] [Group G] [Group H]
    (φ : A →* G) (ψ : G →* H)
    (hφ : Function.Surjective φ) :
    (ψ.comp φ).ker.map φ = ψ.ker := by
  rw [← MonoidHom.comap_ker, Subgroup.map_comap_eq,
    φ.range_eq_top_of_surjective hφ, top_inf_eq]

/-- In a tower of standard Lubin--Tate levels, the Artin image of the lower
level norm subgroup is exactly the kernel of restriction to that level. -/
theorem standardLubinTateNormSubgroup_map_artin_eq_restrictKer
    {π : (standardLocalField K).valuationSubring}
    (hπ :
      (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
        (π : K))
    {m n : ℕ} (hmn : m ≤ n) :
    let F := standardLocalField K
    let E := standardLubinTateLevelField hπ m
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K E :=
      standardLubinTateLevelField_finiteDimensional hπ m
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois K E :=
      standardLubinTateLevelField_isAbelianGalois F hπ m
    letI : IsAbelianGalois K L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    (standardLubinTateNormSubgroup hπ m).map
        (abelianLocalArtinMonoidHom K L) =
      (intermediateFieldRestrictNormalHom E L
        (standardLubinTateLevelField_mono hπ hmn)).ker := by
  let F := standardLocalField K
  let E := standardLubinTateLevelField hπ m
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional K E :=
    standardLubinTateLevelField_finiteDimensional hπ m
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois K E :=
    standardLubinTateLevelField_isAbelianGalois F hπ m
  let : IsAbelianGalois K L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  let hEL : E ≤ L := standardLubinTateLevelField_mono hπ hmn
  let φ := abelianLocalArtinMonoidHom K L
  let ψ := intermediateFieldRestrictNormalHom E L hEL
  have hrestrict :
      ψ.comp φ = abelianLocalArtinMonoidHom K E :=
    abelianLocalArtinMonoidHom_restrict K E L hEL
  have hker :
      (ψ.comp φ).ker = standardLubinTateNormSubgroup hπ m := by
    rw [hrestrict, abelianLocalArtinMonoidHom_ker]
    rfl
  calc
    (standardLubinTateNormSubgroup hπ m).map φ =
        (ψ.comp φ).ker.map φ := by rw [hker]
    _ = ψ.ker :=
      map_composite_ker_eq_ker_of_surjective
        φ ψ (abelianLocalArtinMonoidHom_surjective K L)

/-- Every integral power of the chosen standard base uniformizer lies in
the kernel of the standard finite Artin map. -/
theorem standardLubinTateBaseUniformizerUnit_zpowers_le_artinKer
    {π : (standardLocalField K).valuationSubring}
    (hπ :
      (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
        (π : K))
    (n : ℕ) :
    let F := standardLocalField K
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois K L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    Subgroup.zpowers (standardLubinTateBaseUniformizerUnit hπ) ≤
      (abelianLocalArtinMonoidHom K L).ker := by
  let F := standardLocalField K
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois K L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  dsimp only
  rw [abelianLocalArtinMonoidHom_ker]
  change
    Subgroup.zpowers (standardLubinTateBaseUniformizerUnit hπ) ≤
      standardLubinTateNormSubgroup hπ n
  exact
    standardLubinTateBaseUniformizerUnit_zpowers_le_normSubgroup hπ n

/-- In a tower of canonical standard Lubin--Tate levels, the local Artin
image of `U_K^(m+1)` is exactly the kernel of restriction to level `m`.

The exact norm-subgroup formula supplies the composite kernel
`⟨ϖ⟩ · U_K^(m+1)`.  The uniformizer factor is already in the kernel of the
Artin map to the upper level, so only the principal-unit image remains. -/
theorem
    standardLubinTateCanonicalArtinPrincipalUnitsImage_eq_restrictKer
    {m n : ℕ} (hmn : m ≤ n) :
    let F := standardLocalField K
    let hπ := standardLocalFieldUniformizer_isUniformizer K
    let E := standardLubinTateLevelField hπ m
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K E :=
      standardLubinTateLevelField_finiteDimensional hπ m
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois K E :=
      standardLubinTateLevelField_isAbelianGalois F hπ m
    letI : IsAbelianGalois K L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    (LocalFieldTheory.fieldPrincipalUnits K (m + 1)).map
        (abelianLocalArtinMonoidHom K L) =
      (intermediateFieldRestrictNormalHom E L
        (standardLubinTateLevelField_mono hπ hmn)).ker := by
  let F := standardLocalField K
  let hπ := standardLocalFieldUniformizer_isUniformizer K
  let E := standardLubinTateLevelField hπ m
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional K E :=
    standardLubinTateLevelField_finiteDimensional hπ m
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois K E :=
    standardLubinTateLevelField_isAbelianGalois F hπ m
  let : IsAbelianGalois K L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  let φ := abelianLocalArtinMonoidHom K L
  let Z := Subgroup.zpowers (standardLubinTateBaseUniformizerUnit hπ)
  let U := LocalFieldTheory.fieldPrincipalUnits K (m + 1)
  have hZ : Z ≤ φ.ker := by
    simpa only [Z, φ] using
      standardLubinTateBaseUniformizerUnit_zpowers_le_artinKer
        K hπ n
  have hZU :
      Z ⊔ U = standardLubinTateNormSubgroup hπ m := by
    simpa [Z, U, LocalFieldTheory.uniformizerPrincipalSubgroup] using
      standardLubinTateCanonicalUniformizerPrincipalSubgroup_eq_normSubgroup
        K m
  calc
    (LocalFieldTheory.fieldPrincipalUnits K (m + 1)).map φ =
        ⊥ ⊔ U.map φ := by simp [U]
    _ = Z.map φ ⊔ U.map φ := by
      rw [(Subgroup.map_eq_bot_iff Z).2 hZ]
    _ = (Z ⊔ U).map φ :=
      (Subgroup.map_sup Z U φ).symm
    _ = (standardLubinTateNormSubgroup hπ m).map φ := by
      rw [hZU]
    _ =
        (intermediateFieldRestrictNormalHom E L
          (standardLubinTateLevelField_mono hπ hmn)).ker := by
      simpa [F, hπ, E, L, φ] using
        standardLubinTateNormSubgroup_map_artin_eq_restrictKer
          K hπ hmn

/-- Integral filtered local reciprocity for a canonical standard
Lubin--Tate level.  At every positive visible index `k`, the Artin image of
`U_K^k` is the canonical local upper ramification group at `k`. -/
theorem
    standardLubinTateCanonicalArtinPrincipalUnitsImage_eq_localUpperRamificationGroup
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    let F := standardLocalField K
    let hπ := standardLocalFieldUniformizer_isUniformizer K
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois K L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    artinPrincipalUnitGroup K L k =
      localUpperRamificationGroup K L (k : ℝ) := by
  let F := standardLocalField K
  let hπ := standardLocalFieldUniformizer_isUniformizer K
  let L := standardLubinTateLevelField hπ n
  let m := k - 1
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois K L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  have hmn : m ≤ n := by
    dsimp only [m]
    omega
  have hArtin :=
    standardLubinTateCanonicalArtinPrincipalUnitsImage_eq_restrictKer
      K hmn
  have hUpper :=
    standardLubinTateRealUpperRamificationGroup_eq_restrictKer
      K hπ n k hk hkn
  have hLocal :=
    standardLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
      K hπ n (k : ℝ)
  simpa [artinPrincipalUnitGroup, m, Nat.sub_add_cancel hk] using
    hArtin.trans (hUpper.symm.trans hLocal)

/-- The canonical local upper ramification group is trivial at the first
integral index beyond the nontrivial range of standard level `n`. -/
theorem
    standardLubinTateCanonicalLocalUpperRamificationGroup_succ_eq_bot
    (n : ℕ) :
    let F := standardLocalField K
    let hπ := standardLocalFieldUniformizer_isUniformizer K
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsGalois K L :=
      standardLubinTateLevelField_isGalois (F := F) hπ n
    localUpperRamificationGroup K L ((n + 1 : ℕ) : ℝ) = ⊥ := by
  let F := standardLocalField K
  let hπ := standardLocalFieldUniformizer_isUniformizer K
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsGalois K L :=
    standardLubinTateLevelField_isGalois (F := F) hπ n
  have hcard :
      Nat.card
          (standardLubinTateRealUpperRamificationGroup
            hπ n ((n + 1 : ℕ) : ℝ)) = 1 := by
    simpa using
      standardLubinTateRealUpperRamificationGroup_natCard
        F hπ n (n + 1) (by omega) (by omega)
  have hbot :
      standardLubinTateRealUpperRamificationGroup
          hπ n ((n + 1 : ℕ) : ℝ) = ⊥ :=
    Subgroup.eq_bot_of_card_le _ (by omega)
  calc
    localUpperRamificationGroup K L ((n + 1 : ℕ) : ℝ) =
        standardLubinTateRealUpperRamificationGroup
          hπ n ((n + 1 : ℕ) : ℝ) :=
      (standardLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
        K hπ n ((n + 1 : ℕ) : ℝ)).symm
    _ = ⊥ := hbot

/-- The Artin image of `U_K^(n+1)` is trivial on canonical standard level
`n`. -/
theorem
    standardLubinTateCanonicalArtinPrincipalUnitGroup_succ_eq_bot
    (n : ℕ) :
    let F := standardLocalField K
    let hπ := standardLocalFieldUniformizer_isUniformizer K
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois K L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    artinPrincipalUnitGroup K L (n + 1) = ⊥ := by
  let F := standardLocalField K
  let hπ := standardLocalFieldUniformizer_isUniformizer K
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois K L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  exact
    (standardLubinTateCanonicalArtinPrincipalUnitsImage_eq_localUpperRamificationGroup
      K n (n + 1) (by omega) (by omega)).trans
      (standardLubinTateCanonicalLocalUpperRamificationGroup_succ_eq_bot
        K n)

/-- The canonical standard subgroup and the canonical standard norm
subgroup have the same index. -/
theorem
    standardLubinTateCanonicalUniformizerPrincipalSubgroup_index_eq_normSubgroup_index
    (n : ℕ) :
    (LocalFieldTheory.uniformizerPrincipalSubgroup K
        (standardLubinTateBaseUniformizerUnit
          (standardLocalFieldUniformizer_isUniformizer K))
        1 (n + 1)).index =
      (standardLubinTateNormSubgroup
        (standardLocalFieldUniformizer_isUniformizer K) n).index := by
  rw [
    standardLubinTateCanonicalUniformizerPrincipalSubgroup_index,
    standardLubinTateCanonicalNormSubgroup_index]

/-- The index of the canonical uniformizer-principal subgroup is nonzero,
so equality with a containing subgroup of the same index may be concluded
using `subgroup_eq_of_le_of_index_eq_of_ne_zero`. -/
theorem
    standardLubinTateCanonicalUniformizerPrincipalSubgroup_index_ne_zero
    (n : ℕ) :
    (LocalFieldTheory.uniformizerPrincipalSubgroup K
        (standardLubinTateBaseUniformizerUnit
          (standardLocalFieldUniformizer_isUniformizer K))
        1 (n + 1)).index ≠ 0 := by
  rw [standardLubinTateCanonicalUniformizerPrincipalSubgroup_index]
  have hq : 1 < Nat.card 𝓀[K] := by
    exact Finite.one_lt_card
  exact
    Nat.ne_of_gt
      (Nat.mul_pos
        (Nat.sub_pos_of_lt hq)
        (Nat.pow_pos (Nat.zero_lt_one.trans hq)))

omit [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] in
/-- The explicit lower ramification group of a standard Lubin--Tate level
is full at index zero. -/
theorem standardLubinTateRealLowerRamificationGroup_zero_eq_top
    (F : LocalField K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTateRealLowerRamificationGroup hπ n 0 = ⊤ := by
  have hparameter :
      standardLubinTateUnitParameterSubgroup F n 0 = ⊤ := by
    apply top_unique
    intro a _ha
    rw [← standardLubinTateUnitParameterChosenRepresentative_spec F n a]
    exact
      (standardLubinTateUnitParameterClass_mem_subgroup_iff
        F n 0 (Nat.zero_le (n + 1))
        (standardLubinTateUnitParameterChosenRepresentative F n a)).2
        (by simp)
  ext σ
  obtain ⟨a, rfl⟩ :=
    standardLubinTateUnitParameterToGal_surjective F hπ n σ
  rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) by norm_num]
  rw [mem_standardLubinTateRealLowerRamificationGroup_nat_iff_primitivePoint]
  simpa [hparameter] using
    (standardLubinTateUnitParameterToGal_displacement_addVal_ge_iff_mem_parameterSubgroup
      F hπ n a 0 (Nat.zero_le (n + 1)))

omit [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] in
/-- The explicit upper ramification group of a standard Lubin--Tate level
is full at index zero. -/
theorem standardLubinTateRealUpperRamificationGroup_zero_eq_top
    (F : LocalField K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) :
    standardLubinTateRealUpperRamificationGroup hπ n 0 = ⊤ := by
  rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) by norm_num]
  rw [
    standardLubinTateRealUpperRamificationGroup_nat_eq_lower_pow_sub_one
      F hπ n 0 (by omega)]
  simpa using
    standardLubinTateRealLowerRamificationGroup_zero_eq_top K F hπ n

/-- The canonical local upper ramification group of a standard
Lubin--Tate level is full at index zero. -/
theorem standardLubinTateLocalUpperRamificationGroup_zero_eq_top
    {π : (standardLocalField K).valuationSubring}
    (hπ :
      (standardLocalField K).toCompleteDVF.valuation.IsUniformizer
        (π : K))
    (n : ℕ) :
    let F := standardLocalField K
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsGalois K L :=
      standardLubinTateLevelField_isGalois (F := F) hπ n
    localUpperRamificationGroup K L 0 = ⊤ := by
  let F := standardLocalField K
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsGalois K L :=
    standardLubinTateLevelField_isGalois (F := F) hπ n
  calc
    localUpperRamificationGroup K L 0 =
        standardLubinTateRealUpperRamificationGroup hπ n 0 :=
      (standardLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
        K hπ n 0).symm
    _ = ⊤ :=
      standardLubinTateRealUpperRamificationGroup_zero_eq_top K F hπ n

/-- The Artin image of the full valuation-ring unit group is the full
Galois group of a canonical standard Lubin--Tate level. -/
theorem
    standardLubinTateCanonicalArtinPrincipalUnitGroup_zero_eq_top
    (n : ℕ) :
    let F := standardLocalField K
    let hπ := standardLocalFieldUniformizer_isUniformizer K
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois K L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    artinPrincipalUnitGroup K L 0 = ⊤ := by
  let F := standardLocalField K
  let hπ := standardLocalFieldUniformizer_isUniformizer K
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois K L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  let varpi : Kˣ := standardLubinTateBaseUniformizerUnit hπ
  let pi : Kˣ := varpi⁻¹
  have hpi : valuationMap K (Additive.ofMul pi) = 1 := by
    simpa only [pi, varpi] using
      standardLubinTateCanonicalBaseUniformizerUnit_inv_valuationMap K
  have hpiKer :
      Subgroup.zpowers pi ≤
        (abelianLocalArtinMonoidHom K L).ker := by
    rw [abelianLocalArtinMonoidHom_ker]
    change
      Subgroup.zpowers pi ≤
        standardLubinTateNormSubgroup hπ n
    simpa only [pi, varpi, Subgroup.zpowers_inv] using
      standardLubinTateBaseUniformizerUnit_zpowers_le_normSubgroup hπ n
  unfold artinPrincipalUnitGroup
  apply top_unique
  intro σ _hσ
  obtain ⟨x, hx⟩ :=
    abelianLocalArtinMonoidHom_surjective K L σ
  obtain ⟨u, hdecomp⟩ :=
    exists_integerUnit_mul_uniformizer_zpow K pi hpi x
  have hpowKer :
      pi ^ valuationMap K (Additive.ofMul x) ∈
        (abelianLocalArtinMonoidHom K L).ker :=
    hpiKer (Subgroup.zpow_mem_zpowers pi _)
  have hpow :
      abelianLocalArtinMonoidHom K L
          (pi ^ valuationMap K (Additive.ofMul x)) = 1 :=
    MonoidHom.mem_ker.mp hpowKer
  refine ⟨integerUnitsToFieldUnits K u, ?_, ?_⟩
  · unfold LocalFieldTheory.fieldPrincipalUnits
    exact ⟨u, by simp, rfl⟩
  · rw [← hx, ← hdecomp, map_mul, hpow, mul_one]

/-- Filtered local reciprocity holds at real index zero for the canonical
standard Lubin--Tate level. -/
theorem
    standardLubinTateCanonicalArtinPrincipalUnitStepGroup_zero_eq_localUpper
    (n : ℕ) :
    let F := standardLocalField K
    let hπ := standardLocalFieldUniformizer_isUniformizer K
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois K L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    artinPrincipalUnitStepGroup K L 0 =
      localUpperRamificationGroup K L 0 := by
  let F := standardLocalField K
  let hπ := standardLocalFieldUniformizer_isUniformizer K
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois K L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  calc
    artinPrincipalUnitStepGroup K L 0 =
        artinPrincipalUnitGroup K L 0 := by
      simp [artinPrincipalUnitStepGroup, natCeilStepFiltration]
    _ = ⊤ :=
      standardLubinTateCanonicalArtinPrincipalUnitGroup_zero_eq_top K n
    _ = localUpperRamificationGroup K L 0 :=
      (standardLubinTateLocalUpperRamificationGroup_zero_eq_top
        K hπ n).symm

/-- Beyond the last visible standard level, the real Artin
principal-unit step group is trivial. -/
theorem
    standardLubinTateCanonicalArtinPrincipalUnitStepGroup_eq_bot_of_level_lt_ceil
    (n : ℕ) (t : ℝ) (hlevel : n + 1 < ⌈t⌉₊) :
    let F := standardLocalField K
    let hπ := standardLocalFieldUniformizer_isUniformizer K
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois K L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    artinPrincipalUnitStepGroup K L t = ⊥ := by
  let F := standardLocalField K
  let hπ := standardLocalFieldUniformizer_isUniformizer K
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois K L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  unfold artinPrincipalUnitStepGroup natCeilStepFiltration
  apply le_antisymm
  · have hle :=
      artinPrincipalUnitGroup_antitone K L (Nat.le_of_lt hlevel)
    rw [
      standardLubinTateCanonicalArtinPrincipalUnitGroup_succ_eq_bot
        K n] at hle
    exact hle
  · exact bot_le

/-- Beyond the last visible standard level, the canonical local upper
ramification group is trivial. -/
theorem
    standardLubinTateCanonicalLocalUpperRamificationGroup_eq_bot_of_level_lt_ceil
    (n : ℕ) (t : ℝ) (hlevel : n + 1 < ⌈t⌉₊) :
    let F := standardLocalField K
    let hπ := standardLocalFieldUniformizer_isUniformizer K
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsGalois K L :=
      standardLubinTateLevelField_isGalois (F := F) hπ n
    localUpperRamificationGroup K L t = ⊥ := by
  let F := standardLocalField K
  let hπ := standardLocalFieldUniformizer_isUniformizer K
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsGalois K L :=
    standardLubinTateLevelField_isGalois (F := F) hπ n
  have ht : (((n + 1 : ℕ) : ℝ)) ≤ t := by
    have hsucc : n + 1 + 1 ≤ ⌈t⌉₊ := by
      omega
    exact (Nat.add_one_le_ceil_iff.mp hsucc).le
  apply le_antisymm
  · have hle := localUpperRamificationGroup_antitone K L ht
    rw [
      standardLubinTateCanonicalLocalUpperRamificationGroup_succ_eq_bot
        K n] at hle
    exact hle
  · exact bot_le

/-- Real filtered local reciprocity for every canonical standard
Lubin--Tate level.  At each nonnegative real index, the Artin image of the
natural-ceiling principal-unit step is the canonical upper ramification
group. -/
theorem
    standardLubinTateCanonicalArtinPrincipalUnitStepGroup_eq_localUpperRamificationGroup
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    let F := standardLocalField K
    let hπ := standardLocalFieldUniformizer_isUniformizer K
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional K L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois K L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    artinPrincipalUnitStepGroup K L t =
      localUpperRamificationGroup K L t := by
  let F := standardLocalField K
  let hπ := standardLocalFieldUniformizer_isUniformizer K
  let L := standardLubinTateLevelField hπ n
  let k : ℕ := ⌈t⌉₊
  let : FiniteDimensional K L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois K L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  by_cases hkzero : k = 0
  · have hceilzero : ⌈t⌉₊ = 0 := by
      simpa only [k] using hkzero
    have htzero : t = 0 :=
      le_antisymm (Nat.ceil_eq_zero.mp hceilzero) ht
    subst t
    exact
      standardLubinTateCanonicalArtinPrincipalUnitStepGroup_zero_eq_localUpper
        K n
  · have hk : 1 ≤ k := by
      omega
    by_cases hkn : k ≤ n + 1
    · have hLocalStep :
          localUpperRamificationGroup K L t =
            localUpperRamificationGroup K L (k : ℝ) := by
        calc
          localUpperRamificationGroup K L t =
              standardLubinTateRealUpperRamificationGroup hπ n t :=
            (standardLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
              K hπ n t).symm
          _ =
              standardLubinTateRealUpperRamificationGroup
                hπ n (k : ℝ) := by
            have hstep :=
              standardLubinTateRealUpperRamificationGroup_eq_natCeil
                F hπ n t
                  (by simpa only [k] using hk)
                  (by simpa only [k] using hkn)
            simpa only [k] using hstep
          _ = localUpperRamificationGroup K L (k : ℝ) :=
            standardLubinTateRealUpperRamificationGroup_eq_localUpperRamificationGroup
              K hπ n (k : ℝ)
      change
        artinPrincipalUnitGroup K L k =
          localUpperRamificationGroup K L t
      exact
        (standardLubinTateCanonicalArtinPrincipalUnitsImage_eq_localUpperRamificationGroup
          K n k hk hkn).trans hLocalStep.symm
    · have hlevel : n + 1 < ⌈t⌉₊ := by
        dsimp only [k] at hkn
        omega
      exact
        (standardLubinTateCanonicalArtinPrincipalUnitStepGroup_eq_bot_of_level_lt_ceil
          K n t hlevel).trans
          (standardLubinTateCanonicalLocalUpperRamificationGroup_eq_bot_of_level_lt_ceil
            K n t hlevel).symm

end LocalClassFieldTheory

end
