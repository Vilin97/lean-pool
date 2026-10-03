/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.HerbrandFunctionAtLowerIndex
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.HerbrandFunction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.InverseHerbrandFunction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.IsUpperRamificationJump
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.IsLowerRamificationJump
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.RealLowerRamificationGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.UpperRamificationGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Algebra.AbelianGaloisEquiv
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport
public import Mathlib.Algebra.Algebra.Shrink
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.AbstractUnramified
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Compositum
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.EqualCharacteristic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.EqualCharacteristicStandardCompositum
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelian
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.StandardCompositum
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Unramified
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Core
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.BaseChange
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Unramified
public import Mathlib.FieldTheory.Fixed
public import Mathlib.SetTheory.Cardinal.Finite
/-!
# Hasse--Arf

Reader-facing facade for the Hasse--Arf theorem: upper ramification jumps of
finite Abelian local extensions are integral.  Reusable ramification,
Lubin--Tate, and local reciprocity infrastructure is exported by its owner
libraries rather than through this facade.
-/

@[expose] public section

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction →
    herbrandFunction

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction_nat →
    herbrandFunction_nat

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction_of_floor →
    herbrandFunction_of_floor

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction_of_nonpos →
    herbrandFunction_of_nonpos

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandValueNat →
    herbrandValueNat

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandValueNat_succ →
    herbrandValueNat_succ

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandValueNat_zero →
    herbrandValueNat_zero

open _root_.RamificationTheory.DiscreteValuationField.DVF renaming
  mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension →
    mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension


/-!
# Hasse--Arf integrality

Filtered local reciprocity identifies the Artin principal-unit step
filtration with the upper ramification filtration.  Since the former changes
only at natural-number indices, every upper jump of a finite Abelian local
extension is integral (with the separate possible endpoint `-1`).
-/

noncomputable
section

namespace ClassFieldTheory

universe u v

/-- Each lower ramification group of a finite extension is finite. -/
theorem lowerRamificationGroup_finite
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (A : ValuationSubring L) (n : ℕ) :
    Finite (lowerRamificationGroup K A n) := by
  classical
  infer_instance

/-- The order of each lower ramification group of a finite extension is positive. -/
theorem lowerRamificationGroup_card_pos
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (A : ValuationSubring L) (n : ℕ) :
    0 < Nat.card (lowerRamificationGroup K A n) := by
  exact Nat.card_pos (α := lowerRamificationGroup K A n)

/-- Successive rational Herbrand values differ by the normalized cardinality
of the next lower ramification group. -/
theorem herbrandFunctionAtLowerIndex_succ
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (n : ℕ) :
    herbrandFunctionAtLowerIndex K A (n + 1) =
      herbrandFunctionAtLowerIndex K A n +
        (Nat.card (lowerRamificationGroup K A (n + 1)) : ℚ) /
          Nat.card (lowerRamificationGroup K A 0) := by
  unfold herbrandFunctionAtLowerIndex
  rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)), add_div]

end ClassFieldTheory

namespace HasseArf

open LocalClassFieldTheory
open RamificationTheory
open RamificationTheory.LocalField
open RamificationTheory.HilbertRamification.Higher
open LocalFieldTheory
open scoped Pointwise

/-! ## From filtered reciprocity to integral upper jumps -/

/-- If filtered local reciprocity has been established for a finite Abelian
extension at nonnegative indices, then the right-limit at a nonnegative
index is the right-limit of the Artin principal-unit filtration. -/
theorem
    localUpperRamificationGroupAfter_eq_artinPrincipalUnitStepGroupAfter_of_filteredLocalReciprocity
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hfiltered : ∀ t, 0 ≤ t →
      artinPrincipalUnitStepGroup K L t =
        localUpperRamificationGroup K L t)
    (t : ℝ) (ht : 0 ≤ t) :
    localUpperRamificationGroupAfter K L t =
      natCeilStepFiltrationAfter (artinPrincipalUnitGroup K L) t := by
  unfold localUpperRamificationGroupAfter
  unfold natCeilStepFiltrationAfter
  apply iSup_congr
  intro s
  exact (hfiltered s (ht.trans s.property.le)).symm

/-- At a nonnegative index, filtered local reciprocity identifies intrinsic
upper jumps with jumps of the Artin principal-unit step filtration. -/
theorem
    isLocalUpperRamificationJump_iff_isArtinPrincipalUnitJump_of_filteredLocalReciprocity
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hfiltered : ∀ t, 0 ≤ t →
      artinPrincipalUnitStepGroup K L t =
        localUpperRamificationGroup K L t)
    (t : ℝ) (ht : 0 ≤ t) :
    IsLocalUpperRamificationJump K L t ↔
      IsArtinPrincipalUnitJump K L t := by
  unfold IsLocalUpperRamificationJump
  unfold IsArtinPrincipalUnitJump
  rw [← hfiltered t ht]
  rw [
    localUpperRamificationGroupAfter_eq_artinPrincipalUnitStepGroupAfter_of_filteredLocalReciprocity
      K L hfiltered t ht]
  rfl

/-- The nonnegative part of the formal Hasse--Arf implication: once filtered
local reciprocity is known for a finite Abelian extension, every nonnegative
actual upper jump is a natural number.  The possible index `-1` is handled
separately from the principal-unit filtration. -/
theorem
    isLocalUpperRamificationJump_integer_of_filteredLocalReciprocity
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hfiltered : ∀ t, 0 ≤ t →
      artinPrincipalUnitStepGroup K L t =
        localUpperRamificationGroup K L t)
    {t : ℝ} (ht0 : 0 ≤ t)
    (ht : IsLocalUpperRamificationJump K L t) :
    ∃ n : ℕ, t = n := by
  exact isArtinPrincipalUnitJump_integer K L
    ((isLocalUpperRamificationJump_iff_isArtinPrincipalUnitJump_of_filteredLocalReciprocity
      K L hfiltered t ht0).mp ht)

/-- The full formal Hasse--Arf implication from filtered local reciprocity:
every actual upper jump is an integer.  The endpoint `-1` is treated directly,
while every other jump is nonnegative and hence comes from the natural-number
principal-unit filtration. -/
theorem
    isLocalUpperRamificationJump_int_of_filteredLocalReciprocity
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hfiltered : ∀ t, 0 ≤ t →
      artinPrincipalUnitStepGroup K L t =
        localUpperRamificationGroup K L t)
    {t : ℝ} (ht : IsLocalUpperRamificationJump K L t) :
    ∃ z : ℤ, t = z := by
  rcases isLocalUpperRamificationJump_eq_neg_one_or_nonneg K L ht with hneg | ht0
  · exact ⟨-1, by simpa using hneg⟩
  · obtain ⟨n, hn⟩ :=
      isLocalUpperRamificationJump_integer_of_filteredLocalReciprocity
        K L hfiltered ht0 ht
    exact ⟨n, by simpa using hn⟩

/-- Hasse--Arf integrality: every actual upper ramification jump of
a finite Abelian local extension is an integer. -/
theorem isLocalUpperRamificationJump_int
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {t : ℝ} (ht : IsLocalUpperRamificationJump K L t) :
    ∃ z : ℤ, t = z := by
  exact
    isLocalUpperRamificationJump_int_of_filteredLocalReciprocity
      K L
      (fun s hs =>
        finiteAbelian_filteredLocalReciprocity K L s hs)
      ht

/-- The chosen valuation ring of a finite local extension is invariant under
every base-field automorphism. Thus its Mathlib decomposition group is the
entire Galois group. -/
theorem chosenLocalExtension_decompositionSubgroup_eq_top
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ((chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring).decompositionSubgroup K =
      ⊤ := by
  let base := (localCompleteDVF K).toDVF
  let target := (chosenLocalExtensionCompleteDVF K L).toDVF
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, 0}
        base target :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  apply (Subgroup.eq_top_iff' _).2
  intro σ
  change σ • target.valuation.valuationSubring = target.valuation.valuationSubring
  ext z
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact
    (mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
    (base := base) (target := target) huniq σ⁻¹ z).symm

/-- At integer indices the lower group defined using Mathlib's valuation
subring action agrees elementwise with the existing local lower group. -/
theorem mem_chosenLowerRamificationGroup_iff_mem_localLowerRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ) (σ : Gal(L/K))
    (hσ : σ ∈
      ((chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring).decompositionSubgroup K) :
    (⟨σ, hσ⟩ :
      ((chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring).decompositionSubgroup K) ∈
        ClassFieldTheory.lowerRamificationGroup K
          (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring n ↔
      σ ∈ localLowerRamificationGroup K L (n : ℝ) := by
  let base := (localCompleteDVF K).toDVF
  let target := (chosenLocalExtensionCompleteDVF K L).toDVF
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, 0}
        base target :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  have hact (a : target.valuationSubring) :
      (⟨σ, hσ⟩ : target.valuation.valuationSubring.decompositionSubgroup K) • a =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a := by
    apply Subtype.ext
    rfl
  change (∀ a : target.valuationSubring,
    (⟨σ, hσ⟩ : target.valuation.valuationSubring.decompositionSubgroup K) • a - a ∈
      (IsLocalRing.maximalIdeal target.valuationSubring) ^ (n + 1)) ↔
    σ ∈ lowerRamificationGroup
      (base := base) (target := target) huniq (n : ℝ)
  rw [mem_lowerRamificationGroup_nat_iff]
  simp only [hact]

/-- At every real index, the lower group of the chosen valuation ring agrees
elementwise with the existing local lower filtration after forgetting the
decomposition-subgroup wrapper. -/
theorem mem_chosenRealLowerRamificationGroup_iff_mem_localLowerRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (s : ℝ) (σ : Gal(L/K))
    (hσ : σ ∈
      ((chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring).decompositionSubgroup K) :
    (⟨σ, hσ⟩ :
      ((chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring).decompositionSubgroup K) ∈
        ClassFieldTheory.realLowerRamificationGroup K
          (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring s ↔
      σ ∈ localLowerRamificationGroup K L s := by
  let base := (localCompleteDVF K).toDVF
  let target := (chosenLocalExtensionCompleteDVF K L).toDVF
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, 0}
        base target :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  have hact (a : target.valuationSubring) :
      (⟨σ, hσ⟩ : target.valuation.valuationSubring.decompositionSubgroup K) • a =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a := by
    apply Subtype.ext
    rfl
  change (∀ a : target.valuationSubring,
    (⟨σ, hσ⟩ : target.valuation.valuationSubring.decompositionSubgroup K) • a - a ∈
      (IsLocalRing.maximalIdeal target.valuationSubring) ^
        (Int.ceil (s + 1)).toNat) ↔
    σ ∈ RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup
      (base := base) (target := target) huniq s
  rw [RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff]
  change (∀ a : target.valuationSubring,
    (⟨σ, hσ⟩ : target.valuation.valuationSubring.decompositionSubgroup K) • a - a ∈
      (IsLocalRing.maximalIdeal target.valuationSubring) ^
        (Int.ceil (s + 1)).toNat) ↔
    (∀ a : target.valuationSubring,
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a - a ∈
        (IsLocalRing.maximalIdeal target.valuationSubring) ^
          (Int.ceil (s + 1)).toNat)
  simp only [hact]

/-- The finite lower groups in Mathlib's valuation-subring model and in the
existing local filtration have the same elements, after forgetting the
decomposition-subgroup wrapper. -/
noncomputable def chosenLowerRamificationGroupEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    ClassFieldTheory.lowerRamificationGroup K
        (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring n ≃
      localLowerRamificationGroup K L (n : ℝ) := by
  have htop := chosenLocalExtension_decompositionSubgroup_eq_top K L
  refine {
    toFun := fun g =>
      ⟨g.1.1,
        (mem_chosenLowerRamificationGroup_iff_mem_localLowerRamificationGroup
          K L n g.1.1 g.1.2).mp g.2⟩
    invFun := fun g =>
      ⟨⟨g.1, by rw [htop]; trivial⟩,
        (mem_chosenLowerRamificationGroup_iff_mem_localLowerRamificationGroup
          K L n g.1 (by rw [htop]; trivial)).mpr g.2⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro g
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro g
    apply Subtype.ext
    rfl

/-- The public-style lower group has the same cardinality as the original
local lower group at every nonnegative integral index. -/
theorem card_chosenLowerRamificationGroup_eq_card_localLowerRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    Nat.card (ClassFieldTheory.lowerRamificationGroup K
      (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring n) =
      Nat.card (localLowerRamificationGroup K L (n : ℝ)) :=
  Nat.card_congr (chosenLowerRamificationGroupEquiv K L n)

/-- Successive rational Herbrand values differ by the normalized cardinality
of the next lower group. -/
theorem herbrandFunctionAtLowerIndex_succ
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (n : ℕ) :
    ClassFieldTheory.herbrandFunctionAtLowerIndex K A (n + 1) =
    ClassFieldTheory.herbrandFunctionAtLowerIndex K A n +
        (Nat.card (ClassFieldTheory.lowerRamificationGroup K A (n + 1)) : ℚ) /
          Nat.card (ClassFieldTheory.lowerRamificationGroup K A 0) :=
  ClassFieldTheory.herbrandFunctionAtLowerIndex_succ K A n

/-- After the canonical inclusion `ℚ → ℝ`, the rational finite-sum
Herbrand value agrees with the Herbrand function used by local reciprocity. -/
theorem chosenHerbrandFunctionAtLowerIndex_real_eq
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    ((ClassFieldTheory.herbrandFunctionAtLowerIndex K
      (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring n : ℚ) : ℝ) =
      herbrandFunctionOfUniqueExtension
        (base := (localCompleteDVF K).toDVF)
        (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
        (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L)
        (n : ℝ) := by
  let base := (localCompleteDVF K).toDVF
  let target := (chosenLocalExtensionCompleteDVF K L).toDVF
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, 0}
        base target :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  let F := lowerRamificationFiltrationOfUniqueExtension
    (base := base) (target := target) huniq
  change ((ClassFieldTheory.herbrandFunctionAtLowerIndex K
      target.valuation.valuationSubring n : ℚ) : ℝ) =
    herbrandFunction
      F (n : ℝ)
  induction n with
  | zero =>
      simp only [ClassFieldTheory.herbrandFunctionAtLowerIndex,
        show Finset.Icc (1 : ℕ) 0 = ∅ from by decide,
        Finset.sum_empty, zero_div, Rat.cast_zero,
        herbrandFunction_nat,
        herbrandValueNat_zero]
  | succ n ih =>
      rw [herbrandFunctionAtLowerIndex_succ, Rat.cast_add, Rat.cast_div]
      rw [herbrandFunction_nat,
        herbrandValueNat_succ]
      rw [←
        herbrandFunction_nat
        F n, ih]
      congr 1
      rw [RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandSlope]
      rw [show F.lower (n + 1) =
        localLowerRamificationGroup K L ((n + 1 : ℕ) : ℝ) from rfl]
      rw [show F.lower 0 = localLowerRamificationGroup K L (0 : ℝ) by
        unfold F
        rw [lowerRamificationFiltrationOfUniqueExtension_lower]
        unfold localLowerRamificationGroup
        simp only [Nat.cast_zero]]
      rw [card_chosenLowerRamificationGroup_eq_card_localLowerRamificationGroup K L (n + 1),
        card_chosenLowerRamificationGroup_eq_card_localLowerRamificationGroup K L 0]
      simp only [Rat.cast_natCast, Nat.cast_zero]

/-- For an extension carrying its own compatible local-field valuation, the
chosen integral-closure valuation ring is exactly the canonical one. -/
theorem chosenLocalExtension_valuationSubring_eq_canonical
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring =
      (ValuativeRel.valuation L).valuationSubring := by
  let : (localCompleteDVF K).valuation.HasExtension (ValuativeRel.valuation L) := by
    rw [localCompleteDVF_valuation_eq]
    exact ‹Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)›
  exact
    ValuationTheory.DiscreteValuationField.ValuedExtension.valuationSubring_eq_of_finite_separable
    (localCompleteDVF K) (chosenLocalExtensionCompleteDVF K L)
      (ValuativeRel.valuation L)

/-- The public canonical Herbrand value agrees with the old local Herbrand
function at each natural index, after casting from rationals to reals. -/
theorem canonicalHerbrandFunctionAtLowerIndex_real_eq
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (n : ℕ) :
    ((ClassFieldTheory.herbrandFunctionAtLowerIndex K
      (ValuativeRel.valuation L).valuationSubring n : ℚ) : ℝ) =
      herbrandFunctionOfUniqueExtension
        (base := (localCompleteDVF K).toDVF)
        (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
        (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L)
        (n : ℝ) := by
  rw [← chosenLocalExtension_valuationSubring_eq_canonical K L]
  exact chosenHerbrandFunctionAtLowerIndex_real_eq K L n

/-- The public piecewise-linear Herbrand function of the chosen valuation
ring agrees at every real index with the existing local Herbrand function. -/
theorem chosenHerbrandFunction_eq_localHerbrandFunction
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (s : ℝ) :
    ClassFieldTheory.herbrandFunction K
        (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring s =
      herbrandFunctionOfUniqueExtension
        (base := (localCompleteDVF K).toDVF)
        (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
        (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L) s := by
  let base := (localCompleteDVF K).toDVF
  let target := (chosenLocalExtensionCompleteDVF K L).toDVF
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, 0}
        base target :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  let F := lowerRamificationFiltrationOfUniqueExtension
    (base := base) (target := target) huniq
  have hcard (m : ℕ) :
      Nat.card (ClassFieldTheory.lowerRamificationGroup K
        target.valuation.valuationSubring m) = Nat.card (F.lower m) := by
    calc
      Nat.card (ClassFieldTheory.lowerRamificationGroup K
          target.valuation.valuationSubring m) =
          Nat.card (localLowerRamificationGroup K L (m : ℝ)) :=
        card_chosenLowerRamificationGroup_eq_card_localLowerRamificationGroup K L m
      _ = Nat.card (F.lower m) := rfl
  have hnat (m : ℕ) :
      ((ClassFieldTheory.herbrandFunctionAtLowerIndex K
        target.valuation.valuationSubring m : ℚ) : ℝ) =
        herbrandValueNat
          F m := by
    calc
      ((ClassFieldTheory.herbrandFunctionAtLowerIndex K
          target.valuation.valuationSubring m : ℚ) : ℝ) =
          herbrandFunctionOfUniqueExtension
            (base := base) (target := target) huniq (m : ℝ) :=
        chosenHerbrandFunctionAtLowerIndex_real_eq K L m
      _ =
          herbrandValueNat
            F m := by
        change
          herbrandFunction
            F (m : ℝ) = _
        exact
          herbrandFunction_nat
            F m
  have hslope (m : ℕ) :
      ((Nat.card (ClassFieldTheory.lowerRamificationGroup K
        target.valuation.valuationSubring (m + 1)) : ℝ) /
          Nat.card (ClassFieldTheory.lowerRamificationGroup K
            target.valuation.valuationSubring 0)) =
        RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandSlope
          F m := by
    unfold RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandSlope
    rw [hcard (m + 1), hcard 0]
  change ClassFieldTheory.herbrandFunction K target.valuation.valuationSubring s =
    herbrandFunction
      F s
  unfold ClassFieldTheory.herbrandFunction
  by_cases hs : 0 ≤ s
  · rw [ite_eq_left hs]
    dsimp only
    rw [herbrandFunction_of_floor
      F hs ⌊s⌋₊ rfl]
    rw [hnat ⌊s⌋₊, hslope ⌊s⌋₊]
  · rw [ite_eq_right hs]
    exact
      (herbrandFunction_of_nonpos
        F (le_of_lt (lt_of_not_ge hs))).symm

/-- The public piecewise-linear Herbrand function of the canonical valuation
ring agrees at every real index with the existing local Herbrand function. -/
theorem canonicalHerbrandFunction_eq_localHerbrandFunction
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (s : ℝ) :
    ClassFieldTheory.herbrandFunction K
        (ValuativeRel.valuation L).valuationSubring s =
      herbrandFunctionOfUniqueExtension
        (base := (localCompleteDVF K).toDVF)
        (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
        (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L) s := by
  rw [← chosenLocalExtension_valuationSubring_eq_canonical K L]
  exact chosenHerbrandFunction_eq_localHerbrandFunction K L s

/-- The inverse of the public canonical Herbrand function agrees with the
inverse used by the existing local upper filtration. -/
theorem canonicalInverseHerbrandFunction_eq_localInverseHerbrandFunction
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) :
    ClassFieldTheory.inverseHerbrandFunction K L t =
      inverseHerbrandFunctionOfUniqueExtension
        (base := (localCompleteDVF K).toDVF)
        (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
        (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L) t := by
  have hfun :
      ClassFieldTheory.herbrandFunction K
          (ValuativeRel.valuation L).valuationSubring =
        herbrandFunctionOfUniqueExtension
          (base := (localCompleteDVF K).toDVF)
          (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
          (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L) := by
    funext s
    exact canonicalHerbrandFunction_eq_localHerbrandFunction K L s
  unfold ClassFieldTheory.inverseHerbrandFunction
  rw [hfun]
  rfl

/-- Membership in the public canonical upper group is equivalent to
membership in the existing local upper group, after forgetting the
decomposition-subgroup wrapper. -/
theorem mem_canonicalUpperRamificationGroup_iff_mem_localUpperRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) (σ : Gal(L/K))
    (hσ : σ ∈
      ((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K) :
    (⟨σ, hσ⟩ :
      ((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K) ∈
        ClassFieldTheory.upperRamificationGroup K L t ↔
      σ ∈ localUpperRamificationGroup K L t := by
  have hσChosen : σ ∈
      ((chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring).decompositionSubgroup K
        := by
    rw [chosenLocalExtension_valuationSubring_eq_canonical K L]
    exact hσ
  have hchosen :=
    mem_chosenRealLowerRamificationGroup_iff_mem_localLowerRamificationGroup
      K L (ClassFieldTheory.inverseHerbrandFunction K L t) σ hσChosen
  have hmem_congr (A B : ValuationSubring L) (hAB : A = B)
      (hA : σ ∈ A.decompositionSubgroup K)
      (hB : σ ∈ B.decompositionSubgroup K) (s : ℝ) :
      (⟨σ, hA⟩ : A.decompositionSubgroup K) ∈
          ClassFieldTheory.realLowerRamificationGroup K A s ↔
        (⟨σ, hB⟩ : B.decompositionSubgroup K) ∈
          ClassFieldTheory.realLowerRamificationGroup K B s := by
    subst B
    rfl
  have hcanonical :
      (⟨σ, hσ⟩ :
        ((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K) ∈
          ClassFieldTheory.realLowerRamificationGroup K
            (ValuativeRel.valuation L).valuationSubring
            (ClassFieldTheory.inverseHerbrandFunction K L t) ↔
        σ ∈ localLowerRamificationGroup K L
          (ClassFieldTheory.inverseHerbrandFunction K L t) := by
    have heq := hmem_congr
      (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring
      (ValuativeRel.valuation L).valuationSubring
      (chosenLocalExtension_valuationSubring_eq_canonical K L)
      hσChosen hσ (ClassFieldTheory.inverseHerbrandFunction K L t)
    exact heq.symm.trans hchosen
  change (⟨σ, hσ⟩ :
      ((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K) ∈
      ClassFieldTheory.realLowerRamificationGroup K
        (ValuativeRel.valuation L).valuationSubring
        (ClassFieldTheory.inverseHerbrandFunction K L t) ↔
    σ ∈ localLowerRamificationGroup K L
      (inverseHerbrandFunctionOfUniqueExtension
        (base := (localCompleteDVF K).toDVF)
        (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
        (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L) t)
  rw [← canonicalInverseHerbrandFunction_eq_localInverseHerbrandFunction K L t]
  exact hcanonical

/-- Mapping the public canonical upper group from the decomposition subgroup
into `Gal(L/K)` gives the existing local upper group. -/
theorem upperRamificationGroup_map_subtype_eq_localUpperRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) :
    (ClassFieldTheory.upperRamificationGroup K L t).map
      (((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K).subtype =
        localUpperRamificationGroup K L t := by
  have htop :
      ((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K = ⊤ := by
    rw [← chosenLocalExtension_valuationSubring_eq_canonical K L]
    exact chosenLocalExtension_decompositionSubgroup_eq_top K L
  apply Subgroup.ext
  intro σ
  constructor
  · intro h
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp h
    exact (mem_canonicalUpperRamificationGroup_iff_mem_localUpperRamificationGroup
      K L t g.1 g.2).mp hg
  · intro h
    have hσ : σ ∈
        ((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K := by
      rw [htop]
      trivial
    exact Subgroup.mem_map.mpr
      ⟨⟨σ, hσ⟩,
        (mem_canonicalUpperRamificationGroup_iff_mem_localUpperRamificationGroup
          K L t σ hσ).mpr h,
        rfl⟩

/-- Subgroup transport also identifies the public right-limit upper group
with the existing local right-limit upper group. -/
theorem upperRamificationGroupAfter_map_subtype_eq_localUpperRamificationGroupAfter
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (t : ℝ) :
    (ClassFieldTheory.upperRamificationGroupAfter K L t).map
      (((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K).subtype =
        localUpperRamificationGroupAfter K L t := by
  unfold ClassFieldTheory.upperRamificationGroupAfter
  unfold localUpperRamificationGroupAfter
  rw [Subgroup.map_iSup]
  apply iSup_congr
  intro s
  exact upperRamificationGroup_map_subtype_eq_localUpperRamificationGroup K L s

/-- Equality of natural lower groups is reflected by the local filtration. -/
theorem chosenLowerRamificationGroup_eq_iff_localLowerRamificationGroup_eq
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (m n : ℕ) :
    ClassFieldTheory.lowerRamificationGroup K
        (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring m =
      ClassFieldTheory.lowerRamificationGroup K
        (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring n ↔
      localLowerRamificationGroup K L (m : ℝ) =
        localLowerRamificationGroup K L (n : ℝ) := by
  constructor
  · intro h
    apply Subgroup.ext
    intro σ
    have hσ : σ ∈
        ((chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring).decompositionSubgroup
          K := by
      rw [chosenLocalExtension_decompositionSubgroup_eq_top K L]
      trivial
    rw [← mem_chosenLowerRamificationGroup_iff_mem_localLowerRamificationGroup K L m σ hσ,
      ← mem_chosenLowerRamificationGroup_iff_mem_localLowerRamificationGroup K L n σ hσ, h]
  · intro h
    apply Subgroup.ext
    intro σ
    rw [mem_chosenLowerRamificationGroup_iff_mem_localLowerRamificationGroup K L m σ.1 σ.2,
      mem_chosenLowerRamificationGroup_iff_mem_localLowerRamificationGroup K L n σ.1 σ.2,
      h]

/-- The canonical lower-jump predicate is exactly a strict change in the
original local lower filtration. -/
theorem canonicalIsLowerRamificationJump_iff
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (n : ℕ) :
    ClassFieldTheory.IsLowerRamificationJump K
        (ValuativeRel.valuation L).valuationSubring n ↔
      localLowerRamificationGroup K L (n : ℝ) ≠
        localLowerRamificationGroup K L ((n + 1 : ℕ) : ℝ) := by
  unfold ClassFieldTheory.IsLowerRamificationJump
  rw [← chosenLocalExtension_valuationSubring_eq_canonical K L]
  exact not_congr
    (chosenLowerRamificationGroup_eq_iff_localLowerRamificationGroup_eq K L n (n + 1))

/-- Immediately to the right of the integer `n`, the real lower filtration
has already reached (or passed) the group at `n + 1`. -/
theorem localLowerRamificationGroup_le_succ_of_nat_lt
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ) {s : ℝ} (hs : (n : ℝ) < s) :
    localLowerRamificationGroup K L s ≤
      localLowerRamificationGroup K L ((n + 1 : ℕ) : ℝ) := by
  let target := (chosenLocalExtensionCompleteDVF K L).toDVF
  have hexponent :
      realRamificationExponent ((n + 1 : ℕ) : ℝ) ≤ realRamificationExponent s := by
    rw [realRamificationExponent_nat]
    have hceil : ((n + 2 : ℕ) : ℤ) ≤ Int.ceil (s + 1) := by
      apply (Int.le_ceil_iff).2
      norm_num only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Nat.cast_add, Nat.cast_ofNat,
        Int.cast_one]
      linarith
    unfold realRamificationExponent
    simpa only [Int.toNat_natCast, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Int.toNat_le_toNat hceil
  intro σ hσ a
  have hpow :
      target.maximalIdeal ^ realRamificationExponent s ≤
        target.maximalIdeal ^ realRamificationExponent ((n + 1 : ℕ) : ℝ) :=
    Ideal.pow_le_pow_right hexponent
  exact hpow (hσ a)

/-- A strict change between consecutive integer lower groups yields an
upper jump at the Herbrand image of the lower index. -/
theorem isLocalUpperRamificationJump_herbrand_nat_of_lower_ne_succ
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ)
    (hjump : localLowerRamificationGroup K L (n : ℝ) ≠
      localLowerRamificationGroup K L ((n + 1 : ℕ) : ℝ)) :
    IsLocalUpperRamificationJump K L
      (herbrandFunctionOfUniqueExtension
        (base := (localCompleteDVF K).toDVF)
        (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
        (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L)
        (n : ℝ)) := by
  let base := (localCompleteDVF K).toDVF
  let target := (chosenLocalExtensionCompleteDVF K L).toDVF
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, 0}
        base target :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  let t := herbrandFunctionOfUniqueExtension
    (base := base) (target := target) huniq (n : ℝ)
  have hAt : localUpperRamificationGroup K L t =
      localLowerRamificationGroup K L (n : ℝ) := by
    exact upperRamificationGroupOfUniqueExtension_herbrandFunction
      (base := base) (target := target) huniq (n : ℝ)
  have hAfter : localUpperRamificationGroupAfter K L t ≤
      localLowerRamificationGroup K L ((n + 1 : ℕ) : ℝ) := by
    unfold localUpperRamificationGroupAfter
    apply iSup_le
    intro s
    have hmono :=
      (inverseHerbrandFunctionOfUniqueExtension_strictMono
        (base := base) (target := target) huniq) s.property
    have hs : (n : ℝ) < inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq s.1 := by
      change inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq
          (herbrandFunctionOfUniqueExtension
            (base := base) (target := target) huniq (n : ℝ)) < _ at hmono
      simpa only [inverseHerbrandFunctionOfUniqueExtension_eta] using hmono
    exact localLowerRamificationGroup_le_succ_of_nat_lt K L n hs
  change localUpperRamificationGroup K L t ≠
    localUpperRamificationGroupAfter K L t
  intro hEq
  have hLe : localLowerRamificationGroup K L (n : ℝ) ≤
      localLowerRamificationGroup K L ((n + 1 : ℕ) : ℝ) := by
    rw [← hAt, hEq]
    exact hAfter
  have hRev : localLowerRamificationGroup K L ((n + 1 : ℕ) : ℝ) ≤
      localLowerRamificationGroup K L (n : ℝ) :=
    (lowerRamificationGroup_antitone (base := base) (target := target) huniq)
      (by exact_mod_cast Nat.le_succ n)
  exact hjump (le_antisymm hLe hRev)

/-- The public rational lower-jump formulation of Hasse--Arf for fields in
the universe supported by the existing local reciprocity construction. -/
theorem hasseArf_canonical
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    {n : ℕ}
    (hn : ClassFieldTheory.IsLowerRamificationJump K
      (ValuativeRel.valuation L).valuationSubring n) :
    ∃ z : ℤ,
      ClassFieldTheory.herbrandFunctionAtLowerIndex K
        (ValuativeRel.valuation L).valuationSubring n = (z : ℚ) := by
  have hjump : IsLocalUpperRamificationJump K L
      (herbrandFunctionOfUniqueExtension
        (base := (localCompleteDVF K).toDVF)
        (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
        (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension.{0} K L)
        (n : ℝ)) :=
    isLocalUpperRamificationJump_herbrand_nat_of_lower_ne_succ K L n
      ((canonicalIsLowerRamificationJump_iff K L n).mp hn)
  obtain ⟨z, hz⟩ := isLocalUpperRamificationJump_int K L hjump
  refine ⟨z, ?_⟩
  have hreal :
      ((ClassFieldTheory.herbrandFunctionAtLowerIndex K
        (ValuativeRel.valuation L).valuationSubring n : ℚ) : ℝ) = (z : ℝ) := by
    rw [canonicalHerbrandFunctionAtLowerIndex_real_eq K L n]
    exact hz
  exact_mod_cast hreal

/-! ## Compatible small representatives of finite extensions -/

/-- The algebra structure on the two small representatives, transported from
the original field extension. -/
@[instance_reducible]
noncomputable def shrinkAlgebra
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    Algebra (Shrink.{0} K) (Shrink.{0} L) :=
  ((Shrink.ringEquiv L).symm.toRingHom.comp
    ((algebraMap K L).comp (Shrink.ringEquiv K).toRingHom)).toAlgebra

/-- The two `Shrink` equivalences commute with the algebra maps. -/
theorem shrinkAlgebra_commutes
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    (algebraMap (Shrink.{0} K) (Shrink.{0} L)).comp
      (Shrink.ringEquiv K).symm.toRingHom =
        (Shrink.ringEquiv L).symm.toRingHom.comp (algebraMap K L) :=
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
  by
    apply RingHom.ext
    intro x
    change (Shrink.ringEquiv L).symm
      (algebraMap K L (Shrink.ringEquiv K ((Shrink.ringEquiv K).symm x))) =
        (Shrink.ringEquiv L).symm (algebraMap K L x)
    simp

/-- Finite-dimensionality survives simultaneous shrinking of the base and
extension fields. -/
theorem shrink_finiteDimensional
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Small.{0} K] [Small.{0} L] :
    letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) :=
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
  Module.Finite.of_equiv_equiv
    (Shrink.ringEquiv K).symm (Shrink.ringEquiv L).symm
    (shrinkAlgebra_commutes K L)

/-- Abelian Galois structure survives simultaneous shrinking of both fields. -/
theorem shrink_isAbelianGalois
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [IsAbelianGalois K L] [Small.{0} K] [Small.{0} L] :
    letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    IsAbelianGalois (Shrink.{0} K) (Shrink.{0} L) :=
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
  ClassFieldTheory.isAbelianGalois_of_equiv_equiv
    (Shrink.ringEquiv K).symm (Shrink.ringEquiv L).symm
    (shrinkAlgebra_commutes K L)

/-- Galois automorphisms of a finite extension are identified with those of
its simultaneous small representatives. -/
noncomputable def shrinkGalEquiv
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    Gal(Shrink.{0} L/Shrink.{0} K) ≃ Gal(L/K) :=
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
  ClassFieldTheory.galEquivOfEquivEquiv
    (Shrink.ringEquiv K).symm (Shrink.ringEquiv L).symm
    (shrinkAlgebra_commutes K L)

/-- The Galois equivalence acts by conjugating with the field equivalence. -/
theorem shrinkGalEquiv_apply
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] :
    letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    ∀ (σ : Gal(Shrink.{0} L/Shrink.{0} K)) (x : Shrink.{0} L),
      shrinkGalEquiv K L σ (Shrink.ringEquiv L x) =
        Shrink.ringEquiv L (σ x) :=
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
  by
    intro σ x
    simp [shrinkGalEquiv, ClassFieldTheory.galEquivOfEquivEquiv]

/-- The canonical valuation ring of a small local field is the pullback of
the original canonical valuation ring. This does not depend on the choice of
equivalent representatives for the two valuations. -/
theorem shrink_valuationSubring_eq_comap
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Small.{0} L] :
    letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
    (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring =
      (ValuativeRel.valuation L).valuationSubring.comap
        (Shrink.ringEquiv L).toRingHom :=
  letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
  by
    let v := shrinkLocalFieldValuation L
    have hv : (ValuativeRel.valuation (Shrink.{0} L)).IsEquiv v :=
      letI : v.Compatible := Valuation.Compatible.ofValuation v
      ValuativeRel.isEquiv _ _
    ext x
    change (ValuativeRel.valuation (Shrink.{0} L)) x ≤ 1 ↔
      (ValuativeRel.valuation L) (Shrink.ringEquiv L x) ≤ 1
    exact hv.le_one_iff_le_one.trans (by simp [v, shrinkLocalFieldValuation])

/-- Conjugation of Galois automorphisms preserves the pointwise action on the
canonical valuation rings. -/
theorem shrink_mem_pointwise_smul_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] :
    letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
    ∀ (σ : Gal(Shrink.{0} L/Shrink.{0} K)) (x : Shrink.{0} L),
      x ∈ σ • (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring ↔
        Shrink.ringEquiv L x ∈
          shrinkGalEquiv K L σ •
            (ValuativeRel.valuation L).valuationSubring :=
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
  letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
  by
    let e := Shrink.ringEquiv L
    let B := (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring
    let A := (ValuativeRel.valuation L).valuationSubring
    have hmem (y : Shrink.{0} L) : y ∈ B ↔ e y ∈ A := by
      rw [show B = A.comap e.toRingHom from shrink_valuationSubring_eq_comap L]
      rfl
    intro σ x
    have hleft := ValuationSubring.mem_smul_pointwise_iff_exists σ x B
    have hright := ValuationSubring.mem_smul_pointwise_iff_exists
      (shrinkGalEquiv K L σ) (e x) A
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ := hleft.mp hx
      apply hright.mpr
      refine ⟨e y, (hmem y).mp hy, ?_⟩
      change σ y = x at heq
      change shrinkGalEquiv K L σ (e y) = e x
      rw [shrinkGalEquiv_apply K L σ y]
      exact congrArg e heq
    · intro hx
      obtain ⟨z, hz, heq⟩ := hright.mp hx
      let y := e.symm z
      apply hleft.mpr
      refine ⟨y, (hmem y).mpr ?_, ?_⟩
      · simpa [y] using hz
      · change shrinkGalEquiv K L σ z = e x at heq
        change σ y = x
        apply e.injective
        have hnat := shrinkGalEquiv_apply K L σ y
        change shrinkGalEquiv K L σ (e y) = e (σ y) at hnat
        rw [← hnat]
        simpa [y] using heq

/-- A Galois automorphism stabilizes the small canonical valuation ring
exactly when its conjugate stabilizes the original canonical valuation ring. -/
theorem shrink_mem_decompositionSubgroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] :
    letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
    ∀ σ : Gal(Shrink.{0} L/Shrink.{0} K),
      σ ∈ ((ValuativeRel.valuation (Shrink.{0} L)).valuationSubring).decompositionSubgroup
        (Shrink.{0} K) ↔
      shrinkGalEquiv K L σ ∈
        ((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K :=
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
  letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
  by
    let e := Shrink.ringEquiv L
    let B := (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring
    let A := (ValuativeRel.valuation L).valuationSubring
    have hmem (x : Shrink.{0} L) : x ∈ B ↔ e x ∈ A := by
      rw [show B = A.comap e.toRingHom from shrink_valuationSubring_eq_comap L]
      rfl
    intro σ
    change σ • B = B ↔ shrinkGalEquiv K L σ • A = A
    constructor
    · intro h
      apply ValuationSubring.ext
      intro z
      let x := e.symm z
      calc
        z ∈ shrinkGalEquiv K L σ • A ↔ x ∈ σ • B := by
          simpa [x, e] using (shrink_mem_pointwise_smul_iff K L σ x).symm
        _ ↔ x ∈ B := by rw [h]
        _ ↔ z ∈ A := by simpa [x] using hmem x
    · intro h
      apply ValuationSubring.ext
      intro x
      calc
        x ∈ σ • B ↔ e x ∈ shrinkGalEquiv K L σ • A :=
          shrink_mem_pointwise_smul_iff K L σ x
        _ ↔ e x ∈ A := by rw [h]
        _ ↔ x ∈ B := (hmem x).symm

/-- The field equivalence restricts to the two canonical integer rings. -/
noncomputable def shrinkValuationSubringRingEquiv
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Small.{0} L] :
    letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
    (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring ≃+*
      (ValuativeRel.valuation L).valuationSubring :=
  letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
  RingEquiv.restrict (Shrink.ringEquiv L) _ _ (by
    intro x
    rw [shrink_valuationSubring_eq_comap L]
    rfl)

/-- Membership in a power of the maximal ideal is preserved by the
equivalence of canonical integer rings. -/
theorem shrink_mem_maximalIdeal_pow_iff
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Small.{0} L] (n : ℕ) :
    letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
    ∀ x : (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring,
      x ∈ (IsLocalRing.maximalIdeal
        (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring) ^ n ↔
      shrinkValuationSubringRingEquiv L x ∈
        (IsLocalRing.maximalIdeal
          (ValuativeRel.valuation L).valuationSubring) ^ n :=
  letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
  by
    intro x
    let e := shrinkValuationSubringRingEquiv L
    have hmap :
        (IsLocalRing.maximalIdeal
          (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring ^ n).map e =
          (IsLocalRing.maximalIdeal
            (ValuativeRel.valuation L).valuationSubring) ^ n := by
      rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
    rw [← hmap]
    exact (Ideal.apply_mem_of_equiv_iff (f := e)).symm

/-- Conjugation preserves membership in every lower ramification group of
the canonical valuation ring. -/
theorem shrink_mem_lowerRamificationGroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (n : ℕ) :
    letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
    ∀ (σ : Gal(Shrink.{0} L/Shrink.{0} K))
      (hσ : σ ∈
        ((ValuativeRel.valuation (Shrink.{0} L)).valuationSubring).decompositionSubgroup
          (Shrink.{0} K)),
      (⟨σ, hσ⟩ :
        ((ValuativeRel.valuation (Shrink.{0} L)).valuationSubring).decompositionSubgroup
          (Shrink.{0} K)) ∈
          ClassFieldTheory.lowerRamificationGroup (Shrink.{0} K)
            (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring n ↔
      (⟨shrinkGalEquiv K L σ,
          (shrink_mem_decompositionSubgroup_iff K L σ).mp hσ⟩ :
        ((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K) ∈
          ClassFieldTheory.lowerRamificationGroup K
            (ValuativeRel.valuation L).valuationSubring n :=
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
  letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
  by
    let B := (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring
    let A := (ValuativeRel.valuation L).valuationSubring
    let e := shrinkValuationSubringRingEquiv L
    intro σ hσ
    let τ := shrinkGalEquiv K L σ
    have hτ : τ ∈ A.decompositionSubgroup K :=
      (shrink_mem_decompositionSubgroup_iff K L σ).mp hσ
    have haction (x : B) :
        e ((⟨σ, hσ⟩ : B.decompositionSubgroup (Shrink.{0} K)) • x) =
          (⟨τ, hτ⟩ : A.decompositionSubgroup K) • e x := by
      apply Subtype.ext
      change (Shrink.ringEquiv L) (σ (x : Shrink.{0} L)) =
        τ ((Shrink.ringEquiv L) (x : Shrink.{0} L))
      exact (shrinkGalEquiv_apply K L σ x).symm
    have hpow (x : B) :
        (⟨σ, hσ⟩ : B.decompositionSubgroup (Shrink.{0} K)) • x - x ∈
          (IsLocalRing.maximalIdeal B) ^ (n + 1) ↔
        (⟨τ, hτ⟩ : A.decompositionSubgroup K) • e x - e x ∈
          (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
      have h := shrink_mem_maximalIdeal_pow_iff L (n + 1)
        ((⟨σ, hσ⟩ : B.decompositionSubgroup (Shrink.{0} K)) • x - x)
      change _ ↔ e ((⟨σ, hσ⟩ : B.decompositionSubgroup (Shrink.{0} K)) • x - x) ∈
        (IsLocalRing.maximalIdeal A) ^ (n + 1) at h
      rw [map_sub, haction] at h
      exact h
    change (∀ x : B,
      (⟨σ, hσ⟩ : B.decompositionSubgroup (Shrink.{0} K)) • x - x ∈
        (IsLocalRing.maximalIdeal B) ^ (n + 1)) ↔
      (∀ y : A,
        (⟨τ, hτ⟩ : A.decompositionSubgroup K) • y - y ∈
          (IsLocalRing.maximalIdeal A) ^ (n + 1))
    constructor
    · intro h y
      have hy := (hpow (e.symm y)).mp (h (e.symm y))
      simpa using hy
    · intro h x
      exact (hpow x).mpr (h (e x))

/-- The decomposition groups of the two equivalent local extensions are
equivalent as finite types. -/
noncomputable def shrinkDecompositionGroupEquiv
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] :
    letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
    ((ValuativeRel.valuation (Shrink.{0} L)).valuationSubring).decompositionSubgroup
      (Shrink.{0} K) ≃
      ((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K :=
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
  letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
  (shrinkGalEquiv K L).subtypeEquiv
    (shrink_mem_decompositionSubgroup_iff K L)

/-- Each natural-index lower ramification group has the same elements after
conjugating through the small field representatives. -/
noncomputable def shrinkLowerRamificationGroupEquiv
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (n : ℕ) :
    letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
    ClassFieldTheory.lowerRamificationGroup (Shrink.{0} K)
      (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring n ≃
    ClassFieldTheory.lowerRamificationGroup K
      (ValuativeRel.valuation L).valuationSubring n :=
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
  letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
  (shrinkDecompositionGroupEquiv K L).subtypeEquiv (by
    intro σ
    exact shrink_mem_lowerRamificationGroup_iff K L n σ.1 σ.2)

/-- The canonical lower groups have equal cardinalities at every natural
index before and after shrinking the field carriers. -/
theorem shrink_card_lowerRamificationGroup_eq
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (n : ℕ) :
    letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
    Nat.card (ClassFieldTheory.lowerRamificationGroup (Shrink.{0} K)
      (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring n) =
    Nat.card (ClassFieldTheory.lowerRamificationGroup K
      (ValuativeRel.valuation L).valuationSubring n) :=
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
  letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
  Nat.card_congr (shrinkLowerRamificationGroupEquiv K L n)

/-- Equality of two lower ramification groups is invariant under shrinking
both local fields. -/
theorem shrink_lowerRamificationGroup_eq_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (m n : ℕ) :
    letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
    ClassFieldTheory.lowerRamificationGroup (Shrink.{0} K)
        (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring m =
      ClassFieldTheory.lowerRamificationGroup (Shrink.{0} K)
        (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring n ↔
    ClassFieldTheory.lowerRamificationGroup K
        (ValuativeRel.valuation L).valuationSubring m =
      ClassFieldTheory.lowerRamificationGroup K
        (ValuativeRel.valuation L).valuationSubring n :=
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
  letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
  by
    let B := (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring
    let A := (ValuativeRel.valuation L).valuationSubring
    let e := shrinkDecompositionGroupEquiv K L
    have hmem (i : ℕ) (σ : B.decompositionSubgroup (Shrink.{0} K)) :
        σ ∈ ClassFieldTheory.lowerRamificationGroup (Shrink.{0} K) B i ↔
          e σ ∈ ClassFieldTheory.lowerRamificationGroup K A i :=
      shrink_mem_lowerRamificationGroup_iff K L i σ.1 σ.2
    constructor
    · intro h
      apply Subgroup.ext
      intro τ
      let σ := e.symm τ
      calc
        τ ∈ ClassFieldTheory.lowerRamificationGroup K A m ↔
            σ ∈ ClassFieldTheory.lowerRamificationGroup (Shrink.{0} K) B m := by
              simpa [σ] using (hmem m σ).symm
        _ ↔ σ ∈ ClassFieldTheory.lowerRamificationGroup (Shrink.{0} K) B n := by
              rw [h]
        _ ↔ τ ∈ ClassFieldTheory.lowerRamificationGroup K A n := by
              simpa [σ] using hmem n σ
    · intro h
      apply Subgroup.ext
      intro σ
      calc
        σ ∈ ClassFieldTheory.lowerRamificationGroup (Shrink.{0} K) B m ↔
            e σ ∈ ClassFieldTheory.lowerRamificationGroup K A m := hmem m σ
        _ ↔ e σ ∈ ClassFieldTheory.lowerRamificationGroup K A n := by rw [h]
        _ ↔ σ ∈ ClassFieldTheory.lowerRamificationGroup (Shrink.{0} K) B n :=
          (hmem n σ).symm

/-- The public lower-jump predicate is invariant under changing to the
small representatives of a local extension. -/
theorem shrink_isLowerRamificationJump_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (n : ℕ) :
    letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
    ClassFieldTheory.IsLowerRamificationJump (Shrink.{0} K)
      (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring n ↔
    ClassFieldTheory.IsLowerRamificationJump K
      (ValuativeRel.valuation L).valuationSubring n :=
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
  letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
  not_congr (shrink_lowerRamificationGroup_eq_iff K L n (n + 1))

/-- The rational finite-sum Herbrand value at a natural lower index is
unchanged by shrinking the extension fields. -/
theorem shrink_herbrandFunctionAtLowerIndex_eq
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (n : ℕ) :
    letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
    letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
    ClassFieldTheory.herbrandFunctionAtLowerIndex (Shrink.{0} K)
      (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring n =
    ClassFieldTheory.herbrandFunctionAtLowerIndex K
      (ValuativeRel.valuation L).valuationSubring n :=
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := shrinkAlgebra K L
  letI : ValuativeRel (Shrink.{0} L) := shrinkLocalFieldValuativeRel L
  by
    unfold ClassFieldTheory.herbrandFunctionAtLowerIndex
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [shrink_card_lowerRamificationGroup_eq K L i]
    · rw [shrink_card_lowerRamificationGroup_eq K L 0]

end HasseArf
