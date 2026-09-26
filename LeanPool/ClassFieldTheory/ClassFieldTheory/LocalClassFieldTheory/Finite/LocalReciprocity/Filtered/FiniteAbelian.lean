/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.StandardCompositum
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardDominatingExtension
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Core
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardFixedFieldComparison
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Core
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.BaseChange
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.Unramified
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.FirstRamificationComparison
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.LocalField.InertiaCard
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.FiniteInertiaStructure
/-!
# Filtered reciprocity for arbitrary finite abelian local extensions

An arbitrary finite abelian extension embeds into a standard finite
abelian compositum.  Passing to its field range inside the fixed separable
closure permits descent by restriction, and the resulting algebra
equivalence transports both filtrations back to the original extension.
-/

@[expose] public section

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction_one_pos_le_one →
    herbrandFunction_one_pos_le_one

open _root_.RamificationTheory.HilbertRamification.Higher renaming
  upperRamificationGroupOfUniqueExtension_herbrandFunction →
    upperRamificationGroupOfUniqueExtension_herbrandFunction

open _root_.RamificationTheory.HilbertRamification.ValuationSubring renaming
  ramificationGroup_eq_bot_iff_residueChar_not_dvd_inertia_card →
    ramificationGroup_eq_bot_iff_residueChar_not_dvd_inertia_card


noncomputable
section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open RamificationTheory.LocalField
open LubinTate

open LocalClassFieldTheory
open LocalFieldTheory

/-- Characteristic-independent real filtered local reciprocity for every
finite abelian extension of a nonarchimedean local field. -/
theorem finiteAbelian_filteredLocalReciprocity
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (t : ℝ) (ht : 0 ≤ t) :
    artinPrincipalUnitStepGroup K L t =
      localUpperRamificationGroup K L t := by
  obtain ⟨d, n, hd, _hn, hEmbed⟩ :=
    exists_finiteAbelianDominatingStandardLubinTateCompositum K L
  let P := standardLubinTateFiniteAbelianCompositum K d n hd
  let F :=
    abstractFixedField K (SeparableClosure K) P.field
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) P.field
        (finiteAbelianSubextension_finite_over_absoluteBase K P)
  let : IsAbelianGalois K F :=
    finiteAbelianSubextension_fixedField_isAbelianGalois K P
  let i : L →ₐ[K] F := hEmbed.some
  let j : L →ₐ[K] SeparableClosure K := F.val.comp i
  let E : IntermediateField K (SeparableClosure K) :=
    AlgHom.fieldRange j
  have hEF : E ≤ F := by
    rintro x ⟨y, rfl⟩
    exact (i y).property
  let e : L ≃ₐ[K] E :=
    AlgEquiv.ofInjectiveField j
  let : FiniteDimensional K E :=
    e.toLinearEquiv.finiteDimensional
  let : IsAbelianGalois K E :=
    IsAbelianGalois.of_algHom (IntermediateField.inclusion hEF)
  have hcover :
      ∀ s : ℝ, 0 ≤ s →
        artinPrincipalUnitStepGroup K F s =
          localUpperRamificationGroup K F s := by
    intro s hs
    exact
      standardLubinTateFiniteAbelianCompositum_filteredLocalReciprocity
        K d n hd s hs
  have hupper :
      ∀ s : ℝ,
        Subgroup.map
            (RamificationTheory.intermediateFieldRestrictNormalHom E F hEF)
            (localUpperRamificationGroup K F s) =
          localUpperRamificationGroup K E s := by
    intro s
    exact localUpperRamificationGroup_map_restrict K E F hEF s
  have hEfiltered :
      artinPrincipalUnitStepGroup K E t =
        localUpperRamificationGroup K E t :=
    filteredLocalReciprocity_descends
      K E F hEF
      (localUpperRamificationGroup K E)
      (localUpperRamificationGroup K F)
      hupper hcover t ht
  let q : Gal(E/K) ≃* Gal(L/K) :=
    AlgEquiv.autCongr e.symm
  have hArtin :
      Subgroup.map q.toMonoidHom
          (artinPrincipalUnitStepGroup K E t) =
        artinPrincipalUnitStepGroup K L t :=
    artinPrincipalUnitStepGroup_map_standardFixedFieldEquiv
      K E L e.symm t
  have hUpper :
      Subgroup.map q.toMonoidHom
          (localUpperRamificationGroup K E t) =
        localUpperRamificationGroup K L t :=
    localUpperRamificationGroup_map_autCongr K E L e.symm t
  calc
    artinPrincipalUnitStepGroup K L t =
        Subgroup.map q.toMonoidHom
          (artinPrincipalUnitStepGroup K E t) :=
      hArtin.symm
    _ =
        Subgroup.map q.toMonoidHom
          (localUpperRamificationGroup K E t) := by
      rw [hEfiltered]
    _ = localUpperRamificationGroup K L t := hUpper

/-- In a finite abelian local extension the first upper and lower groups
coincide. The normalization matters: `φ(1)` need not equal `1`, but it lies
in `(0, 1]`, where filtered reciprocity makes the upper group constant. -/
theorem finiteAbelian_localUpperRamificationGroup_one_eq_localLowerRamificationGroup_one
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    localUpperRamificationGroup K L 1 =
      localLowerRamificationGroup K L 1 := by
  let base := (localCompleteDVF K).toDVF
  let target := (chosenLocalExtensionCompleteDVF K L).toDVF
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base target :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
  let s : ℝ :=
    RamificationTheory.HilbertRamification.Higher.herbrandFunctionOfUniqueExtension
      (base := base) (target := target) huniq 1
  have hs : 0 < s ∧ s ≤ 1 := by
    change 0 <
      (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
      (RamificationTheory.HilbertRamification.Higher.lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq)) 1 ∧
      (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
      (RamificationTheory.HilbertRamification.Higher.lowerRamificationFiltrationOfUniqueExtension
        (base := base) (target := target) huniq)) 1 ≤ 1
    exact
      herbrandFunction_one_pos_le_one _
  have hStep (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
      localUpperRamificationGroup K L t =
        artinPrincipalUnitGroup K L 1 := by
    have hceil : ⌈t⌉₊ = 1 :=
      (Nat.ceil_eq_iff (by
        decide : (1 : ℕ) ≠ 0)).2 (by
        simpa using (show (0 : ℝ) < t ∧ t ≤ 1 from ⟨ht0, ht1⟩))
    calc
      localUpperRamificationGroup K L t =
          artinPrincipalUnitStepGroup K L t :=
        (finiteAbelian_filteredLocalReciprocity K L t ht0.le).symm
      _ = artinPrincipalUnitGroup K L 1 := by
        change artinPrincipalUnitGroup K L ⌈t⌉₊ = _
        rw [hceil]
  have hAtS :
      localUpperRamificationGroup K L s =
        localLowerRamificationGroup K L 1 := by
    change RamificationTheory.HilbertRamification.Higher.upperRamificationGroupOfUniqueExtension
        (base := base) (target := target) huniq
        (RamificationTheory.HilbertRamification.Higher.herbrandFunctionOfUniqueExtension
          (base := base) (target := target) huniq 1) =
      RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup
        (base := base) (target := target) huniq 1
    exact
      upperRamificationGroupOfUniqueExtension_herbrandFunction
      (base := base) (target := target) huniq 1
  calc
    localUpperRamificationGroup K L 1 = artinPrincipalUnitGroup K L 1 :=
      hStep 1 (by norm_num) le_rfl
    _ = localUpperRamificationGroup K L s := (hStep s hs.1 hs.2).symm
    _ = localLowerRamificationGroup K L 1 := hAtS

/-- The first upper group of a finite abelian local extension is Hilbert's
ramification group for the chosen valuation ring, transported to `Gal(L/K)`. -/
theorem finiteAbelian_localUpperRamificationGroup_one_eq_hilbertRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    localUpperRamificationGroup K L 1 =
      Subgroup.comap
        (RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup
          (base := localCompleteDVF K)
          (target := chosenLocalExtensionCompleteDVF K L)).toMonoidHom
        (RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInDecomposition K
          (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring) :=
  (finiteAbelian_localUpperRamificationGroup_one_eq_localLowerRamificationGroup_one K L).trans
    (localLowerRamificationGroup_one_eq_hilbertRamificationGroup K L)

/-- For a finite abelian local extension, the conductor exponent is at most
one exactly when its first upper ramification group is trivial.  This is the
filtered-reciprocity bridge used by the tame-ramification criterion. -/
theorem localConductorExponent_le_one_iff_localUpperRamificationGroup_one_eq_bot
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    localConductorExponent K L ≤ 1 ↔
      localUpperRamificationGroup K L 1 = ⊥ := by
  have hstep :
      artinPrincipalUnitStepGroup K L (1 : ℝ) =
        artinPrincipalUnitGroup K L 1 := by
    change artinPrincipalUnitGroup K L ⌈(1 : ℝ)⌉₊ =
      artinPrincipalUnitGroup K L 1
    have hone : ⌈(1 : ℝ)⌉₊ = (1 : ℕ) := by norm_num
    rw [hone]
  rw [← finiteAbelian_filteredLocalReciprocity K L 1 (by norm_num), hstep]
  exact (artinPrincipalUnitGroup_eq_bot_iff K L 1).symm

/-- Conductor exponent at most one is equivalent to the absence of wild
ramification in the chosen valuation ring. -/
theorem localConductorExponent_le_one_iff_hilbertRamificationGroup_eq_bot
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    localConductorExponent K L ≤ 1 ↔
      RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup K
        (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring = ⊥ := by
  rw [localConductorExponent_le_one_iff_localUpperRamificationGroup_one_eq_bot,
    finiteAbelian_localUpperRamificationGroup_one_eq_localLowerRamificationGroup_one]
  exact localLowerRamificationGroup_one_eq_bot_iff_hilbertRamificationGroup_eq_bot K L

/-- The first conductor threshold is the usual tame criterion: the residue
characteristic does not divide the ramification index. -/
theorem localConductorExponent_le_one_iff_residueChar_not_dvd_ramificationIndex
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring) p] :
    localConductorExponent K L ≤ 1 ↔
      ¬ p ∣ ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        (localCompleteDVF K).toDVF
        (chosenLocalExtensionCompleteDVF K L).toDVF := by
  let A := (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring
  rw [localConductorExponent_le_one_iff_hilbertRamificationGroup_eq_bot]
  exact
    (ramificationGroup_eq_bot_iff_residueChar_not_dvd_inertia_card
    K A p).trans (by
      rw [RamificationTheory.LocalField.chosenLocalExtension_inertia_card_eq_ramificationIndex K L])

end LocalClassFieldTheory

end
