/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Mathlib.Algebra.Order.Hom.Units
public import Mathlib.NumberTheory.LocalField.Basic
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.ValuedAdicComplete
/-!
# Complete-DVF packages for local fields and their finite extensions

The canonical complete discrete valuation on a nonarchimedean local field,
and an integral-closure valuation chosen on each finite separable extension.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped ValuativeRel

universe u v y

/-! ## The canonical complete discrete valuation -/

/-- The canonical valuation of a nonarchimedean local field, packaged as a
complete discrete valuation field. -/
noncomputable def localCompleteDVF
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    CompleteDVF.{u, u} K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let v : Valuation K (ValuativeRel.ValueGroupWithZero K) := Valued.v
  let e :=
    (OrderMonoidIso.unitsCongr
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).trans
      OrderMonoidIso.unitsWithZero
  letI : IsCyclic (ValuativeRel.ValueGroupWithZero K)ˣ :=
    e.toMulEquiv.isCyclic.mpr inferInstance
  letI : v.IsNontrivial :=
    (ValuativeRel.isNontrivial_iff_isNontrivial v).mp inferInstance
  letI : IsCyclic (MonoidWithZeroHom.valueGroup v.toMonoidWithZeroHom) :=
    Subgroup.isCyclic_of_le
      (show MonoidWithZeroHom.valueGroup v.toMonoidWithZeroHom ≤ ⊤ from le_top)
  letI : v.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' v
  exact ValuationTheory.Valuations.completeDVFOfCompleteValuedField

/-- The canonical complete-DVF packages preserve an existing extension of
the underlying valuative relations. -/
theorem localCompleteDVFValuation_hasExtension
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] :
    (localCompleteDVF K).valuation.HasExtension
      (localCompleteDVF L).valuation := by
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change
    ValuativeRel.valuation L (algebraMap K L x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
  exact
    Valuation.HasExtension.val_map_le_one_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation L) x

/-- The valuation integer ring of a finite separable local extension is the
integral closure of the base valuation integer ring. -/
theorem localCompleteDVF_integerRing_isIntegralClosure
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] :
    IsIntegralClosure 𝒪[L] 𝒪[K] L := by
  let : (localCompleteDVF K).valuation.HasExtension
      (localCompleteDVF L).valuation :=
    localCompleteDVFValuation_hasExtension K L
  let : IsScalarTower
      (localCompleteDVF K).valuationSubring
      (localCompleteDVF L).valuationSubring L :=
    Valuation.valuationSubring_isScalarTower_of_hasExtension
      (localCompleteDVF K).valuation (localCompleteDVF L).valuation
  exact
    target_valuationSubring_isIntegralClosure_of_finite_separable
      (K := K) (L := L) (localCompleteDVF K) (localCompleteDVF L)

/-- The valuation integer ring of a finite separable local extension is a
finite module over the base valuation integer ring. -/
theorem localCompleteDVF_integerRing_moduleFinite
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] :
    Module.Finite 𝒪[K] 𝒪[L] := by
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
    localCompleteDVF_integerRing_isIntegralClosure K L
  exact IsIntegralClosure.finite 𝒪[K] K L 𝒪[L]

/-! ## Chosen ramification data for an arbitrary finite local extension -/

private theorem chosenLocalExtensionCompleteDVF_exists
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ target : CompleteDVF.{0, 0} L,
      ∃ hExt : (localCompleteDVF K).valuation.HasExtension target.valuation,
        letI : (localCompleteDVF K).valuation.HasExtension target.valuation :=
          hExt
        IsIntegralClosure target.valuationSubring
          (localCompleteDVF K).valuationSubring L := by
  obtain ⟨target, hExt, hIntegralClosure, _hDefectless⟩ :=
    exists_integralClosure_standard_fundamental_identity
      (K := K) (L := L) (localCompleteDVF K)
  exact ⟨target, hExt, hIntegralClosure⟩

/-- A complete discrete valuation on an arbitrary finite separable extension
of a nonarchimedean local field, chosen from its actual integral closure. -/
noncomputable def chosenLocalExtensionCompleteDVF
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    CompleteDVF.{0, 0} L :=
  Classical.choose (chosenLocalExtensionCompleteDVF_exists K L)

/-- The chosen valuation on a finite local extension extends the canonical
valuation of its base field. -/
theorem chosenLocalExtensionCompleteDVF_hasExtension
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (localCompleteDVF K).valuation.HasExtension
      (chosenLocalExtensionCompleteDVF K L).valuation :=
  Classical.choose
    (Classical.choose_spec (chosenLocalExtensionCompleteDVF_exists K L))

/-- Supplies the valuation-extension instance for the chosen finite local
extension target. -/
noncomputable instance chosenLocalExtensionCompleteDVF.instHasExtension
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (localCompleteDVF K).valuation.HasExtension
      (chosenLocalExtensionCompleteDVF K L).valuation :=
  chosenLocalExtensionCompleteDVF_hasExtension K L

/-- The chosen valuation ring is the actual integral closure of the
canonical valuation ring of the base local field. -/
theorem chosenLocalExtensionCompleteDVF_isIntegralClosure
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    IsIntegralClosure
      (chosenLocalExtensionCompleteDVF K L).valuationSubring
      (localCompleteDVF K).valuationSubring L :=
  Classical.choose_spec
    (Classical.choose_spec (chosenLocalExtensionCompleteDVF_exists K L))

/-- The chosen valuation ring of a finite separable local extension is a
finite module over the canonical base valuation ring. -/
theorem chosenLocalExtensionCompleteDVF_valuationSubring_moduleFinite
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Module.Finite
      (localCompleteDVF K).valuationSubring
      (chosenLocalExtensionCompleteDVF K L).valuationSubring := by
  let : IsIntegralClosure
      (chosenLocalExtensionCompleteDVF K L).valuationSubring
      (localCompleteDVF K).valuationSubring L :=
    chosenLocalExtensionCompleteDVF_isIntegralClosure K L
  exact IsIntegralClosure.finite
    (localCompleteDVF K).valuationSubring K L
    (chosenLocalExtensionCompleteDVF K L).valuationSubring

/-- Completeness of the base makes the chosen valuation extension unique. -/
theorem chosenLocalExtensionCompleteDVF_hasUniqueValuationExtension
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ValuedExtension.HasUniqueValuationExtension.{0, 0, 0, 0, y}
      (base := localCompleteDVF K)
      (target := chosenLocalExtensionCompleteDVF K L) :=
  hasUniqueValuationExtension_of_finite_separable
    (localCompleteDVF K) (chosenLocalExtensionCompleteDVF K L)

end LocalFieldTheory
