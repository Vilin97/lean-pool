/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.UnramifiedConductor
/-!
# Lubin--Tate application: index of the explicit level norm subgroup

The equality between the norm-subgroup index and the extension degree uses
finite local reciprocity.  It therefore belongs to the concrete local class
field theory application layer, not to the reusable Lubin--Tate library.
-/

@[expose] public section

noncomputable
section

open scoped LaurentSeries ValuativeRel

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory

variable {K : Type} [Field K]

private theorem normSubgroup_index_eq_finrank_of_isAbelianGalois
    {B E : Type} [Field B] [Field E] [Algebra B E]
    (hab : IsAbelianGalois B E)
    (hfd : FiniteDimensional B E)
    [ValuativeRel B] [TopologicalSpace B]
    [IsNonarchimedeanLocalField B] :
    (localNormSubgroup B E).index = Module.finrank B E := by
  let : IsAbelianGalois B E := hab
  let : FiniteDimensional B E := hfd
  rw [Subgroup.index_eq_card]
  exact LocalClassFieldTheory.card_normQuotient_eq_finrank_of_isAbelianGalois B E

/-- The norm subgroup of the level-`n+1` Lubin--Tate extension has index
`(q - 1) q^n`, its extension degree. -/
theorem equalCharacteristicLubinTateNormSubgroup_index
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    letI : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    (equalCharacteristicLubinTateNormSubgroup F n).index =
      (Nat.card F.residueField - 1) * Nat.card F.residueField ^ n := by
  let B := F.residueField⸨X⸩
  let E := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F n
  change (localNormSubgroup B E).index = _
  calc
    (localNormSubgroup B E).index = Module.finrank B E :=
      normSubgroup_index_eq_finrank_of_isAbelianGalois
        (equalCharacteristicLubinTateLevelField_isAbelianGalois F n)
        (equalCharacteristicLubinTateLevelField_finiteDimensional F n)
    _ = (Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n :=
      equalCharacteristicLubinTateLevelField_finrank F n

end EqualCharacteristic
end LubinTate
