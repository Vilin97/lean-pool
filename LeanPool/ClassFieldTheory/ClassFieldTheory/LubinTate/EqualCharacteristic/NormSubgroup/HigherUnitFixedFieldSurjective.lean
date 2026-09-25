/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldDegree
/-!
# LubinTate the explicit norm-subgroup computation: surjectivity of the higher-unit fixed-field
  embedding

The standard level and the fixed field have the same finite degree
`(q - 1) q^n`; hence the canonical injective embedding is surjective.
-/

@[expose] public section

noncomputable section


open scoped LaurentSeries PowerSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type} [Field K]

attribute [local instance]
  equalCharacteristicCompletedFrobeniusFixedBaseAlgebra
  equalCharacteristicCompletedFrobeniusFixedFieldAlgebra
  equalCharacteristicCompletedFrobeniusFixedFieldSMul
  equalCharacteristicCompletedFrobeniusFixedFieldModule

private theorem ringHom_surjective_of_finrank_eq
    {B E L : Type*}
    [Field B] [Field E] [Field L]
    [Algebra B E] [Algebra B L]
    [FiniteDimensional B E] [FiniteDimensional B L]
    (f : E →+* L)
    (hcomm : ∀ b : B,
      f (algebraMap B E b) = algebraMap B L b)
    (hdim : Module.finrank B E = Module.finrank B L) :
    Function.Surjective f := by
  let fAlg : E →ₐ[B] L :=
    { f with commutes' := hcomm }
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := fAlg.toLinearMap) hdim).mp fAlg.injective

/-- The canonical standard-level embedding onto the higher-unit fixed field
is surjective. -/
theorem equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnit_surjective
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n) :
    Function.Surjective
      (equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnit
        F a n ha) := by
  change Function.Surjective
    (equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnitRingHom
      F a n ha)
  let f :=
    equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnitRingHom
      F a n ha
  let : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicCompletedFrobeniusFixedField F a n) :=
    FiniteDimensional.of_finrank_pos (by
      rw [equalCharacteristicCompletedFrobeniusFixedField_finrank]
      exact Nat.mul_pos
        (Nat.sub_pos_of_lt
          (Finite.one_lt_card : 1 < Nat.card F.residueField))
        (Nat.pow_pos Nat.card_pos))
  have hdim : Module.finrank F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) =
      Module.finrank F.residueField⸨X⸩
        (equalCharacteristicCompletedFrobeniusFixedField F a n) := by
    rw [equalCharacteristicLubinTateLevelField_finrank,
      equalCharacteristicCompletedFrobeniusFixedField_finrank]
  exact ringHom_surjective_of_finrank_eq f (by
    intro b
    apply Subtype.ext
    exact equalCharacteristicLubinTateLevelFieldToCompletedRingHom_algebraMap F n b) hdim

end EqualCharacteristic
end LubinTate
