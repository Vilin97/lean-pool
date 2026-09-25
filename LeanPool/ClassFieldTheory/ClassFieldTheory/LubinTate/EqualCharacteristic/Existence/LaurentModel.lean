/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.IwasawaPrincipalUnits
/-!
# Equal-characteristic Laurent-series model

For the positive-characteristic branch of the existence theorem, the local-field classification
identifies a local field with a Laurent-series field over its residue field.
The earlier complete-DVR development constructs the coefficient section and proves that Laurent
series evaluation is onto.  Here we package that concrete evaluation as the
actual field equivalence needed by the Lubin--Tate construction; no existence
or norm-subgroup statement is assumed.
-/

noncomputable section

open scoped PowerSeries LaurentSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The Laurent-series parameter `T`, written through the localization map
from power series so its later transport to the local field is definitional. -/
noncomputable def equalCharacteristicLaurentUniformizer
    (F : LocalField.{u, v} K) : F.residueField⸨X⸩ :=
  algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
    (PowerSeries.X : F.residueField⟦X⟧)

open CompleteDVF.higherPrincipalUnitGroup renaming
  residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank →
    residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank in
/-- In equal characteristic, Laurent-series evaluation at a chosen
uniformizer is a field equivalence onto the local field. -/
noncomputable def equalCharacteristicLaurentRingEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    F.residueField⸨X⸩ ≃+* K := by
  let f := CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank F
  let n : ℕ+ :=
    ⟨f, Module.finrank_pos⟩
  let eval : F.residueField⸨X⸩ →+* K :=
    CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom
      (F := F.toCompleteDVF) F.residueCharacteristic (n := n)
      (by
        simpa [f, n] using
          residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank F)
      pi hpi
  exact RingEquiv.ofBijective eval
    ⟨RingHom.injective eval,
      CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom_surjective
        (F := F.toCompleteDVF) F.residueCharacteristic (n := n)
        (by
          simpa [f, n] using
            residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank F)
        pi hpi⟩

open CompleteDVF.higherPrincipalUnitGroup renaming
  residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank →
    residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank in
/-- States the theorem `equalCharacteristicLaurentRingEquiv_apply`. -/
@[simp]
theorem equalCharacteristicLaurentRingEquiv_apply
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (x : F.residueField⸨X⸩) :
    equalCharacteristicLaurentRingEquiv F hpi x =
      CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom
        (F := F.toCompleteDVF) F.residueCharacteristic
        (n :=
          ⟨CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank F,
            Module.finrank_pos⟩)
        (by
          simpa using
            residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank F)
        pi hpi x := by
  rfl

open CompleteDVF.higherPrincipalUnitGroup renaming
  residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank →
    residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank in
/-- States the theorem `equalCharacteristicLaurentRingEquiv_algebraMap_C`. -/
theorem equalCharacteristicLaurentRingEquiv_algebraMap_C
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K))
    (a : F.residueField) :
    equalCharacteristicLaurentRingEquiv F hpi
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          (PowerSeries.C a)) =
      CompleteDVF.EqualCharacteristicLaurent.coeffHom
        (F := F.toCompleteDVF) F.residueCharacteristic
        (n :=
          ⟨CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank F,
            Module.finrank_pos⟩)
        (by
          simpa using
            residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank F)
        a := by
  rw [equalCharacteristicLaurentRingEquiv_apply]
  exact
    CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom_algebraMap_C
      (F := F.toCompleteDVF) F.residueCharacteristic
      (n :=
        ⟨CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank F,
          Module.finrank_pos⟩)
      (by
        simpa using
          residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank F)
      pi hpi a

open CompleteDVF.higherPrincipalUnitGroup renaming
  residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank →
    residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank in
/-- States the theorem `equalCharacteristicLaurentRingEquiv_algebraMap_X`. -/
theorem equalCharacteristicLaurentRingEquiv_algebraMap_X
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {pi : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) :
    equalCharacteristicLaurentRingEquiv F hpi
        (algebraMap F.residueField⟦X⟧ F.residueField⸨X⸩
          (PowerSeries.X : F.residueField⟦X⟧)) =
      (pi : K) := by
  rw [equalCharacteristicLaurentRingEquiv_apply]
  exact
    CompleteDVF.EqualCharacteristicLaurent.adicLaurentSeriesEvalHom_algebraMap_X
      (F := F.toCompleteDVF) F.residueCharacteristic
      (n :=
        ⟨CompleteDVF.higherPrincipalUnitGroup.iwasawaResidueRank F,
          Module.finrank_pos⟩)
      (by
        simpa using
          residueField_card_eq_residueCharacteristic_pow_iwasawaResidueRank F)
      pi hpi

end EqualCharacteristic
end LubinTate
