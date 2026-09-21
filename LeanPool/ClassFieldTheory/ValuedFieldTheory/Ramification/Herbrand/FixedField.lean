/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.Herbrand.Quotient
import Mathlib.FieldTheory.Galois.Basic
/-!
# Fixed-field group models for Herbrand towers
-/

noncomputable section

universe u w

namespace RamificationTheory.HilbertRamification
namespace Higher

open RamificationTheory.DiscreteValuationField
open RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

/-- The ambient subgroup filtration transported to the actual Galois group
of `L / L^H`. -/
def fixedFieldSubextensionFiltration
    (F : AntitoneNormalSubgroupFiltration Gal(L/K))
    (H : Subgroup Gal(L/K)) :
    AntitoneNormalSubgroupFiltration Gal(L/IntermediateField.fixedField H) :=
  RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.transportEquiv (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.subgroupFiltration F H)
    (IntermediateField.subgroupEquivAlgEquiv H)

omit [IsGalois K L] in
/-- States the theorem `fixedFieldSubextensionFiltration_lower`. -/
@[simp] theorem fixedFieldSubextensionFiltration_lower
    (F : AntitoneNormalSubgroupFiltration Gal(L/K))
    (H : Subgroup Gal(L/K)) (n : ℕ) :
    (fixedFieldSubextensionFiltration F H).lower n =
      ((F.lower n).comap H.subtype).comap
        (IntermediateField.subgroupEquivAlgEquiv H).symm.toMonoidHom :=
  rfl

/-- The quotient-image filtration transported to the actual Galois group
of `L^H / K`. -/
def fixedFieldQuotientImageFiltration
    (F : AntitoneNormalSubgroupFiltration Gal(L/K))
    (H : Subgroup Gal(L/K)) [H.Normal] :
    AntitoneNormalSubgroupFiltration Gal(IntermediateField.fixedField H/K) :=
  (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.quotientImageTransport F H) (IsGalois.normalAutEquivQuotient H)

/-- States the theorem `fixedFieldQuotientImageFiltration_lower`. -/
@[simp] theorem fixedFieldQuotientImageFiltration_lower
    (F : AntitoneNormalSubgroupFiltration Gal(L/K))
    (H : Subgroup Gal(L/K)) [H.Normal] (n : ℕ) :
    (fixedFieldQuotientImageFiltration F H).lower n =
      ((F.lower n).map (QuotientGroup.mk' H)).comap
        (IsGalois.normalAutEquivQuotient H).symm.toMonoidHom :=
  rfl

/-- Exact cardinality factorization in the two actual fixed-field Galois
group models. -/
theorem card_fixedFieldSubextension_mul_card_fixedFieldQuotientImage
    [Finite Gal(L/K)]
    (F : AntitoneNormalSubgroupFiltration Gal(L/K))
    (H : Subgroup Gal(L/K)) [H.Normal] (n : ℕ) :
    Nat.card ((fixedFieldSubextensionFiltration F H).lower n) *
        Nat.card ((fixedFieldQuotientImageFiltration F H).lower n) =
      Nat.card (F.lower n) := by
  change Nat.card ((RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.transportEquiv (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.subgroupFiltration F H)
      (IntermediateField.subgroupEquivAlgEquiv H)).lower n) *
    Nat.card (((RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.quotientImageTransport F H)
      (IsGalois.normalAutEquivQuotient H)).lower n) = _
  rw [RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.card_lower_transportEquiv (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.subgroupFiltration F H)
    (IntermediateField.subgroupEquivAlgEquiv H) n]
  exact RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.card_subgroupFiltration_mul_card_quotientImageTransport F H
    (IsGalois.normalAutEquivQuotient H) n

omit [IsGalois K L] in
/-- States the theorem `fixedFieldSubextension_herbrandFunction`. -/
theorem fixedFieldSubextension_herbrandFunction
    [Fintype Gal(L/K)]
    (F : AntitoneNormalSubgroupFiltration Gal(L/K))
    (H : Subgroup Gal(L/K)) (s : ℝ) :
    (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction (fixedFieldSubextensionFiltration F H)) s =
      (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.subgroupFiltration F H)) s := by
  let : Fintype H := Fintype.ofFinite H
  let : Fintype Gal(L/IntermediateField.fixedField H) :=
    Fintype.ofFinite Gal(L/IntermediateField.fixedField H)
  exact RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_transportEquiv (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.subgroupFiltration F H)
    (IntermediateField.subgroupEquivAlgEquiv H) s

omit [IsGalois K L] in
/-- States the theorem `fixedFieldSubextension_inverseHerbrandFunction`. -/
theorem fixedFieldSubextension_inverseHerbrandFunction
    [Fintype Gal(L/K)]
    (F : AntitoneNormalSubgroupFiltration Gal(L/K))
    (H : Subgroup Gal(L/K)) (t : ℝ) :
    (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction (fixedFieldSubextensionFiltration F H)) t =
      (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.subgroupFiltration F H)) t := by
  let : Fintype H := Fintype.ofFinite H
  let : Fintype Gal(L/IntermediateField.fixedField H) :=
    Fintype.ofFinite Gal(L/IntermediateField.fixedField H)
  exact RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction_transportEquiv (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.subgroupFiltration F H)
    (IntermediateField.subgroupEquivAlgEquiv H) t

/-- States the theorem `fixedFieldQuotientImage_herbrandFunction`. -/
theorem fixedFieldQuotientImage_herbrandFunction
    [Fintype Gal(L/K)]
    (F : AntitoneNormalSubgroupFiltration Gal(L/K))
    (H : Subgroup Gal(L/K)) [H.Normal] (s : ℝ) :
    (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction (fixedFieldQuotientImageFiltration F H)) s =
      (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.quotientImageFiltration F H)) s := by
  let : Fintype Gal(IntermediateField.fixedField H/K) :=
    Fintype.ofFinite Gal(IntermediateField.fixedField H/K)
  exact RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.quotientImageTransport_herbrandFunction F H
    (IsGalois.normalAutEquivQuotient H) s

/-- States the theorem `fixedFieldQuotientImage_inverseHerbrandFunction`. -/
theorem fixedFieldQuotientImage_inverseHerbrandFunction
    [Fintype Gal(L/K)]
    (F : AntitoneNormalSubgroupFiltration Gal(L/K))
    (H : Subgroup Gal(L/K)) [H.Normal] (t : ℝ) :
    (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction (fixedFieldQuotientImageFiltration F H)) t =
      (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.inverseHerbrandFunction (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.quotientImageFiltration F H)) t := by
  let : Fintype Gal(IntermediateField.fixedField H/K) :=
    Fintype.ofFinite Gal(IntermediateField.fixedField H/K)
  exact RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.quotientImageTransport_inverseHerbrandFunction F H
    (IsGalois.normalAutEquivQuotient H) t

end Higher
end RamificationTheory.HilbertRamification
