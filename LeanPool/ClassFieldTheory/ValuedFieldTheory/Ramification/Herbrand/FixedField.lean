/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.Herbrand.Quotient
public import Mathlib.FieldTheory.Galois.Basic
/-!
# Fixed-field group models for Herbrand towers
-/

@[expose] public section

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  card_lower_transportEquiv →
    card_lower_transportEquiv

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  card_subgroupFiltration_mul_card_quotientImageTransport →
    card_subgroupFiltration_mul_card_quotientImageTransport

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction →
    herbrandFunction

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction_transportEquiv →
    herbrandFunction_transportEquiv

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  inverseHerbrandFunction →
    inverseHerbrandFunction

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  inverseHerbrandFunction_transportEquiv →
    inverseHerbrandFunction_transportEquiv

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  quotientImageFiltration →
    quotientImageFiltration

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  quotientImageTransport →
    quotientImageTransport

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  quotientImageTransport_herbrandFunction →
    quotientImageTransport_herbrandFunction

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  quotientImageTransport_inverseHerbrandFunction →
    quotientImageTransport_inverseHerbrandFunction

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  subgroupFiltration →
    subgroupFiltration


noncomputable
section

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
  RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.transportEquiv
    (subgroupFiltration F H)
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
  (quotientImageTransport F H) (IsGalois.normalAutEquivQuotient H)

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
  change Nat.card
    ((RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.transportEquiv
    (subgroupFiltration F H)
      (IntermediateField.subgroupEquivAlgEquiv H)).lower n) *
    Nat.card
      (((quotientImageTransport F H)
      (IsGalois.normalAutEquivQuotient H)).lower n) = _
  rw [card_lower_transportEquiv (subgroupFiltration F H)
    (IntermediateField.subgroupEquivAlgEquiv H) n]
  exact
    card_subgroupFiltration_mul_card_quotientImageTransport F H
    (IsGalois.normalAutEquivQuotient H) n

omit [IsGalois K L] in
/-- States the theorem `fixedFieldSubextension_herbrandFunction`. -/
theorem fixedFieldSubextension_herbrandFunction
    (F : AntitoneNormalSubgroupFiltration Gal(L/K))
    (H : Subgroup Gal(L/K)) (s : ℝ) :
    (herbrandFunction
      (fixedFieldSubextensionFiltration F H)) s =
      (herbrandFunction (subgroupFiltration F H)) s := by
  let : Fintype H := Fintype.ofFinite H
  let : Fintype Gal(L/IntermediateField.fixedField H) :=
    Fintype.ofFinite Gal(L/IntermediateField.fixedField H)
  exact
    herbrandFunction_transportEquiv (subgroupFiltration F H)
    (IntermediateField.subgroupEquivAlgEquiv H) s

omit [IsGalois K L] in
/-- States the theorem `fixedFieldSubextension_inverseHerbrandFunction`. -/
theorem fixedFieldSubextension_inverseHerbrandFunction
    (F : AntitoneNormalSubgroupFiltration Gal(L/K))
    (H : Subgroup Gal(L/K)) (t : ℝ) :
    (inverseHerbrandFunction (fixedFieldSubextensionFiltration F H)) t =
      (inverseHerbrandFunction (subgroupFiltration F H)) t := by
  let : Fintype H := Fintype.ofFinite H
  let : Fintype Gal(L/IntermediateField.fixedField H) :=
    Fintype.ofFinite Gal(L/IntermediateField.fixedField H)
  exact
    inverseHerbrandFunction_transportEquiv (subgroupFiltration F H)
    (IntermediateField.subgroupEquivAlgEquiv H) t

/-- States the theorem `fixedFieldQuotientImage_herbrandFunction`. -/
theorem fixedFieldQuotientImage_herbrandFunction
    (F : AntitoneNormalSubgroupFiltration Gal(L/K))
    (H : Subgroup Gal(L/K)) [H.Normal] (s : ℝ) :
    (herbrandFunction
      (fixedFieldQuotientImageFiltration F H)) s =
      (herbrandFunction (quotientImageFiltration F H)) s := by
  let : Fintype Gal(IntermediateField.fixedField H/K) :=
    Fintype.ofFinite Gal(IntermediateField.fixedField H/K)
  exact
    quotientImageTransport_herbrandFunction F H
    (IsGalois.normalAutEquivQuotient H) s

/-- States the theorem `fixedFieldQuotientImage_inverseHerbrandFunction`. -/
theorem fixedFieldQuotientImage_inverseHerbrandFunction
    (F : AntitoneNormalSubgroupFiltration Gal(L/K))
    (H : Subgroup Gal(L/K)) [H.Normal] (t : ℝ) :
    (inverseHerbrandFunction (fixedFieldQuotientImageFiltration F H)) t =
      (inverseHerbrandFunction (quotientImageFiltration F H)) t := by
  let : Fintype Gal(IntermediateField.fixedField H/K) :=
    Fintype.ofFinite Gal(IntermediateField.fixedField H/K)
  exact
    quotientImageTransport_inverseHerbrandFunction F H
    (IsGalois.normalAutEquivQuotient H) t

end Higher
end RamificationTheory.HilbertRamification
