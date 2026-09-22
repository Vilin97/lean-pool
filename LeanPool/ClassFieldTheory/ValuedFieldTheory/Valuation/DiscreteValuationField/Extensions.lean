/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Group.Units.Hom

/-! # Extensions -/
namespace ValuationTheory

/-!
# Finite extensions of discretely valued fields

The extension relation is ambient data: an algebra, finite-dimensionality, and
mathlib's `Valuation.HasExtension` property.  There is deliberately no
proof-irrelevant marker object.  All invariants and maps are defined once for
`DVF` values and can therefore be used unchanged for Henselian and complete
discretely valued fields through their canonical `toDVF` projections.
-/

noncomputable section

universe u v w x

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : DVF.{u, v} K) (target : DVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The field degree of a finite valued extension. -/
def degree (_base : DVF.{u, v} K) (_target : DVF.{w, x} L) : ℕ :=
  Module.finrank K L

omit [FiniteDimensional K L]
    [base.valuation.HasExtension target.valuation] in
/-- The degree of a finite extension of discrete valuation fields is its linear `finrank`. -/
@[simp] theorem degree_eq_finrank :
    degree base target = Module.finrank K L :=
  rfl

/-- The canonical ramification index of the target maximal ideal over the
base maximal ideal. -/
noncomputable def ramificationIndex : ℕ :=
  Ideal.ramificationIdx'
    (base.maximalIdeal : Ideal base.valuationSubring)
    (target.maximalIdeal : Ideal target.valuationSubring)

/-- The canonical residue degree of the target maximal ideal over the base
maximal ideal. -/
noncomputable def residueDegree : ℕ :=
  (target.maximalIdeal : Ideal target.valuationSubring).inertiaDeg
    base.valuationSubring

/-- The induced map between valuation subrings. -/
def integerMap :
    base.valuationSubring →+* target.valuationSubring :=
  algebraMap base.valuationSubring target.valuationSubring

omit [FiniteDimensional K L] in
/-- The induced map between valuation subrings is injective. -/
theorem integerMap_injective :
    Function.Injective (integerMap base target) := by
  change Function.Injective
    (algebraMap base.valuation.valuationSubring
      target.valuation.valuationSubring)
  exact _root_.Valuation.HasExtension.algebraMap_injective
    (vK := base.valuation) (vA := target.valuation)

omit [FiniteDimensional K L] in
/-- The valuation-subring map evaluates through the ambient algebra map. -/
@[simp] theorem integerMap_apply (a : base.valuationSubring) :
    (((integerMap base target) a : target.valuationSubring) : L) =
      algebraMap K L (a : K) := by
  change ((algebraMap base.valuation.valuationSubring
    target.valuation.valuationSubring) a : L) = algebraMap K L (a : K)
  rfl

omit [FiniteDimensional K L] in
/-- Elementwise form of valuation-ring pullback along the field algebra map. -/
theorem algebraMap_mem_valuationSubring_iff (a : K) :
    algebraMap K L a ∈ target.valuation.valuationSubring ↔
      a ∈ base.valuation.valuationSubring := by
  rw [target.mem_valuationSubring_iff, base.mem_valuationSubring_iff]
  exact _root_.Valuation.HasExtension.val_map_le_one_iff
    (vR := base.valuation) (vA := target.valuation) a

omit [FiniteDimensional K L] in
/-- Maximal-ideal membership is reflected by a valued extension. -/
theorem integerMap_mem_maximalIdeal_iff (a : base.valuationSubring) :
    integerMap base target a ∈ target.maximalIdeal ↔
      a ∈ base.maximalIdeal := by
  rw [target.mem_maximalIdeal_iff (integerMap base target a),
    base.mem_maximalIdeal_iff a, integerMap_apply base target a]
  exact _root_.Valuation.HasExtension.val_map_lt_one_iff
    (vR := base.valuation) (vA := target.valuation) (a : K)

omit [FiniteDimensional K L] in
/-- Nonmembership in the maximal ideal is reflected by a valued extension. -/
theorem integerMap_not_mem_maximalIdeal_iff (a : base.valuationSubring) :
    integerMap base target a ∉ target.maximalIdeal ↔
      a ∉ base.maximalIdeal :=
  not_congr (integerMap_mem_maximalIdeal_iff base target a)

omit [FiniteDimensional K L] in
/-- The integer map of a valued extension preserves and reflects units. -/
theorem integerMap_isUnit_iff (a : base.valuationSubring) :
    IsUnit (integerMap base target a) ↔ IsUnit a := by
  rw [← IsLocalRing.notMem_maximalIdeal,
    ← IsLocalRing.notMem_maximalIdeal]
  exact integerMap_not_mem_maximalIdeal_iff base target a

omit [FiniteDimensional K L] in
/-- The target maximal ideal pulls back to the base maximal ideal. -/
theorem maximalIdeal_comap_integerMap_eq :
    target.maximalIdeal.comap (integerMap base target) =
      base.maximalIdeal := by
  ext a
  exact integerMap_mem_maximalIdeal_iff base target a

omit [FiniteDimensional K L] in
/-- The image of the source maximal ideal in the target valuation ring is nonzero. -/
theorem maximalIdeal_map_integerMap_ne_bot :
    Ideal.map (integerMap base target) base.maximalIdeal ≠ ⊥ := by
  intro h
  exact base.maximalIdeal_ne_bot
    ((Ideal.map_eq_bot_iff_of_injective
      (integerMap_injective base target)).1 h)

omit [FiniteDimensional K L] in
/-- The source maximal ideal maps into the target maximal ideal. -/
theorem maximalIdeal_map_integerMap_le :
    Ideal.map (integerMap base target) base.maximalIdeal ≤
      target.maximalIdeal := by
  rw [Ideal.map_le_iff_le_comap,
    maximalIdeal_comap_integerMap_eq base target]

/- A valued extension preserves the residue-field characteristic. -/
omit [FiniteDimensional K L] in
/-- Residue fields connected by a valued extension have the same ring characteristic. -/
theorem residueField_ringChar_eq_of_hasExtension :
    ringChar target.residueField = ringChar base.residueField :=
  (Algebra.ringChar_eq base.residueField target.residueField).symm

/-- The induced map on residue fields. -/
def residueMap :
    base.residueField →+* target.residueField :=
  algebraMap base.residueField target.residueField

omit [FiniteDimensional K L] in
/-- The residue-field map sends the residue of an integer to its target residue. -/
@[simp] theorem residueMap_residue (a : base.valuationSubring) :
    residueMap base target (base.residueMap a) =
      target.residueMap (integerMap base target a) := by
  change
    (algebraMap
      (_root_.IsLocalRing.ResidueField base.valuation.valuationSubring)
      (_root_.IsLocalRing.ResidueField target.valuation.valuationSubring))
      (_root_.IsLocalRing.residue base.valuation.valuationSubring a) =
    _root_.IsLocalRing.residue target.valuation.valuationSubring
      ((algebraMap base.valuation.valuationSubring
        target.valuation.valuationSubring) a)
  rfl

omit [FiniteDimensional K L] in
/-- The residue-field map of a valued extension is injective. -/
theorem residueMap_injective :
    Function.Injective (residueMap base target) := by
  change Function.Injective
    (algebraMap
      (_root_.IsLocalRing.ResidueField base.valuation.valuationSubring)
      (_root_.IsLocalRing.ResidueField target.valuation.valuationSubring))
  rw [ValuationTheory.DiscreteValuationField.ResidueField.algebraMap_eq_map_algebraMap]
  exact ValuationTheory.DiscreteValuationField.ResidueField.map_algebraMap_injective

omit [FiniteDimensional K L] in
/-- The residue-field map of a valued extension has trivial kernel. -/
theorem residueMap_eq_zero_iff (z : base.residueField) :
    residueMap base target z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    exact residueMap_injective base target (by simpa using hz)
  · rintro rfl
    exact map_zero (residueMap base target)

omit [FiniteDimensional K L] in
/-- Nonzero residue classes remain nonzero after mapping. -/
theorem residueMap_ne_zero_iff (z : base.residueField) :
    residueMap base target z ≠ 0 ↔ z ≠ 0 :=
  not_congr (residueMap_eq_zero_iff base target z)

omit [FiniteDimensional K L] in
/-- Equality of base residue classes can be checked after mapping. -/
theorem residueMap_eq_iff (a b : base.residueField) :
    residueMap base target a = residueMap base target b ↔ a = b := by
  constructor
  · intro h
    exact residueMap_injective base target h
  · rintro rfl
    rfl

omit [FiniteDimensional K L] in
/-- The residue-field map reflects the unit element. -/
theorem residueMap_eq_one_iff (a : base.residueField) :
    residueMap base target a = 1 ↔ a = 1 := by
  rw [← map_one (residueMap base target),
    residueMap_eq_iff base target a 1]

omit [FiniteDimensional K L] in
/-- Surjectivity of the residue map upgrades its canonical injectivity to
bijectivity. -/
theorem residueMap_bijective_of_surjective
    (hSurj : Function.Surjective (residueMap base target)) :
    Function.Bijective (residueMap base target) :=
  ⟨residueMap_injective base target, hSurj⟩

omit [FiniteDimensional K L] in
/-- The residue-field isomorphism attached to a surjective residue map. -/
noncomputable def residueFieldEquivOfSurjective
    (hSurj : Function.Surjective (residueMap base target)) :
    base.residueField ≃+* target.residueField :=
  RingEquiv.ofBijective (residueMap base target)
    (residueMap_bijective_of_surjective base target hSurj)

omit [FiniteDimensional K L] in
/-- The residue-field equivalence induced by surjectivity evaluates by the residue map. -/
@[simp] theorem residueFieldEquivOfSurjective_apply
    (hSurj : Function.Surjective (residueMap base target))
    (z : base.residueField) :
    residueFieldEquivOfSurjective base target hSurj z =
      residueMap base target z :=
  rfl

omit [FiniteDimensional K L] in
/-- The inverse residue-field equivalence recovers a source class after applying the residue map. -/
@[simp] theorem residueFieldEquivOfSurjective_symm_apply_residueMap
    (hSurj : Function.Surjective (residueMap base target))
    (z : base.residueField) :
    (residueFieldEquivOfSurjective base target hSurj).symm
        (residueMap base target z) = z := by
  simpa using
    (residueFieldEquivOfSurjective base target hSurj).symm_apply_apply z

omit [FiniteDimensional K L] in
/-- Applying the residue map after the inverse residue-field equivalence recovers
the target class. -/
@[simp] theorem residueMap_residueFieldEquivOfSurjective_symm_apply
    (hSurj : Function.Surjective (residueMap base target))
    (z : target.residueField) :
    residueMap base target
        ((residueFieldEquivOfSurjective base target hSurj).symm z) = z :=
  (residueFieldEquivOfSurjective base target hSurj).apply_symm_apply z

omit [FiniteDimensional K L] in
/-- Zero of a mapped residue class is exactly base maximal-ideal membership. -/
theorem residueMap_residue_eq_zero_iff (a : base.valuationSubring) :
    residueMap base target (base.residueMap a) = 0 ↔
      a ∈ base.maximalIdeal := by
  rw [residueMap_eq_zero_iff base target,
    base.residue_eq_zero_iff]

omit [FiniteDimensional K L] in
/-- Nonzero of a mapped residue class is exactly nonmembership in the base
maximal ideal. -/
theorem residueMap_residue_ne_zero_iff (a : base.valuationSubring) :
    residueMap base target (base.residueMap a) ≠ 0 ↔
      a ∉ base.maximalIdeal :=
  not_congr (residueMap_residue_eq_zero_iff base target a)

omit [FiniteDimensional K L] in
/-- Nonzero of a mapped residue class is exactly unitness of its
representative. -/
theorem residueMap_residue_ne_zero_iff_isUnit
    (a : base.valuationSubring) :
    residueMap base target (base.residueMap a) ≠ 0 ↔ IsUnit a :=
  (residueMap_residue_ne_zero_iff base target a).trans
    (IsLocalRing.notMem_maximalIdeal (x := a))

omit [FiniteDimensional K L] in
/-- Equality of mapped residue classes is equality in the base residue field. -/
theorem residueMap_residue_eq_iff (a b : base.valuationSubring) :
    residueMap base target (base.residueMap a) =
        residueMap base target (base.residueMap b) ↔
      base.residueMap a = base.residueMap b :=
  residueMap_eq_iff base target (base.residueMap a) (base.residueMap b)

omit [FiniteDimensional K L] in
/-- Congruence criterion comparing a mapped base residue with a target
representative. -/
theorem residueMap_residue_eq_target_residue_iff_sub_mem_maximalIdeal
    (a : base.valuationSubring) (b : target.valuationSubring) :
    residueMap base target (base.residueMap a) = target.residueMap b ↔
      integerMap base target a - b ∈ target.maximalIdeal := by
  rw [residueMap_residue base target]
  exact
    ValuationTheory.DiscreteValuationField.ResidueField.residue_eq_residue_iff_sub_mem_maximalIdeal
      (R := target.valuationSubring) (integerMap base target a) b

omit [FiniteDimensional K L] in
/-- Opposite-orientation form of the target congruence criterion. -/
theorem target_residue_eq_residueMap_residue_iff_sub_mem_maximalIdeal
    (b : target.valuationSubring) (a : base.valuationSubring) :
    target.residueMap b = residueMap base target (base.residueMap a) ↔
      b - integerMap base target a ∈ target.maximalIdeal := by
  rw [residueMap_residue base target]
  exact
    ValuationTheory.DiscreteValuationField.ResidueField.residue_eq_residue_iff_sub_mem_maximalIdeal
      (R := target.valuationSubring) b (integerMap base target a)

omit [FiniteDimensional K L] in
/-- Target-residue form of zero detection for a mapped base integer. -/
theorem target_residue_integerMap_eq_zero_iff
    (a : base.valuationSubring) :
    target.residueMap (integerMap base target a) = 0 ↔
      a ∈ base.maximalIdeal := by
  rw [← residueMap_residue base target a,
    residueMap_residue_eq_zero_iff base target]

omit [FiniteDimensional K L] in
/-- Target-residue form of nonzero detection for a mapped base integer. -/
theorem target_residue_integerMap_ne_zero_iff
    (a : base.valuationSubring) :
    target.residueMap (integerMap base target a) ≠ 0 ↔
      a ∉ base.maximalIdeal :=
  not_congr (target_residue_integerMap_eq_zero_iff base target a)

omit [FiniteDimensional K L] in
/-- A mapped base integer has nonzero target residue exactly when it is a
unit in the base valuation ring. -/
theorem target_residue_integerMap_ne_zero_iff_isUnit
    (a : base.valuationSubring) :
    target.residueMap (integerMap base target a) ≠ 0 ↔ IsUnit a :=
  (target_residue_integerMap_ne_zero_iff base target a).trans
    (IsLocalRing.notMem_maximalIdeal (x := a))

omit [FiniteDimensional K L] in
/-- A mapped base integer has nonzero target residue exactly when its image is
a unit. -/
theorem target_residue_integerMap_ne_zero_iff_integerMap_isUnit
    (a : base.valuationSubring) :
    target.residueMap (integerMap base target a) ≠ 0 ↔
      IsUnit (integerMap base target a) :=
  target.residue_ne_zero_iff_isUnit (integerMap base target a)

omit [FiniteDimensional K L] in
/-- Nonzero residue is preserved and reflected by the integer map. -/
theorem target_residue_integerMap_ne_zero_iff_base_residue_ne_zero
    (a : base.valuationSubring) :
    target.residueMap (integerMap base target a) ≠ 0 ↔
      base.residueMap a ≠ 0 :=
  (target_residue_integerMap_ne_zero_iff_isUnit base target a).trans
    (base.residue_ne_zero_iff_isUnit a).symm

omit [FiniteDimensional K L] in
/-- A mapped valuation-ring element is a unit exactly when its target residue is nonzero. -/
theorem integerMap_isUnit_iff_target_residue_integerMap_ne_zero
    (a : base.valuationSubring) :
    IsUnit (integerMap base target a) ↔
      target.residueMap (integerMap base target a) ≠ 0 :=
  (target_residue_integerMap_ne_zero_iff_integerMap_isUnit
    base target a).symm

omit [FiniteDimensional K L] in
/-- A mapped valuation-ring element is a unit exactly when its source residue is nonzero. -/
theorem integerMap_isUnit_iff_base_residue_ne_zero
    (a : base.valuationSubring) :
    IsUnit (integerMap base target a) ↔ base.residueMap a ≠ 0 :=
  (integerMap_isUnit_iff base target a).trans
    (base.residue_ne_zero_iff_isUnit a).symm

omit [FiniteDimensional K L] in
/-- Equality of target residues of mapped base integers is equality of their
base residues. -/
theorem target_residue_integerMap_eq_iff
    (a b : base.valuationSubring) :
    target.residueMap (integerMap base target a) =
        target.residueMap (integerMap base target b) ↔
      base.residueMap a = base.residueMap b := by
  rw [← residueMap_residue base target a,
    ← residueMap_residue base target b,
    residueMap_residue_eq_iff base target]

omit [FiniteDimensional K L] in
/-- A mapped integer has target residue one exactly when its source residue is one. -/
theorem target_residue_integerMap_eq_one_iff_base_residue_eq_one
    (a : base.valuationSubring) :
    target.residueMap (integerMap base target a) = 1 ↔
      base.residueMap a = 1 := by
  rw [← residueMap_residue base target a,
    residueMap_eq_one_iff base target]

/-- The induced map on unit groups of valuation rings. -/
def unitMap :
    base.valuationSubringˣ →* target.valuationSubringˣ :=
  Units.map (integerMap base target).toMonoidHom

omit [FiniteDimensional K L] in
/-- The induced unit map agrees with the valuation-ring map on underlying elements. -/
@[simp] theorem unitMap_apply (a : base.valuationSubringˣ) :
    ((unitMap base target a : target.valuationSubringˣ) :
        target.valuationSubring) =
      integerMap base target (a : base.valuationSubring) :=
  rfl

omit [FiniteDimensional K L] in
/-- The induced map on residue-field units is injective. -/
theorem residueUnitsMap_injective :
    Function.Injective
      (Units.map (residueMap base target).toMonoidHom) :=
  Units.map_injective (residueMap_injective base target)

omit [FiniteDimensional K L] in
/-- Surjectivity of the residue map implies surjectivity on residue-field units. -/
theorem residueUnitsMap_surjective_of_residueMap_surjective
    (hSurj : Function.Surjective (residueMap base target)) :
    Function.Surjective
      (Units.map (residueMap base target).toMonoidHom) := by
  intro y
  obtain ⟨z, hz⟩ := hSurj (y : target.residueField)
  have hz0 : z ≠ 0 := by
    intro h
    exact y.ne_zero (by simpa [h] using hz.symm)
  refine ⟨Units.mk0 z hz0, ?_⟩
  apply Units.ext
  simpa using hz

omit [FiniteDimensional K L] in
/-- A surjective residue map induces a bijection on residue-field units. -/
theorem residueUnitsMap_bijective_of_residueMap_surjective
    (hSurj : Function.Surjective (residueMap base target)) :
    Function.Bijective
      (Units.map (residueMap base target).toMonoidHom) :=
  ⟨residueUnitsMap_injective base target,
    residueUnitsMap_surjective_of_residueMap_surjective base target hSurj⟩

omit [FiniteDimensional K L] in
/-- The unit-group equivalence induced by a surjective residue map. -/
noncomputable def residueUnitsEquivOfResidueMapSurjective
    (hSurj : Function.Surjective (residueMap base target)) :
    base.residueFieldˣ ≃* target.residueFieldˣ :=
  MulEquiv.ofBijective (Units.map (residueMap base target).toMonoidHom)
    (residueUnitsMap_bijective_of_residueMap_surjective
      base target hSurj)

omit [FiniteDimensional K L] in
/-- The residue-unit equivalence evaluates by the induced residue-unit map. -/
@[simp] theorem residueUnitsEquivOfResidueMapSurjective_apply
    (hSurj : Function.Surjective (residueMap base target))
    (a : base.residueFieldˣ) :
    residueUnitsEquivOfResidueMapSurjective base target hSurj a =
      Units.map (residueMap base target).toMonoidHom a :=
  rfl

omit [FiniteDimensional K L] in
/-- The residue-field equivalence sends a source residue to the corresponding target residue. -/
theorem residueFieldEquivOfSurjective_apply_residue
    (hSurj : Function.Surjective (residueMap base target))
    (a : base.valuationSubring) :
    residueFieldEquivOfSurjective base target hSurj (base.residueMap a) =
      target.residueMap (integerMap base target a) := by
  rw [residueFieldEquivOfSurjective_apply,
    residueMap_residue]

omit [FiniteDimensional K L] in
/-- The inverse residue-field equivalence sends a target residue back to its source residue. -/
@[simp] theorem residueFieldEquivOfSurjective_symm_apply_target_residue
    (hSurj : Function.Surjective (residueMap base target))
    (a : base.valuationSubring) :
    (residueFieldEquivOfSurjective base target hSurj).symm
        (target.residueMap (integerMap base target a)) =
      base.residueMap a := by
  rw [← residueMap_residue base target,
    residueFieldEquivOfSurjective_symm_apply_residueMap]

/-- Unramified means that the canonical ramification index is one. -/
def IsUnramified : Prop :=
  ramificationIndex base target = 1

/-- Totally ramified means that the canonical residue degree is one. -/
def IsTotallyRamified : Prop :=
  residueDegree base target = 1

/-- Defectlessness is the exact fundamental equality. -/
def IsDefectless : Prop :=
  degree base target =
    ramificationIndex base target * residueDegree base target

end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
