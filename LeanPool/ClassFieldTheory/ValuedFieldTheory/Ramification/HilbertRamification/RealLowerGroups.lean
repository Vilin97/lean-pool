/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.FieldTheory.Galois.Basic
/-!
# Real lower ramification groups

This file gives the intrinsic definitions and the elementary structural
facts in the real lower-ramification definition and the lower-ramification base-change law.  It uses
discretely valued fields, not complete discretely valued fields.  The unique
extension hypothesis is stated for `DVF` itself and is used to derive (rather
than assume) preservation of the chosen valuation ring by the Galois group.

The real index is implemented canonically by the maximal-ideal filtration:
the condition at `s` is membership in `m ^ ceil(s + 1)`.  The exponent is
truncated at zero, so the definition extends harmlessly to every real number
and is the full Galois group for `s <= -1`.
-/

@[expose] public section

noncomputable
section

open scoped Pointwise

universe u v w x y

namespace RamificationTheory.DiscreteValuationField

open ValuationTheory.DiscreteValuationField

namespace DVF

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

/-- Unique extension of a valuation, at the general DVF level.

This is the direct noncomplete analogue of the existing predicates on
`HenselianDVF` and `CompleteDVF`: every valuation of `L` extending the chosen
base valuation is equivalent to the chosen target valuation. -/
def HasUniqueValuationExtension (base : DVF.{u, v} K)
    (target : DVF.{w, x} L) : Prop :=
  ∀ {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'],
      target.valuation.IsEquiv v'

/-- Pulling the target valuation back along a `K`-automorphism again gives an
extension of the base valuation. -/
theorem algEquiv_comap_valuation_hasExtension
    {base : DVF.{u, v} K} {target : DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (σ : L ≃ₐ[K] L) :
    base.valuation.HasExtension (target.valuation.comap (σ : L →+* L)) where
  val_isEquiv_comap := by
    rw [_root_.Valuation.isEquiv_iff_val_le_one]
    intro a
    simpa [_root_.Valuation.comap, σ.commutes a] using
      (_root_.Valuation.HasExtension.val_map_le_one_iff
        (vR := base.valuation) (vA := target.valuation) a).symm

/-- Unique extension makes every `K`-automorphism preserve membership in the
chosen target valuation ring. -/
theorem mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
    {base : DVF.{u, v} K} {target : DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (σ : L ≃ₐ[K] L) (z : L) :
    z ∈ target.valuation.valuationSubring ↔
      σ z ∈ target.valuation.valuationSubring := by
  let vσ := target.valuation.comap (σ : L →+* L)
  let : base.valuation.HasExtension vσ :=
    algEquiv_comap_valuation_hasExtension
      (base := base) (target := target) σ
  have hsub :
      target.valuation.valuationSubring = vσ.valuationSubring :=
    (_root_.Valuation.isEquiv_iff_valuationSubring target.valuation vσ).1
      (huniq vσ)
  change z ∈ target.valuation.valuationSubring ↔ z ∈ vσ.valuationSubring
  rw [hsub]

end DVF
end RamificationTheory.DiscreteValuationField

namespace RamificationTheory.HilbertRamification
namespace Higher

open RamificationTheory.DiscreteValuationField.DVF

open RamificationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- The integral exponent corresponding to a real lower ramification index.

For `s >= -1` this is `ceil (s + 1)`.  The use of `Int.toNat` also makes it
zero for `s <= -1`, which gives the expected constant extension below the
natural indexing range. -/
def realRamificationExponent (s : ℝ) : ℕ :=
  (Int.ceil (s + 1)).toNat

/-- States the theorem `realRamificationExponent_mono`. -/
theorem realRamificationExponent_mono :
    Monotone realRamificationExponent := by
  intro s t hst
  apply Int.toNat_le_toNat
  apply Int.ceil_mono
  linarith

/-- States the theorem `realRamificationExponent_neg_one`. -/
@[simp] theorem realRamificationExponent_neg_one :
    realRamificationExponent (-1) = 0 := by
  simp [realRamificationExponent]

/-- States the theorem `realRamificationExponent_eq_zero_of_le_neg_one`. -/
theorem realRamificationExponent_eq_zero_of_le_neg_one
    {s : ℝ} (hs : s ≤ -1) :
    realRamificationExponent s = 0 := by
  rw [realRamificationExponent, Int.toNat_eq_zero]
  have hs' : s + 1 ≤ 0 := by linarith
  exact Int.ceil_le.mpr (by simpa using hs')

/-- States the theorem `realRamificationExponent_nat`. -/
@[simp] theorem realRamificationExponent_nat (n : ℕ) :
    realRamificationExponent (n : ℝ) = n + 1 := by
  simp [realRamificationExponent]

/-- The maximal-ideal power representing the real lower index `s`. -/
def realRamificationIdeal (target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L)
    (s : ℝ) : Ideal target.valuationSubring :=
  target.maximalIdeal ^ realRamificationExponent s

/-- States the theorem `realRamificationIdeal_antitone`. -/
theorem realRamificationIdeal_antitone {s t : ℝ} (hst : s ≤ t) :
    realRamificationIdeal target t ≤ realRamificationIdeal target s := by
  exact Ideal.pow_le_pow_right (realRamificationExponent_mono hst)

/-- States the theorem `realRamificationIdeal_neg_one`. -/
@[simp] theorem realRamificationIdeal_neg_one :
    realRamificationIdeal target (-1) = ⊤ := by
  simp [realRamificationIdeal]

/-- States the theorem `realRamificationIdeal_nat`. -/
@[simp] theorem realRamificationIdeal_nat (n : ℕ) :
    realRamificationIdeal target (n : ℝ) = target.maximalIdeal ^ (n + 1) := by
  simp [realRamificationIdeal]

/-- States the theorem `realRamificationIdeal_eq_top_of_le_neg_one`. -/
theorem realRamificationIdeal_eq_top_of_le_neg_one
    {s : ℝ} (hs : s ≤ -1) :
    realRamificationIdeal target s = ⊤ := by
  simp [realRamificationIdeal,
    realRamificationExponent_eq_zero_of_le_neg_one hs]

/-- The automorphism induced on the target valuation ring by uniqueness of the
valuation extension. -/
def valuationSubringAutOfUniqueExtension
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) :
    target.valuationSubring ≃+* target.valuationSubring where
  toFun a :=
    ⟨σ (a : L),
      (mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
          (base := base) (target := target) huniq σ (a : L)).1 a.property⟩
  invFun a :=
    ⟨σ⁻¹ (a : L),
      (mem_valuationSubring_algEquiv_iff_of_hasUniqueValuationExtension
          (base := base) (target := target) huniq σ⁻¹ (a : L)).1 a.property⟩
  left_inv a := by
    ext
    simp
  right_inv a := by
    ext
    simp
  map_mul' a b := by
    ext
    simp
  map_add' a b := by
    ext
    simp

/-- States the theorem `valuationSubringAutOfUniqueExtension_apply_coe`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_apply_coe
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (a : target.valuationSubring) :
    ((valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ a :
        target.valuationSubring) : L) = σ (a : L) :=
  rfl

/-- States the theorem `valuationSubringAutOfUniqueExtension_one_apply`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_one_apply
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq 1 a = a := by
  ext
  simp

/-- States the theorem `valuationSubringAutOfUniqueExtension_mul_apply`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_mul_apply
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ τ : Gal(L/K)) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq (σ * τ) a =
      valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq τ a) := by
  ext
  rfl

/-- States the theorem `valuationSubringAutOfUniqueExtension_apply_inv_apply`. -/
@[simp] theorem valuationSubringAutOfUniqueExtension_apply_inv_apply
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ⁻¹ a) = a := by
  ext
  simp

/-- A uniquely extended valuation-ring automorphism preserves the maximal
ideal. -/
theorem valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a ∈ target.maximalIdeal ↔
      a ∈ target.maximalIdeal := by
  let e := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq σ
  change e a ∈ target.maximalIdeal ↔ a ∈ target.maximalIdeal
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hea ha
    exact hea (by simpa using ha.map (e : target.valuationSubring →* target.valuationSubring))
  · intro ha hea
    exact ha (by simpa using hea.map (e.symm : target.valuationSubring →* target.valuationSubring))

/-- A uniquely extended valuation-ring automorphism preserves every power of
the maximal ideal. -/
theorem valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (n : ℕ) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a ∈ target.maximalIdeal ^ n ↔
      a ∈ target.maximalIdeal ^ n := by
  let e := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq σ
  have hm :
      Ideal.map (e : target.valuationSubring →+* target.valuationSubring)
          target.maximalIdeal = target.maximalIdeal := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective
      (e : target.valuationSubring →+* target.valuationSubring) e.surjective]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact
        (valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff
          (base := base) (target := target) huniq σ b).2 hb
    · intro ha
      refine ⟨e.symm a, ?_, by simp [e]⟩
      exact
        (valuationSubringAutOfUniqueExtension_mem_maximalIdeal_iff
          (base := base) (target := target) huniq σ (e.symm a)).1
          (by simpa [e] using ha)
  have hmap :
      Ideal.map (e : target.valuationSubring →+* target.valuationSubring)
          (target.maximalIdeal ^ n) = target.maximalIdeal ^ n := by
    rw [Ideal.map_pow, hm]
  constructor
  · intro ha
    rw [← hmap] at ha
    rcases (Ideal.mem_map_iff_of_surjective
      (e : target.valuationSubring →+* target.valuationSubring) e.surjective).1 ha with
      ⟨b, hb, hba⟩
    have : b = a := e.injective hba
    simpa [this] using hb
  · intro ha
    rw [← hmap]
    exact Ideal.mem_map_of_mem
      (e : target.valuationSubring →+* target.valuationSubring) ha

/-- States the theorem `valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff`. -/
theorem valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (σ : Gal(L/K)) (s : ℝ) (a : target.valuationSubring) :
    valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a ∈
          realRamificationIdeal target s ↔
      a ∈ realRamificationIdeal target s := by
  exact valuationSubringAutOfUniqueExtension_mem_maximalIdeal_pow_iff
    (base := base) (target := target) huniq σ
      (realRamificationExponent s) a

/-- The real lower-ramification definition: the real-index lower ramification
group.  On the natural range `s >= -1`, membership is exactly the condition that
all integral displacements have normalized additive value at least `s + 1`,
expressed intrinsically as membership in `m ^ ceil(s + 1)`. -/
def lowerRamificationGroup
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (s : ℝ) : Subgroup Gal(L/K) where
  carrier :=
    {σ | ∀ a : target.valuationSubring,
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a - a ∈
        realRamificationIdeal target s}
  one_mem' := by
    intro a
    simp
  mul_mem' := by
    intro σ τ hσ hτ a
    have hτa :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq τ a - a ∈
          realRamificationIdeal target s :=
      hτ a
    have hmapτa :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq τ a - a) ∈
          realRamificationIdeal target s :=
      (valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff
        (base := base) (target := target) huniq σ s _).2 hτa
    have hσa :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - a ∈
          realRamificationIdeal target s :=
      hσ a
    have hdecomp :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq (σ * τ) a - a =
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ
              (valuationSubringAutOfUniqueExtension
                (base := base) (target := target) huniq τ a - a) +
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a) := by
      rw [valuationSubringAutOfUniqueExtension_mul_apply, map_sub]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hmapτa hσa
  inv_mem' := by
    intro σ hσ a
    let b := valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ⁻¹ a
    have hb :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ b - b ∈
          realRamificationIdeal target s :=
      hσ b
    have hab : a - b ∈ realRamificationIdeal target s := by
      simpa [b] using hb
    have hba : b - a ∈ realRamificationIdeal target s := by
      simpa [sub_eq_add_neg, add_comm] using
        (realRamificationIdeal target s).neg_mem hab
    simpa [b] using hba

/-- States the theorem `mem_lowerRamificationGroup_iff`. -/
@[simp] theorem mem_lowerRamificationGroup_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (s : ℝ) (σ : Gal(L/K)) :
    σ ∈ lowerRamificationGroup
        (base := base) (target := target) huniq s ↔
      ∀ a : target.valuationSubring,
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - a ∈
          realRamificationIdeal target s :=
  Iff.rfl

/-- At an integral index, the real definition is exactly the usual
`m^(n+1)` displacement condition. -/
theorem mem_lowerRamificationGroup_nat_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (n : ℕ) (σ : Gal(L/K)) :
    σ ∈ lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ) ↔
      ∀ a : target.valuationSubring,
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - a ∈
          target.maximalIdeal ^ (n + 1) := by
  simp only [mem_lowerRamificationGroup_iff, realRamificationIdeal_nat]

/-- The real lower-ramification definition: the lower groups are decreasing in their real index. -/
theorem lowerRamificationGroup_antitone
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target) :
    Antitone (lowerRamificationGroup
      (base := base) (target := target) huniq) := by
  intro s t hst σ hσ a
  exact realRamificationIdeal_antitone (target := target) hst (hσ a)

/-- The real lower-ramification definition: every real lower ramification group is normal. -/
theorem lowerRamificationGroup_normal
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (s : ℝ) :
    (lowerRamificationGroup
      (base := base) (target := target) huniq s).Normal := by
  refine Subgroup.Normal.mk ?_
  intro σ hσ τ a
  let b := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq τ⁻¹ a
  have hb :
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ b - b ∈
        realRamificationIdeal target s :=
    hσ b
  have hmap :
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq τ
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ b - b) ∈
        realRamificationIdeal target s :=
    (valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff
      (base := base) (target := target) huniq τ s _).2 hb
  have hrewrite :
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq (τ * σ * τ⁻¹) a - a =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq τ
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ b - b) := by
    simp [b, map_sub]
  rwa [hrewrite]

/-- Provides the instance `instNormal`. -/
instance lowerRamificationGroup.instNormal
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (s : ℝ) :
    (lowerRamificationGroup
      (base := base) (target := target) huniq s).Normal :=
  lowerRamificationGroup_normal
    (base := base) (target := target) huniq s

/-- The real lower-ramification definition: `G_{-1}` is the full Galois group. -/
@[simp] theorem lowerRamificationGroup_neg_one
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target) :
    lowerRamificationGroup
      (base := base) (target := target) huniq (-1) = ⊤ := by
  ext σ
  simp [mem_lowerRamificationGroup_iff]

/-- The all-real extension is constant at the full Galois group below the
distinguished endpoint `-1`. -/
theorem lowerRamificationGroup_eq_top_of_le_neg_one
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    {s : ℝ} (hs : s ≤ -1) :
    lowerRamificationGroup
      (base := base) (target := target) huniq s = ⊤ := by
  ext σ
  simp [mem_lowerRamificationGroup_iff,
    realRamificationIdeal_eq_top_of_le_neg_one (target := target) hs]

/-- Restriction of scalars from `Gal(L/M)` to `Gal(L/K)`. -/
def galRestrictScalarsToIntermediate (M : IntermediateField K L) :
    Gal(L/M) →* Gal(L/K) where
  toFun σ := AlgEquiv.restrictScalars K σ
  map_one' := rfl
  map_mul' _ _ := rfl

/-- States the theorem `galRestrictScalarsToIntermediate_apply`. -/
@[simp] theorem galRestrictScalarsToIntermediate_apply
    (M : IntermediateField K L) (σ : Gal(L/M)) :
    galRestrictScalarsToIntermediate M σ = AlgEquiv.restrictScalars K σ :=
  rfl

/-- States the theorem `galRestrictScalarsToIntermediate_injective`. -/
theorem galRestrictScalarsToIntermediate_injective
    (M : IntermediateField K L) :
    Function.Injective (galRestrictScalarsToIntermediate M) :=
  AlgEquiv.restrictScalars_injective K

/-- The range of restriction of scalars is precisely the subgroup fixing the
intermediate field. -/
theorem galRestrictScalarsToIntermediate_range
    (M : IntermediateField K L) :
    (galRestrictScalarsToIntermediate M).range = M.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    simpa using τ.commutes ⟨z, hz⟩
  · intro hσ
    let τ : Gal(L/M) := IntermediateField.fixingSubgroupEquiv M ⟨σ, hσ⟩
    refine ⟨τ, ?_⟩
    ext z
    rfl

/-- The lower ramification group for `L/M`, using the same normalized top
valuation as for `L/K`.  This is the real lower-ramification definition with only the automorphism
group changed. -/
def lowerRamificationGroupOverIntermediate
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (M : IntermediateField K L) (s : ℝ) : Subgroup Gal(L/M) :=
  (lowerRamificationGroup
    (base := base) (target := target) huniq s).comap
      (galRestrictScalarsToIntermediate M)

/-- States the theorem `mem_lowerRamificationGroupOverIntermediate_iff`. -/
@[simp] theorem mem_lowerRamificationGroupOverIntermediate_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (M : IntermediateField K L) (s : ℝ) (σ : Gal(L/M)) :
    σ ∈ lowerRamificationGroupOverIntermediate
        (base := base) (target := target) huniq M s ↔
      ∀ a : target.valuationSubring,
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq
            (galRestrictScalarsToIntermediate M σ) a - a ∈
          realRamificationIdeal target s :=
  Iff.rfl

/-- The lower-ramification base-change law: changing only the base field
intersects the lower ramification group with `Gal(L/M)`.  The left side is
transported into `Gal(L/K)` by restriction of scalars, so the statement is a
literal subgroup equality. -/
theorem lowerRamificationGroupOverIntermediate_map_eq_inf
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (M : IntermediateField K L) (s : ℝ) :
    Subgroup.map (galRestrictScalarsToIntermediate M)
        (lowerRamificationGroupOverIntermediate
          (base := base) (target := target) huniq M s) =
      lowerRamificationGroup
          (base := base) (target := target) huniq s ⊓ M.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    have hrange :
        galRestrictScalarsToIntermediate M τ ∈
          (galRestrictScalarsToIntermediate M).range :=
      ⟨τ, rfl⟩
    rw [galRestrictScalarsToIntermediate_range] at hrange
    exact ⟨hτ, hrange⟩
  · intro hσ
    have hrange : σ ∈ (galRestrictScalarsToIntermediate M).range := by
      rw [galRestrictScalarsToIntermediate_range]
      exact hσ.2
    rcases hrange with ⟨τ, rfl⟩
    exact ⟨τ, hσ.1, rfl⟩

end Higher
end RamificationTheory.HilbertRamification
