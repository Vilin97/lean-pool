/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Monogeneity
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal
/-!
# Ramification numbers for a general discretely valued field

This file gives the noncomplete version of the ramification number used in
ramification-number theory.  Under the stated unique-extension and
separable-residue hypotheses, the monogenic integral-generator theorem supplies
an integral generator.  We choose that generator internally, so downstream
statements do not carry a generator hypothesis.
-/

@[expose] public section

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher


variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- Elements whose displacement has a fixed maximal-ideal lower bound form a
base valuation-ring subalgebra. -/
def valuationSubringDisplacementSubalgebraOfUniqueExtension
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (n : ℕ) (sigma : Gal(L/K)) :
    Subalgebra base.valuationSubring target.valuationSubring where
  carrier :=
    {a | valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a ∈
        target.maximalIdeal ^ n}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change
      valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma (a + b) - (a + b) ∈
        target.maximalIdeal ^ n
    change valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a ∈
        target.maximalIdeal ^ n at ha
    change valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma b - b ∈
        target.maximalIdeal ^ n at hb
    have hrewrite :
        valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma (a + b) - (a + b) =
          (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma a - a) +
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma b - b) := by
      simp
      ring
    rw [hrewrite]
    exact Ideal.add_mem _ ha hb
  mul_mem' := by
    intro a b ha hb
    change
      valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma (a * b) - a * b ∈
        target.maximalIdeal ^ n
    change valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a ∈
        target.maximalIdeal ^ n at ha
    change valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma b - b ∈
        target.maximalIdeal ^ n at hb
    have hrewrite :
        valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma (a * b) - a * b =
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq sigma a *
              (valuationSubringAutOfUniqueExtension
                (base := base) (target := target) huniq sigma b - b) +
            (valuationSubringAutOfUniqueExtension
                (base := base) (target := target) huniq sigma a - a) * b := by
      simp
      ring
    rw [hrewrite]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ hb)
      (Ideal.mul_mem_right _ _ ha)
  algebraMap_mem' := by
    intro r
    change
      valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma
            (algebraMap base.valuationSubring target.valuationSubring r) -
          algebraMap base.valuationSubring target.valuationSubring r ∈
        target.maximalIdeal ^ n
    have hcomm :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma
            (algebraMap base.valuationSubring target.valuationSubring r) =
          algebraMap base.valuationSubring target.valuationSubring r := by
      apply Subtype.ext
      exact sigma.commutes (r : K)
    rw [hcomm, sub_self]
    exact Ideal.zero_mem _

/-- States the theorem `mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff`. -/
@[simp] theorem mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (n : ℕ) (sigma : Gal(L/K)) (a : target.valuationSubring) :
    a ∈ valuationSubringDisplacementSubalgebraOfUniqueExtension
        (base := base) (target := target) huniq n sigma ↔
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a ∈
        target.maximalIdeal ^ n :=
  Iff.rfl

/-- A displacement bound on a generator extends to every integral polynomial
expression in that generator. -/
theorem valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {a z : target.valuationSubring} {n : ℕ} {sigma : Gal(L/K)}
    (ha : valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a ∈
        target.maximalIdeal ^ n)
    (hz : z ∈ Algebra.adjoin base.valuationSubring
      ({a} : Set target.valuationSubring)) :
    valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma z - z ∈
      target.maximalIdeal ^ n := by
  have hle :
      Algebra.adjoin base.valuationSubring ({a} : Set target.valuationSubring) ≤
        valuationSubringDisplacementSubalgebraOfUniqueExtension
          (base := base) (target := target) huniq n sigma := by
    rw [Algebra.adjoin_le_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact ha
  exact hle hz

/-- Ramification number attached to an integral element, before choosing the
integral generator. -/
def ramificationNumberOfUniqueExtension
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (a : target.valuationSubring) (sigma : Gal(L/K)) : ℕ∞ :=
  IsDiscreteValuationRing.addVal target.valuationSubring
    (valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq sigma a - a)

/-- States the theorem `ramificationNumberOfUniqueExtension_one`. -/
@[simp] theorem ramificationNumberOfUniqueExtension_one
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (a : target.valuationSubring) :
    ramificationNumberOfUniqueExtension
      (base := base) (target := target) huniq a 1 = ⊤ := by
  simp [ramificationNumberOfUniqueExtension]

/-- States the theorem `natCast_le_ramificationNumberOfUniqueExtension_iff`. -/
theorem natCast_le_ramificationNumberOfUniqueExtension_iff
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (a : target.valuationSubring) (sigma : Gal(L/K)) (n : ℕ) :
    (n : ℕ∞) ≤ ramificationNumberOfUniqueExtension
        (base := base) (target := target) huniq a sigma ↔
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a ∈
        target.maximalIdeal ^ n := by
  exact (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge
    (valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq sigma a - a) n).symm

/-- The ramification number is independent of the monogenic generator. -/
theorem ramificationNumberOfUniqueExtension_eq_of_adjoin_eq_top
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {a b : target.valuationSubring}
    (ha : Algebra.adjoin base.valuationSubring
      ({a} : Set target.valuationSubring) = ⊤)
    (hb : Algebra.adjoin base.valuationSubring
      ({b} : Set target.valuationSubring) = ⊤)
    (sigma : Gal(L/K)) :
    ramificationNumberOfUniqueExtension
        (base := base) (target := target) huniq a sigma =
      ramificationNumberOfUniqueExtension
        (base := base) (target := target) huniq b sigma := by
  apply le_antisymm
  · rw [← ENat.forall_natCast_le_iff_le]
    intro n han
    rw [natCast_le_ramificationNumberOfUniqueExtension_iff] at han ⊢
    exact valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin
      (base := base) (target := target) huniq han (by rw [ha]; simp)
  · rw [← ENat.forall_natCast_le_iff_le]
    intro n hbn
    rw [natCast_le_ramificationNumberOfUniqueExtension_iff] at hbn ⊢
    exact valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin
      (base := base) (target := target) huniq hbn (by rw [hb]; simp)

variable [FiniteDimensional K L] [IsGalois K L]
variable [Algebra.IsSeparable base.residueField target.residueField]

/-- The integral generator supplied internally by the monogeneity theorem under
the standing hypotheses. -/
def chosenRamificationGeneratorOfUniqueExtension
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) : target.valuationSubring :=
  Classical.choose
    (exists_valuationSubring_adjoin_eq_top_of_uniqueExtension
      (base := base) (target := target) huniq)

/-- States the theorem `chosenRamificationGeneratorOfUniqueExtension_adjoin_eq_top`. -/
theorem chosenRamificationGeneratorOfUniqueExtension_adjoin_eq_top
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) :
    Algebra.adjoin base.valuationSubring
        ({chosenRamificationGeneratorOfUniqueExtension
            (base := base) (target := target) huniq} :
          Set target.valuationSubring) = ⊤ :=
  Classical.choose_spec
    (exists_valuationSubring_adjoin_eq_top_of_uniqueExtension
      (base := base) (target := target) huniq)

/-- The canonical ramification number.  Its generator is supplied
internally by the monogenic integral-generator theorem. -/
def intrinsicRamificationNumberOfUniqueExtension
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (sigma : Gal(L/K)) : ℕ∞ :=
  ramificationNumberOfUniqueExtension
    (base := base) (target := target) huniq
    (chosenRamificationGeneratorOfUniqueExtension
      (base := base) (target := target) huniq) sigma

/-- States the theorem `intrinsicRamificationNumberOfUniqueExtension_one`. -/
@[simp] theorem intrinsicRamificationNumberOfUniqueExtension_one
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) :
    intrinsicRamificationNumberOfUniqueExtension
      (base := base) (target := target) huniq 1 = ⊤ := by
  simp [intrinsicRamificationNumberOfUniqueExtension]

/-- The canonical ramification number recovers the integral lower groups. -/
theorem mem_lowerRamificationGroup_nat_iff_intrinsicRamificationNumberOfUniqueExtension_ge
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (n : ℕ) (sigma : Gal(L/K)) :
    sigma ∈ lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ) ↔
      ((n + 1 : ℕ) : ℕ∞) ≤
        intrinsicRamificationNumberOfUniqueExtension
          (base := base) (target := target) huniq sigma := by
  change sigma ∈ lowerRamificationGroup
      (base := base) (target := target) huniq (n : ℝ) ↔
    ((n + 1 : ℕ) : ℕ∞) ≤ ramificationNumberOfUniqueExtension
      (base := base) (target := target) huniq
      (chosenRamificationGeneratorOfUniqueExtension
        (base := base) (target := target) huniq) sigma
  rw [mem_lowerRamificationGroup_nat_iff,
    natCast_le_ramificationNumberOfUniqueExtension_iff]
  constructor
  · intro hsigma
    exact hsigma _
  · intro hgen z
    exact valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin
      (base := base) (target := target) huniq hgen (by
        rw [chosenRamificationGeneratorOfUniqueExtension_adjoin_eq_top
          (base := base) (target := target) huniq]
        simp)

end Higher
end RamificationTheory.HilbertRamification
