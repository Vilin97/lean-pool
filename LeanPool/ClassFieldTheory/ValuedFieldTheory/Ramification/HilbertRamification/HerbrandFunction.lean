/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.Herbrand.Function
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups
/-!
# Herbrand functions for a general discretely valued field

This file attaches the group-theoretic Herbrand functions directly to the
real lower ramification groups of `RealLowerGroups`.  The only valued-field
input is the stated unique-extension hypothesis that the chosen valuation on the top
field is the unique extension of the base valuation.  In particular, none of
the definitions or elementary inverse-function facts below assumes that either
field is complete.
-/

@[expose] public section

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction_inverseHerbrandFunction →
    herbrandFunction_inverseHerbrandFunction

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  herbrandFunction_strictMono →
    herbrandFunction_strictMono

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  inverseHerbrandFunction →
    inverseHerbrandFunction

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  inverseHerbrandFunction_herbrandFunction →
    inverseHerbrandFunction_herbrandFunction

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  inverseHerbrandFunction_mem_Ici_neg_one_iff →
    inverseHerbrandFunction_mem_Ici_neg_one_iff

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration renaming
  inverseHerbrandFunction_strictMono →
    inverseHerbrandFunction_strictMono


noncomputable
section

universe u v w x

namespace RamificationTheory.HilbertRamification
open ValuationTheory.DiscreteValuationField
namespace Higher


variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- The integral levels of the real lower-ramification groups, packaged as a
`AntitoneNormalSubgroupFiltration`.  This is the general-DVF replacement for the
complete-only `toLowerRamificationFiltration`. -/
def lowerRamificationFiltrationOfUniqueExtension
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w,
      x, x}
      base target) :
    RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration Gal(L/K) where
  lower n := lowerRamificationGroup
    (base := base) (target := target) huniq (n : ℝ)
  lower_normal n := lowerRamificationGroup_normal
    (base := base) (target := target) huniq (n : ℝ)
  antitone := by
    intro m n hmn
    apply lowerRamificationGroup_antitone
      (base := base) (target := target) huniq
    exact_mod_cast hmn

/-- States the theorem `lowerRamificationFiltrationOfUniqueExtension_lower`. -/
@[simp] theorem lowerRamificationFiltrationOfUniqueExtension_lower
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w,
      x, x}
      base target)
    (n : ℕ) :
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq).lower n =
      lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ) :=
  rfl

variable [FiniteDimensional K L]

/-- The finite Galois group is equipped with an enumeration for ramification-group sums. -/
noncomputable local instance generalDVFGalFintype : Fintype Gal(L/K) :=
  Fintype.ofFinite Gal(L/K)

/-- The Herbrand-function sum formula, defined under the stated unique-extension and
separable-residue assumptions:
the Herbrand function attached to the actual lower groups. -/
noncomputable def herbrandFunctionOfUniqueExtension
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w,
      x, x}
      base target) (s : ℝ) : ℝ :=
  RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq) s

/-- The inverse Herbrand function in the general-DVF setting. -/
noncomputable def inverseHerbrandFunctionOfUniqueExtension
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w,
      x, x}
      base target) (t : ℝ) : ℝ :=
  inverseHerbrandFunction
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq) t

omit [FiniteDimensional K L] in
/-- States the theorem `herbrandFunctionOfUniqueExtension_apply`. -/
@[simp] theorem herbrandFunctionOfUniqueExtension_apply
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w,
      x, x}
      base target) (s : ℝ) :
    herbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq s =
      RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction
        (lowerRamificationFiltrationOfUniqueExtension
          (base := base) (target := target) huniq) s :=
  rfl

omit [FiniteDimensional K L] in
/-- States the theorem `inverseHerbrandFunctionOfUniqueExtension_apply`. -/
@[simp] theorem inverseHerbrandFunctionOfUniqueExtension_apply
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w,
      x, x}
      base target) (t : ℝ) :
    inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq t =
      inverseHerbrandFunction
        (lowerRamificationFiltrationOfUniqueExtension
          (base := base) (target := target) huniq) t :=
  rfl

/-- States the theorem `herbrandFunctionOfUniqueExtension_psi`. -/
theorem herbrandFunctionOfUniqueExtension_psi
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w,
      x, x}
      base target) (t : ℝ) :
    herbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq
        (inverseHerbrandFunctionOfUniqueExtension
          (base := base) (target := target) huniq t) = t :=
  herbrandFunction_inverseHerbrandFunction
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq) t

/-- States the theorem `inverseHerbrandFunctionOfUniqueExtension_eta`. -/
theorem inverseHerbrandFunctionOfUniqueExtension_eta
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w,
      x, x}
      base target) (s : ℝ) :
    inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq
        (herbrandFunctionOfUniqueExtension
          (base := base) (target := target) huniq s) = s :=
  inverseHerbrandFunction_herbrandFunction
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq) s

/-- States the theorem `herbrandFunctionOfUniqueExtension_strictMono`. -/
theorem herbrandFunctionOfUniqueExtension_strictMono
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w,
      x, x}
      base target) :
    StrictMono (herbrandFunctionOfUniqueExtension
      (base := base) (target := target) huniq) :=
  herbrandFunction_strictMono
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq)

/-- States the theorem `inverseHerbrandFunctionOfUniqueExtension_strictMono`. -/
theorem inverseHerbrandFunctionOfUniqueExtension_strictMono
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w,
      x, x}
      base target) :
    StrictMono (inverseHerbrandFunctionOfUniqueExtension
      (base := base) (target := target) huniq) :=
  inverseHerbrandFunction_strictMono
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq)

/-- The upper ramification group defined through the inverse Herbrand function
under the noncomplete standing assumptions: `G^t = G_{psi(t)}`. -/
def upperRamificationGroupOfUniqueExtension
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w,
      x, x}
      base target) (t : ℝ) : Subgroup Gal(L/K) :=
  lowerRamificationGroup
    (base := base) (target := target) huniq
    (inverseHerbrandFunctionOfUniqueExtension
      (base := base) (target := target) huniq t)

/-- States the theorem `upperRamificationGroupOfUniqueExtension_herbrandFunction`. -/
theorem upperRamificationGroupOfUniqueExtension_herbrandFunction
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w,
      x, x}
      base target) (s : ℝ) :
    upperRamificationGroupOfUniqueExtension
        (base := base) (target := target) huniq
        (herbrandFunctionOfUniqueExtension
          (base := base) (target := target) huniq s) =
      lowerRamificationGroup
        (base := base) (target := target) huniq s := by
  exact congrArg
    (lowerRamificationGroup (base := base) (target := target) huniq)
    (inverseHerbrandFunctionOfUniqueExtension_eta
      (base := base) (target := target) huniq s)

/-- States the theorem `inverseHerbrandFunctionOfUniqueExtension_ge_neg_one_iff`. -/
theorem inverseHerbrandFunctionOfUniqueExtension_ge_neg_one_iff
    (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w,
      x, x}
      base target) {t : ℝ} :
    -1 ≤ inverseHerbrandFunctionOfUniqueExtension
        (base := base) (target := target) huniq t ↔ -1 ≤ t :=
  inverseHerbrandFunction_mem_Ici_neg_one_iff
    (lowerRamificationFiltrationOfUniqueExtension
      (base := base) (target := target) huniq)

end Higher
end RamificationTheory.HilbertRamification
