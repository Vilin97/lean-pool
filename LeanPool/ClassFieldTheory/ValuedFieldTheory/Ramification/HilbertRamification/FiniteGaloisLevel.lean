/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.Profinite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction
/-!
# Chosen integral-closure ramification filtrations at finite Galois levels

For a complete discretely valued field `K` and a finite Galois intermediate
field `E` of an algebraic closure, an existence theorem for the integral
closure of the valuation ring of `K` supplies complete-DVF structures on
`E`.  This file makes one noncomputable choice of such data.  Completeness
then gives uniqueness of the extended valuation, so real lower groups and
Herbrand upper groups can be formed without asking a caller to provide a
filtration. Choice independence is proved in the companion module.
-/

@[expose] public section

noncomputable
section

universe u v y

namespace RamificationTheory.HilbertRamification.FiniteGaloisLevel

open ValuationTheory
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} [Field K]

private theorem chosenIntegralClosureData_exists
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    ∃ target : CompleteDVF.{u, 0} E,
      ∃ hExt : base.valuation.HasExtension target.valuation,
        letI : base.valuation.HasExtension target.valuation := hExt
        IsIntegralClosure target.valuationSubring
          base.valuationSubring E ∧
          degree base.toDVF target.toDVF =
            ramificationIndex base.toDVF target.toDVF *
              residueDegree base.toDVF target.toDVF :=
  exists_integralClosure_standard_fundamental_identity
    (K := K) (L := E) base

/-- A complete-DVF structure on a finite Galois level, chosen from the
integral-closure existence theorem. -/
noncomputable def chosenIntegralClosureTarget
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    CompleteDVF.{u, 0} E :=
  Classical.choose (show ∃ target : CompleteDVF.{u, 0} E,
      ∃ hExt : base.valuation.HasExtension target.valuation,
        letI : base.valuation.HasExtension target.valuation := hExt
        IsIntegralClosure target.valuationSubring
          base.valuationSubring E ∧
          degree base.toDVF target.toDVF =
            ramificationIndex base.toDVF target.toDVF *
              residueDegree base.toDVF target.toDVF from by
    exact chosenIntegralClosureData_exists base E)

/-- The valuation on `chosenIntegralClosureTarget` extends the valuation on the base
complete DVF. -/
theorem chosenIntegralClosureTargetHasExtension
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    base.valuation.HasExtension (chosenIntegralClosureTarget base E).valuation :=
  Classical.choose (Classical.choose_spec (chosenIntegralClosureData_exists base E))

/-- Provides the instance `instChosenIntegralClosureTargetHasExtension`. -/
noncomputable instance instChosenIntegralClosureTargetHasExtension
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    base.valuation.HasExtension (chosenIntegralClosureTarget base E).valuation :=
  chosenIntegralClosureTargetHasExtension base E

/-- The valuation ring of the chosen finite-level target is the integral
closure of the base valuation ring. -/
theorem chosenIntegralClosureTarget_isIntegralClosure
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    IsIntegralClosure (chosenIntegralClosureTarget base E).valuationSubring
      base.valuationSubring E :=
  (Classical.choose_spec
    (Classical.choose_spec (chosenIntegralClosureData_exists base E))).1

/-- The chosen target satisfies the fundamental equality; no auxiliary
extension marker is selected. -/
theorem chosenIntegralClosureTarget_isDefectless
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    IsDefectless base.toDVF (chosenIntegralClosureTarget base E).toDVF :=
  (Classical.choose_spec
    (Classical.choose_spec (chosenIntegralClosureData_exists base E))).2

/-- Uniqueness of the extended valuation at a finite Galois level, in the
complete-DVF formulation. -/
theorem chosenIntegralClosureTarget_hasUniqueValuationExtension
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    ValuedExtension.HasUniqueValuationExtension.{u, v, u, 0, y}
      (base := base) (target := chosenIntegralClosureTarget base E) :=
  hasUniqueValuationExtension_of_finite_separable
    base (chosenIntegralClosureTarget base E)

/-- Uniqueness after forgetting completeness, in the precise universe needed
by the real lower ramification groups. -/
theorem chosenIntegralClosureTarget_hasUniqueDVFValuationExtension
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, u, 0, y}
      base.toDVF (chosenIntegralClosureTarget base E).toDVF :=
  chosenIntegralClosureTarget_hasUniqueValuationExtension base E

/-- The finite-level lower ramification filtration attached to the chosen
integral-closure valuation. -/
noncomputable def chosenLowerRamificationFiltration
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration
      Gal(E/K) :=
  Higher.lowerRamificationFiltrationOfUniqueExtension
    (base := base.toDVF) (target := (chosenIntegralClosureTarget base E).toDVF)
    (chosenIntegralClosureTarget_hasUniqueDVFValuationExtension base E)

/-- The finite-level real upper ramification filtration attached to the chosen
integral-closure valuation. -/
noncomputable def chosenUpperRamificationFiltration
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    ℝ → Subgroup Gal(E/K) := fun t =>
  Higher.upperRamificationGroupOfUniqueExtension
    (base := base.toDVF) (target := (chosenIntegralClosureTarget base E).toDVF)
    (chosenIntegralClosureTarget_hasUniqueDVFValuationExtension base E) t

/-- The chosen upper ramification group at a real index. -/
noncomputable abbrev chosenUpperRamificationGroup
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (t : ℝ) : Subgroup Gal(E/K) :=
  chosenUpperRamificationFiltration base E t

/-- States the theorem `chosenUpperRamificationFiltration_apply`. -/
@[simp]
theorem chosenUpperRamificationFiltration_apply
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (t : ℝ) :
    chosenUpperRamificationFiltration base E t =
      Higher.upperRamificationGroupOfUniqueExtension
        (base := base.toDVF) (target := (chosenIntegralClosureTarget base E).toDVF)
        (chosenIntegralClosureTarget_hasUniqueDVFValuationExtension base E) t :=
  rfl

/-- States the theorem `chosenLowerRamificationGroup_normal`. -/
theorem chosenLowerRamificationGroup_normal
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (n : ℕ) :
    ((chosenLowerRamificationFiltration base E).lower n).Normal :=
  (chosenLowerRamificationFiltration base E).lower_normal n

/-- Every chosen finite-level integral lower ramification group is closed. -/
theorem chosenLowerRamificationGroup_isClosed
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (n : ℕ) :
    IsClosed
      ((chosenLowerRamificationFiltration base E).lower n : Set Gal(E/K)) :=
  ((chosenLowerRamificationFiltration base E).lower n : Set Gal(E/K)).toFinite.isClosed

/-- States the theorem `chosenUpperRamificationGroup_normal`. -/
theorem chosenUpperRamificationGroup_normal
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (t : ℝ) :
    (chosenUpperRamificationGroup base E t).Normal := by
  exact Higher.lowerRamificationGroup_normal
    (base := base.toDVF) (target := (chosenIntegralClosureTarget base E).toDVF)
    (chosenIntegralClosureTarget_hasUniqueDVFValuationExtension base E)
    (Higher.inverseHerbrandFunctionOfUniqueExtension
      (base := base.toDVF) (target := (chosenIntegralClosureTarget base E).toDVF)
      (chosenIntegralClosureTarget_hasUniqueDVFValuationExtension base E) t)

/-- Every chosen finite-level upper ramification group is closed. -/
theorem chosenUpperRamificationGroup_isClosed
    (base : CompleteDVF.{u, v} K)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (t : ℝ) :
    IsClosed (chosenUpperRamificationGroup base E t : Set Gal(E/K)) :=
  (chosenUpperRamificationGroup base E t : Set Gal(E/K)).toFinite.isClosed

end RamificationTheory.HilbertRamification.FiniteGaloisLevel
