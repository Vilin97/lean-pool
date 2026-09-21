/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Examples.OmnificFactorization
public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.ConwayRefinementConsequences
public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.OmnificFiniteDegree
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Primality.OrdinaryIntegers
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Reduced
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.RefinementConjecture
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.DenominatorIdeal

import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Degree
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.DegreeTransfer
import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Conway cuts and the normal-form presentation of omnific integers

Conway normal forms give a ring equivalence between the cut-defined omnific integers and the
generalised-power-series presentation used by the standalone factorisation statements.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass
open scoped HahnSeries NatOrdinal

universe u

namespace ConwayRefinement.Standalone.Oz

/-- The standalone cut predicate agrees with membership in the omnific-integer subring. -/
theorem isConwayOmnificInteger_iff_mem {x : Surreal.{u}} :
    IsConwayOmnificInteger x ↔ x ∈ Surreal.omnificIntegers := by
  rw [isConwayOmnificInteger_iff, Surreal.mem_omnificIntegers, Surreal.isOmnificInteger_iff,
    Surreal.omnificIntegerCut_eq]

/-- The cut-defined and subring formulations of Conway's refinement conjecture are equivalent. -/
@[blueprint "thm:conway-cut-subring-equivalence"
  (phase := "Surreal numbers and omnific integers")
  (title := "Equivalence of the cut and subring formulations of Conway's refinement conjecture")
  (statement := /--
    Conway's refinement conjecture for cut-defined omnific integers is
    equivalent to the refinement property of the omnific-integer subring of
    the surreal numbers.
  -/)
  (proof := /--
    The cut predicate for omnific integers is equivalent to membership in the
    omnific-integer subring. Substitute this equivalence into the two
    four-factor statements; their equations and quantifiers are identical.
  -/)]
theorem conwayConjecture_iff_native : ConwayConjecture.{u} ↔ ConwayRefinementConjecture.{u} := by
  rw [conwayConjecture_iff, conwayRefinementConjecture_def, ← hasFourFactorRefinement_def]
  simpa only [isConwayOmnificInteger_iff_mem] using
    (Subring.hasFourFactorRefinement_iff Surreal.omnificIntegers).symm

/-- Conway's refinement conjecture is equivalent to primality of every omnific integer. -/
theorem conwayConjecture_iff_forall_isPrimal :
    ConwayConjecture.{u} ↔ ∀ b : Surreal.OmnificInteger.{u}, IsPrimal b := by
  rw [conwayConjecture_iff_native, conwayRefinementConjecture_def,
    ← hasFourFactorRefinement_def, hasFourFactorRefinement_iff_forall_isPrimal]

/-- Conway's refinement conjecture is equivalent to the pre-Schreier property of the omnific
integers. -/
theorem conwayConjecture_iff_decompositionMonoid :
    ConwayConjecture.{u} ↔ DecompositionMonoid Surreal.OmnificInteger.{u} := by
  rw [conwayConjecture_iff_forall_isPrimal, decompositionMonoid_iff]

/-- Conway's refinement conjecture is equivalent to the common-divisor criterion for denominator
ideals. -/
theorem conwayConjecture_iff_forall_denominatorIdeal_exists_commonDivisor :
    ConwayConjecture.{u} ↔
      ∀ (ξ : Surreal.{u})
        (x y : Subring.denominatorIdeal Surreal.omnificIntegers ξ),
        ∃ s : Subring.denominatorIdeal Surreal.omnificIntegers ξ,
          (s : Surreal.OmnificInteger) ∣ (x : Surreal.OmnificInteger) ∧
            (s : Surreal.OmnificInteger) ∣ (y : Surreal.OmnificInteger) := by
  rw [conwayConjecture_iff_native, conwayRefinementConjecture_def,
    ← hasFourFactorRefinement_def,
    Subring.hasFourFactorRefinement_iff_forall_denominatorIdeal_exists_common_divisor]

/-- The Conway normal-form equivalence identifies the two definitions of omnific integers. -/
theorem normalFormIdentifiesOmnificIntegers :
    NormalFormIdentifiesOmnificIntegers.{u} := by
  refine ⟨Surreal.toHahnSeriesRingEquiv, ?_⟩
  intro x
  rw [Surreal.toHahnSeriesRingEquiv_apply, isConwayOmnificInteger_iff,
    mem_omnificIntegers, Surreal.support_toHahnSeries,
    congrFun (Surreal.coeff_toHahnSeries x) 0,
    ← Surreal.isOmnificInteger_iff_normalForm, Surreal.isOmnificInteger_iff,
    Surreal.omnificIntegerCut_eq]

/-- The normal-form and cut-defined omnific-integer rings are isomorphic. -/
def normalFormRingEquiv : OmnificInteger.{u} ≃+* Surreal.OmnificInteger.{u} :=
  Surreal.toHahnSeriesRingEquiv.symm.restrict
    omnificIntegers Surreal.omnificIntegers fun x ↦ by
      rw [mem_omnificIntegers, Surreal.mem_omnificIntegers,
        Surreal.isOmnificInteger_iff_normalForm]
      simp only [Surreal.toHahnSeriesRingEquiv_symm_apply,
        SurrealHahnSeries.support_toSurreal, SurrealHahnSeries.coeff_toSurreal]

@[simp]
theorem coe_normalFormRingEquiv (x : OmnificInteger.{u}) :
    (normalFormRingEquiv x : Surreal.{u}) = x.1.toSurreal :=
  Surreal.toHahnSeriesRingEquiv_symm_apply x.1

theorem toHahnSeries_normalFormRingEquiv (x : OmnificInteger.{u}) :
    (normalFormRingEquiv x : Surreal.{u}).toHahnSeries = x.1 := by
  rw [coe_normalFormRingEquiv]
  exact SurrealHahnSeries.toHahnSeries_toSurreal x.1

theorem normalFormRingEquiv_not_isOrdinaryInteger
    (x : OmnificInteger.{u}) (hx : ¬ IsOrdinaryInteger x) :
    ¬ Surreal.OmnificInteger.IsOrdinaryInteger (normalFormRingEquiv x) := by
  intro hordinary
  apply hx
  rw [Surreal.OmnificInteger.isOrdinaryInteger_iff] at hordinary
  obtain ⟨z, hz⟩ := hordinary
  have htarget : normalFormRingEquiv x = (z : Surreal.OmnificInteger.{u}) :=
    Subtype.ext hz
  have hsource : x = (z : OmnificInteger.{u}) := by
    apply normalFormRingEquiv.injective
    simpa using htarget
  exact ⟨z, congrArg Subtype.val hsource⟩

theorem normalFormRingEquiv_isReduced
    (x : OmnificInteger.{u}) (hx : IsReduced x) :
    HahnSeries.Nonpositive.IsReduced
      (normalFormRingEquiv x).toSignedNonpositiveHahn := by
  obtain ⟨hx0, c, hclass⟩ := hx
  have hy0 : normalFormRingEquiv x ≠ 0 :=
    normalFormRingEquiv.map_eq_zero_iff.not.mpr hx0
  refine HahnSeries.Nonpositive.isReduced_of_support_inter_support_sub_one_subset
    ?_ c ?_
  · intro hzero
    apply hy0
    apply Subtype.ext
    apply Surreal.toSignedFullHahnSeries_injective
    have hraw := congrArg (fun q : HahnSeries.Nonpositive Surreal ℝ ↦
      (q : HahnSeries Surreal ℝ)) hzero
    rw [Surreal.OmnificInteger.coe_toSignedNonpositiveHahn] at hraw
    exact hraw.trans Surreal.toSignedFullHahnSeries_zero.symm
  · intro g hg
    have hgSource : g ∈
        (normalFormRingEquiv x).1.toSignedFullHahnSeries.support := by
      rw [← Surreal.OmnificInteger.coe_toSignedNonpositiveHahn]
      exact hg.1
    have hsub :
        ((((normalFormRingEquiv x).toSignedNonpositiveHahn - 1 :
          HahnSeries.Nonpositive Surreal ℝ)) : HahnSeries Surreal ℝ) =
            ((normalFormRingEquiv x).1 - 1).toSignedFullHahnSeries := by
      calc
        _ = ((normalFormRingEquiv x).toSignedNonpositiveHahn :
            HahnSeries Surreal ℝ) - 1 := rfl
        _ = (normalFormRingEquiv x).1.toSignedFullHahnSeries - 1 := by
          rw [Surreal.OmnificInteger.coe_toSignedNonpositiveHahn]
        _ = ((normalFormRingEquiv x).1 - 1).toSignedFullHahnSeries := by
          rw [Surreal.toSignedFullHahnSeries_sub]
          congr 1
          simpa using (Surreal.toSignedFullHahnSeries_realCast (1 : ℝ)).symm
    have hgSub : g ∈
        ((normalFormRingEquiv x).1 - 1).toSignedFullHahnSeries.support := by
      rw [← hsub]
      exact hg.2
    have huSource : -g ∈ x.1.support := by
      have hu : -g ∈ (normalFormRingEquiv x).1.support := by
        simpa using (Surreal.mem_support_toSignedFullHahnSeries.mp hgSource)
      rw [← toHahnSeries_normalFormRingEquiv x]
      simpa using hu
    have hnormalSub :
        ((normalFormRingEquiv x).1 - 1).toHahnSeries = x.1 - 1 := by
      rw [← Surreal.toHahnSeriesRingEquiv_apply, map_sub,
        Surreal.toHahnSeriesRingEquiv_apply, toHahnSeries_normalFormRingEquiv,
        map_one]
    have huSub : -g ∈ (x.1 - 1).support := by
      have hu : -g ∈ ((normalFormRingEquiv x).1 - 1).support := by
        simpa using (Surreal.mem_support_toSignedFullHahnSeries.mp hgSub)
      rw [← hnormalSub, Surreal.support_toHahnSeries]
      exact hu
    simpa using hclass ⟨huSource, huSub⟩

end ConwayRefinement.Standalone.Oz
