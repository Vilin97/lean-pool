/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.HerbrandFunctionAtLowerIndex
import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.IsLowerRamificationJump
import LeanPool.ClassFieldTheory.ClassFieldTheory.HasseArf
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Extension
/-!
# Hasse--Arf theorem

Let `L/K` be a finite abelian extension of nonarchimedean local fields, with
the valuation of `L` extending that of `K`.  If `n` is a jump in the lower
ramification filtration, the corresponding upper index is the Herbrand
value `φ(n)`.  Hasse--Arf says that this upper index is an integer.

This is the standard equivalent integral-lower-jump formulation of the
theorem.  It avoids postulating an opaque predicate for upper jumps: the
lower groups and the Herbrand value are defined explicitly in
`ClassFieldTheory.Definitions.HasseArf` modules from Mathlib's valuation-subring
data.
-/

noncomputable section

namespace ClassFieldTheory

/-- **Hasse--Arf.** For a finite abelian extension of nonarchimedean local
fields, the Herbrand image of every lower ramification jump is integral.

Here the lower filtration is attached to the canonical valuation subring of
`L`.  The `Valuation.HasExtension` assumption records compatibility of the
canonical valuations on `K` and `L`; it is data about the extension, not a
ramification or integrality conclusion. -/
theorem hasseArf
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    {n : ℕ}
    (hn : IsLowerRamificationJump K
      (ValuativeRel.valuation L).valuationSubring n) :
    ∃ z : ℤ,
      herbrandFunctionAtLowerIndex K
        (ValuativeRel.valuation L).valuationSubring n = (z : ℚ) :=
  letI : Small.{0} K := LocalFieldTheory.nonarchimedeanLocalField_small K
  letI : Small.{0} L := LocalFieldTheory.nonarchimedeanLocalField_small L
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) := HasseArf.shrinkAlgebra K L
  letI : FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) :=
    HasseArf.shrink_finiteDimensional K L
  letI : IsAbelianGalois (Shrink.{0} K) (Shrink.{0} L) :=
    HasseArf.shrink_isAbelianGalois K L
  letI : ValuativeRel (Shrink.{0} K) := LocalFieldTheory.shrinkLocalFieldValuativeRel K
  letI : ValuativeRel (Shrink.{0} L) := LocalFieldTheory.shrinkLocalFieldValuativeRel L
  letI : IsNonarchimedeanLocalField (Shrink.{0} K) :=
    LocalFieldTheory.shrinkLocalField_isNonarchimedeanLocalField K
  letI : IsNonarchimedeanLocalField (Shrink.{0} L) :=
    LocalFieldTheory.shrinkLocalField_isNonarchimedeanLocalField L
  letI : Valuation.HasExtension
      (LocalFieldTheory.shrinkLocalFieldValuation K)
      (LocalFieldTheory.shrinkLocalFieldValuation L) := by
    have hcomm (a : Shrink.{0} K) :
        Shrink.ringEquiv L (algebraMap (Shrink.{0} K) (Shrink.{0} L) a) =
          algebraMap K L (Shrink.ringEquiv K a) := by
      have h := congrArg
        (fun F : K →+* Shrink.{0} L => F (Shrink.ringEquiv K a))
        (HasseArf.shrinkAlgebra_commutes K L)
      simpa using congrArg (Shrink.ringEquiv L) h
    exact LocalFieldTheory.hasExtension_comap_ringEquivs
      (Shrink.ringEquiv K) (Shrink.ringEquiv L) hcomm
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)
  letI : Valuation.HasExtension
      (ValuativeRel.valuation (Shrink.{0} K))
      (ValuativeRel.valuation (Shrink.{0} L)) := by
    have hK :
        (LocalFieldTheory.shrinkLocalFieldValuation K).IsEquiv
          (ValuativeRel.valuation (Shrink.{0} K)) :=
      letI : (LocalFieldTheory.shrinkLocalFieldValuation K).Compatible :=
        Valuation.Compatible.ofValuation _
      ValuativeRel.isEquiv _ _
    have hL :
        (LocalFieldTheory.shrinkLocalFieldValuation L).IsEquiv
          (ValuativeRel.valuation (Shrink.{0} L)) :=
      letI : (LocalFieldTheory.shrinkLocalFieldValuation L).Compatible :=
        Valuation.Compatible.ofValuation _
      ValuativeRel.isEquiv _ _
    exact LocalFieldTheory.hasExtension_of_isEquiv
      (LocalFieldTheory.shrinkLocalFieldValuation K)
      (ValuativeRel.valuation (Shrink.{0} K))
      (LocalFieldTheory.shrinkLocalFieldValuation L)
      (ValuativeRel.valuation (Shrink.{0} L)) hK hL
  by
    have hn' : IsLowerRamificationJump (Shrink.{0} K)
        (ValuativeRel.valuation (Shrink.{0} L)).valuationSubring n :=
      (HasseArf.shrink_isLowerRamificationJump_iff K L n).mpr hn
    obtain ⟨z, hz⟩ := HasseArf.hasseArf_canonical
      (Shrink.{0} K) (Shrink.{0} L) hn'
    refine ⟨z, ?_⟩
    rw [← HasseArf.shrink_herbrandFunctionAtLowerIndex_eq K L n]
    exact hz

end ClassFieldTheory
