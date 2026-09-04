/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.CoefficientTransfiniteExtension
import LeanPool.Wallace.TriangularPreprocess

/-!
# Transfinite extension of an integer-valued local character

This file specializes the coefficient-parametric Wallace recursion to the free Abelian group.
An integer coordinate character is uniquely determined by its value at one.
-/

open Filter Set Topology

namespace Wallace
namespace TransfiniteExtension

noncomputable section

universe u

open CoefficientTransfiniteExtension

/-- Extend a prescribed circle value to the corresponding integer character. -/
private def integerCoordinateExtension : CoordinateExtension ℤ where
  ofValue := fun t ↦ (zmultiplesHom UnitAddCircle) t
  ofValue_one := by
    intro t
    simp

/-- Triangular data for integer-valued prepared sequences. -/
abbrev Data (I : Type u) [LT I] := CoefficientTransfiniteExtension.Data ℤ I

/-- Closure under the integer prepared supports associated to local code coordinates. -/
abbrev ClosedUnderPreparedSupports {I : Type u} [LT I]
    (E : Data I) (D : Set I) : Prop :=
  CoefficientTransfiniteExtension.ClosedUnderPreparedSupports E D

/-- The local integer character realizes every limit whose code coordinate is local. -/
abbrev LocallyAdmissible {I : Type u} [LT I] (E : Data I) (D : Set I)
    (character : (D →₀ ℤ) →+ UnitAddCircle) : Prop :=
  CoefficientTransfiniteExtension.LocallyAdmissible E D character

/-- The global integer character produced by the shared transfinite recursion. -/
abbrev globalCharacter {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (character : (D →₀ ℤ) →+ UnitAddCircle) :
    (I →₀ ℤ) →+ UnitAddCircle :=
  CoefficientTransfiniteExtension.globalCharacter integerCoordinateExtension E D character

theorem globalCharacter_eq_local_restriction {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (character : (D →₀ ℤ) →+ UnitAddCircle)
    (x : I →₀ ℤ) (hx : ∀ i ∈ x.support, i ∈ D) :
    globalCharacter E D character x = character (Finsupp.subtypeDomain D x) :=
  CoefficientTransfiniteExtension.globalCharacter_eq_local_restriction
    integerCoordinateExtension E D character x hx

theorem globalCharacter_admissible {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (character : (D →₀ ℤ) →+ UnitAddCircle)
    (hclosed : ClosedUnderPreparedSupports E D)
    (hlocal : LocallyAdmissible E D character) :
    ∀ c : E.Code,
      Tendsto (fun n ↦ globalCharacter E D character (E.prepared c n)) (E.p c)
        (nhds (globalCharacter E D character (Finsupp.single (E.codeIndex c) 1))) :=
  CoefficientTransfiniteExtension.globalCharacter_admissible
    integerCoordinateExtension E D character hclosed hlocal

/-- Integer transfinite-extension data over the canonical continuum index. -/
abbrev ContinuumData := Data TriangularPreprocess.ContinuumIndex

end
end TransfiniteExtension
end Wallace
