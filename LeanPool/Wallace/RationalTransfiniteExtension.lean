/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.CoefficientTransfiniteExtension
import LeanPool.Wallace.RationalTriangularPreprocess
import Mathlib.Algebra.Category.Grp.Injective

/-!
# Transfinite extension for the rational direct sum

This file supplies the coefficient-specific input to the shared transfinite recursion. Baer's
extension theorem extends the integer character with prescribed value at one to a character on
each rational coordinate.
-/

open Filter Set Topology

namespace Wallace
namespace RationalTransfiniteExtension

noncomputable section

universe u

open CoefficientTransfiniteExtension

/-- The integer character with prescribed value at one. -/
private def integerCircleHom (t : UnitAddCircle) : ℤ →+ UnitAddCircle :=
  (zmultiplesHom UnitAddCircle) t

private theorem intCastAddHom_rational_injective :
    Function.Injective (Int.castAddHom ℚ) := by
  intro m n h
  exact Rat.intCast_injective h

/-- An additive homomorphism on `ℚ` extending the integer character with value `t` at one. -/
private def extendRationalCoordinate (t : UnitAddCircle) : ℚ →+ UnitAddCircle :=
  Classical.choose <|
    (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
      (Int.castAddHom ℚ) intCastAddHom_rational_injective (integerCircleHom t)

private theorem extendRationalCoordinate_comp_intCast (t : UnitAddCircle) :
    (extendRationalCoordinate t).comp (Int.castAddHom ℚ) = integerCircleHom t :=
  Classical.choose_spec <|
    (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
      (Int.castAddHom ℚ) intCastAddHom_rational_injective (integerCircleHom t)

@[simp]
private theorem extendRationalCoordinate_one (t : UnitAddCircle) :
    extendRationalCoordinate t 1 = t := by
  have h := DFunLike.congr_fun (extendRationalCoordinate_comp_intCast t) 1
  simpa [integerCircleHom] using h

/-- Baer's extension supplies the coordinate extension used by the generic recursion. -/
private def rationalCoordinateExtension : CoordinateExtension ℚ where
  ofValue := extendRationalCoordinate
  ofValue_one := extendRationalCoordinate_one

/-- Triangular data for rational-valued prepared sequences. -/
abbrev Data (I : Type u) [LT I] := CoefficientTransfiniteExtension.Data ℚ I

/-- Closure under the rational prepared supports associated to local code coordinates. -/
abbrev ClosedUnderPreparedSupports {I : Type u} [LT I]
    (E : Data I) (D : Set I) : Prop :=
  CoefficientTransfiniteExtension.ClosedUnderPreparedSupports E D

/-- The local rational character realizes every limit whose code coordinate is local. -/
abbrev LocallyAdmissible {I : Type u} [LT I] (E : Data I) (D : Set I)
    (character : (D →₀ ℚ) →+ UnitAddCircle) : Prop :=
  CoefficientTransfiniteExtension.LocallyAdmissible E D character

/-- The global rational character produced by the shared transfinite recursion. -/
abbrev globalCharacter {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (character : (D →₀ ℚ) →+ UnitAddCircle) :
    (I →₀ ℚ) →+ UnitAddCircle :=
  CoefficientTransfiniteExtension.globalCharacter rationalCoordinateExtension E D character

theorem globalCharacter_eq_local_restriction {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (character : (D →₀ ℚ) →+ UnitAddCircle)
    (x : I →₀ ℚ) (hx : ∀ i ∈ x.support, i ∈ D) :
    globalCharacter E D character x = character (Finsupp.subtypeDomain D x) :=
  CoefficientTransfiniteExtension.globalCharacter_eq_local_restriction
    rationalCoordinateExtension E D character x hx

theorem globalCharacter_admissible {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (character : (D →₀ ℚ) →+ UnitAddCircle)
    (hclosed : ClosedUnderPreparedSupports E D)
    (hlocal : LocallyAdmissible E D character) :
    ∀ c : E.Code,
      Tendsto (fun n ↦ globalCharacter E D character (E.prepared c n)) (E.p c)
        (nhds (globalCharacter E D character (Finsupp.single (E.codeIndex c) 1))) :=
  CoefficientTransfiniteExtension.globalCharacter_admissible
    rationalCoordinateExtension E D character hclosed hlocal

/-- Rational transfinite-extension data over the canonical continuum index. -/
abbrev ContinuumData := Data RationalTriangularPreprocess.ContinuumIndex

end
end RationalTransfiniteExtension
end Wallace
