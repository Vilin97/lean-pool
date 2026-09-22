/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageCurve
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveSeparability

/-!
# A rational-function-field model for a plane curve

The first coordinate of an irreducible plane curve with nonzero second
partial derivative is separating and transcendental.  This file uses that
coordinate to put the function field over the standard field `K(X)`.  It
then transports finiteness, separability, and the exact extension degree from
the intrinsic first-coordinate subfield.

This is the model required by the exhaustive finite-plus-infinity divisor
formalization: its base is literally `RatFunc K`, and `X` specializes to the
first coordinate function.
-/

namespace BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K]

/-- The `RatFunc K`-algebra structure obtained by specializing `X` at the
first coordinate of the plane curve. -/
@[reducible] noncomputable def planeCurveFirstCoordinateRatFuncAlgebra
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)]
    (hx : Transcendental K (planeCurveFunction f 0)) :
    Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
  (ratFuncSpecialization (planeCurveFunction f 0) hx).toAlgebra

@[simp] theorem planeCurveFirstCoordinateRatFuncAlgebra_algebraMap_apply
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)]
    (hx : Transcendental K (planeCurveFunction f 0)) (z : RatFunc K) :
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    algebraMap (RatFunc K) (PlaneCurveFunctionField f) z =
      ratFuncSpecialization (planeCurveFunction f 0) hx z :=
  rfl

@[simp] theorem planeCurveFirstCoordinateRatFuncAlgebra_X
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)]
    (hx : Transcendental K (planeCurveFunction f 0)) :
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    algebraMap (RatFunc K) (PlaneCurveFunctionField f) RatFunc.X =
      planeCurveFunction f 0 := by
  let := planeCurveFirstCoordinateRatFuncAlgebra f hx
  change ratFuncSpecialization (planeCurveFunction f 0) hx RatFunc.X = _
  simp [ratFuncSpecialization, RatFunc.algEquivOfTranscendental_X]

private theorem planeCurve_firstCoordinate_changeBase_commutes
    {f : MvPolynomial (Fin 2) K} [IsDomain (PlaneCurveCoordinateRing f)]
    (hx : Transcendental K (planeCurveFunction f 0)) :
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    (algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (RatFunc.algEquivOfTranscendental
          (planeCurveFunction f 0) hx).symm.toRingEquiv.toRingHom =
      (RingEquiv.refl (PlaneCurveFunctionField f)).toRingHom.comp
        (algebraMap (FirstCoordinateSubfield f)
          (PlaneCurveFunctionField f)) := by
  let := planeCurveFirstCoordinateRatFuncAlgebra f hx
  ext z
  simp [ratFuncSpecialization]

/-- The plane-curve function field is finite over the standard rational
function field when `X` is specialized to the first coordinate. -/
theorem finiteDimensional_planeCurveFunctionField_over_ratFunc
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (FirstCoordinateSubfield f)
      (PlaneCurveFunctionField f) :=
    (finiteSeparable_over_firstCoordinate_of_irreducible
      hf hpartialSecond).1
  exact Module.Finite.of_equiv_equiv
    (RatFunc.algEquivOfTranscendental
      (planeCurveFunction f 0) hx).symm.toRingEquiv
    (RingEquiv.refl (PlaneCurveFunctionField f))
    (planeCurve_firstCoordinate_changeBase_commutes hx)

/-- The same change of base transports separability. -/
theorem separable_planeCurveFunctionField_over_ratFunc
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra.IsSeparable (FirstCoordinateSubfield f)
      (PlaneCurveFunctionField f) :=
    (finiteSeparable_over_firstCoordinate_of_irreducible
      hf hpartialSecond).2
  exact Algebra.IsSeparable.of_equiv_equiv
    (RatFunc.algEquivOfTranscendental
      (planeCurveFunction f 0) hx).symm.toRingEquiv
    (RingEquiv.refl (PlaneCurveFunctionField f))
    (planeCurve_firstCoordinate_changeBase_commutes hx)

/-- The extension degree over `K(X)` is exactly the degree of the equation in
the second coordinate. -/
theorem finrank_planeCurveFunctionField_over_ratFunc_eq_degreeOf_second
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    Module.finrank (RatFunc K) (PlaneCurveFunctionField f) =
      MvPolynomial.degreeOf 1 f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  calc
    Module.finrank (RatFunc K) (PlaneCurveFunctionField f) =
        Module.finrank (FirstCoordinateSubfield f)
          (PlaneCurveFunctionField f) :=
      (Algebra.finrank_eq_of_equiv_equiv
        (RatFunc.algEquivOfTranscendental
          (planeCurveFunction f 0) hx).symm.toRingEquiv
        (RingEquiv.refl (PlaneCurveFunctionField f))
        (planeCurve_firstCoordinate_changeBase_commutes hx)).symm
    _ = MvPolynomial.degreeOf 1 f :=
      finrank_over_firstCoordinate_eq_degreeOf_second_of_irreducible
        hf hpartialSecond

/-! ## The symmetric second-coordinate model -/

/-- The `RatFunc K`-algebra structure obtained by specializing `X` at the
second coordinate of the plane curve. -/
@[reducible] noncomputable def planeCurveSecondCoordinateRatFuncAlgebra
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)]
    (hy : Transcendental K (planeCurveFunction f 1)) :
    Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
  (ratFuncSpecialization (planeCurveFunction f 1) hy).toAlgebra

@[simp] theorem planeCurveSecondCoordinateRatFuncAlgebra_X
    (f : MvPolynomial (Fin 2) K) [IsDomain (PlaneCurveCoordinateRing f)]
    (hy : Transcendental K (planeCurveFunction f 1)) :
    letI := planeCurveSecondCoordinateRatFuncAlgebra f hy
    algebraMap (RatFunc K) (PlaneCurveFunctionField f) RatFunc.X =
      planeCurveFunction f 1 := by
  let := planeCurveSecondCoordinateRatFuncAlgebra f hy
  change ratFuncSpecialization (planeCurveFunction f 1) hy RatFunc.X = _
  simp [ratFuncSpecialization, RatFunc.algEquivOfTranscendental_X]

private theorem planeCurve_secondCoordinate_changeBase_commutes
    {f : MvPolynomial (Fin 2) K} [IsDomain (PlaneCurveCoordinateRing f)]
    (hy : Transcendental K (planeCurveFunction f 1)) :
    letI := planeCurveSecondCoordinateRatFuncAlgebra f hy
    (algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (RatFunc.algEquivOfTranscendental
          (planeCurveFunction f 1) hy).symm.toRingEquiv.toRingHom =
      (RingEquiv.refl (PlaneCurveFunctionField f)).toRingHom.comp
        (algebraMap (SecondCoordinateSubfield f)
          (PlaneCurveFunctionField f)) := by
  let := planeCurveSecondCoordinateRatFuncAlgebra f hy
  ext z
  change ratFuncSpecialization (planeCurveFunction f 1) hy
      ((RatFunc.algEquivOfTranscendental
        (planeCurveFunction f 1) hy).symm z) =
    algebraMap (SecondCoordinateSubfield f) (PlaneCurveFunctionField f) z
  exact DFunLike.congr_fun
    (ratFuncSpecialization_comp_symm_algEquiv
      (planeCurveFunction f 1) hy) z

/-- The second-coordinate specialization also makes the plane-curve function
field finite over the standard rational-function field. -/
theorem finiteDimensional_planeCurveFunctionField_over_secondRatFunc
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hy := secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
    letI := planeCurveSecondCoordinateRatFuncAlgebra f hy
    FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hy := secondCoordinate_transcendental hf
    (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveSecondCoordinateRatFuncAlgebra f hy
  let : FiniteDimensional (SecondCoordinateSubfield f)
      (PlaneCurveFunctionField f) :=
    (finiteSeparable_over_secondCoordinate_of_irreducible
      hf hpartialFirst).1
  exact Module.Finite.of_equiv_equiv
    (RatFunc.algEquivOfTranscendental
      (planeCurveFunction f 1) hy).symm.toRingEquiv
    (RingEquiv.refl (PlaneCurveFunctionField f))
    (planeCurve_secondCoordinate_changeBase_commutes hy)

/-- The second-coordinate change of base transports separability. -/
theorem separable_planeCurveFunctionField_over_secondRatFunc
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hy := secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
    letI := planeCurveSecondCoordinateRatFuncAlgebra f hy
    Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hy := secondCoordinate_transcendental hf
    (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveSecondCoordinateRatFuncAlgebra f hy
  let : Algebra.IsSeparable (SecondCoordinateSubfield f)
      (PlaneCurveFunctionField f) :=
    (finiteSeparable_over_secondCoordinate_of_irreducible
      hf hpartialFirst).2
  exact Algebra.IsSeparable.of_equiv_equiv
    (RatFunc.algEquivOfTranscendental
      (planeCurveFunction f 1) hy).symm.toRingEquiv
    (RingEquiv.refl (PlaneCurveFunctionField f))
    (planeCurve_secondCoordinate_changeBase_commutes hy)

/-- In the second-coordinate model the extension degree is exactly the degree
of the equation in the first coordinate. -/
theorem finrank_planeCurveFunctionField_over_secondRatFunc_eq_degreeOf_first
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hy := secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
    letI := planeCurveSecondCoordinateRatFuncAlgebra f hy
    Module.finrank (RatFunc K) (PlaneCurveFunctionField f) =
      MvPolynomial.degreeOf 0 f := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hy := secondCoordinate_transcendental hf
    (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveSecondCoordinateRatFuncAlgebra f hy
  calc
    Module.finrank (RatFunc K) (PlaneCurveFunctionField f) =
        Module.finrank (SecondCoordinateSubfield f)
          (PlaneCurveFunctionField f) :=
      (Algebra.finrank_eq_of_equiv_equiv
        (RatFunc.algEquivOfTranscendental
          (planeCurveFunction f 1) hy).symm.toRingEquiv
        (RingEquiv.refl (PlaneCurveFunctionField f))
        (planeCurve_secondCoordinate_changeBase_commutes hy)).symm
    _ = MvPolynomial.degreeOf 0 f :=
      finrank_over_secondCoordinate_eq_degreeOf_first_of_irreducible
        hf hpartialFirst

end

end BGS.CorvajaZannier
