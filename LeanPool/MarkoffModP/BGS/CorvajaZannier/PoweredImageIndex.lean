/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageHeightFactor
import Mathlib.Tactic

/-!
# The common source-to-powered-image index

The powered image field is presented twice, once over each powered coordinate.
Although these presentations have different base fields, their underlying
intermediate field in the source function field is the same.  This file
transports finrank across `IntermediateField.restrictScalars`, identifies the
two source-to-image indices, and records the elementary projection bounds.

These statements do not identify image-curve degrees with source heights.
The missing exponent-independent bound on the common index is a genuinely
additional logarithmic-geometric input.
-/

namespace BGS.CorvajaZannier

noncomputable section

private theorem finrank_restrictScalars_intermediateField
    {K E L : Type*} [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    (A : IntermediateField E L) :
    Module.finrank (A.restrictScalars K) L = Module.finrank A L := by
  let e : (A.restrictScalars K) ≃+* A :=
    { toFun := fun z => ⟨z.1, z.2⟩
      invFun := fun z => ⟨z.1, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  exact Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl L)
    (by ext z; rfl)

/-- The first-coordinate presentation has the same source degree as the
common powered image field `K(x^m,y^n)`. -/
theorem finrank_poweredImageOverFirst_eq_imageField
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    [IsDomain (PlaneCurveCoordinateRing f)] (m n : ℕ) :
    Module.finrank (PoweredImageOverFirst f m n)
        (PlaneCurveFunctionField f) =
      Module.finrank (PoweredCoordinateImageField f m n)
        (PlaneCurveFunctionField f) := by
  let A := PoweredImageOverFirst f m n
  have htransport : Module.finrank (A.restrictScalars K)
      (PlaneCurveFunctionField f) =
      Module.finrank A (PlaneCurveFunctionField f) :=
    finrank_restrictScalars_intermediateField A
  have hfield := restrictScalars_poweredImageOverFirst_eq f m n
  have hrank := congrArg
    (fun E : IntermediateField K (PlaneCurveFunctionField f) =>
      Module.finrank E (PlaneCurveFunctionField f)) hfield
  exact htransport.symm.trans hrank

/-- The second-coordinate presentation has the same source degree as the
common powered image field `K(x^m,y^n)`. -/
theorem finrank_poweredImageOverSecond_eq_imageField
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    [IsDomain (PlaneCurveCoordinateRing f)] (m n : ℕ) :
    Module.finrank (PoweredImageOverSecond f m n)
        (PlaneCurveFunctionField f) =
      Module.finrank (PoweredCoordinateImageField f m n)
        (PlaneCurveFunctionField f) := by
  let A := PoweredImageOverSecond f m n
  have htransport : Module.finrank (A.restrictScalars K)
      (PlaneCurveFunctionField f) =
      Module.finrank A (PlaneCurveFunctionField f) :=
    finrank_restrictScalars_intermediateField A
  have hfield := restrictScalars_poweredImageOverSecond_eq f m n
  have hrank := congrArg
    (fun E : IntermediateField K (PlaneCurveFunctionField f) =>
      Module.finrank E (PlaneCurveFunctionField f)) hfield
  exact htransport.symm.trans hrank

/-- Both relative presentations compute one and the same geometric degree of
the source-to-powered-image map. -/
theorem finrank_poweredImageOverFirst_eq_poweredImageOverSecond
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    [IsDomain (PlaneCurveCoordinateRing f)] (m n : ℕ) :
    Module.finrank (PoweredImageOverFirst f m n)
        (PlaneCurveFunctionField f) =
      Module.finrank (PoweredImageOverSecond f m n)
        (PlaneCurveFunctionField f) := by
  rw [finrank_poweredImageOverFirst_eq_imageField,
    finrank_poweredImageOverSecond_eq_imageField]

/-- The common powered-image index is at most the source degree over the
powered first coordinate, hence at most `m * degreeOf 1 f`. -/
theorem finrank_poweredImageOverFirst_le_firstProjectionPowerDegree
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (PoweredImageOverFirst f m n)
        (PlaneCurveFunctionField f) ≤
      m * MvPolynomial.degreeOf 1 f := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : FiniteDimensional (FirstPoweredCoordinateSubfield f m)
      (PlaneCurveFunctionField f) :=
    finiteDimensional_over_firstPoweredCoordinate hf hpartialSecond m hm
  have htower := Module.finrank_mul_finrank
    (FirstPoweredCoordinateSubfield f m)
    (PoweredImageOverFirst f m n)
    (PlaneCurveFunctionField f)
  have hfactor : 0 < Module.finrank (FirstPoweredCoordinateSubfield f m)
      (PoweredImageOverFirst f m n) := Module.finrank_pos
  have hindexSource : Module.finrank (PoweredImageOverFirst f m n)
      (PlaneCurveFunctionField f) ≤
      Module.finrank (FirstPoweredCoordinateSubfield f m)
        (PlaneCurveFunctionField f) := by
    calc
      Module.finrank (PoweredImageOverFirst f m n)
          (PlaneCurveFunctionField f) ≤
          Module.finrank (FirstPoweredCoordinateSubfield f m)
            (PoweredImageOverFirst f m n) *
            Module.finrank (PoweredImageOverFirst f m n)
              (PlaneCurveFunctionField f) := by
        exact Nat.le_mul_of_pos_left _ hfactor
      _ = Module.finrank (FirstPoweredCoordinateSubfield f m)
          (PlaneCurveFunctionField f) := htower
  exact hindexSource.trans
    (finrank_over_firstPoweredCoordinate_le hf hpartialSecond m hm)

/-- The common powered-image index is at most the source degree over the
powered second coordinate, hence at most `n * degreeOf 0 f`. -/
theorem finrank_poweredImageOverSecond_le_secondProjectionPowerDegree
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f) (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (m n : ℕ) (hn : 0 < n) :
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (PoweredImageOverSecond f m n)
        (PlaneCurveFunctionField f) ≤
      n * MvPolynomial.degreeOf 0 f := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  letI : FiniteDimensional (SecondPoweredCoordinateSubfield f n)
      (PlaneCurveFunctionField f) :=
    finiteDimensional_over_secondPoweredCoordinate hf hpartialFirst n hn
  have htower := Module.finrank_mul_finrank
    (SecondPoweredCoordinateSubfield f n)
    (PoweredImageOverSecond f m n)
    (PlaneCurveFunctionField f)
  have hfactor : 0 < Module.finrank (SecondPoweredCoordinateSubfield f n)
      (PoweredImageOverSecond f m n) := Module.finrank_pos
  have hindexSource : Module.finrank (PoweredImageOverSecond f m n)
      (PlaneCurveFunctionField f) ≤
      Module.finrank (SecondPoweredCoordinateSubfield f n)
        (PlaneCurveFunctionField f) := by
    calc
      Module.finrank (PoweredImageOverSecond f m n)
          (PlaneCurveFunctionField f) ≤
          Module.finrank (SecondPoweredCoordinateSubfield f n)
            (PoweredImageOverSecond f m n) *
            Module.finrank (PoweredImageOverSecond f m n)
              (PlaneCurveFunctionField f) := by
        exact Nat.le_mul_of_pos_left _ hfactor
      _ = Module.finrank (SecondPoweredCoordinateSubfield f n)
          (PlaneCurveFunctionField f) := htower
  exact hindexSource.trans
    (finrank_over_secondPoweredCoordinate_le hf hpartialFirst n hn)

end


end BGS.CorvajaZannier
