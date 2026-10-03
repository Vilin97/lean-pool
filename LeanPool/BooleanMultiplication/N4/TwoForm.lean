/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Geometry

/-!
# Target alternating two-forms

The quadratic target is represented as the alternating `8 × 8` matrix with
the `4 × 4` Hankel matrix in its two cross blocks.  This small coordinate
layer is shared by the quadratic lower bound and the cubic annihilator.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Coordinate linear forms on the two four-dimensional input blocks. -/
@[expose] def aLinear (i : Fin 4) : LinearForm :=
  (Pi.basisFun F₂ (Fin 8)) (aCoord i)

/-- The linear form selecting one coefficient of the second input polynomial. -/
@[expose] def bLinear (i : Fin 4) : LinearForm :=
  (Pi.basisFun F₂ (Fin 8)) (bCoord i)

/-- The first three Hasse coefficients at the rational place zero. -/
@[expose] def zeroPlaceTwo : TwoForm := vectorWedge (aLinear 0) (bLinear 0)

/-- The two-form of the first Hasse coefficient at zero. -/
@[expose] def zeroFirstJetTwo : TwoForm :=
  vectorWedge (aLinear 0) (bLinear 1) +
    vectorWedge (aLinear 1) (bLinear 0)

/-- The two-form of the second Hasse coefficient at zero. -/
def zeroSecondJetTwo : TwoForm :=
  vectorWedge (aLinear 0) (bLinear 2) +
    vectorWedge (aLinear 1) (bLinear 1) +
    vectorWedge (aLinear 2) (bLinear 0)

/-- The alternating two-form whose mixed block is the target Hankel matrix. -/
@[expose] def targetTwo (c : TargetCoeff) : TwoForm := fun i j =>
  if hi : i.val < 4 then
    if hj : 4 ≤ j.val then
      c ⟨i.val + (j.val - 4), by omega⟩
    else 0
  else if hj : j.val < 4 then
    c ⟨j.val + (i.val - 4), by omega⟩
  else 0

/-- The target Hankel two-form construction as a linear map. -/
@[expose] def targetTwoLinear : TargetCoeff →ₗ[F₂] TwoForm where
  toFun := targetTwo
  map_add' c d := by
    funext i j
    simp only [targetTwo, Pi.add_apply]
    split_ifs <;> rfl
  map_smul' a c := by
    funext i j
    simp only [targetTwo, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp

theorem targetTwo_cross (c : TargetCoeff) (i j : Fin 4) :
    targetTwo c (aCoord i) (bCoord j) =
      c ⟨i.val + j.val, by omega⟩ := by
  fin_cases i <;> fin_cases j <;> simp [targetTwo, aCoord, bCoord]

theorem targetTwo_sameA (c : TargetCoeff) (i j : Fin 4) :
    targetTwo c (aCoord i) (aCoord j) = 0 := by
  fin_cases i <;> fin_cases j <;> simp [targetTwo, aCoord]

theorem targetTwo_sameB (c : TargetCoeff) (i j : Fin 4) :
    targetTwo c (bCoord i) (bCoord j) = 0 := by
  fin_cases i <;> fin_cases j <;> simp [targetTwo, bCoord]

@[simp] theorem targetTwo_basis_zero :
    targetTwo (targetBasis 0) = zeroPlaceTwo := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [targetTwo, targetBasis, zeroPlaceTwo, vectorWedge, aLinear, bLinear, aCoord, bCoord,
      Pi.basisFun]

@[simp] theorem targetTwo_basis_one :
    targetTwo (targetBasis 1) = zeroFirstJetTwo := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [targetTwo, targetBasis, zeroFirstJetTwo, vectorWedge, aLinear, bLinear, aCoord,
      bCoord, Pi.basisFun]

@[simp] theorem targetTwo_basis_two :
    targetTwo (targetBasis 2) = zeroSecondJetTwo := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [targetTwo, targetBasis, zeroSecondJetTwo, vectorWedge, aLinear, bLinear, aCoord,
      bCoord, Pi.basisFun]

@[simp] theorem rationalPlaceTwo_zero_eq :
    rationalPlaceTwo 0 = zeroPlaceTwo := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalPlaceTwo, zeroPlaceTwo, vectorWedge, placeA, placeB, aLinear, bLinear,
      aCoord, bCoord, Pi.basisFun]

theorem targetTwo_injective : Function.Injective targetTwo := by
  intro c d h
  funext s
  fin_cases s
  · simpa [targetTwo_cross] using congrFun (congrFun h (aCoord 0)) (bCoord 0)
  · simpa [targetTwo_cross] using congrFun (congrFun h (aCoord 0)) (bCoord 1)
  · simpa [targetTwo_cross] using congrFun (congrFun h (aCoord 0)) (bCoord 2)
  · simpa [targetTwo_cross] using congrFun (congrFun h (aCoord 0)) (bCoord 3)
  · simpa [targetTwo_cross] using congrFun (congrFun h (aCoord 1)) (bCoord 3)
  · simpa [targetTwo_cross] using congrFun (congrFun h (aCoord 2)) (bCoord 3)
  · simpa [targetTwo_cross] using congrFun (congrFun h (aCoord 3)) (bCoord 3)

/-- The concrete rational-place coordinates agree in the Hankel and exterior
models. -/
theorem targetTwo_rationalCoeffRep (α : Fin 3 → F₂) :
    targetTwo (rationalCoeffRep α) = rationalTwo α := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [targetTwo, rationalCoeffRep, rationalTwo, rationalPlaceTwo, vectorWedge, placeA,
      placeB, rZeroCoeff, rOneCoeff, rInfinityCoeff, Fin.sum_univ_succ]

/-- The seven-dimensional subspace of target Hankel two-forms. -/
@[expose]
def targetTwoSpace : Submodule F₂ TwoForm := LinearMap.range targetTwoLinear

/-- The two-form is the exterior product of two linear forms. -/
@[expose] def IsDecomposableTwo (q : TwoForm) : Prop :=
  ∃ u v : LinearForm, q = vectorWedge u v

theorem targetTwoSpace_finrank : Module.finrank F₂ targetTwoSpace = 7 := by
  have he := (LinearEquiv.ofInjective targetTwoLinear targetTwo_injective).finrank_eq
  change Module.finrank F₂ targetTwoLinear.range = 7
  calc
    Module.finrank F₂ targetTwoLinear.range = Module.finrank F₂ TargetCoeff := he.symm
    _ = 7 := by simp [TargetCoeff]

end

end N4
end UnrestrictedBooleanMul
