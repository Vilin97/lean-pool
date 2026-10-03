/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.CubicSemantic

/-!
# Algebraic ANF models for zero-place slices

The quartic exclusion compares restrictions to the six variables outside
`a₀,b₀`.  These models keep the six complementary variables in their original
eight-coordinate positions and set the two anchor coefficients to zero.  This
lets the homogeneous projections already used by the exterior argument apply
without introducing a second ANF type or enumerating Boolean functions.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Remove the two anchor coordinates from a linear form. -/
def sliceComplementLinear (ell : LinearForm) : LinearForm :=
  ell + ell 0 • sliceX + ell 4 • sliceY

/-- Evaluate the anchor-supported part of a linear form at fixed anchor values. -/
def sliceAnchorValue (ell : LinearForm) (x y : F₂) : F₂ :=
  ell 0 * x + ell 4 * y

/-- The ANF product of the two complementary evaluation-at-one directions. -/
@[expose] def sliceQuadraticAANF : ANF 8 :=
  linearANF sliceABar * linearANF sliceBBar

/-- The product of the two leading input coefficients. -/
@[expose] def sliceInfinityQuadraticANF : ANF 8 :=
  linearANF (placeA 2) * linearANF (placeB 2)

/-- The sum of the complementary evaluation-at-one and infinity products. -/
@[expose] def sliceQuadraticBANF : ANF 8 :=
  sliceQuadraticAANF + sliceInfinityQuadraticANF

/-- Restrict an affine factor plus the zero-place product to an anchor slice. -/
@[expose] def sliceZeroFactorModel
    (a : F₂) (ell : LinearForm) (x y : F₂) : ANF 8 :=
  affineANF (a + sliceAnchorValue ell x y + x * y)
    (sliceComplementLinear ell)

/-- Restrict an affine factor plus the evaluation-at-one product to an anchor slice. -/
@[expose] def sliceOneFactorModel
    (a : F₂) (ell : LinearForm) (x y : F₂) : ANF 8 :=
  affineANF (a + sliceAnchorValue ell x y + x * y)
      (sliceComplementLinear ell + sliceVaryingLinear x y) +
    sliceQuadraticAANF

/-- Restrict an affine factor plus the infinity-place product to an anchor slice. -/
@[expose] def sliceInfinityFactorModel
    (a : F₂) (ell : LinearForm) (x y : F₂) : ANF 8 :=
  affineANF (a + sliceAnchorValue ell x y)
      (sliceComplementLinear ell) +
    sliceInfinityQuadraticANF

/-- Restrict an affine factor with type-B quadratic part to an anchor slice. -/
@[expose] def sliceTypeBFactorModel
    (a : F₂) (ell : LinearForm) (x y : F₂) : ANF 8 :=
  affineANF (a + sliceAnchorValue ell x y + x * y)
      (sliceComplementLinear ell + sliceVaryingLinear x y) +
    sliceQuadraticBANF

/-- Restrict an affine-plus-rational-target correction to an anchor slice. -/
@[expose] def sliceCorrectionModel
    (a : F₂) (ell : LinearForm) (alpha : Fin 3 → F₂)
    (x y : F₂) : ANF 8 :=
  affineANF
      (a + sliceAnchorValue ell x y + (alpha 0 + alpha 1) * x * y)
      (sliceComplementLinear ell + alpha 1 • sliceVaryingLinear x y) +
    alpha 1 • sliceQuadraticAANF +
    alpha 2 • sliceInfinityQuadraticANF

/-- Restrict an affine perturbation of a first-jet tangent target to an anchor slice. -/
@[expose] def sliceTangentModel
    (a : F₂) (ell : LinearForm) (eps x y : F₂) : ANF 8 :=
  affineANF (a + sliceAnchorValue ell x y + eps * x * y)
    (sliceComplementLinear ell + y • sliceU + x • sliceV)

/-- Extract the six non-anchor input coordinates. -/
def sliceComplementOf (w : Fin 8 → F₂) : Fin 6 → F₂ :=
  ![w 1, w 2, w 3, w 5, w 6, w 7]

theorem sliceAssignment_complementOf (x y : F₂) (w : Fin 8 → F₂) :
    sliceAssignment x y (sliceComplementOf w) =
      ![x, w 1, w 2, w 3, y, w 5, w 6, w 7] := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem sliceComplementLinear_anchor_zero (ell : LinearForm) :
    sliceComplementLinear ell 0 = 0 ∧ sliceComplementLinear ell 4 = 0 := by
  constructor <;>
    simp [sliceComplementLinear, sliceX, sliceY, aLinear, bLinear, aCoord, bCoord, Pi.basisFun
      ] <;>
    ring_nf <;>
    simp [N3Certificate.two_eq_zero_f2]

theorem sliceComplementLinear_other
    (ell : LinearForm) (i : Fin 8) (hi0 : i ≠ 0) (hi4 : i ≠ 4) :
    sliceComplementLinear ell i = ell i := by
  simp [sliceComplementLinear, sliceX, sliceY, aLinear, bLinear, aCoord, bCoord, Pi.basisFun,
    hi0, hi4]

@[simp] theorem eval_linearANF_formula
    (ell : LinearForm) (w : Fin 8 → F₂) :
    eval (linearANF ell) w = ∑ i, ell i * w i := by
  rw [linearANF, eval_eq_evalHom, map_sum]
  simp_rw [map_smul, ← eval_eq_evalHom, eval_X]
  rfl

@[simp] theorem eval_affineANF_formula
    (a : F₂) (ell : LinearForm) (w : Fin 8 → F₂) :
    eval (affineANF a ell) w = a + ∑ i, ell i * w i := by
  simp [affineANF, eval_add', eval_smul']

theorem eval_linearANF_slice
    (ell : LinearForm) (x y : F₂) (z : Fin 6 → F₂) :
    eval (linearANF ell) (sliceAssignment x y z) =
      sliceAnchorValue ell x y +
        eval (linearANF (sliceComplementLinear ell))
          (sliceAssignment x y z) := by
  simp [sliceAssignment, sliceAnchorValue, sliceComplementLinear, sliceX, sliceY, aLinear,
    bLinear, aCoord, bCoord, Pi.basisFun, Fin.sum_univ_succ]
  ring_nf
  simp [N3Certificate.three_eq_one_f2]

theorem eval_affineANF_slice
    (a : F₂) (ell : LinearForm) (x y : F₂) (z : Fin 6 → F₂) :
    eval (affineANF a ell) (sliceAssignment x y z) =
      eval (affineANF (a + sliceAnchorValue ell x y)
        (sliceComplementLinear ell)) (sliceAssignment x y z) := by
  simp only [affineANF, eval_add', eval_smul', eval_one', mul_one]
  rw [eval_linearANF_slice]
  ring

theorem eval_rationalANF_slice
    (alpha : Fin 3 → F₂) (x y : F₂) (z : Fin 6 → F₂) :
    eval (rationalANF alpha) (sliceAssignment x y z) =
      alpha 0 * x * y +
      alpha 1 *
        (x + eval (linearANF sliceABar) (sliceAssignment x y z)) *
        (y + eval (linearANF sliceBBar) (sliceAssignment x y z)) +
      alpha 2 *
        eval (linearANF (placeA 2)) (sliceAssignment x y z) *
        eval (linearANF (placeB 2)) (sliceAssignment x y z) := by
  rw [rationalANF_eq_sum]
  simp only [rationalPlaceANF_direct]
  simp [Fin.sum_univ_succ, sliceAssignment, sliceABar, sliceBBar, placeA, placeB]
  ring_nf
  rw [N3Certificate.three_eq_one_f2,
    show (9 : F₂) = 1 by decide]
  ring

theorem eval_affineANF_linear_add
    (a : F₂) (ell m : LinearForm) (w : Fin 8 → F₂) :
    eval (affineANF a (ell + m)) w =
      eval (affineANF a ell) w + eval (linearANF m) w := by
  simp only [affineANF, linearANF_add, eval_add', eval_smul', eval_one', mul_one]
  ring

theorem eval_affineANF_const_add
    (a b : F₂) (ell : LinearForm) (w : Fin 8 → F₂) :
    eval (affineANF (a + b) ell) w =
      b + eval (affineANF a ell) w := by
  simp only [affineANF, add_smul, eval_add', eval_smul', eval_one', mul_one]
  ring

theorem eval_linearANF_sliceVarying
    (x y : F₂) (w : Fin 8 → F₂) :
    eval (linearANF (sliceVaryingLinear x y)) w =
      x * eval (linearANF sliceBBar) w +
        y * eval (linearANF sliceABar) w := by
  rw [sliceVaryingLinear, linearANF_add,
    linearANF_smul, linearANF_smul]
  simp [eval_add', eval_smul']

@[simp] theorem eval_sliceQuadraticAANF (w : Fin 8 → F₂) :
    eval sliceQuadraticAANF w =
      eval (linearANF sliceABar) w * eval (linearANF sliceBBar) w := by
  simp [sliceQuadraticAANF]

@[simp] theorem eval_sliceInfinityQuadraticANF (w : Fin 8 → F₂) :
    eval sliceInfinityQuadraticANF w =
      eval (linearANF (placeA 2)) w *
        eval (linearANF (placeB 2)) w := by
  simp [sliceInfinityQuadraticANF]

@[simp] theorem eval_sliceQuadraticBANF (w : Fin 8 → F₂) :
    eval sliceQuadraticBANF w =
      eval sliceQuadraticAANF w + eval sliceInfinityQuadraticANF w := by
  simp [sliceQuadraticBANF]

theorem eval_representedLowFactor_slice
    (a : F₂) (ell : LinearForm) (alpha : Fin 3 → F₂)
    (x y : F₂) (z : Fin 6 → F₂) :
    eval (representedLowFactor a ell alpha) (sliceAssignment x y z) =
      eval (affineANF (a + sliceAnchorValue ell x y)
          (sliceComplementLinear ell)) (sliceAssignment x y z) +
        eval (rationalANF alpha) (sliceAssignment x y z) := by
  rw [representedLowFactor, eval_add', eval_affineANF_slice]

theorem eval_sliceZeroFactorModel
    (a : F₂) (ell : LinearForm) (x y : F₂) (z : Fin 6 → F₂) :
    eval (sliceZeroFactorModel a ell x y) (sliceAssignment x y z) =
      eval (representedLowFactor a ell (rationalSingleton 0))
        (sliceAssignment x y z) := by
  rw [eval_representedLowFactor_slice]
  simp [sliceZeroFactorModel, rationalSingleton, eval_rationalANF_slice, sliceAnchorValue]
  ring

theorem eval_sliceOneFactorModel
    (a : F₂) (ell : LinearForm) (x y : F₂) (z : Fin 6 → F₂) :
    eval (sliceOneFactorModel a ell x y) (sliceAssignment x y z) =
      eval (representedLowFactor a ell (rationalSingleton 1))
        (sliceAssignment x y z) := by
  rw [eval_representedLowFactor_slice]
  rw [sliceOneFactorModel, eval_add', eval_affineANF_linear_add,
    eval_linearANF_sliceVarying, eval_sliceQuadraticAANF,
    eval_rationalANF_slice]
  simp [rationalSingleton]
  ring

theorem eval_sliceInfinityFactorModel
    (a : F₂) (ell : LinearForm) (x y : F₂) (z : Fin 6 → F₂) :
    eval (sliceInfinityFactorModel a ell x y) (sliceAssignment x y z) =
      eval (representedLowFactor a ell (rationalSingleton 2))
        (sliceAssignment x y z) := by
  rw [eval_representedLowFactor_slice]
  rw [sliceInfinityFactorModel, eval_add',
    eval_sliceInfinityQuadraticANF, eval_rationalANF_slice]
  simp [rationalSingleton]

theorem eval_sliceTypeBFactorModel
    (a : F₂) (ell : LinearForm) (x y : F₂) (z : Fin 6 → F₂) :
    eval (sliceTypeBFactorModel a ell x y) (sliceAssignment x y z) =
      eval (representedLowFactor a ell
        (rationalSingleton 1 + rationalSingleton 2))
        (sliceAssignment x y z) := by
  rw [eval_representedLowFactor_slice]
  rw [sliceTypeBFactorModel, eval_add', eval_affineANF_linear_add,
    eval_linearANF_sliceVarying, eval_sliceQuadraticBANF,
    eval_sliceQuadraticAANF, eval_sliceInfinityQuadraticANF,
    eval_rationalANF_slice]
  simp [rationalSingleton]
  ring

theorem eval_sliceCorrectionModel
    (a : F₂) (ell : LinearForm) (alpha : Fin 3 → F₂)
    (x y : F₂) (z : Fin 6 → F₂) :
    eval (sliceCorrectionModel a ell alpha x y) (sliceAssignment x y z) =
      eval (representedLowFactor a ell alpha) (sliceAssignment x y z) := by
  rw [eval_representedLowFactor_slice]
  rw [sliceCorrectionModel, eval_add', eval_add',
    eval_affineANF_linear_add, linearANF_smul, eval_smul',
    eval_linearANF_sliceVarying]
  simp only [eval_smul']
  rw [eval_sliceQuadraticAANF,
    eval_sliceInfinityQuadraticANF, eval_rationalANF_slice]
  rw [eval_affineANF_const_add]
  ring

theorem eval_sliceTangentModel
    (a : F₂) (ell : LinearForm) (eps x y : F₂) (z : Fin 6 → F₂) :
    eval (sliceTangentModel a ell eps x y) (sliceAssignment x y z) =
      eval (affineANF a ell + targetANF (rationalTangentAt 0 eps))
        (sliceAssignment x y z) := by
  rw [targetANF_zero_tangent, eval_add', eval_affineANF_slice]
  rw [sliceTangentModel, eval_affineANF_linear_add,
    eval_affineANF_linear_add, eval_affineANF_const_add]
  simp only [linearANF_smul, eval_smul']
  rw [mul_target_zero_anf, mul_target_one_anf]
  simp [sliceAssignment, sliceU, sliceV, aLinear, bLinear, aCoord, bCoord, Pi.basisFun,
    Fin.sum_univ_succ]
  ring

/-- The Boolean function is unchanged when either anchor input is reassigned. -/
def AnchorsIndependent (p : ANF 8) : Prop :=
  ∀ x y : F₂, ∀ w : Fin 8 → F₂,
    eval p w = eval p (sliceAssignment x y (sliceComplementOf w))

theorem anchorsIndependent_linearANF
    {ell : LinearForm} (h0 : ell 0 = 0) (h4 : ell 4 = 0) :
    AnchorsIndependent (linearANF ell) := by
  intro x y w
  simp [sliceComplementOf, sliceAssignment, Fin.sum_univ_succ, h0, h4]

theorem anchorsIndependent_affineANF
    (a : F₂) {ell : LinearForm} (h0 : ell 0 = 0) (h4 : ell 4 = 0) :
    AnchorsIndependent (affineANF a ell) := by
  intro x y w
  simp only [affineANF, eval_add', eval_smul', eval_one']
  rw [anchorsIndependent_linearANF h0 h4 x y w]

theorem AnchorsIndependent.add {p q : ANF 8}
    (hp : AnchorsIndependent p) (hq : AnchorsIndependent q) :
    AnchorsIndependent (p + q) := by
  intro x y w
  simp only [eval_add']
  rw [hp x y w, hq x y w]

theorem AnchorsIndependent.mul {p q : ANF 8}
    (hp : AnchorsIndependent p) (hq : AnchorsIndependent q) :
    AnchorsIndependent (p * q) := by
  intro x y w
  simp only [eval_mul']
  rw [hp x y w, hq x y w]

theorem AnchorsIndependent.smul (a : F₂) {p : ANF 8}
    (hp : AnchorsIndependent p) : AnchorsIndependent (a • p) := by
  intro x y w
  simp only [eval_smul']
  rw [hp x y w]

theorem sliceABar_anchor_zero : sliceABar 0 = 0 ∧ sliceABar 4 = 0 := by
  decide

theorem sliceBBar_anchor_zero : sliceBBar 0 = 0 ∧ sliceBBar 4 = 0 := by
  decide

theorem sliceInfinityA_anchor_zero : placeA 2 0 = 0 ∧ placeA 2 4 = 0 := by
  decide

theorem sliceInfinityB_anchor_zero : placeB 2 0 = 0 ∧ placeB 2 4 = 0 := by
  decide

theorem sliceU_anchor_zero : sliceU 0 = 0 ∧ sliceU 4 = 0 := by
  simp [sliceU, aLinear, aCoord, Pi.basisFun]

theorem sliceV_anchor_zero : sliceV 0 = 0 ∧ sliceV 4 = 0 := by
  simp [sliceV, bLinear, bCoord, Pi.basisFun]

theorem sliceVaryingLinear_anchor_zero (x y : F₂) :
    sliceVaryingLinear x y 0 = 0 ∧ sliceVaryingLinear x y 4 = 0 := by
  simp [sliceVaryingLinear, sliceABar_anchor_zero, sliceBBar_anchor_zero]

theorem sliceComplementLinear_anchor_zero_separate (ell : LinearForm) :
    sliceComplementLinear ell 0 = 0 ∧
      sliceComplementLinear ell 4 = 0 :=
  sliceComplementLinear_anchor_zero ell

theorem anchorsIndependent_sliceZeroFactorModel
    (a : F₂) (ell : LinearForm) (x y : F₂) :
    AnchorsIndependent (sliceZeroFactorModel a ell x y) := by
  apply anchorsIndependent_affineANF
  · exact (sliceComplementLinear_anchor_zero ell).1
  · exact (sliceComplementLinear_anchor_zero ell).2

theorem anchorsIndependent_sliceOneFactorModel
    (a : F₂) (ell : LinearForm) (x y : F₂) :
    AnchorsIndependent (sliceOneFactorModel a ell x y) := by
  apply AnchorsIndependent.add
  · apply anchorsIndependent_affineANF
    · simp [sliceComplementLinear_anchor_zero, sliceVaryingLinear_anchor_zero]
    · simp [sliceComplementLinear_anchor_zero, sliceVaryingLinear_anchor_zero]
  · exact (anchorsIndependent_linearANF sliceABar_anchor_zero.1
      sliceABar_anchor_zero.2).mul
        (anchorsIndependent_linearANF sliceBBar_anchor_zero.1
          sliceBBar_anchor_zero.2)

theorem anchorsIndependent_sliceInfinityFactorModel
    (a : F₂) (ell : LinearForm) (x y : F₂) :
    AnchorsIndependent (sliceInfinityFactorModel a ell x y) := by
  apply AnchorsIndependent.add
  · exact anchorsIndependent_affineANF _
      (sliceComplementLinear_anchor_zero ell).1
      (sliceComplementLinear_anchor_zero ell).2
  · exact (anchorsIndependent_linearANF sliceInfinityA_anchor_zero.1
      sliceInfinityA_anchor_zero.2).mul
        (anchorsIndependent_linearANF sliceInfinityB_anchor_zero.1
          sliceInfinityB_anchor_zero.2)

theorem anchorsIndependent_sliceTypeBFactorModel
    (a : F₂) (ell : LinearForm) (x y : F₂) :
    AnchorsIndependent (sliceTypeBFactorModel a ell x y) := by
  apply AnchorsIndependent.add
  · apply anchorsIndependent_affineANF
    · simp [sliceComplementLinear_anchor_zero, sliceVaryingLinear_anchor_zero]
    · simp [sliceComplementLinear_anchor_zero, sliceVaryingLinear_anchor_zero]
  · exact
      ((anchorsIndependent_linearANF sliceABar_anchor_zero.1
        sliceABar_anchor_zero.2).mul
          (anchorsIndependent_linearANF sliceBBar_anchor_zero.1
            sliceBBar_anchor_zero.2)).add
        ((anchorsIndependent_linearANF sliceInfinityA_anchor_zero.1
          sliceInfinityA_anchor_zero.2).mul
            (anchorsIndependent_linearANF sliceInfinityB_anchor_zero.1
              sliceInfinityB_anchor_zero.2))

theorem anchorsIndependent_sliceCorrectionModel
    (a : F₂) (ell : LinearForm) (alpha : Fin 3 → F₂)
    (x y : F₂) : AnchorsIndependent (sliceCorrectionModel a ell alpha x y) := by
  apply AnchorsIndependent.add
  · apply AnchorsIndependent.add
    · apply anchorsIndependent_affineANF
      · simp [sliceComplementLinear_anchor_zero, sliceVaryingLinear_anchor_zero]
      · simp [sliceComplementLinear_anchor_zero, sliceVaryingLinear_anchor_zero]
    · exact ((anchorsIndependent_linearANF sliceABar_anchor_zero.1
        sliceABar_anchor_zero.2).mul
          (anchorsIndependent_linearANF sliceBBar_anchor_zero.1
            sliceBBar_anchor_zero.2)).smul (alpha 1)
  · exact ((anchorsIndependent_linearANF sliceInfinityA_anchor_zero.1
      sliceInfinityA_anchor_zero.2).mul
        (anchorsIndependent_linearANF sliceInfinityB_anchor_zero.1
          sliceInfinityB_anchor_zero.2)).smul (alpha 2)

theorem anchorsIndependent_sliceTangentModel
    (a : F₂) (ell : LinearForm) (eps x y : F₂) :
    AnchorsIndependent (sliceTangentModel a ell eps x y) := by
  apply anchorsIndependent_affineANF
  · simp [sliceComplementLinear_anchor_zero, sliceU_anchor_zero, sliceV_anchor_zero]
  · simp [sliceComplementLinear_anchor_zero, sliceU_anchor_zero, sliceV_anchor_zero]

theorem eval_eq_of_slice_eq
    {p q : ANF 8} {x y : F₂}
    (hp : AnchorsIndependent p) (hq : AnchorsIndependent q)
    (h : ∀ z : Fin 6 → F₂,
      eval p (sliceAssignment x y z) =
        eval q (sliceAssignment x y z)) :
    ∀ w : Fin 8 → F₂, eval p w = eval q w := by
  intro w
  rw [hp x y w, h (sliceComplementOf w), ← hq x y w]

end

end N4
end UnrestrictedBooleanMul
