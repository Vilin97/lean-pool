/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.SliceProjection

/-!
# Semantic bridge from active slices to the algebraic exclusions

The hypotheses below are equalities of six-variable slice functions.  Möbius
polarization recovers their cubic, quadratic, and linear ANF coefficients.
Those three coefficient equations are exactly the inputs consumed by
`no_typeA_active_slice_pair` and `no_typeB_active_slice_pair`.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

theorem sliceComplement_coefficients_zero
    {p q : F₂}
    (h : p • sliceABar + q • sliceBBar = 0) :
    p = 0 ∧ q = 0 := by
  have hp := congrFun h (aCoord 1)
  have hq := congrFun h (bCoord 1)
  simp only [sliceABar, placeA, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.add_cons, Matrix.head_cons, Matrix.tail_cons, add_zero, Matrix.empty_add_empty,
    Matrix.smul_cons, smul_eq_mul, mul_one, mul_zero, Matrix.smul_empty, sliceBBar, placeB,
    aCoord, Fin.coe_ofNat_eq_mod, Nat.one_mod, Fin.mk_one, Pi.add_apply, Pi.zero_apply,
    bCoord, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val, zero_add] at hp hq
  exact ⟨hp, hq⟩

/-- Two distinct active Type-A slice models cannot both equal slices of the
same zero-place target tangent. -/
theorem no_typeA_slice_model_pair
    {x y x' y' : F₂}
    (hdistinct : x ≠ x' ∨ y ≠ y')
    (leftConst rightConst correctionConst targetConst eps : F₂)
    (leftLinear rightLinear correctionLinear targetLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂)
    (hslice : ∀ z : Fin 6 → F₂,
      eval
          (sliceTypeAFullModel leftConst leftLinear rightConst rightLinear
            correctionConst correctionLinear correctionCoeff x y)
          (sliceAssignment x y z) =
        eval (sliceTangentModel targetConst targetLinear eps x y)
          (sliceAssignment x y z))
    (hslice' : ∀ z : Fin 6 → F₂,
      eval
          (sliceTypeAFullModel leftConst leftLinear rightConst rightLinear
            correctionConst correctionLinear correctionCoeff x' y')
          (sliceAssignment x' y' z) =
        eval (sliceTangentModel targetConst targetLinear eps x' y')
          (sliceAssignment x' y' z)) : False := by
  let ell := sliceComplementLinear leftLinear
  let m := sliceComplementLinear rightLinear
  let base := sliceComplementLinear correctionLinear
  let mu := leftConst + sliceAnchorValue leftLinear x y + x * y
  let mu' := leftConst + sliceAnchorValue leftLinear x' y' + x' * y'
  let nu := rightConst + sliceAnchorValue rightLinear x y + x * y
  let nu' := rightConst + sliceAnchorValue rightLinear x' y' + x' * y'
  let n := m + sliceVaryingLinear x y
  let n' := m + sliceVaryingLinear x' y'
  have heval := eval_eq_of_slice_eq
    (anchorsIndependent_sliceTypeAFullModel leftConst leftLinear
      rightConst rightLinear correctionConst correctionLinear
      correctionCoeff x y)
    (anchorsIndependent_sliceTangentModel targetConst targetLinear eps x y)
    hslice
  have heval' := eval_eq_of_slice_eq
    (anchorsIndependent_sliceTypeAFullModel leftConst leftLinear
      rightConst rightLinear correctionConst correctionLinear
      correctionCoeff x' y')
    (anchorsIndependent_sliceTangentModel targetConst targetLinear eps x' y')
    hslice'
  have hcubic := anfThreeProjection_congr_of_eval_eq heval
  rw [anfThreeProjection_sliceTypeAFullModel,
    anfThreeProjection_sliceTangentModel] at hcubic
  change vectorWedgeTwo ell sliceQuadraticA = 0 at hcubic
  rcases sliceQuadraticA_annihilator hcubic with ⟨p, q, hpq⟩
  have hcontract :
      booleanContraction ell sliceQuadraticA =
        (p + q) • sliceQuadraticA := by
    rw [hpq]
    exact booleanContraction_sliceComplement_sliceQuadraticA p q
  let quadMu := mu + p + q
  let quadMu' := mu' + p + q
  have htwo := anfTwoProjection_congr_of_eval_eq heval
  rw [anfTwoProjection_sliceTypeAFullModel,
    anfTwoProjection_sliceTangentModel] at htwo
  change
    mu • sliceQuadraticA + vectorWedge ell n +
          booleanContraction ell sliceQuadraticA +
        correctionCoeff 1 • sliceQuadraticA +
      correctionCoeff 2 • sliceInfinityQuadratic = 0 at htwo
  rw [hcontract] at htwo
  have hquad : SliceQuadraticEquationA quadMu ell n
      (correctionCoeff 1) (correctionCoeff 2) := by
    rw [SliceQuadraticEquationA]
    calc
      quadMu • sliceQuadraticA + vectorWedge ell n +
            correctionCoeff 1 • sliceQuadraticA +
          correctionCoeff 2 • sliceInfinityQuadratic =
        mu • sliceQuadraticA + vectorWedge ell n +
            (p + q) • sliceQuadraticA +
          correctionCoeff 1 • sliceQuadraticA +
          correctionCoeff 2 • sliceInfinityQuadratic := by
            dsimp [quadMu]
            module
      _ = 0 := htwo
  have htwo' := anfTwoProjection_congr_of_eval_eq heval'
  rw [anfTwoProjection_sliceTypeAFullModel,
    anfTwoProjection_sliceTangentModel] at htwo'
  change
    mu' • sliceQuadraticA + vectorWedge ell n' +
          booleanContraction ell sliceQuadraticA +
        correctionCoeff 1 • sliceQuadraticA +
      correctionCoeff 2 • sliceInfinityQuadratic = 0 at htwo'
  rw [hcontract] at htwo'
  have hquad' : SliceQuadraticEquationA quadMu' ell n'
      (correctionCoeff 1) (correctionCoeff 2) := by
    rw [SliceQuadraticEquationA]
    calc
      quadMu' • sliceQuadraticA + vectorWedge ell n' +
            correctionCoeff 1 • sliceQuadraticA +
          correctionCoeff 2 • sliceInfinityQuadratic =
        mu' • sliceQuadraticA + vectorWedge ell n' +
            (p + q) • sliceQuadraticA +
          correctionCoeff 1 • sliceQuadraticA +
          correctionCoeff 2 • sliceInfinityQuadratic := by
            dsimp [quadMu']
            module
      _ = 0 := htwo'
  have hquadMu : ell = 0 → quadMu = mu := by
    intro hell
    have hpqZero : p = 0 ∧ q = 0 := by
      apply sliceComplement_coefficients_zero
      rw [← hpq, hell]
    simp [quadMu, hpqZero.1, hpqZero.2]
  have hquadMu' : ell = 0 → quadMu' = mu' := by
    intro hell
    have hpqZero : p = 0 ∧ q = 0 := by
      apply sliceComplement_coefficients_zero
      rw [← hpq, hell]
    simp [quadMu', hpqZero.1, hpqZero.2]
  have hlinear := anfLinearProjection_congr_of_eval_eq heval
  rw [anfLinearProjection_sliceTypeAFullModel,
    anfLinearProjection_sliceTangentModel] at hlinear
  change sliceProductLinear mu nu ell n base
      (correctionCoeff 1) x y =
    sliceComplementLinear targetLinear + y • sliceU + x • sliceV at hlinear
  have hlinear' := anfLinearProjection_congr_of_eval_eq heval'
  rw [anfLinearProjection_sliceTypeAFullModel,
    anfLinearProjection_sliceTangentModel] at hlinear'
  change sliceProductLinear mu' nu' ell n' base
      (correctionCoeff 1) x' y' =
    sliceComplementLinear targetLinear + y' • sliceU + x' • sliceV at hlinear'
  have hlinearPair :
      sliceProductLinear mu nu ell n base (correctionCoeff 1) x y +
          sliceProductLinear mu' nu' ell n' base
            (correctionCoeff 1) x' y' =
        sliceTargetDifference x y x' y' := by
    rw [hlinear, hlinear']
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sliceTargetDifference]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  exact no_typeA_active_slice_pair hdistinct rfl rfl hcubic
    hquad hquad' hquadMu hquadMu' hlinearPair

/-- Two distinct active Type-B slice models cannot both equal slices of the
same zero-place target tangent. -/
theorem no_typeB_slice_model_pair
    {x y x' y' : F₂}
    (hdistinct : x ≠ x' ∨ y ≠ y')
    (leftConst rightConst correctionConst targetConst eps : F₂)
    (leftLinear rightLinear correctionLinear targetLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂)
    (hslice : ∀ z : Fin 6 → F₂,
      eval
          (sliceTypeBFullModel leftConst leftLinear rightConst rightLinear
            correctionConst correctionLinear correctionCoeff x y)
          (sliceAssignment x y z) =
        eval (sliceTangentModel targetConst targetLinear eps x y)
          (sliceAssignment x y z))
    (hslice' : ∀ z : Fin 6 → F₂,
      eval
          (sliceTypeBFullModel leftConst leftLinear rightConst rightLinear
            correctionConst correctionLinear correctionCoeff x' y')
          (sliceAssignment x' y' z) =
        eval (sliceTangentModel targetConst targetLinear eps x' y')
          (sliceAssignment x' y' z)) : False := by
  let ell := sliceComplementLinear leftLinear
  let m := sliceComplementLinear rightLinear
  let base := sliceComplementLinear correctionLinear
  let mu := leftConst + sliceAnchorValue leftLinear x y + x * y
  let mu' := leftConst + sliceAnchorValue leftLinear x' y' + x' * y'
  let nu := rightConst + sliceAnchorValue rightLinear x y + x * y
  let nu' := rightConst + sliceAnchorValue rightLinear x' y' + x' * y'
  let n := m + sliceVaryingLinear x y
  let n' := m + sliceVaryingLinear x' y'
  have heval := eval_eq_of_slice_eq
    (anchorsIndependent_sliceTypeBFullModel leftConst leftLinear
      rightConst rightLinear correctionConst correctionLinear
      correctionCoeff x y)
    (anchorsIndependent_sliceTangentModel targetConst targetLinear eps x y)
    hslice
  have heval' := eval_eq_of_slice_eq
    (anchorsIndependent_sliceTypeBFullModel leftConst leftLinear
      rightConst rightLinear correctionConst correctionLinear
      correctionCoeff x' y')
    (anchorsIndependent_sliceTangentModel targetConst targetLinear eps x' y')
    hslice'
  have hcubic := anfThreeProjection_congr_of_eval_eq heval
  rw [anfThreeProjection_sliceTypeBFullModel,
    anfThreeProjection_sliceTangentModel] at hcubic
  change vectorWedgeTwo ell sliceQuadraticB = 0 at hcubic
  have hell : ell = 0 := sliceQuadraticB_annihilator hcubic
  have htwo := anfTwoProjection_congr_of_eval_eq heval
  rw [anfTwoProjection_sliceTypeBFullModel,
    anfTwoProjection_sliceTangentModel] at htwo
  change
    mu • sliceQuadraticB + vectorWedge ell n +
          booleanContraction ell sliceQuadraticB +
        correctionCoeff 1 • sliceQuadraticA +
      correctionCoeff 2 • sliceInfinityQuadratic = 0 at htwo
  have hquad : SliceQuadraticEquationB mu ell n
      (correctionCoeff 1) (correctionCoeff 2) := by
    rw [hell, booleanContraction_zero] at htwo
    rw [SliceQuadraticEquationB, hell]
    simpa [vectorWedge] using htwo
  have htwo' := anfTwoProjection_congr_of_eval_eq heval'
  rw [anfTwoProjection_sliceTypeBFullModel,
    anfTwoProjection_sliceTangentModel] at htwo'
  change
    mu' • sliceQuadraticB + vectorWedge ell n' +
          booleanContraction ell sliceQuadraticB +
        correctionCoeff 1 • sliceQuadraticA +
      correctionCoeff 2 • sliceInfinityQuadratic = 0 at htwo'
  have hquad' : SliceQuadraticEquationB mu' ell n'
      (correctionCoeff 1) (correctionCoeff 2) := by
    rw [hell, booleanContraction_zero] at htwo'
    rw [SliceQuadraticEquationB, hell]
    simpa [vectorWedge] using htwo'
  have hlinear := anfLinearProjection_congr_of_eval_eq heval
  rw [anfLinearProjection_sliceTypeBFullModel,
    anfLinearProjection_sliceTangentModel] at hlinear
  change sliceProductLinear mu nu ell n base
      (correctionCoeff 1) x y =
    sliceComplementLinear targetLinear + y • sliceU + x • sliceV at hlinear
  have hlinear' := anfLinearProjection_congr_of_eval_eq heval'
  rw [anfLinearProjection_sliceTypeBFullModel,
    anfLinearProjection_sliceTangentModel] at hlinear'
  change sliceProductLinear mu' nu' ell n' base
      (correctionCoeff 1) x' y' =
    sliceComplementLinear targetLinear + y' • sliceU + x' • sliceV at hlinear'
  have hlinearPair :
      sliceProductLinear mu nu ell n base (correctionCoeff 1) x y +
          sliceProductLinear mu' nu' ell n' base
            (correctionCoeff 1) x' y' =
        sliceTargetDifference x y x' y' := by
    rw [hlinear, hlinear']
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sliceTargetDifference]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  exact no_typeB_active_slice_pair hdistinct rfl rfl hcubic
    hquad hquad' hlinearPair

theorem sliceInfinity_coefficients_zero
    {p q : F₂}
    (h : p • placeA 2 + q • placeB 2 = 0) :
    p = 0 ∧ q = 0 := by
  have hp := congrFun h (aCoord 3)
  have hq := congrFun h (bCoord 3)
  simp only [placeA, Fin.isValue, Matrix.cons_val, Matrix.smul_cons, smul_eq_mul, mul_zero,
    mul_one, Matrix.smul_empty, placeB, aCoord, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
    Fin.reduceFinMk, Pi.add_apply, add_zero, Pi.zero_apply, bCoord, Nat.reduceAdd, zero_add
    ] at hp hq
  exact ⟨hp, hq⟩

theorem no_typeInfinity_slice_model_pair
    {x y x' y' : F₂}
    (hdistinct : x ≠ x' ∨ y ≠ y')
    (leftConst rightConst correctionConst targetConst eps : F₂)
    (leftLinear rightLinear correctionLinear targetLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂)
    (hslice : ∀ z : Fin 6 → F₂,
      eval
          (sliceTypeInfinityFullModel leftConst leftLinear
            rightConst rightLinear correctionConst correctionLinear
            correctionCoeff x y)
          (sliceAssignment x y z) =
        eval (sliceTangentModel targetConst targetLinear eps x y)
          (sliceAssignment x y z))
    (hslice' : ∀ z : Fin 6 → F₂,
      eval
          (sliceTypeInfinityFullModel leftConst leftLinear
            rightConst rightLinear correctionConst correctionLinear
            correctionCoeff x' y')
          (sliceAssignment x' y' z) =
        eval (sliceTangentModel targetConst targetLinear eps x' y')
          (sliceAssignment x' y' z)) : False := by
  let ell := sliceComplementLinear leftLinear
  let n := sliceComplementLinear rightLinear
  let base := sliceComplementLinear correctionLinear
  let mu := leftConst + sliceAnchorValue leftLinear x y + x * y
  let mu' := leftConst + sliceAnchorValue leftLinear x' y' + x' * y'
  let nu := rightConst + sliceAnchorValue rightLinear x y
  let nu' := rightConst + sliceAnchorValue rightLinear x' y'
  have heval := eval_eq_of_slice_eq
    (anchorsIndependent_sliceTypeInfinityFullModel leftConst leftLinear
      rightConst rightLinear correctionConst correctionLinear
      correctionCoeff x y)
    (anchorsIndependent_sliceTangentModel targetConst targetLinear eps x y)
    hslice
  have heval' := eval_eq_of_slice_eq
    (anchorsIndependent_sliceTypeInfinityFullModel leftConst leftLinear
      rightConst rightLinear correctionConst correctionLinear
      correctionCoeff x' y')
    (anchorsIndependent_sliceTangentModel targetConst targetLinear eps x' y')
    hslice'
  have hcubic := anfThreeProjection_congr_of_eval_eq heval
  rw [anfThreeProjection_sliceTypeInfinityFullModel,
    anfThreeProjection_sliceTangentModel] at hcubic
  change vectorWedgeTwo ell sliceInfinityQuadratic = 0 at hcubic
  rcases sliceInfinityQuadratic_annihilator hcubic with ⟨p, q, hpq⟩
  have hcontract :
      booleanContraction ell sliceInfinityQuadratic =
        (p + q) • sliceInfinityQuadratic := by
    rw [hpq]
    exact booleanContraction_sliceInfinity_sliceInfinityQuadratic p q
  let quadMu := mu + p + q
  let quadMu' := mu' + p + q
  have htwo := anfTwoProjection_congr_of_eval_eq heval
  rw [anfTwoProjection_sliceTypeInfinityFullModel,
    anfTwoProjection_sliceTangentModel] at htwo
  change
    mu • sliceInfinityQuadratic + vectorWedge ell n +
          booleanContraction ell sliceInfinityQuadratic +
        correctionCoeff 1 • sliceQuadraticA +
      correctionCoeff 2 • sliceInfinityQuadratic = 0 at htwo
  rw [hcontract] at htwo
  have hquad : SliceQuadraticEquationInfinity quadMu ell n
      (correctionCoeff 1) (correctionCoeff 2) := by
    rw [SliceQuadraticEquationInfinity]
    calc
      quadMu • sliceInfinityQuadratic + vectorWedge ell n +
            correctionCoeff 1 • sliceQuadraticA +
          correctionCoeff 2 • sliceInfinityQuadratic =
        mu • sliceInfinityQuadratic + vectorWedge ell n +
            (p + q) • sliceInfinityQuadratic +
          correctionCoeff 1 • sliceQuadraticA +
          correctionCoeff 2 • sliceInfinityQuadratic := by
            dsimp [quadMu]
            module
      _ = 0 := htwo
  have htwo' := anfTwoProjection_congr_of_eval_eq heval'
  rw [anfTwoProjection_sliceTypeInfinityFullModel,
    anfTwoProjection_sliceTangentModel] at htwo'
  change
    mu' • sliceInfinityQuadratic + vectorWedge ell n +
          booleanContraction ell sliceInfinityQuadratic +
        correctionCoeff 1 • sliceQuadraticA +
      correctionCoeff 2 • sliceInfinityQuadratic = 0 at htwo'
  rw [hcontract] at htwo'
  have hquad' : SliceQuadraticEquationInfinity quadMu' ell n
      (correctionCoeff 1) (correctionCoeff 2) := by
    rw [SliceQuadraticEquationInfinity]
    calc
      quadMu' • sliceInfinityQuadratic + vectorWedge ell n +
            correctionCoeff 1 • sliceQuadraticA +
          correctionCoeff 2 • sliceInfinityQuadratic =
        mu' • sliceInfinityQuadratic + vectorWedge ell n +
            (p + q) • sliceInfinityQuadratic +
          correctionCoeff 1 • sliceQuadraticA +
          correctionCoeff 2 • sliceInfinityQuadratic := by
            dsimp [quadMu']
            module
      _ = 0 := htwo'
  have hquadMu : ell = 0 → quadMu = mu := by
    intro hell
    have hpqZero : p = 0 ∧ q = 0 := by
      apply sliceInfinity_coefficients_zero
      rw [← hpq, hell]
    simp [quadMu, hpqZero.1, hpqZero.2]
  have hquadMu' : ell = 0 → quadMu' = mu' := by
    intro hell
    have hpqZero : p = 0 ∧ q = 0 := by
      apply sliceInfinity_coefficients_zero
      rw [← hpq, hell]
    simp [quadMu', hpqZero.1, hpqZero.2]
  have hlinear := anfLinearProjection_congr_of_eval_eq heval
  rw [anfLinearProjection_sliceTypeInfinityFullModel,
    anfLinearProjection_sliceTangentModel] at hlinear
  change sliceProductLinear mu nu ell n base
      (correctionCoeff 1) x y =
    sliceComplementLinear targetLinear + y • sliceU + x • sliceV at hlinear
  have hlinear' := anfLinearProjection_congr_of_eval_eq heval'
  rw [anfLinearProjection_sliceTypeInfinityFullModel,
    anfLinearProjection_sliceTangentModel] at hlinear'
  change sliceProductLinear mu' nu' ell n base
      (correctionCoeff 1) x' y' =
    sliceComplementLinear targetLinear + y' • sliceU + x' • sliceV at hlinear'
  have hlinearPair :
      sliceProductLinear mu nu ell n base (correctionCoeff 1) x y +
          sliceProductLinear mu' nu' ell n base
            (correctionCoeff 1) x' y' =
        sliceTargetDifference x y x' y' := by
    rw [hlinear, hlinear']
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sliceTargetDifference]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  exact no_typeInfinity_active_slice_pair hdistinct hcubic hquad hquad'
    hquadMu hquadMu' hlinearPair

theorem exists_representedLowFactor_of_mem
    {p : ANF 8} (hp : p ∈ rationalLowSpace) :
    ∃ (a : F₂) (ell : LinearForm) (alpha : Fin 3 → F₂),
      p = representedLowFactor a ell alpha := by
  rcases Submodule.mem_sup.mp hp with ⟨u, hu, v, hv, rfl⟩
  rcases exists_affineANF_of_mem hu with ⟨a, ell, rfl⟩
  rcases (mem_rationalTargetSpace_iff v).mp hv with ⟨alpha, rfl⟩
  exact ⟨a, ell, alpha, rfl⟩

theorem eval_sliceTypeAFullModel_eq_normalized
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) (z : Fin 6 → F₂) :
    eval
        (sliceTypeAFullModel leftConst leftLinear rightConst rightLinear
          correctionConst correctionLinear correctionCoeff x y)
        (sliceAssignment x y z) =
      eval
        (representedLowFactor leftConst leftLinear (rationalSingleton 0) *
            representedLowFactor rightConst rightLinear
              (rationalSingleton 1) +
          representedLowFactor correctionConst correctionLinear
            correctionCoeff)
        (sliceAssignment x y z) := by
  simp only [sliceTypeAFullModel, eval_add', eval_mul']
  rw [eval_sliceZeroFactorModel, eval_sliceOneFactorModel,
    eval_sliceCorrectionModel]

theorem eval_sliceTypeBFullModel_eq_normalized
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) (z : Fin 6 → F₂) :
    eval
        (sliceTypeBFullModel leftConst leftLinear rightConst rightLinear
          correctionConst correctionLinear correctionCoeff x y)
        (sliceAssignment x y z) =
      eval
        (representedLowFactor leftConst leftLinear (rationalSingleton 0) *
            representedLowFactor rightConst rightLinear
              (rationalSingleton 1 + rationalSingleton 2) +
          representedLowFactor correctionConst correctionLinear
            correctionCoeff)
        (sliceAssignment x y z) := by
  simp only [sliceTypeBFullModel, eval_add', eval_mul']
  rw [eval_sliceZeroFactorModel, eval_sliceTypeBFactorModel,
    eval_sliceCorrectionModel]

theorem eval_sliceTypeInfinityFullModel_eq_normalized
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) (z : Fin 6 → F₂) :
    eval
        (sliceTypeInfinityFullModel leftConst leftLinear
          rightConst rightLinear correctionConst correctionLinear
          correctionCoeff x y)
        (sliceAssignment x y z) =
      eval
        (representedLowFactor leftConst leftLinear (rationalSingleton 0) *
            representedLowFactor rightConst rightLinear
              (rationalSingleton 2) +
          representedLowFactor correctionConst correctionLinear
            correctionCoeff)
        (sliceAssignment x y z) := by
  simp only [sliceTypeInfinityFullModel, eval_add', eval_mul']
  rw [eval_sliceZeroFactorModel, eval_sliceInfinityFactorModel,
    eval_sliceCorrectionModel]

theorem typeA_slice_eq_of_active
    {factor target : ANF 8}
    {delta rho sigma : F₂}
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂)
    (targetConst eps : F₂) (targetLinear : LinearForm)
    {x y : F₂}
    (hsource : target =
      (representedLowFactor leftConst leftLinear (rationalSingleton 0) *
          representedLowFactor rightConst rightLinear
            (rationalSingleton 1) +
        representedLowFactor correctionConst correctionLinear
          correctionCoeff) * factor)
    (htarget : target =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (hfactor : factor =
      affineANF delta (rho • sliceX + sigma • sliceY) +
        rationalANF (rationalSingleton 0))
    (hactive : feedbackCorner delta rho sigma x y = 1) :
    ∀ z : Fin 6 → F₂,
      eval
          (sliceTypeAFullModel leftConst leftLinear rightConst rightLinear
            correctionConst correctionLinear correctionCoeff x y)
          (sliceAssignment x y z) =
        eval (sliceTangentModel targetConst targetLinear eps x y)
          (sliceAssignment x y z) := by
  intro z
  let w := sliceAssignment x y z
  calc
    eval
        (sliceTypeAFullModel leftConst leftLinear rightConst rightLinear
          correctionConst correctionLinear correctionCoeff x y) w =
      eval
        (representedLowFactor leftConst leftLinear (rationalSingleton 0) *
            representedLowFactor rightConst rightLinear
              (rationalSingleton 1) +
          representedLowFactor correctionConst correctionLinear
            correctionCoeff) w :=
      eval_sliceTypeAFullModel_eq_normalized leftConst leftLinear
        rightConst rightLinear correctionConst correctionLinear
        correctionCoeff x y z
    _ = eval target w := by
      have hs := congrArg (fun p : ANF 8 => eval p w) hsource
      rw [eval_mul', eval_zero_place_feedback hfactor,
        hactive, mul_one] at hs
      exact hs.symm
    _ = eval (sliceTangentModel targetConst targetLinear eps x y) w := by
      rw [htarget]
      exact (eval_sliceTangentModel targetConst targetLinear eps x y z).symm

theorem typeB_slice_eq_of_active
    {factor target : ANF 8}
    {delta rho sigma : F₂}
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂)
    (targetConst eps : F₂) (targetLinear : LinearForm)
    {x y : F₂}
    (hsource : target =
      (representedLowFactor leftConst leftLinear (rationalSingleton 0) *
          representedLowFactor rightConst rightLinear
            (rationalSingleton 1 + rationalSingleton 2) +
        representedLowFactor correctionConst correctionLinear
          correctionCoeff) * factor)
    (htarget : target =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (hfactor : factor =
      affineANF delta (rho • sliceX + sigma • sliceY) +
        rationalANF (rationalSingleton 0))
    (hactive : feedbackCorner delta rho sigma x y = 1) :
    ∀ z : Fin 6 → F₂,
      eval
          (sliceTypeBFullModel leftConst leftLinear rightConst rightLinear
            correctionConst correctionLinear correctionCoeff x y)
          (sliceAssignment x y z) =
        eval (sliceTangentModel targetConst targetLinear eps x y)
          (sliceAssignment x y z) := by
  intro z
  let w := sliceAssignment x y z
  calc
    eval
        (sliceTypeBFullModel leftConst leftLinear rightConst rightLinear
          correctionConst correctionLinear correctionCoeff x y) w =
      eval
        (representedLowFactor leftConst leftLinear (rationalSingleton 0) *
            representedLowFactor rightConst rightLinear
              (rationalSingleton 1 + rationalSingleton 2) +
          representedLowFactor correctionConst correctionLinear
            correctionCoeff) w :=
      eval_sliceTypeBFullModel_eq_normalized leftConst leftLinear
        rightConst rightLinear correctionConst correctionLinear
        correctionCoeff x y z
    _ = eval target w := by
      have hs := congrArg (fun p : ANF 8 => eval p w) hsource
      rw [eval_mul', eval_zero_place_feedback hfactor,
        hactive, mul_one] at hs
      exact hs.symm
    _ = eval (sliceTangentModel targetConst targetLinear eps x y) w := by
      rw [htarget]
      exact (eval_sliceTangentModel targetConst targetLinear eps x y z).symm

theorem typeInfinity_slice_eq_of_active
    {factor target : ANF 8}
    {delta rho sigma : F₂}
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂)
    (targetConst eps : F₂) (targetLinear : LinearForm)
    {x y : F₂}
    (hsource : target =
      (representedLowFactor leftConst leftLinear (rationalSingleton 0) *
          representedLowFactor rightConst rightLinear
            (rationalSingleton 2) +
        representedLowFactor correctionConst correctionLinear
          correctionCoeff) * factor)
    (htarget : target =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (hfactor : factor =
      affineANF delta (rho • sliceX + sigma • sliceY) +
        rationalANF (rationalSingleton 0))
    (hactive : feedbackCorner delta rho sigma x y = 1) :
    ∀ z : Fin 6 → F₂,
      eval
          (sliceTypeInfinityFullModel leftConst leftLinear
            rightConst rightLinear correctionConst correctionLinear
            correctionCoeff x y)
          (sliceAssignment x y z) =
        eval (sliceTangentModel targetConst targetLinear eps x y)
          (sliceAssignment x y z) := by
  intro z
  let w := sliceAssignment x y z
  calc
    eval
        (sliceTypeInfinityFullModel leftConst leftLinear
          rightConst rightLinear correctionConst correctionLinear
          correctionCoeff x y) w =
      eval
        (representedLowFactor leftConst leftLinear (rationalSingleton 0) *
            representedLowFactor rightConst rightLinear
              (rationalSingleton 2) +
          representedLowFactor correctionConst correctionLinear
            correctionCoeff) w :=
      eval_sliceTypeInfinityFullModel_eq_normalized leftConst leftLinear
        rightConst rightLinear correctionConst correctionLinear
        correctionCoeff x y z
    _ = eval target w := by
      have hs := congrArg (fun p : ANF 8 => eval p w) hsource
      rw [eval_mul', eval_zero_place_feedback hfactor,
        hactive, mul_one] at hs
      exact hs.symm
    _ = eval (sliceTangentModel targetConst targetLinear eps x y) w := by
      rw [htarget]
      exact (eval_sliceTangentModel targetConst targetLinear eps x y z).symm

theorem f2_add_one_ne_self (a : F₂) : a + 1 ≠ a := by
  rcases f2_eq_zero_or_one a with rfl | rfl <;> decide

/-- Extract a concrete pair of distinct active corners from the three-corner
statement. -/
theorem exists_distinct_active_corner_pair
    {delta rho sigma : F₂}
    (h : ExactlyThreeActiveCorners delta rho sigma) :
    ∃ x y x' y' : F₂,
      (x ≠ x' ∨ y ≠ y') ∧
      feedbackCorner delta rho sigma x y = 1 ∧
      feedbackCorner delta rho sigma x' y' = 1 := by
  rcases h with ⟨x₀, y₀, _hzero, hactive⟩
  refine ⟨x₀ + 1, y₀, x₀, y₀ + 1, ?_, ?_, ?_⟩
  · exact Or.inl (f2_add_one_ne_self x₀)
  · apply hactive
    exact Or.inl (f2_add_one_ne_self x₀)
  · apply hactive
    exact Or.inr (f2_add_one_ne_self y₀)

theorem no_normalized_typeA_feedback_target
    {factor target : ANF 8}
    {delta rho sigma : F₂}
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂)
    (targetConst eps : F₂) (targetLinear : LinearForm)
    (hsource : target =
      (representedLowFactor leftConst leftLinear (rationalSingleton 0) *
          representedLowFactor rightConst rightLinear
            (rationalSingleton 1) +
        representedLowFactor correctionConst correctionLinear
          correctionCoeff) * factor)
    (htarget : target =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (hfactor : factor =
      affineANF delta (rho • sliceX + sigma • sliceY) +
        rationalANF (rationalSingleton 0))
    (hright : target * factor = target) : False := by
  have hcorners := exactlyThreeActiveCorners_of_right_idempotence
    htarget hfactor hright
  rcases exists_distinct_active_corner_pair hcorners with
    ⟨x, y, x', y', hdistinct, hactive, hactive'⟩
  apply no_typeA_slice_model_pair hdistinct leftConst rightConst
    correctionConst targetConst eps leftLinear rightLinear
    correctionLinear targetLinear correctionCoeff
  · exact typeA_slice_eq_of_active leftConst leftLinear rightConst
      rightLinear correctionConst correctionLinear correctionCoeff
      targetConst eps targetLinear hsource htarget hfactor hactive
  · exact typeA_slice_eq_of_active leftConst leftLinear rightConst
      rightLinear correctionConst correctionLinear correctionCoeff
      targetConst eps targetLinear hsource htarget hfactor hactive'

theorem no_normalized_typeB_feedback_target
    {factor target : ANF 8}
    {delta rho sigma : F₂}
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂)
    (targetConst eps : F₂) (targetLinear : LinearForm)
    (hsource : target =
      (representedLowFactor leftConst leftLinear (rationalSingleton 0) *
          representedLowFactor rightConst rightLinear
            (rationalSingleton 1 + rationalSingleton 2) +
        representedLowFactor correctionConst correctionLinear
          correctionCoeff) * factor)
    (htarget : target =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (hfactor : factor =
      affineANF delta (rho • sliceX + sigma • sliceY) +
        rationalANF (rationalSingleton 0))
    (hright : target * factor = target) : False := by
  have hcorners := exactlyThreeActiveCorners_of_right_idempotence
    htarget hfactor hright
  rcases exists_distinct_active_corner_pair hcorners with
    ⟨x, y, x', y', hdistinct, hactive, hactive'⟩
  apply no_typeB_slice_model_pair hdistinct leftConst rightConst
    correctionConst targetConst eps leftLinear rightLinear
    correctionLinear targetLinear correctionCoeff
  · exact typeB_slice_eq_of_active leftConst leftLinear rightConst
      rightLinear correctionConst correctionLinear correctionCoeff
      targetConst eps targetLinear hsource htarget hfactor hactive
  · exact typeB_slice_eq_of_active leftConst leftLinear rightConst
      rightLinear correctionConst correctionLinear correctionCoeff
      targetConst eps targetLinear hsource htarget hfactor hactive'

theorem no_normalized_typeInfinity_feedback_target
    {factor target : ANF 8}
    {delta rho sigma : F₂}
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂)
    (targetConst eps : F₂) (targetLinear : LinearForm)
    (hsource : target =
      (representedLowFactor leftConst leftLinear (rationalSingleton 0) *
          representedLowFactor rightConst rightLinear
            (rationalSingleton 2) +
        representedLowFactor correctionConst correctionLinear
          correctionCoeff) * factor)
    (htarget : target =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (hfactor : factor =
      affineANF delta (rho • sliceX + sigma • sliceY) +
        rationalANF (rationalSingleton 0))
    (hright : target * factor = target) : False := by
  have hcorners := exactlyThreeActiveCorners_of_right_idempotence
    htarget hfactor hright
  rcases exists_distinct_active_corner_pair hcorners with
    ⟨x, y, x', y', hdistinct, hactive, hactive'⟩
  apply no_typeInfinity_slice_model_pair hdistinct leftConst rightConst
    correctionConst targetConst eps leftLinear rightLinear
    correctionLinear targetLinear correctionCoeff
  · exact typeInfinity_slice_eq_of_active leftConst leftLinear rightConst
      rightLinear correctionConst correctionLinear correctionCoeff
      targetConst eps targetLinear hsource htarget hfactor hactive
  · exact typeInfinity_slice_eq_of_active leftConst leftLinear rightConst
      rightLinear correctionConst correctionLinear correctionCoeff
      targetConst eps targetLinear hsource htarget hfactor hactive'

/-- After the two main slice exclusions, the only zero-anchored seed-plane
representative that can remain is the infinity singleton. -/
theorem zeroAnchored_seed_second_is_infinity
    {g correction factor target : ANF 8}
    {targetConst eps delta rho sigma : F₂}
    {targetLinear : LinearForm}
    (hseed : ZeroAnchoredQuarticSeedForm g correction)
    (hsource : target = (g + correction) * factor)
    (htarget : target =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (hfactor : factor =
      affineANF delta (rho • sliceX + sigma • sliceY) +
        rationalANF (rationalSingleton 0))
    (hright : target * factor = target) :
    ∃ (leftConst rightConst correctionConst : F₂)
      (leftLinear rightLinear correctionLinear : LinearForm)
      (correctionCoeff : Fin 3 → F₂),
      target =
        (representedLowFactor leftConst leftLinear (rationalSingleton 0) *
            representedLowFactor rightConst rightLinear
              (rationalSingleton 2) +
          representedLowFactor correctionConst correctionLinear
            correctionCoeff) * factor := by
  rcases hseed with
    ⟨normalizedSeed, normalizedCorrection, leftConst, rightConst,
      leftLinear, rightLinear, zeta, hnormalizedSeed,
      hnormalizedCorrectionLow, hnormalize, htype⟩
  rcases exists_representedLowFactor_of_mem hnormalizedCorrectionLow with
    ⟨correctionConst, correctionLinear, correctionCoeff,
      hnormalizedCorrection⟩
  have hnormalizedSource : target =
      (representedLowFactor leftConst leftLinear (rationalSingleton 0) *
          representedLowFactor rightConst rightLinear zeta +
        representedLowFactor correctionConst correctionLinear
          correctionCoeff) * factor := by
    rw [hnormalizedCorrection] at hnormalize
    rw [hsource, hnormalize, hnormalizedSeed]
  rcases htype with hzetaOne | hzetaInfinity | hzetaB
  · exfalso
    apply no_normalized_typeA_feedback_target leftConst leftLinear
      rightConst rightLinear correctionConst correctionLinear
      correctionCoeff targetConst eps targetLinear
    · simpa [hzetaOne] using hnormalizedSource
    · exact htarget
    · exact hfactor
    · exact hright
  · refine ⟨leftConst, rightConst, correctionConst, leftLinear,
      rightLinear, correctionLinear, correctionCoeff, ?_⟩
    simpa [hzetaInfinity] using hnormalizedSource
  · exfalso
    apply no_normalized_typeB_feedback_target leftConst leftLinear
      rightConst rightLinear correctionConst correctionLinear
      correctionCoeff targetConst eps targetLinear
    · simpa [hzetaB] using hnormalizedSource
    · exact htarget
    · exact hfactor
    · exact hright

/-- Complete zero-place quartic exclusion: all three complementary seed
directions are impossible. -/
theorem no_zeroAnchored_quartic_feedback_target
    {g correction factor target : ANF 8}
    {targetConst eps delta rho sigma : F₂}
    {targetLinear : LinearForm}
    (hseed : ZeroAnchoredQuarticSeedForm g correction)
    (hsource : target = (g + correction) * factor)
    (htarget : target =
      affineANF targetConst targetLinear +
        targetANF (rationalTangentAt 0 eps))
    (hfactor : factor =
      affineANF delta (rho • sliceX + sigma • sliceY) +
        rationalANF (rationalSingleton 0))
    (hright : target * factor = target) : False := by
  rcases zeroAnchored_seed_second_is_infinity hseed hsource htarget
      hfactor hright with
    ⟨leftConst, rightConst, correctionConst, leftLinear, rightLinear,
      correctionLinear, correctionCoeff, hnormalizedSource⟩
  exact no_normalized_typeInfinity_feedback_target leftConst leftLinear
    rightConst rightLinear correctionConst correctionLinear correctionCoeff
    targetConst eps targetLinear hnormalizedSource htarget hfactor hright

end

end N4
end UnrestrictedBooleanMul
