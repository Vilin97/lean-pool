/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.SliceModels

/-!
# Homogeneous projections of the slice models

These lemmas calculate only the degree-three, degree-two, and degree-one
parts used by the manuscript.  The fixed coordinate checks concern the two
explicit complementary quadratics; there is no search over circuits or
Boolean functions.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

theorem anfLinearProjection_linearANF (ell : LinearForm) :
    anfLinearProjection (linearANF ell) = ell := by
  funext j
  simp [linearANF, anfLinearProjection_X]

theorem anfLinearProjection_affineANF (a : F₂) (ell : LinearForm) :
    anfLinearProjection (affineANF a ell) = ell := by
  rw [affineANF, map_add, map_smul, anfLinearProjection_one,
    smul_zero, zero_add, anfLinearProjection_linearANF]

theorem eval_linearANF_supportAssignment
    (ell : LinearForm) (t : Finset (Fin 8)) :
    eval (linearANF ell) (supportAssignment t) = ∑ i ∈ t, ell i := by
  rw [eval_linearANF_formula]
  simp [supportAssignment]

/-- The first finite difference at zero in one coordinate direction. -/
@[expose]
def singlePolarMap (i : Fin 8) : ANF 8 →ₗ[F₂] F₂ :=
  sparseEvalMap ∅ + sparseEvalMap {i}

/-- Extract the coefficient of one linear monomial. -/
@[expose]
def singleCoeffMap (i : Fin 8) : ANF 8 →ₗ[F₂] F₂ where
  toFun p := p.coeff ⟨{i}⟩
  map_add' p q := by simp
  map_smul' a p := by simp

private theorem subset_single_polar_identity
    (s : Finset (Fin 8)) (i : Fin 8) :
    (if s ⊆ ∅ then (1 : F₂) else 0) +
      (if s ⊆ {i} then 1 else 0) =
        if s = {i} then 1 else 0 := by
  by_cases hsub : s ⊆ {i}
  · by_cases hi : i ∈ s
    · have heq : s = {i} := by
        apply Finset.Subset.antisymm hsub
        simp [hi]
      subst s
      simp
    · have heq : s = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hxi : x = i := by simpa using hsub hx
        subst x
        exact hi hx
      subst s
      simp; ring_nf; simp [N3Certificate.two_eq_zero_f2]
  · have hEmpty : ¬s ⊆ ∅ := fun h => hsub (h.trans (by simp))
    have hne : s ≠ {i} := fun h => hsub (by rw [h])
    simp [hsub, hEmpty, hne]

theorem singlePolarMap_eq_singleCoeffMap (i : Fin 8) :
    singlePolarMap i = singleCoeffMap i := by
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext
  intro c
  change singlePolarMap i (MonoidAlgebra.single s c) =
    singleCoeffMap i (MonoidAlgebra.single s c)
  simp only [singlePolarMap, LinearMap.add_apply]
  rw [sparseEvalMap_single, sparseEvalMap_single]
  change c * (if s.vars ⊆ ∅ then 1 else 0) +
      c * (if s.vars ⊆ {i} then 1 else 0) =
        (MonoidAlgebra.single s c : ANF 8).coeff ⟨{i}⟩
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hid := subset_single_polar_identity s.vars i
  have heq : s = ⟨{i}⟩ ↔ s.vars = {i} := by
    constructor
    · intro h
      simp [h]
    · exact Monomial.ext
  calc
    _ = c * ((if s.vars ⊆ ∅ then 1 else 0) +
        (if s.vars ⊆ {i} then 1 else 0)) := by ring
    _ = c * (if s.vars = {i} then 1 else 0) := by rw [hid]
    _ = if s = ⟨{i}⟩ then c else 0 := by
      by_cases hs : s.vars = {i}
      · rw [ite_eq_left hs, ite_eq_left (heq.mpr hs), mul_one]
      · rw [ite_eq_right hs, ite_eq_right (fun h => hs (heq.mp h)), mul_zero]

/-- Equality of Boolean functions determines the homogeneous linear
projection. -/
theorem anfLinearProjection_congr_of_eval_eq {p q : ANF 8}
    (h : ∀ x, eval p x = eval q x) :
    anfLinearProjection p = anfLinearProjection q := by
  exact congrArg anfLinearProjection (eval_injective 8 (funext h))

theorem anfLinearProjection_linear_mul_linear
    (ell m : LinearForm) :
    anfLinearProjection (linearANF ell * linearANF m) =
      pointwiseLinearProduct ell m := by
  funext i
  have hp := congrArg (fun L : ANF 8 →ₗ[F₂] F₂ =>
      L (linearANF ell * linearANF m))
    (singlePolarMap_eq_singleCoeffMap i)
  change singlePolarMap i (linearANF ell * linearANF m) =
    anfLinearProjection (linearANF ell * linearANF m) i at hp
  rw [← hp]
  change eval (linearANF ell * linearANF m) (supportAssignment ∅) +
      eval (linearANF ell * linearANF m) (supportAssignment {i}) = _
  simp [eval_mul', supportAssignment, pointwiseLinearProduct]

theorem anfLinearProjection_affine_mul_affine
    (a b : F₂) (ell m : LinearForm) :
    anfLinearProjection (affineANF a ell * affineANF b m) =
      a • m + b • ell + pointwiseLinearProduct ell m := by
  rw [affineANF, affineANF]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, map_add,
    map_smul, anfLinearProjection_one, anfLinearProjection_linearANF,
    anfLinearProjection_linear_mul_linear, smul_zero, zero_add]
  module

theorem anfThreeProjection_linear_mul_quadratic
    (ell m n : LinearForm) :
    anfThreeProjection
        (linearANF ell * (linearANF m * linearANF n)) =
      vectorWedgeTwo ell (vectorWedge m n) := by
  funext i j k
  change
    (if ({i, j, k} : Finset (Fin 8)).card = 3 then
      (linearANF ell * (linearANF m * linearANF n)).coeff
        ⟨{i, j, k}⟩ else 0) =
      vectorWedgeTwo ell (vectorWedge m n) i j k
  by_cases hcard : ({i, j, k} : Finset (Fin 8)).card = 3
  · have hij : i ≠ j := by
      intro heq
      subst j
      have hle : ({i, k} : Finset (Fin 8)).card ≤ 2 :=
        Finset.card_le_two
      have hc : ({i, k} : Finset (Fin 8)).card = 3 := by
        simpa using hcard
      omega
    have hik : i ≠ k := by
      intro heq
      subst k
      have hle : ({j, i} : Finset (Fin 8)).card ≤ 2 :=
        Finset.card_le_two
      have hc : ({j, i} : Finset (Fin 8)).card = 3 := by
        simpa using hcard
      omega
    have hjk : j ≠ k := by
      intro heq
      subst k
      have hle : ({i, j} : Finset (Fin 8)).card ≤ 2 :=
        Finset.card_le_two
      have hc : ({i, j} : Finset (Fin 8)).card = 3 := by
        simpa using hcard
      omega
    rw [ite_eq_left hcard]
    change (linearANF ell * (linearANF m * linearANF n)).coeff
        ⟨{i, j, k}⟩ = _
    have hp := congrArg (fun L : ANF 8 →ₗ[F₂] F₂ =>
        L (linearANF ell * (linearANF m * linearANF n)))
      (triplePolarMap_eq_tripleCoeffMap i j k hij hik hjk)
    change triplePolarMap i j k
        (linearANF ell * (linearANF m * linearANF n)) =
      (linearANF ell * (linearANF m * linearANF n)).coeff
        ⟨{i, j, k}⟩ at hp
    rw [← hp]
    change
      eval (linearANF ell * (linearANF m * linearANF n))
          (supportAssignment ∅) +
        eval (linearANF ell * (linearANF m * linearANF n))
          (supportAssignment {i}) +
        eval (linearANF ell * (linearANF m * linearANF n))
          (supportAssignment {j}) +
        eval (linearANF ell * (linearANF m * linearANF n))
          (supportAssignment {k}) +
        eval (linearANF ell * (linearANF m * linearANF n))
          (supportAssignment {i, j}) +
        eval (linearANF ell * (linearANF m * linearANF n))
          (supportAssignment {i, k}) +
        eval (linearANF ell * (linearANF m * linearANF n))
          (supportAssignment {j, k}) +
        eval (linearANF ell * (linearANF m * linearANF n))
          (supportAssignment {i, j, k}) = _
    simp only [eval_mul', eval_linearANF_supportAssignment]
    simp [hij, hik, hjk, vectorWedgeTwo, vectorWedge]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2]
  · rw [ite_eq_right hcard]
    by_cases hij : i = j
    · subst j
      simp [vectorWedgeTwo, vectorWedge]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    by_cases hik : i = k
    · subst k
      simp [vectorWedgeTwo, vectorWedge]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    by_cases hjk : j = k
    · subst k
      simp [vectorWedgeTwo, vectorWedge]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    · have : ({i, j, k} : Finset (Fin 8)).card = 3 := by
        simp [hij, hik, hjk]
      exact (hcard this).elim

theorem anfThreeProjection_linear_mul_sliceQuadraticA
    (ell : LinearForm) :
    anfThreeProjection (linearANF ell * sliceQuadraticAANF) =
      vectorWedgeTwo ell sliceQuadraticA := by
  exact anfThreeProjection_linear_mul_quadratic
    ell sliceABar sliceBBar

theorem anfThreeProjection_linear_mul_sliceInfinityQuadratic
    (ell : LinearForm) :
    anfThreeProjection (linearANF ell * sliceInfinityQuadraticANF) =
      vectorWedgeTwo ell sliceInfinityQuadratic := by
  exact anfThreeProjection_linear_mul_quadratic
    ell (placeA 2) (placeB 2)

theorem anfTwoProjection_linear_mul_quadratic
    (ell m n : LinearForm)
    (hdisjoint : pointwiseLinearProduct m n = 0) :
    anfTwoProjection
        (linearANF ell * (linearANF m * linearANF n)) =
      booleanContraction ell (vectorWedge m n) := by
  funext i j
  change (if i = j then 0 else
      (linearANF ell * (linearANF m * linearANF n)).coeff
        ⟨{i, j}⟩) =
    booleanContraction ell (vectorWedge m n) i j
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    simp [booleanContraction, vectorWedge]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  · rw [ite_eq_right hij]
    have hp := congrArg (fun L : ANF 8 →ₗ[F₂] F₂ =>
        L (linearANF ell * (linearANF m * linearANF n)))
      (pairPolarMap_eq_pairCoeffMap i j hij)
    change pairPolarMap i j
        (linearANF ell * (linearANF m * linearANF n)) =
      (linearANF ell * (linearANF m * linearANF n)).coeff
        ⟨{i, j}⟩ at hp
    rw [← hp]
    change
      eval (linearANF ell * (linearANF m * linearANF n))
          (supportAssignment ∅) +
        eval (linearANF ell * (linearANF m * linearANF n))
          (supportAssignment {i}) +
        eval (linearANF ell * (linearANF m * linearANF n))
          (supportAssignment {j}) +
        eval (linearANF ell * (linearANF m * linearANF n))
          (supportAssignment {i, j}) = _
    have hi := congrFun hdisjoint i
    have hj := congrFun hdisjoint j
    simp only [pointwiseLinearProduct, Pi.zero_apply] at hi hj
    simp only [eval_mul', eval_linearANF_supportAssignment]
    simp [hij, booleanContraction, vectorWedge]
    ring_nf
    simp only [N3Certificate.two_eq_zero_f2, mul_zero, add_zero]
    rw [mul_assoc (ell i) (m j) (n j), hj, mul_zero, hi,
      zero_mul, zero_add]
    ring

theorem anfLinearProjection_linear_mul_quadratic
    (ell m n : LinearForm)
    (hdisjoint : pointwiseLinearProduct m n = 0) :
    anfLinearProjection
        (linearANF ell * (linearANF m * linearANF n)) = 0 := by
  funext i
  have hp := congrArg (fun L : ANF 8 →ₗ[F₂] F₂ =>
      L (linearANF ell * (linearANF m * linearANF n)))
    (singlePolarMap_eq_singleCoeffMap i)
  change singlePolarMap i
      (linearANF ell * (linearANF m * linearANF n)) =
    anfLinearProjection
      (linearANF ell * (linearANF m * linearANF n)) i at hp
  rw [← hp]
  change
    eval (linearANF ell * (linearANF m * linearANF n))
        (supportAssignment ∅) +
      eval (linearANF ell * (linearANF m * linearANF n))
        (supportAssignment {i}) = 0
  have hi := congrFun hdisjoint i
  simp only [pointwiseLinearProduct, Pi.zero_apply] at hi
  simp only [eval_mul', eval_linearANF_supportAssignment]
  simp [hi]

theorem sliceQuadraticA_disjoint :
    pointwiseLinearProduct sliceABar sliceBBar = 0 := by
  funext i
  fin_cases i <;>
    simp [pointwiseLinearProduct, sliceABar, sliceBBar, placeA, placeB]

theorem sliceInfinityQuadratic_disjoint :
    pointwiseLinearProduct (placeA 2) (placeB 2) = 0 := by
  funext i
  fin_cases i <;> simp [pointwiseLinearProduct, placeA, placeB]

@[simp] theorem anfTwoProjection_sliceQuadraticAANF :
    anfTwoProjection sliceQuadraticAANF = sliceQuadraticA := by
  exact anfTwoProjection_linear_mul_linear sliceABar sliceBBar

@[simp] theorem anfTwoProjection_sliceInfinityQuadraticANF :
    anfTwoProjection sliceInfinityQuadraticANF =
      sliceInfinityQuadratic := by
  exact anfTwoProjection_linear_mul_linear (placeA 2) (placeB 2)

@[simp] theorem anfTwoProjection_sliceQuadraticBANF :
    anfTwoProjection sliceQuadraticBANF = sliceQuadraticB := by
  rw [sliceQuadraticBANF, map_add,
    anfTwoProjection_sliceQuadraticAANF,
    anfTwoProjection_sliceInfinityQuadraticANF]
  rfl

@[simp] theorem anfThreeProjection_sliceQuadraticAANF :
    anfThreeProjection sliceQuadraticAANF = 0 :=
  anfThreeProjection_linear_mul_linear sliceABar sliceBBar

@[simp] theorem anfThreeProjection_sliceInfinityQuadraticANF :
    anfThreeProjection sliceInfinityQuadraticANF = 0 :=
  anfThreeProjection_linear_mul_linear (placeA 2) (placeB 2)

@[simp] theorem anfThreeProjection_sliceQuadraticBANF :
    anfThreeProjection sliceQuadraticBANF = 0 := by
  simp [sliceQuadraticBANF]

@[simp] theorem anfLinearProjection_sliceQuadraticAANF :
    anfLinearProjection sliceQuadraticAANF = 0 := by
  rw [sliceQuadraticAANF, anfLinearProjection_linear_mul_linear,
    sliceQuadraticA_disjoint]

@[simp] theorem anfLinearProjection_sliceInfinityQuadraticANF :
    anfLinearProjection sliceInfinityQuadraticANF = 0 := by
  rw [sliceInfinityQuadraticANF,
    anfLinearProjection_linear_mul_linear,
    sliceInfinityQuadratic_disjoint]

@[simp] theorem anfLinearProjection_sliceQuadraticBANF :
    anfLinearProjection sliceQuadraticBANF = 0 := by
  simp [sliceQuadraticBANF]

theorem anfTwoProjection_affine_mul_sliceQuadraticA
    (a : F₂) (ell : LinearForm) :
    anfTwoProjection (affineANF a ell * sliceQuadraticAANF) =
      a • sliceQuadraticA + booleanContraction ell sliceQuadraticA := by
  rw [sliceQuadraticAANF]
  rw [affineANF, add_mul]
  simp only [smul_mul_assoc, one_mul, map_add, map_smul, anfTwoProjection_linear_mul_linear,
    anfTwoProjection_linear_mul_quadratic ell sliceABar sliceBBar sliceQuadraticA_disjoint]
  rfl

theorem anfTwoProjection_affine_mul_sliceInfinityQuadratic
    (a : F₂) (ell : LinearForm) :
    anfTwoProjection (affineANF a ell * sliceInfinityQuadraticANF) =
      a • sliceInfinityQuadratic +
        booleanContraction ell sliceInfinityQuadratic := by
  rw [sliceInfinityQuadraticANF]
  rw [affineANF, add_mul]
  simp only [smul_mul_assoc, one_mul, map_add, map_smul, anfTwoProjection_linear_mul_linear,
    anfTwoProjection_linear_mul_quadratic ell (placeA 2) (placeB 2)
    sliceInfinityQuadratic_disjoint]
  rfl

theorem anfLinearProjection_affine_mul_sliceQuadraticA
    (a : F₂) (ell : LinearForm) :
    anfLinearProjection (affineANF a ell * sliceQuadraticAANF) = 0 := by
  rw [sliceQuadraticAANF]
  rw [affineANF, add_mul]
  simp only [smul_mul_assoc, one_mul, map_add, map_smul,
    anfLinearProjection_linear_mul_linear, sliceQuadraticA_disjoint,
    anfLinearProjection_linear_mul_quadratic ell sliceABar sliceBBar sliceQuadraticA_disjoint,
    smul_zero, add_zero]

theorem anfLinearProjection_affine_mul_sliceInfinityQuadratic
    (a : F₂) (ell : LinearForm) :
    anfLinearProjection
        (affineANF a ell * sliceInfinityQuadraticANF) = 0 := by
  rw [sliceInfinityQuadraticANF]
  rw [affineANF, add_mul]
  simp only [smul_mul_assoc, one_mul, map_add, map_smul,
    anfLinearProjection_linear_mul_linear, sliceInfinityQuadratic_disjoint,
    anfLinearProjection_linear_mul_quadratic ell (placeA 2) (placeB 2)
    sliceInfinityQuadratic_disjoint, smul_zero, add_zero]

theorem anfThreeProjection_affine_mul_sliceQuadraticA
    (a : F₂) (ell : LinearForm) :
    anfThreeProjection (affineANF a ell * sliceQuadraticAANF) =
      vectorWedgeTwo ell sliceQuadraticA := by
  rw [sliceQuadraticAANF]
  rw [affineANF, add_mul]
  simp only [smul_mul_assoc, one_mul, map_add, map_smul, anfThreeProjection_linear_mul_linear,
    anfThreeProjection_linear_mul_quadratic, smul_zero, zero_add]
  rfl

theorem anfThreeProjection_affine_mul_sliceInfinityQuadratic
    (a : F₂) (ell : LinearForm) :
    anfThreeProjection
        (affineANF a ell * sliceInfinityQuadraticANF) =
      vectorWedgeTwo ell sliceInfinityQuadratic := by
  rw [sliceInfinityQuadraticANF]
  rw [affineANF, add_mul]
  simp only [smul_mul_assoc, one_mul, map_add, map_smul, anfThreeProjection_linear_mul_linear,
    anfThreeProjection_linear_mul_quadratic, smul_zero, zero_add]
  rfl

theorem anfTwoProjection_affine_mul_sliceQuadraticB
    (a : F₂) (ell : LinearForm) :
    anfTwoProjection (affineANF a ell * sliceQuadraticBANF) =
      a • sliceQuadraticB + booleanContraction ell sliceQuadraticB := by
  rw [sliceQuadraticBANF, mul_add, map_add,
    anfTwoProjection_affine_mul_sliceQuadraticA,
    anfTwoProjection_affine_mul_sliceInfinityQuadratic,
    sliceQuadraticB, smul_add,
    booleanContraction_add_right_h]
  module

theorem anfLinearProjection_affine_mul_sliceQuadraticB
    (a : F₂) (ell : LinearForm) :
    anfLinearProjection (affineANF a ell * sliceQuadraticBANF) = 0 := by
  simp [sliceQuadraticBANF, mul_add, anfLinearProjection_affine_mul_sliceQuadraticA,
    anfLinearProjection_affine_mul_sliceInfinityQuadratic]

theorem anfThreeProjection_affine_mul_sliceQuadraticB
    (a : F₂) (ell : LinearForm) :
    anfThreeProjection (affineANF a ell * sliceQuadraticBANF) =
      vectorWedgeTwo ell sliceQuadraticB := by
  rw [sliceQuadraticBANF, mul_add, map_add,
    anfThreeProjection_affine_mul_sliceQuadraticA,
    anfThreeProjection_affine_mul_sliceInfinityQuadratic,
    sliceQuadraticB, vectorWedgeTwo_add_right_h]

theorem anfThreeProjection_affineANF (a : F₂) (ell : LinearForm) :
    anfThreeProjection (affineANF a ell) = 0 := by
  have h := anfThreeProjection_affine_mul_affine a 1 ell 0
  simpa [affineANF] using h

@[simp] theorem anfThreeProjection_sliceCorrectionModel
    (a : F₂) (ell : LinearForm) (alpha : Fin 3 → F₂)
    (x y : F₂) :
    anfThreeProjection (sliceCorrectionModel a ell alpha x y) = 0 := by
  simp [sliceCorrectionModel, anfThreeProjection_affineANF]

@[simp] theorem anfTwoProjection_sliceCorrectionModel
    (a : F₂) (ell : LinearForm) (alpha : Fin 3 → F₂)
    (x y : F₂) :
    anfTwoProjection (sliceCorrectionModel a ell alpha x y) =
      alpha 1 • sliceQuadraticA +
        alpha 2 • sliceInfinityQuadratic := by
  rw [sliceCorrectionModel, map_add, map_add,
    anfTwoProjection_kills_affine (affineANF_mem _ _),
    map_smul, map_smul,
    anfTwoProjection_sliceQuadraticAANF,
    anfTwoProjection_sliceInfinityQuadraticANF,
    zero_add]

@[simp] theorem anfLinearProjection_sliceCorrectionModel
    (a : F₂) (ell : LinearForm) (alpha : Fin 3 → F₂)
    (x y : F₂) :
    anfLinearProjection (sliceCorrectionModel a ell alpha x y) =
      sliceComplementLinear ell +
        alpha 1 • sliceVaryingLinear x y := by
  simp [sliceCorrectionModel, anfLinearProjection_affineANF]

@[simp] theorem anfThreeProjection_sliceTangentModel
    (a : F₂) (ell : LinearForm) (eps x y : F₂) :
    anfThreeProjection (sliceTangentModel a ell eps x y) = 0 := by
  simp [sliceTangentModel, anfThreeProjection_affineANF]

@[simp] theorem anfTwoProjection_sliceTangentModel
    (a : F₂) (ell : LinearForm) (eps x y : F₂) :
    anfTwoProjection (sliceTangentModel a ell eps x y) = 0 := by
  apply anfTwoProjection_kills_affine
  exact affineANF_mem _ _

@[simp] theorem anfLinearProjection_sliceTangentModel
    (a : F₂) (ell : LinearForm) (eps x y : F₂) :
    anfLinearProjection (sliceTangentModel a ell eps x y) =
      sliceComplementLinear ell + y • sliceU + x • sliceV := by
  simp [sliceTangentModel, anfLinearProjection_affineANF, add_assoc]

/-- The Boolean degree-lowering contraction on the type-A support plane. -/
theorem booleanContraction_sliceComplement_sliceQuadraticA
    (p q : F₂) :
    booleanContraction (p • sliceABar + q • sliceBBar)
        sliceQuadraticA =
      (p + q) • sliceQuadraticA := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [booleanContraction, sliceQuadraticA, vectorWedge, sliceABar, sliceBBar, placeA,
      placeB] <;>
    ring_nf <;>
    simp [N3Certificate.two_eq_zero_f2]

theorem booleanContraction_sliceInfinity_sliceInfinityQuadratic
    (p q : F₂) :
    booleanContraction (p • placeA 2 + q • placeB 2)
        sliceInfinityQuadratic =
      (p + q) • sliceInfinityQuadratic := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [booleanContraction, sliceInfinityQuadratic, vectorWedge, placeA, placeB]
  all_goals ring_nf

theorem booleanContraction_zero (q : TwoForm) :
    booleanContraction 0 q = 0 := by
  funext i j
  simp [booleanContraction]

/-- The full sliced type-A product, including its affine and rational-target correction. -/
@[expose] def sliceTypeAFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) : ANF 8 :=
  sliceZeroFactorModel leftConst leftLinear x y *
      sliceOneFactorModel rightConst rightLinear x y +
    sliceCorrectionModel correctionConst correctionLinear
      correctionCoeff x y

/-- The full sliced type-B product, including its affine and rational-target correction. -/
@[expose] def sliceTypeBFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) : ANF 8 :=
  sliceZeroFactorModel leftConst leftLinear x y *
      sliceTypeBFactorModel rightConst rightLinear x y +
    sliceCorrectionModel correctionConst correctionLinear
      correctionCoeff x y

/-- The full sliced infinity-type product, including its affine and rational-target correction. -/
@[expose] def sliceTypeInfinityFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) : ANF 8 :=
  sliceZeroFactorModel leftConst leftLinear x y *
      sliceInfinityFactorModel rightConst rightLinear x y +
    sliceCorrectionModel correctionConst correctionLinear
      correctionCoeff x y

theorem anchorsIndependent_sliceTypeAFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    AnchorsIndependent
      (sliceTypeAFullModel leftConst leftLinear rightConst rightLinear
        correctionConst correctionLinear correctionCoeff x y) := by
  exact
    ((anchorsIndependent_sliceZeroFactorModel leftConst leftLinear x y).mul
      (anchorsIndependent_sliceOneFactorModel rightConst rightLinear x y)).add
      (anchorsIndependent_sliceCorrectionModel correctionConst
        correctionLinear correctionCoeff x y)

theorem anchorsIndependent_sliceTypeBFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    AnchorsIndependent
      (sliceTypeBFullModel leftConst leftLinear rightConst rightLinear
        correctionConst correctionLinear correctionCoeff x y) := by
  exact
    ((anchorsIndependent_sliceZeroFactorModel leftConst leftLinear x y).mul
      (anchorsIndependent_sliceTypeBFactorModel rightConst rightLinear x y)).add
      (anchorsIndependent_sliceCorrectionModel correctionConst
        correctionLinear correctionCoeff x y)

theorem anchorsIndependent_sliceTypeInfinityFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    AnchorsIndependent
      (sliceTypeInfinityFullModel leftConst leftLinear rightConst rightLinear
        correctionConst correctionLinear correctionCoeff x y) := by
  exact
    ((anchorsIndependent_sliceZeroFactorModel leftConst leftLinear x y).mul
      (anchorsIndependent_sliceInfinityFactorModel rightConst rightLinear x y)).add
      (anchorsIndependent_sliceCorrectionModel correctionConst
        correctionLinear correctionCoeff x y)

@[simp] theorem anfThreeProjection_sliceTypeAFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    anfThreeProjection
        (sliceTypeAFullModel leftConst leftLinear rightConst rightLinear
          correctionConst correctionLinear correctionCoeff x y) =
      vectorWedgeTwo (sliceComplementLinear leftLinear)
        sliceQuadraticA := by
  simp [sliceTypeAFullModel, sliceZeroFactorModel, sliceOneFactorModel, mul_add,
    anfThreeProjection_affine_mul_affine, anfThreeProjection_affine_mul_sliceQuadraticA]

@[simp] theorem anfThreeProjection_sliceTypeBFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    anfThreeProjection
        (sliceTypeBFullModel leftConst leftLinear rightConst rightLinear
          correctionConst correctionLinear correctionCoeff x y) =
      vectorWedgeTwo (sliceComplementLinear leftLinear)
        sliceQuadraticB := by
  simp [sliceTypeBFullModel, sliceZeroFactorModel, sliceTypeBFactorModel, mul_add,
    anfThreeProjection_affine_mul_affine, anfThreeProjection_affine_mul_sliceQuadraticB]

@[simp] theorem anfThreeProjection_sliceTypeInfinityFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    anfThreeProjection
        (sliceTypeInfinityFullModel leftConst leftLinear rightConst rightLinear
          correctionConst correctionLinear correctionCoeff x y) =
      vectorWedgeTwo (sliceComplementLinear leftLinear)
        sliceInfinityQuadratic := by
  simp [sliceTypeInfinityFullModel, sliceZeroFactorModel, sliceInfinityFactorModel, mul_add,
    anfThreeProjection_affine_mul_affine, anfThreeProjection_affine_mul_sliceInfinityQuadratic]

theorem anfTwoProjection_sliceTypeAFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    anfTwoProjection
        (sliceTypeAFullModel leftConst leftLinear rightConst rightLinear
          correctionConst correctionLinear correctionCoeff x y) =
      (leftConst + sliceAnchorValue leftLinear x y + x * y) •
          sliceQuadraticA +
        vectorWedge (sliceComplementLinear leftLinear)
          (sliceComplementLinear rightLinear + sliceVaryingLinear x y) +
        booleanContraction (sliceComplementLinear leftLinear)
          sliceQuadraticA +
        correctionCoeff 1 • sliceQuadraticA +
        correctionCoeff 2 • sliceInfinityQuadratic := by
  simp only [sliceTypeAFullModel, sliceZeroFactorModel, sliceOneFactorModel, mul_add, map_add,
    anfTwoProjection_affine_mul_affine, anfTwoProjection_affine_mul_sliceQuadraticA,
    anfTwoProjection_sliceCorrectionModel]
  module

theorem anfTwoProjection_sliceTypeBFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    anfTwoProjection
        (sliceTypeBFullModel leftConst leftLinear rightConst rightLinear
          correctionConst correctionLinear correctionCoeff x y) =
      (leftConst + sliceAnchorValue leftLinear x y + x * y) •
          sliceQuadraticB +
        vectorWedge (sliceComplementLinear leftLinear)
          (sliceComplementLinear rightLinear + sliceVaryingLinear x y) +
        booleanContraction (sliceComplementLinear leftLinear)
          sliceQuadraticB +
        correctionCoeff 1 • sliceQuadraticA +
        correctionCoeff 2 • sliceInfinityQuadratic := by
  simp only [sliceTypeBFullModel, sliceZeroFactorModel, sliceTypeBFactorModel, mul_add,
    map_add, anfTwoProjection_affine_mul_affine, anfTwoProjection_affine_mul_sliceQuadraticB,
    anfTwoProjection_sliceCorrectionModel]
  module

theorem anfTwoProjection_sliceTypeInfinityFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    anfTwoProjection
        (sliceTypeInfinityFullModel leftConst leftLinear rightConst rightLinear
          correctionConst correctionLinear correctionCoeff x y) =
      (leftConst + sliceAnchorValue leftLinear x y + x * y) •
          sliceInfinityQuadratic +
        vectorWedge (sliceComplementLinear leftLinear)
          (sliceComplementLinear rightLinear) +
        booleanContraction (sliceComplementLinear leftLinear)
          sliceInfinityQuadratic +
        correctionCoeff 1 • sliceQuadraticA +
        correctionCoeff 2 • sliceInfinityQuadratic := by
  simp only [sliceTypeInfinityFullModel, sliceZeroFactorModel, sliceInfinityFactorModel,
    mul_add, map_add, anfTwoProjection_affine_mul_affine,
    anfTwoProjection_affine_mul_sliceInfinityQuadratic, anfTwoProjection_sliceCorrectionModel]
  module

theorem anfLinearProjection_sliceTypeAFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    anfLinearProjection
        (sliceTypeAFullModel leftConst leftLinear rightConst rightLinear
          correctionConst correctionLinear correctionCoeff x y) =
      sliceProductLinear
        (leftConst + sliceAnchorValue leftLinear x y + x * y)
        (rightConst + sliceAnchorValue rightLinear x y + x * y)
        (sliceComplementLinear leftLinear)
        (sliceComplementLinear rightLinear + sliceVaryingLinear x y)
        (sliceComplementLinear correctionLinear)
        (correctionCoeff 1) x y := by
  simp only [sliceTypeAFullModel, sliceZeroFactorModel, sliceOneFactorModel, mul_add, map_add,
    anfLinearProjection_affine_mul_affine, anfLinearProjection_affine_mul_sliceQuadraticA,
    anfLinearProjection_sliceCorrectionModel, add_zero]
  rw [sliceProductLinear]
  module

theorem anfLinearProjection_sliceTypeBFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    anfLinearProjection
        (sliceTypeBFullModel leftConst leftLinear rightConst rightLinear
          correctionConst correctionLinear correctionCoeff x y) =
      sliceProductLinear
        (leftConst + sliceAnchorValue leftLinear x y + x * y)
        (rightConst + sliceAnchorValue rightLinear x y + x * y)
        (sliceComplementLinear leftLinear)
        (sliceComplementLinear rightLinear + sliceVaryingLinear x y)
        (sliceComplementLinear correctionLinear)
        (correctionCoeff 1) x y := by
  simp only [sliceTypeBFullModel, sliceZeroFactorModel, sliceTypeBFactorModel, mul_add,
    map_add, anfLinearProjection_affine_mul_affine,
    anfLinearProjection_affine_mul_sliceQuadraticB, anfLinearProjection_sliceCorrectionModel,
    add_zero]
  rw [sliceProductLinear]
  module

theorem anfLinearProjection_sliceTypeInfinityFullModel
    (leftConst : F₂) (leftLinear : LinearForm)
    (rightConst : F₂) (rightLinear : LinearForm)
    (correctionConst : F₂) (correctionLinear : LinearForm)
    (correctionCoeff : Fin 3 → F₂) (x y : F₂) :
    anfLinearProjection
        (sliceTypeInfinityFullModel leftConst leftLinear rightConst rightLinear
          correctionConst correctionLinear correctionCoeff x y) =
      sliceProductLinear
        (leftConst + sliceAnchorValue leftLinear x y + x * y)
        (rightConst + sliceAnchorValue rightLinear x y)
        (sliceComplementLinear leftLinear)
        (sliceComplementLinear rightLinear)
        (sliceComplementLinear correctionLinear)
        (correctionCoeff 1) x y := by
  simp only [sliceTypeInfinityFullModel, sliceZeroFactorModel, sliceInfinityFactorModel,
    mul_add, map_add, anfLinearProjection_affine_mul_affine,
    anfLinearProjection_affine_mul_sliceInfinityQuadratic,
    anfLinearProjection_sliceCorrectionModel, add_zero]
  rw [sliceProductLinear]
  module

end

end N4
end UnrestrictedBooleanMul
