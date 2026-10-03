/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.SliceVanishing

/-!
# Algebraic exclusion of the two quartic slice types

This file is the coordinate-free bookkeeping core of the manuscript's
type-A/type-B slice argument.  Its inputs are the cubic, quadratic, and
linear coefficient equations on two distinct active slices.  The proof uses
only exterior products and the two support planes established in
`SliceGeometry`; it does not enumerate circuits or Boolean functions.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The linear slice variation induced by the two anchor values. -/
@[expose] def sliceVaryingLinear (x y : F₂) : LinearForm :=
  x • sliceBBar + y • sliceABar

/-- Coordinatewise product of two linear coefficient vectors. -/
@[expose] def pointwiseLinearProduct (ell m : LinearForm) : LinearForm :=
  fun i => ell i * m i

/-- Linear part of `(mu + ell) * (nu + n + Q)`, followed by the fixed
correction and the `r₁` slice variation. -/
@[expose] def sliceProductLinear
    (mu nu : F₂) (ell n base : LinearForm) (lambdaOne x y : F₂) :
    LinearForm :=
  mu • n + nu • ell + pointwiseLinearProduct ell n + base +
    lambdaOne • sliceVaryingLinear x y

/-- The difference in the target linear parts at two anchor assignments. -/
@[expose] def sliceTargetDifference (x y x' y' : F₂) : LinearForm :=
  (y + y') • sliceU + (x + x') • sliceV

/-- Vanishing of the type-A slice quadratic after its rational correction. -/
@[expose] def SliceQuadraticEquationA
    (mu : F₂) (ell n : LinearForm)
    (lambdaOne lambdaInfinity : F₂) : Prop :=
  mu • sliceQuadraticA + vectorWedge ell n +
      lambdaOne • sliceQuadraticA +
      lambdaInfinity • sliceInfinityQuadratic = 0

/-- Vanishing of the type-B slice quadratic after its rational correction. -/
@[expose] def SliceQuadraticEquationB
    (mu : F₂) (ell n : LinearForm)
    (lambdaOne lambdaInfinity : F₂) : Prop :=
  mu • sliceQuadraticB + vectorWedge ell n +
      lambdaOne • sliceQuadraticA +
      lambdaInfinity • sliceInfinityQuadratic = 0

theorem inSliceComplementPlane_zero :
    InSliceComplementPlane 0 := by
  exact ⟨0, 0, by simp⟩

theorem InSliceComplementPlane.add {ell m : LinearForm}
    (hell : InSliceComplementPlane ell)
    (hm : InSliceComplementPlane m) :
    InSliceComplementPlane (ell + m) := by
  rcases hell with ⟨a, b, rfl⟩
  rcases hm with ⟨c, d, rfl⟩
  refine ⟨a + c, b + d, ?_⟩
  module

theorem InSliceComplementPlane.smul (a : F₂) {ell : LinearForm}
    (hell : InSliceComplementPlane ell) :
    InSliceComplementPlane (a • ell) := by
  rcases hell with ⟨p, q, rfl⟩
  refine ⟨a * p, a * q, ?_⟩
  module

theorem sliceABar_mem_complement_plane :
    InSliceComplementPlane sliceABar := by
  exact ⟨1, 0, by simp⟩

theorem sliceBBar_mem_complement_plane :
    InSliceComplementPlane sliceBBar := by
  exact ⟨0, 1, by simp⟩

theorem sliceVaryingLinear_mem (x y : F₂) :
    InSliceComplementPlane (sliceVaryingLinear x y) := by
  exact (sliceBBar_mem_complement_plane.smul x).add
    (sliceABar_mem_complement_plane.smul y)

/-- Coordinatewise Boolean contraction preserves the complementary plane:
the two generators have disjoint support and are idempotent. -/
theorem pointwiseLinearProduct_mem
    {ell m : LinearForm}
    (hell : InSliceComplementPlane ell)
    (hm : InSliceComplementPlane m) :
    InSliceComplementPlane (pointwiseLinearProduct ell m) := by
  rcases hell with ⟨a, b, rfl⟩
  rcases hm with ⟨c, d, rfl⟩
  refine ⟨a * c, b * d, ?_⟩
  funext i
  fin_cases i <;>
    simp [pointwiseLinearProduct, sliceABar, sliceBBar, placeA, placeB] <;> ring_nf <;>
    simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2]

theorem sliceQuadratics_independent
    {a b : F₂}
    (h : a • sliceQuadraticA + b • sliceInfinityQuadratic = 0) :
    a = 0 ∧ b = 0 := by
  have hA := congrFun (congrFun h (aCoord 1)) (bCoord 1)
  have hI := congrFun (congrFun h (aCoord 3)) (bCoord 3)
  simp only [sliceQuadraticA, sliceABar, placeA, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.add_cons, Matrix.head_cons, Matrix.tail_cons, add_zero,
    Matrix.empty_add_empty, sliceBBar, placeB, sliceInfinityQuadratic, Matrix.cons_val,
    aCoord, Fin.coe_ofNat_eq_mod, Nat.one_mod, Fin.mk_one, bCoord, Nat.reduceAdd,
    Fin.reduceFinMk, Pi.add_apply, Pi.smul_apply, vectorWedge, mul_one, mul_zero, smul_eq_mul,
    Pi.zero_apply, Nat.mod_succ] at hA hI
  constructor
  · exact hA
  · rw [hA, zero_add] at hI
    exact hI

/-- Membership in the two-input support of the infinity place. -/
@[expose]
def InSliceInfinityPlane (ell : LinearForm) : Prop :=
  ∃ a b : F₂, ell = a • placeA 2 + b • placeB 2

theorem sliceInfinityQuadratic_ne_zero :
    sliceInfinityQuadratic ≠ 0 := by
  intro h
  have hc := congrFun (congrFun h (aCoord 3)) (bCoord 3)
  simp [sliceInfinityQuadratic, vectorWedge, placeA, placeB, aCoord, bCoord] at hc

theorem sliceInfinityQuadratic_annihilator {ell : LinearForm}
    (h : vectorWedgeTwo ell sliceInfinityQuadratic = 0) :
    InSliceInfinityPlane ell := by
  exact mem_support_of_vectorWedgeTwo_zero ell (placeA 2) (placeB 2)
    sliceInfinityQuadratic_ne_zero h

theorem complement_infinity_plane_intersection
    {ell : LinearForm}
    (hc : InSliceComplementPlane ell)
    (hi : InSliceInfinityPlane ell) : ell = 0 := by
  rcases hc with ⟨a, b, hc⟩
  rcases hi with ⟨p, q, hi⟩
  have ha := congrFun (hc.symm.trans hi) (aCoord 1)
  have hb := congrFun (hc.symm.trans hi) (bCoord 1)
  simp only [sliceABar, placeA, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.add_cons, Matrix.head_cons, Matrix.tail_cons, add_zero, Matrix.empty_add_empty,
    Matrix.smul_cons, smul_eq_mul, mul_one, mul_zero, Matrix.smul_empty, sliceBBar, placeB,
    aCoord, Fin.coe_ofNat_eq_mod, Nat.one_mod, Fin.mk_one, Pi.add_apply, Matrix.cons_val,
    bCoord, Nat.reduceAdd, Fin.reduceFinMk, zero_add] at ha hb
  subst a
  subst b
  simp only [zero_smul, add_zero] at hc
  exact hc

theorem vectorWedge_eq_typeA_plus_infinity_impossible
    {ell n : LinearForm} {a : F₂}
    (hell : InSliceComplementPlane ell) (hellNe : ell ≠ 0)
    (h : vectorWedge ell n =
      a • sliceQuadraticA + sliceInfinityQuadratic) : False := by
  rcases f2_eq_zero_or_one a with rfl | rfl
  · have hw := congrArg (fun q : TwoForm => vectorWedgeTwo ell q) h
    rw [vectorWedgeTwo_repeated_left] at hw
    simp only [zero_smul, zero_add] at hw
    have hi := sliceInfinityQuadratic_annihilator hw.symm
    exact hellNe (complement_infinity_plane_intersection hell hi)
  · have hw := congrArg (fun q : TwoForm => vectorWedgeTwo ell q) h
    rw [vectorWedgeTwo_repeated_left] at hw
    have hB : vectorWedgeTwo ell sliceQuadraticB = 0 := by
      simpa [sliceQuadraticB, vectorWedgeTwo_add_right_h] using hw.symm
    exact hellNe (sliceQuadraticB_annihilator hB)

theorem second_factor_mem_of_typeA_wedge
    {ell n : LinearForm} {a : F₂}
    (hell : InSliceComplementPlane ell) (hellNe : ell ≠ 0)
    (h : vectorWedge ell n = a • sliceQuadraticA) :
    InSliceComplementPlane n := by
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simp only [zero_smul] at h
    have hminors : ∀ i j, ell i * n j + ell j * n i = 0 := by
      intro i j
      exact congrFun (congrFun h i) j
    rcases dependent_of_vectorWedge_zero ell n hminors with
        hzero | hnzero | heq
    · exact (hellNe hzero).elim
    · rw [hnzero]
      exact inSliceComplementPlane_zero
    · rw [← heq]
      exact hell
  · have hw := congrArg (fun q : TwoForm => vectorWedgeTwo n q) h
    rw [vectorWedgeTwo_repeated_right] at hw
    have hA : vectorWedgeTwo n sliceQuadraticA = 0 := by simpa using hw.symm
    exact sliceQuadraticA_annihilator hA

theorem add_ne_zero_of_ne_f2 {a b : F₂} (h : a ≠ b) : a + b ≠ 0 := by
  intro hz
  have hab := (add_eq_zero_iff_eq_neg.mp hz).trans (neg_eq_self_f2 b)
  exact h hab

theorem distinct_corner_target_difference_not_in_plane
    {x y x' y' : F₂} (h : x ≠ x' ∨ y ≠ y') :
    ¬ InSliceComplementPlane (sliceTargetDifference x y x' y') := by
  apply sliceUV_combination_not_in_complement_plane
  rcases h with hx | hy
  · exact Or.inr (add_ne_zero_of_ne_f2 hx)
  · exact Or.inl (add_ne_zero_of_ne_f2 hy)

theorem solve_typeB_quadratic
    {mu lambdaOne lambdaInfinity : F₂}
    (h : mu • sliceQuadraticB +
        lambdaOne • sliceQuadraticA +
        lambdaInfinity • sliceInfinityQuadratic = 0) :
    mu = lambdaOne ∧ mu = lambdaInfinity := by
  have h' :
      (mu + lambdaOne) • sliceQuadraticA +
        (mu + lambdaInfinity) • sliceInfinityQuadratic = 0 := by
    rw [sliceQuadraticB, smul_add] at h
    calc
      (mu + lambdaOne) • sliceQuadraticA +
          (mu + lambdaInfinity) • sliceInfinityQuadratic =
        mu • sliceQuadraticA + mu • sliceInfinityQuadratic +
          lambdaOne • sliceQuadraticA +
          lambdaInfinity • sliceInfinityQuadratic := by module
      _ = mu • sliceQuadraticA +
          (mu • sliceInfinityQuadratic +
            (lambdaOne • sliceQuadraticA +
              lambdaInfinity • sliceInfinityQuadratic)) := by ac_rfl
      _ = 0 := by simpa only [add_assoc] using h
  rcases sliceQuadratics_independent h' with ⟨hOne, hInfinity⟩
  exact ⟨(add_eq_zero_iff_eq_neg.mp hOne).trans (neg_eq_self_f2 _),
    (add_eq_zero_iff_eq_neg.mp hInfinity).trans (neg_eq_self_f2 _)⟩

theorem solve_typeA_quadratic_zero_first
    {mu lambdaOne lambdaInfinity : F₂}
    (h : mu • sliceQuadraticA +
        lambdaOne • sliceQuadraticA +
        lambdaInfinity • sliceInfinityQuadratic = 0) :
    mu = lambdaOne ∧ lambdaInfinity = 0 := by
  have h' :
      (mu + lambdaOne) • sliceQuadraticA +
        lambdaInfinity • sliceInfinityQuadratic = 0 := by
    simpa [add_smul, add_assoc] using h
  rcases sliceQuadratics_independent h' with ⟨hOne, hInfinity⟩
  exact ⟨(add_eq_zero_iff_eq_neg.mp hOne).trans (neg_eq_self_f2 _),
    hInfinity⟩

theorem sliceProductLinear_zero_first_cancel
    (mu nu lambdaOne x y : F₂) (n base m : LinearForm)
    (hmu : mu = lambdaOne)
    (hn : n = m + sliceVaryingLinear x y) :
    sliceProductLinear mu nu 0 n base lambdaOne x y =
      lambdaOne • m + base := by
  subst mu
  subst n
  funext i
  simp [sliceProductLinear, pointwiseLinearProduct, sliceVaryingLinear]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

theorem sliceProductLinear_add_base_mem
    (mu nu lambdaOne x y : F₂) (ell n base : LinearForm)
    (hell : InSliceComplementPlane ell)
    (hn : InSliceComplementPlane n) :
    InSliceComplementPlane
      (sliceProductLinear mu nu ell n base lambdaOne x y + base) := by
  have hterms : InSliceComplementPlane
      (mu • n + nu • ell + pointwiseLinearProduct ell n +
        lambdaOne • sliceVaryingLinear x y) :=
    (((hn.smul mu).add (hell.smul nu)).add
      (pointwiseLinearProduct_mem hell hn)).add
      ((sliceVaryingLinear_mem x y).smul lambdaOne)
  have heq :
      sliceProductLinear mu nu ell n base lambdaOne x y + base =
        mu • n + nu • ell + pointwiseLinearProduct ell n +
          lambdaOne • sliceVaryingLinear x y := by
    funext i
    simp [sliceProductLinear]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  rw [heq]
  exact hterms

/-- Type B: rank four kills the first complementary linear form, after
which quadratic matching cancels every slice-varying linear term. -/
theorem no_typeB_active_slice_pair
    {x y x' y' mu mu' nu nu' lambdaOne lambdaInfinity : F₂}
    {ell m n n' base : LinearForm}
    (hdistinct : x ≠ x' ∨ y ≠ y')
    (hn : n = m + sliceVaryingLinear x y)
    (hn' : n' = m + sliceVaryingLinear x' y')
    (hcubic : vectorWedgeTwo ell sliceQuadraticB = 0)
    (hquad : SliceQuadraticEquationB mu ell n lambdaOne lambdaInfinity)
    (hquad' : SliceQuadraticEquationB mu' ell n' lambdaOne lambdaInfinity)
    (hlinear :
      sliceProductLinear mu nu ell n base lambdaOne x y +
          sliceProductLinear mu' nu' ell n' base lambdaOne x' y' =
        sliceTargetDifference x y x' y') : False := by
  have hell : ell = 0 := sliceQuadraticB_annihilator hcubic
  subst ell
  have hq : mu = lambdaOne ∧ mu = lambdaInfinity := by
    apply solve_typeB_quadratic
    simpa [SliceQuadraticEquationB, vectorWedge] using hquad
  have hq' : mu' = lambdaOne ∧ mu' = lambdaInfinity := by
    apply solve_typeB_quadratic
    simpa [SliceQuadraticEquationB, vectorWedge] using hquad'
  have hlin0 := sliceProductLinear_zero_first_cancel
    mu nu lambdaOne x y n base m hq.1 hn
  have hlin1 := sliceProductLinear_zero_first_cancel
    mu' nu' lambdaOne x' y' n' base m hq'.1 hn'
  rw [hlin0, hlin1] at hlinear
  have hzero : sliceTargetDifference x y x' y' = 0 := by
    rw [← hlinear]
    funext i
    change (lambdaOne • m + base) i + (lambdaOne • m + base) i = 0
    exact CharTwo.add_self_eq_zero ((lambdaOne • m + base) i)
  exact distinct_corner_target_difference_not_in_plane hdistinct
    (hzero ▸ inSliceComplementPlane_zero)

/-- Type A: either the first complementary form is zero (constant-slice
case), or quadratic matching puts both factor forms in the type-A support
plane, so every slice difference stays in that plane. -/
theorem no_typeA_active_slice_pair
    {x y x' y' mu mu' quadMu quadMu' nu nu'
      lambdaOne lambdaInfinity : F₂}
    {ell m n n' base : LinearForm}
    (hdistinct : x ≠ x' ∨ y ≠ y')
    (hn : n = m + sliceVaryingLinear x y)
    (hn' : n' = m + sliceVaryingLinear x' y')
    (hcubic : vectorWedgeTwo ell sliceQuadraticA = 0)
    (hquad : SliceQuadraticEquationA quadMu ell n lambdaOne lambdaInfinity)
    (hquad' : SliceQuadraticEquationA quadMu' ell n' lambdaOne lambdaInfinity)
    (hquadMu : ell = 0 → quadMu = mu)
    (hquadMu' : ell = 0 → quadMu' = mu')
    (hlinear :
      sliceProductLinear mu nu ell n base lambdaOne x y +
          sliceProductLinear mu' nu' ell n' base lambdaOne x' y' =
        sliceTargetDifference x y x' y') : False := by
  have hellPlane : InSliceComplementPlane ell :=
    sliceQuadraticA_annihilator hcubic
  by_cases hellZero : ell = 0
  · subst ell
    have hqQuad : quadMu = lambdaOne ∧ lambdaInfinity = 0 := by
      apply solve_typeA_quadratic_zero_first
      simpa [SliceQuadraticEquationA, vectorWedge] using hquad
    have hqQuad' : quadMu' = lambdaOne ∧ lambdaInfinity = 0 := by
      apply solve_typeA_quadratic_zero_first
      simpa [SliceQuadraticEquationA, vectorWedge] using hquad'
    have hq : mu = lambdaOne ∧ lambdaInfinity = 0 :=
      ⟨(hquadMu rfl).symm.trans hqQuad.1, hqQuad.2⟩
    have hq' : mu' = lambdaOne ∧ lambdaInfinity = 0 :=
      ⟨(hquadMu' rfl).symm.trans hqQuad'.1, hqQuad'.2⟩
    have hlin0 := sliceProductLinear_zero_first_cancel
      mu nu lambdaOne x y n base m hq.1 hn
    have hlin1 := sliceProductLinear_zero_first_cancel
      mu' nu' lambdaOne x' y' n' base m hq'.1 hn'
    rw [hlin0, hlin1] at hlinear
    have hzero : sliceTargetDifference x y x' y' = 0 := by
      rw [← hlinear]
      funext i
      change (lambdaOne • m + base) i + (lambdaOne • m + base) i = 0
      exact CharTwo.add_self_eq_zero ((lambdaOne • m + base) i)
    exact distinct_corner_target_difference_not_in_plane hdistinct
      (hzero ▸ inSliceComplementPlane_zero)
  · have hwedge (muS : F₂) (nS : LinearForm)
        (hqS : SliceQuadraticEquationA muS ell nS
          lambdaOne lambdaInfinity) :
        vectorWedge ell nS =
          (muS + lambdaOne) • sliceQuadraticA +
            lambdaInfinity • sliceInfinityQuadratic := by
      funext i j
      have hc := congrFun (congrFun hqS i) j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hc
      change vectorWedge ell nS i j =
        (muS + lambdaOne) * sliceQuadraticA i j +
          lambdaInfinity * sliceInfinityQuadratic i j
      apply sub_eq_zero.mp
      rw [CharTwo.sub_eq_add]
      calc
        vectorWedge ell nS i j +
            ((muS + lambdaOne) * sliceQuadraticA i j +
              lambdaInfinity * sliceInfinityQuadratic i j) =
          muS * sliceQuadraticA i j + vectorWedge ell nS i j +
            lambdaOne * sliceQuadraticA i j +
            lambdaInfinity * sliceInfinityQuadratic i j := by ring
        _ = 0 := hc
    have hw := hwedge quadMu n hquad
    have hw' := hwedge quadMu' n' hquad'
    have hInfinity : lambdaInfinity = 0 := by
      rcases f2_eq_zero_or_one lambdaInfinity with hzero | hone
      · exact hzero
      · exfalso
        rw [hone, one_smul] at hw
        exact vectorWedge_eq_typeA_plus_infinity_impossible
          hellPlane hellZero hw
    rw [hInfinity, zero_smul, add_zero] at hw hw'
    have hnPlane : InSliceComplementPlane n :=
      second_factor_mem_of_typeA_wedge hellPlane hellZero hw
    have hnPlane' : InSliceComplementPlane n' :=
      second_factor_mem_of_typeA_wedge hellPlane hellZero hw'
    have hleftPlane := sliceProductLinear_add_base_mem
      mu nu lambdaOne x y ell n base hellPlane hnPlane
    have hrightPlane := sliceProductLinear_add_base_mem
      mu' nu' lambdaOne x' y' ell n' base hellPlane hnPlane'
    have hsumPlane := hleftPlane.add hrightPlane
    have heq :
        (sliceProductLinear mu nu ell n base lambdaOne x y + base) +
            (sliceProductLinear mu' nu' ell n' base lambdaOne x' y' + base) =
          sliceTargetDifference x y x' y' := by
      rw [← hlinear]
      funext i
      simp
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    rw [heq] at hsumPlane
    exact distinct_corner_target_difference_not_in_plane hdistinct hsumPlane

/-- Vanishing of the infinity-type slice quadratic after its rational correction. -/
@[expose] def SliceQuadraticEquationInfinity
    (mu : F₂) (ell n : LinearForm)
    (lambdaOne lambdaInfinity : F₂) : Prop :=
  mu • sliceInfinityQuadratic + vectorWedge ell n +
      lambdaOne • sliceQuadraticA +
      lambdaInfinity • sliceInfinityQuadratic = 0

theorem InSliceInfinityPlane.zero : InSliceInfinityPlane 0 := by
  exact ⟨0, 0, by simp⟩

theorem InSliceInfinityPlane.add {ell m : LinearForm}
    (hell : InSliceInfinityPlane ell)
    (hm : InSliceInfinityPlane m) :
    InSliceInfinityPlane (ell + m) := by
  rcases hell with ⟨a, b, rfl⟩
  rcases hm with ⟨c, d, rfl⟩
  refine ⟨a + c, b + d, ?_⟩
  module

theorem InSliceInfinityPlane.smul (a : F₂) {ell : LinearForm}
    (hell : InSliceInfinityPlane ell) :
    InSliceInfinityPlane (a • ell) := by
  rcases hell with ⟨p, q, rfl⟩
  refine ⟨a * p, a * q, ?_⟩
  module

theorem pointwiseLinearProduct_infinity_mem
    {ell m : LinearForm}
    (hell : InSliceInfinityPlane ell)
    (hm : InSliceInfinityPlane m) :
    InSliceInfinityPlane (pointwiseLinearProduct ell m) := by
  rcases hell with ⟨a, b, rfl⟩
  rcases hm with ⟨c, d, rfl⟩
  refine ⟨a * c, b * d, ?_⟩
  funext i
  fin_cases i <;>
    simp [pointwiseLinearProduct, placeA, placeB]

theorem sliceUV_combination_not_in_infinity_plane
    (a b : F₂) (hne : a ≠ 0 ∨ b ≠ 0) :
    ¬ InSliceInfinityPlane (a • sliceU + b • sliceV) := by
  rintro ⟨p, q, h⟩
  have ha := congrFun h (aCoord 1)
  have hb := congrFun h (bCoord 1)
  simp only [sliceU, aLinear, Pi.basisFun, aCoord, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.one_mod, Fin.mk_one, Module.Basis.coe_ofEquivFun, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, sliceV, bLinear, bCoord, Nat.reduceAdd, Fin.reduceFinMk,
    Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, ne_eq, Fin.reduceEq,
    not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero, placeA, Matrix.cons_val,
    Matrix.smul_cons, Matrix.smul_empty, placeB, Matrix.cons_val_one, Matrix.cons_val_zero,
    zero_add] at ha hb
  exact hne.elim (fun hna => hna ha) (fun hnb => hnb hb)

theorem distinct_corner_target_difference_not_in_infinity_plane
    {x y x' y' : F₂} (h : x ≠ x' ∨ y ≠ y') :
    ¬ InSliceInfinityPlane (sliceTargetDifference x y x' y') := by
  apply sliceUV_combination_not_in_infinity_plane
  rcases h with hx | hy
  · exact Or.inr (add_ne_zero_of_ne_f2 hx)
  · exact Or.inl (add_ne_zero_of_ne_f2 hy)

theorem solve_infinity_quadratic_zero_first
    {mu lambdaOne lambdaInfinity : F₂}
    (h : mu • sliceInfinityQuadratic +
        lambdaOne • sliceQuadraticA +
        lambdaInfinity • sliceInfinityQuadratic = 0) :
    lambdaOne = 0 ∧ mu = lambdaInfinity := by
  have h' :
      lambdaOne • sliceQuadraticA +
        (mu + lambdaInfinity) • sliceInfinityQuadratic = 0 := by
    calc
      lambdaOne • sliceQuadraticA +
          (mu + lambdaInfinity) • sliceInfinityQuadratic =
        mu • sliceInfinityQuadratic +
          lambdaOne • sliceQuadraticA +
          lambdaInfinity • sliceInfinityQuadratic := by module
      _ = 0 := h
  rcases sliceQuadratics_independent h' with ⟨hOne, hInfinity⟩
  exact ⟨hOne,
    (add_eq_zero_iff_eq_neg.mp hInfinity).trans (neg_eq_self_f2 _)⟩

theorem vectorWedge_eq_infinity_plus_typeA_impossible
    {ell n : LinearForm} {a : F₂}
    (hell : InSliceInfinityPlane ell) (hellNe : ell ≠ 0)
    (h : vectorWedge ell n =
      sliceQuadraticA + a • sliceInfinityQuadratic) : False := by
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simp only [zero_smul, add_zero] at h
    have hw := congrArg (fun q : TwoForm => vectorWedgeTwo ell q) h
    rw [vectorWedgeTwo_repeated_left] at hw
    have hc : InSliceComplementPlane ell := by
      apply sliceQuadraticA_annihilator
      simpa using hw.symm
    exact hellNe (complement_infinity_plane_intersection hc hell)
  · have hw := congrArg (fun q : TwoForm => vectorWedgeTwo ell q) h
    rw [vectorWedgeTwo_repeated_left] at hw
    have hB : vectorWedgeTwo ell sliceQuadraticB = 0 := by
      simpa [sliceQuadraticB, vectorWedgeTwo_add_right_h] using hw.symm
    exact hellNe (sliceQuadraticB_annihilator hB)

theorem second_factor_mem_of_infinity_wedge
    {ell n : LinearForm} {a : F₂}
    (hell : InSliceInfinityPlane ell) (hellNe : ell ≠ 0)
    (h : vectorWedge ell n = a • sliceInfinityQuadratic) :
    InSliceInfinityPlane n := by
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simp only [zero_smul] at h
    have hminors : ∀ i j, ell i * n j + ell j * n i = 0 := by
      intro i j
      exact congrFun (congrFun h i) j
    rcases dependent_of_vectorWedge_zero ell n hminors with
        hzero | hnzero | heq
    · exact (hellNe hzero).elim
    · rw [hnzero]
      exact InSliceInfinityPlane.zero
    · rw [← heq]
      exact hell
  · have hw := congrArg (fun q : TwoForm => vectorWedgeTwo n q) h
    rw [vectorWedgeTwo_repeated_right] at hw
    have hI : vectorWedgeTwo n sliceInfinityQuadratic = 0 := by
      simpa using hw.symm
    exact sliceInfinityQuadratic_annihilator hI

theorem sliceProductLinear_add_base_infinity_mem
    (mu nu x y : F₂) (ell n base : LinearForm)
    (hell : InSliceInfinityPlane ell)
    (hn : InSliceInfinityPlane n) :
    InSliceInfinityPlane
      (sliceProductLinear mu nu ell n base 0 x y + base) := by
  have hterms : InSliceInfinityPlane
      (mu • n + nu • ell + pointwiseLinearProduct ell n) :=
    ((hn.smul mu).add (hell.smul nu)).add
      (pointwiseLinearProduct_infinity_mem hell hn)
  have heq :
      sliceProductLinear mu nu ell n base 0 x y + base =
        mu • n + nu • ell + pointwiseLinearProduct ell n := by
    funext i
    simp [sliceProductLinear]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  rw [heq]
  exact hterms

/-- The remaining singleton-at-infinity seed type is excluded directly,
without appealing to a coordinate symmetry. -/
theorem no_typeInfinity_active_slice_pair
    {x y x' y' mu mu' quadMu quadMu' nu nu'
      lambdaOne lambdaInfinity : F₂}
    {ell n base : LinearForm}
    (hdistinct : x ≠ x' ∨ y ≠ y')
    (hcubic : vectorWedgeTwo ell sliceInfinityQuadratic = 0)
    (hquad : SliceQuadraticEquationInfinity quadMu ell n
      lambdaOne lambdaInfinity)
    (hquad' : SliceQuadraticEquationInfinity quadMu' ell n
      lambdaOne lambdaInfinity)
    (hquadMu : ell = 0 → quadMu = mu)
    (hquadMu' : ell = 0 → quadMu' = mu')
    (hlinear :
      sliceProductLinear mu nu ell n base lambdaOne x y +
          sliceProductLinear mu' nu' ell n base lambdaOne x' y' =
        sliceTargetDifference x y x' y') : False := by
  have hellPlane : InSliceInfinityPlane ell :=
    sliceInfinityQuadratic_annihilator hcubic
  by_cases hellZero : ell = 0
  · subst ell
    have hqQuad : lambdaOne = 0 ∧ quadMu = lambdaInfinity := by
      apply solve_infinity_quadratic_zero_first
      simpa [SliceQuadraticEquationInfinity, vectorWedge] using hquad
    have hqQuad' : lambdaOne = 0 ∧ quadMu' = lambdaInfinity := by
      apply solve_infinity_quadratic_zero_first
      simpa [SliceQuadraticEquationInfinity, vectorWedge] using hquad'
    have hq : lambdaOne = 0 ∧ mu = lambdaInfinity :=
      ⟨hqQuad.1, (hquadMu rfl).symm.trans hqQuad.2⟩
    have hq' : lambdaOne = 0 ∧ mu' = lambdaInfinity :=
      ⟨hqQuad'.1, (hquadMu' rfl).symm.trans hqQuad'.2⟩
    have hmu : mu = mu' := hq.2.trans hq'.2.symm
    rw [hq.1] at hlinear
    have hzero : sliceTargetDifference x y x' y' = 0 := by
      rw [← hlinear, hmu]
      funext i
      simp only [Pi.add_apply, Pi.zero_apply, sliceProductLinear, Pi.smul_apply, smul_eq_mul,
        pointwiseLinearProduct, zero_mul]
      exact CharTwo.add_self_eq_zero _
    exact distinct_corner_target_difference_not_in_infinity_plane hdistinct
      (hzero ▸ InSliceInfinityPlane.zero)
  · have hwedge (muS : F₂)
        (hqS : SliceQuadraticEquationInfinity muS ell n
          lambdaOne lambdaInfinity) :
        vectorWedge ell n =
          lambdaOne • sliceQuadraticA +
            (muS + lambdaInfinity) • sliceInfinityQuadratic := by
      funext i j
      have hc := congrFun (congrFun hqS i) j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hc
      change vectorWedge ell n i j =
        lambdaOne * sliceQuadraticA i j +
          (muS + lambdaInfinity) * sliceInfinityQuadratic i j
      apply sub_eq_zero.mp
      rw [CharTwo.sub_eq_add]
      calc
        vectorWedge ell n i j +
            (lambdaOne * sliceQuadraticA i j +
              (muS + lambdaInfinity) * sliceInfinityQuadratic i j) =
          muS * sliceInfinityQuadratic i j + vectorWedge ell n i j +
            lambdaOne * sliceQuadraticA i j +
            lambdaInfinity * sliceInfinityQuadratic i j := by ring
        _ = 0 := hc
    have hw := hwedge quadMu hquad
    have hw' := hwedge quadMu' hquad'
    have hOne : lambdaOne = 0 := by
      rcases f2_eq_zero_or_one lambdaOne with hzero | hone
      · exact hzero
      · exfalso
        rw [hone, one_smul] at hw
        exact vectorWedge_eq_infinity_plus_typeA_impossible
          hellPlane hellZero hw
    rw [hOne, zero_smul, zero_add] at hw hw'
    have hnPlane : InSliceInfinityPlane n :=
      second_factor_mem_of_infinity_wedge hellPlane hellZero hw
    have hleftPlane := sliceProductLinear_add_base_infinity_mem
      mu nu x y ell n base hellPlane hnPlane
    have hrightPlane := sliceProductLinear_add_base_infinity_mem
      mu' nu' x' y' ell n base hellPlane hnPlane
    rw [hOne] at hlinear
    have hsumPlane := hleftPlane.add hrightPlane
    have heq :
        (sliceProductLinear mu nu ell n base 0 x y + base) +
            (sliceProductLinear mu' nu' ell n base 0 x' y' + base) =
          sliceTargetDifference x y x' y' := by
      rw [← hlinear]
      funext i
      simp
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    rw [heq] at hsumPlane
    exact distinct_corner_target_difference_not_in_infinity_plane
      hdistinct hsumPlane

end

end N4
end UnrestrictedBooleanMul
