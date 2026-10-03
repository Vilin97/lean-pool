/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuarticPlaneNormalization

/-!
# Exterior geometry for the zero-place slice argument

The quartic exclusion leaves two six-variable complementary quadratic
geometries.  The type-A form is decomposable and its linear annihilator is
exactly its two-dimensional support.  The type-B form has alternating rank
four and therefore has no nonzero linear annihilator.  Everything below is
proved from fixed exterior coordinates; no circuits or truth tables are
enumerated.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The two anchor variables used to slice the Boolean identities. -/
@[expose] def sliceX : LinearForm := aLinear 0
/-- The second polynomial constant coefficient, used as a slice anchor. -/
@[expose] def sliceY : LinearForm := bLinear 0

/-- The first complementary target directions. -/
@[expose] def sliceU : LinearForm := aLinear 1
/-- The second polynomial linear coefficient, complementary to its slice anchor. -/
@[expose] def sliceV : LinearForm := bLinear 1

/-- Sums of the three variables complementary to the zero place. -/
@[expose] def sliceABar : LinearForm := placeA 1 + placeA 0
/-- The sum of the three second-polynomial input variables away from the zero-place anchor. -/
@[expose] def sliceBBar : LinearForm := placeB 1 + placeB 0

/-- Type A complementary quadratic part. -/
@[expose] def sliceQuadraticA : TwoForm := vectorWedge sliceABar sliceBBar

/-- The extra infinity-place term producing type B. -/
@[expose] def sliceInfinityQuadratic : TwoForm :=
  vectorWedge (placeA 2) (placeB 2)

/-- Type B complementary quadratic part. -/
@[expose] def sliceQuadraticB : TwoForm :=
  sliceQuadraticA + sliceInfinityQuadratic

/-- The plane spanned by the complementary evaluation-at-one input directions. -/
@[expose]
def InSliceComplementPlane (ell : LinearForm) : Prop :=
  ∃ a b : F₂, ell = a • sliceABar + b • sliceBBar

instance (ell : LinearForm) : Decidable (InSliceComplementPlane ell) := by
  unfold InSliceComplementPlane
  infer_instance

theorem sliceQuadraticA_ne_zero : sliceQuadraticA ≠ 0 := by
  intro h
  have hc := congrFun (congrFun h (aCoord 1)) (bCoord 1)
  simp [sliceQuadraticA, sliceABar, sliceBBar, vectorWedge, placeA, placeB, aCoord, bCoord] at hc

/-- The annihilator of the decomposable type-A quadratic is its support
plane. -/
theorem sliceQuadraticA_annihilator {ell : LinearForm}
    (h : vectorWedgeTwo ell sliceQuadraticA = 0) :
    InSliceComplementPlane ell := by
  exact mem_support_of_vectorWedgeTwo_zero ell sliceABar sliceBBar
    sliceQuadraticA_ne_zero h

/-- The type-B form has alternating rank four.  The selected triples expose
two independent cross blocks and force every coordinate of an annihilating
linear form to vanish. -/
theorem sliceQuadraticB_annihilator {ell : LinearForm}
    (h : vectorWedgeTwo ell sliceQuadraticB = 0) : ell = 0 := by
  have h0 := congrFun (congrFun (congrFun h 0) 1) 5
  have h1 := congrFun (congrFun (congrFun h 1) 3) 5
  have h2 := congrFun (congrFun (congrFun h 2) 3) 5
  have h3 := congrFun (congrFun (congrFun h 1) 3) 7
  have h4 := congrFun (congrFun (congrFun h 4) 1) 5
  have h5 := congrFun (congrFun (congrFun h 1) 5) 7
  have h6 := congrFun (congrFun (congrFun h 1) 6) 7
  have h7 := congrFun (congrFun (congrFun h 3) 5) 7
  simp [sliceQuadraticB, sliceQuadraticA, sliceInfinityQuadratic, sliceABar, sliceBBar,
    vectorWedgeTwo, vectorWedge, placeA, placeB]
    at h0 h1 h2 h3 h4 h5 h6 h7
  ring_nf at h0 h3 h4 h7
  simp [N3Certificate.two_eq_zero_f2] at h0 h1 h2 h3 h4 h5 h6 h7
  funext i
  fin_cases i
  · simpa using h0
  · simpa [h3] using h1
  · simpa [h3] using h2
  · simpa using h3
  · simpa using h4
  · simpa [h7] using h5
  · simpa [h7] using h6
  · simpa using h7

theorem sliceU_not_in_complement_plane :
    ¬ InSliceComplementPlane sliceU := by
  rintro ⟨a, b, h⟩
  have hb := congrFun h (bCoord 1)
  have ha := congrFun h (aCoord 2)
  have hu := congrFun h (aCoord 1)
  simp only [sliceU, aLinear, Pi.basisFun, aCoord, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.one_mod, Fin.mk_one, bCoord, Nat.reduceAdd, Fin.reduceFinMk,
    Module.Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply, ne_eq,
    Fin.reduceEq, not_false_eq_true, Pi.single_eq_of_ne, sliceABar, placeA,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.add_cons, Matrix.head_cons,
    Matrix.tail_cons, add_zero, Matrix.empty_add_empty, Matrix.smul_cons, smul_eq_mul,
    mul_one, mul_zero, Matrix.smul_empty, sliceBBar, placeB, Pi.add_apply, Matrix.cons_val,
    zero_add, Nat.reduceMod, Pi.single_eq_same] at hb ha hu
  subst a
  subst b
  contradiction

theorem sliceV_not_in_complement_plane :
    ¬ InSliceComplementPlane sliceV := by
  rintro ⟨a, b, h⟩
  have ha := congrFun h (aCoord 1)
  have hb := congrFun h (bCoord 2)
  have hv := congrFun h (bCoord 1)
  simp only [sliceV, bLinear, Pi.basisFun, bCoord, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.one_mod, Nat.reduceAdd, Fin.reduceFinMk, aCoord, Fin.mk_one,
    Module.Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply, ne_eq,
    Fin.reduceEq, not_false_eq_true, Pi.single_eq_of_ne, sliceABar, placeA,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.add_cons, Matrix.head_cons,
    Matrix.tail_cons, add_zero, Matrix.empty_add_empty, Matrix.smul_cons, smul_eq_mul,
    mul_one, mul_zero, Matrix.smul_empty, sliceBBar, placeB, Pi.add_apply, Nat.reduceMod,
    Matrix.cons_val, zero_add, Pi.single_eq_same] at ha hb hv
  subst a
  subst b
  contradiction

/-- A nonzero combination of the two target difference directions cannot
lie in the type-A support plane. -/
theorem sliceUV_combination_not_in_complement_plane
    (a b : F₂) (hne : a ≠ 0 ∨ b ≠ 0) :
    ¬ InSliceComplementPlane (a • sliceU + b • sliceV) := by
  rintro ⟨p, q, h⟩
  have hp := congrFun h (aCoord 2)
  have hq := congrFun h (bCoord 2)
  have ha := congrFun h (aCoord 1)
  have hb := congrFun h (bCoord 1)
  simp only [sliceU, aLinear, Pi.basisFun, aCoord, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.one_mod, Fin.mk_one, Module.Basis.coe_ofEquivFun, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, sliceV, bLinear, bCoord, Nat.reduceAdd, Fin.reduceFinMk,
    Nat.reduceMod, Pi.add_apply, Pi.smul_apply, ne_eq, Fin.reduceEq, not_false_eq_true,
    Pi.single_eq_of_ne, smul_eq_mul, mul_zero, add_zero, sliceABar, placeA,
    Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.add_cons, Matrix.head_cons,
    Matrix.tail_cons, Matrix.empty_add_empty, Matrix.smul_cons, mul_one, Matrix.smul_empty,
    sliceBBar, placeB, Matrix.cons_val, zero_add, Pi.single_eq_same] at hp hq ha hb
  subst p
  subst q
  exact hne.elim (fun hna => hna ha) (fun hnb => hnb hb)

end

end N4
end UnrestrictedBooleanMul
