/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.EllipticCurve.Infinity
import LeanPool.RiemannRochFunctionFields.EllipticCurve.Dedekind
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Place–point dictionary for Weierstrass function fields
For an elliptic Weierstrass curve `W/k`, affine nonsingular points should correspond to
degree-one places, with a unique degree-one place at infinity.

Following the `ClassGroup.mk` design, the function field is an abstract field `K` linked to
the curve by `[Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]`, carrying the
The coordinate instance pack. Working over the concrete `FractionRing W.CoordinateRing` would
tie every statement to one `Semiring` derivation path and break instance unification
(`OreLocalization.instSemiring` vs `FractionRing.field`).
-/

@[expose] public section

open FunctionField
open FunctionField.Chart

open scoped Polynomial RatFunc

namespace WeierstrassCurve.Affine.Chart

variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]

variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]

variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]

/-! ## Finite places -/

/-- The integral-closure identification between the affine coordinate ring and the
finite-integer ring of its fraction field. -/
noncomputable def coordinateRingEquivIntegers :
    W.CoordinateRing ≃ₐ[k[X]] ringOfIntegers k K :=
  IsIntegralClosure.equiv k[X] W.CoordinateRing K (ringOfIntegers k K)

omit [W.IsElliptic] in
/-- The ideal of a nonsingular affine point is maximal. -/
lemma XYIdeal_isMaximal {x y : k} (h : W.Nonsingular x y) :
    (CoordinateRing.XYIdeal W x (Polynomial.C y)).IsMaximal := by
  let e := CoordinateRing.quotientXYIdealEquiv (W' := W) (x := x)
    (y := Polynomial.C y) h.1
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr
    (e.toRingEquiv.isField (Field.toIsField k))

omit [W.IsElliptic] in
/-- The ideal of an affine point is nonzero. -/
lemma XYIdeal_ne_bot {x y : k} (_h : W.Nonsingular x y) :
    CoordinateRing.XYIdeal W x (Polynomial.C y) ≠ ⊥ := by
  intro hbot
  apply CoordinateRing.XClass_ne_zero (W' := W) x
  rw [← Ideal.mem_bot, ← hbot]
  exact Ideal.subset_span (Set.mem_insert _ _)

/-- A nonsingular affine point as a height-one prime of the coordinate ring. -/
noncomputable def affineHeightOne {x y : k} (h : W.Nonsingular x y) :
    IsDedekindDomain.HeightOneSpectrum W.CoordinateRing :=
  ⟨CoordinateRing.XYIdeal W x (Polynomial.C y),
    (XYIdeal_isMaximal W h).isPrime, XYIdeal_ne_bot W h⟩

/-- The finite place corresponding to a nonsingular affine pair. -/
noncomputable def finitePlaceOfAffine {x y : k} (h : W.Nonsingular x y) : PlaceA k K :=
  Sum.inl (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
    (coordinateRingEquivIntegers W K).toRingEquiv (affineHeightOne W h))

omit [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
/-- A rational affine point gives a degree-one finite place. -/
lemma finitePlaceOfAffine_degree {x y : k} (h : W.Nonsingular x y) :
    placeDegree k K (finitePlaceOfAffine W K h) = 1 := by
  let e := coordinateRingEquivIntegers W K
  let I := CoordinateRing.XYIdeal W x (Polynomial.C y)
  let v := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e.toRingEquiv
    (affineHeightOne W h)
  have hv : v.asIdeal = I.map e.toRingHom := by
    change I.comap e.symm.toRingHom = I.map e.toRingHom
    exact Ideal.comap_symm e.toRingEquiv
  let ek : W.CoordinateRing ≃ₐ[k] ringOfIntegers k K := e.restrictScalars k
  let eqQuot : (W.CoordinateRing ⧸ I) ≃ₐ[k] (ringOfIntegers k K ⧸ v.asIdeal) :=
    Ideal.quotientEquivAlg I v.asIdeal ek hv
  change Module.finrank k (ringOfIntegers k K ⧸ v.asIdeal) = 1
  rw [← eqQuot.toLinearEquiv.finrank_eq]
  let exy := CoordinateRing.quotientXYIdealEquiv (W' := W) (x := x)
    (y := Polynomial.C y) h.1
  rw [exy.toLinearEquiv.finrank_eq]
  exact Module.finrank_self k

/-- Over an algebraically closed field, every maximal ideal of the affine coordinate ring
is the ideal of a nonsingular rational point. -/
lemma maximal_eq_XYIdeal [IsAlgClosed k] (I : Ideal W.CoordinateRing) [I.IsMaximal] :
    ∃ x y : k, ∃ _ : W.Nonsingular x y,
      I = CoordinateRing.XYIdeal W x (Polynomial.C y) := by
  let L := W.CoordinateRing ⧸ I
  let : Field L := Ideal.Quotient.field I
  have : Algebra.FiniteType k L := Algebra.FiniteType.quotient k I
  have : Module.Finite k L := finite_of_finite_type_of_isJacobsonRing k L
  have : Algebra.IsIntegral k L := Algebra.IsIntegral.of_finite k L
  obtain ⟨x, hx⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2
    (Ideal.Quotient.mk I (CoordinateRing.mk W (Polynomial.C Polynomial.X)))
  obtain ⟨y, hy⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2
    (Ideal.Quotient.mk I (CoordinateRing.mk W Polynomial.X))
  have heq : W.Equation x y := by
    apply (W.map_equation (algebraMap k L).injective x y).mp
    rw [hx, hy]
    simpa [WeierstrassCurve.baseChange, WeierstrassCurve.map] using
      (coordinate_equation W).map (Ideal.Quotient.mk I)
  have hns : W.Nonsingular x y := W.equation_iff_nonsingular.mp heq
  have hle : CoordinateRing.XYIdeal W x (Polynomial.C y) ≤ I := by
    rw [CoordinateRing.XYIdeal, Ideal.span_le]
    rintro z (rfl | hz)
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp only [CoordinateRing.XClass, map_sub]
      rw [sub_eq_zero]
      change (Ideal.Quotient.mk I) (CoordinateRing.mk W (Polynomial.C Polynomial.X)) =
        algebraMap k L x
      exact hx.symm
    · have : z = CoordinateRing.YClass W (Polynomial.C y) := by simpa using hz
      subst z
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp only [CoordinateRing.YClass, map_sub]
      rw [sub_eq_zero]
      change (Ideal.Quotient.mk I) (CoordinateRing.mk W Polynomial.X) =
        algebraMap k L y
      exact hy.symm
  refine ⟨x, y, hns, ?_⟩
  exact ((XYIdeal_isMaximal W hns).eq_of_le (Ideal.IsMaximal.ne_top inferInstance) hle).symm

/-- The finite place corresponding to a nonsingular affine point `(x, y)`. -/
noncomputable def placeOfPoint : W.Point → PlaceA k K
  | .zero => infinityPlace K
  | .some _ _ h => finitePlaceOfAffine W K h

include W in
theorem placeOfPoint_deg_one (P : W.Point) :
    placeDegree k K (placeOfPoint W K P) = 1 := by
  cases P with
  | zero => exact infinityPlace_deg_one W K
  | some x y h => exact finitePlaceOfAffine_degree W K h

include W in
theorem place_dichotomy [IsAlgClosed k] (v : PlaceA k K) :
    (∃ P : W.Point, v = placeOfPoint W K P) ∨ v = infinityPlace K := by
  rcases v with v | v
  · let e := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
      (coordinateRingEquivIntegers W K).toRingEquiv
    let u := e.symm v
    let : u.asIdeal.IsMaximal := u.isPrime.isMaximal u.ne_bot
    obtain ⟨x, y, h, hu⟩ := maximal_eq_XYIdeal W u.asIdeal
    have hueq : u = affineHeightOne W h := by
      apply IsDedekindDomain.HeightOneSpectrum.ext
      exact hu
    left
    refine ⟨.some x y h, ?_⟩
    change Sum.inl v = Sum.inl (e (affineHeightOne W h))
    congr 1
    rw [← hueq, Equiv.apply_symm_apply]
  · right
    exact congrArg Sum.inr
      (infinity_heightOne_unique W K v (infinityHeightOne (k := k) K))

end WeierstrassCurve.Affine.Chart
