/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.EllipticCurve.PlaceDictionary
import Mathlib.Tactic.Convert
import Mathlib.Tactic.ByContra

/-!
# Degree-one places are rational Weierstrass points

Unlike the all-place dichotomy over an algebraically closed field, this direction only uses that
the residue field has dimension one over the base field.
-/

@[expose] public section

open FunctionField
open FunctionField.Chart
open scoped Polynomial RatFunc

namespace WeierstrassCurve.Affine.Chart

noncomputable section

variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K]

local instance instCoordinateConstantsTowerPic : IsScalarTower k W.CoordinateRing K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k k[X] W.CoordinateRing,
      ← IsScalarTower.algebraMap_apply k[X] W.CoordinateRing K]

lemma maximal_eq_XYIdeal_of_finrank_one (I : Ideal W.CoordinateRing) [I.IsMaximal]
    (hfin : Module.finrank k (W.CoordinateRing ⧸ I) = 1) :
    ∃ x y : k, ∃ _ : W.Nonsingular x y,
      I = CoordinateRing.XYIdeal W x (Polynomial.C y) := by
  let L := W.CoordinateRing ⧸ I
  let : Field L := Ideal.Quotient.field I
  have hbij : Function.Bijective (algebraMap k L) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfin
  obtain ⟨x, hx⟩ := hbij.2
    (Ideal.Quotient.mk I (CoordinateRing.mk W (Polynomial.C Polynomial.X)))
  obtain ⟨y, hy⟩ := hbij.2
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

include W in
omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
lemma exists_point_of_place_degree_one (v : PlaceA k K) (hv : placeDegree k K v = 1) :
    ∃ P : W.Point, v = placeOfPoint W K P := by
  rcases v with v | v
  · let e := coordinateRingEquivIntegers W K
    let E := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e.toRingEquiv
    let u := E.symm v
    let : u.asIdeal.IsMaximal := u.isPrime.isMaximal u.ne_bot
    have hideal : v.asIdeal = u.asIdeal.map e.toRingHom := by
      change v.asIdeal = (v.asIdeal.comap e.toRingHom).map e.toRingHom
      exact (Ideal.map_comap_eq_self_of_equiv e.toRingEquiv v.asIdeal).symm
    let ek : W.CoordinateRing ≃ₐ[k] ringOfIntegers k K := e.restrictScalars k
    let eqQuot : (W.CoordinateRing ⧸ u.asIdeal) ≃ₐ[k]
        (ringOfIntegers k K ⧸ v.asIdeal) :=
      Ideal.quotientEquivAlg u.asIdeal v.asIdeal ek hideal
    have hfin : Module.finrank k (W.CoordinateRing ⧸ u.asIdeal) = 1 := by
      rw [eqQuot.toLinearEquiv.finrank_eq]
      exact hv
    obtain ⟨x, y, h, hu⟩ := maximal_eq_XYIdeal_of_finrank_one W u.asIdeal hfin
    have hueq : u = affineHeightOne W h := by
      apply IsDedekindDomain.HeightOneSpectrum.ext
      exact hu
    refine ⟨.some x y h, ?_⟩
    change Sum.inl v = Sum.inl (E (affineHeightOne W h))
    congr 1
    rw [← hueq, Equiv.apply_symm_apply]
  · refine ⟨.zero, ?_⟩
    exact congrArg Sum.inr (infinity_heightOne_unique W K v (infinityHeightOne (k := k) K))

end
end WeierstrassCurve.Affine.Chart
