/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.ExactDivisorialVisibleFrameExistence

/-!
# Divisorial visible frames for arbitrary prime affine components

An invertible, transcendental coordinate on a prime affine component gives
a normalized visible divisor frame. This removes the canonical Weyl-support
hypotheses from the boundary producer. Identification of the resulting Laurent
direction with the smooth projective conormal closure is performed downstream
in the general asymptotic-conormal construction.
-/

namespace Stafford38.Geometry.GeneralDivisorialVisibleFrame

open IsLocalRing Polynomial
open Stafford38
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveOrder
open Stafford38.Geometry.ExactDivisorialVisibleFrameExistence
open Stafford38.Geometry.ExactVisibleDivisorFrameInterface
open Stafford38.Geometry.KaehlerDVRVisibility
open Stafford38.Geometry.ProjectiveDivisorOrderGap
open Stafford38.Geometry.ProjectiveValuationNormalization
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedDVR
open Stafford38.Geometry.DivisorTangentLattice

noncomputable section


universe u

/-- A polynomial inverse modulo the prime component forces the normalized
projective denominator to vanish at the retained boundary place. The visible
differential frame is then supplied by the generic divisorial construction. -/
theorem generalDivisorialVisibleFrameExistence
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (hunit : ∃ g : MvPolynomial (Fin m) k,
      MvPolynomial.X ⟨0, hm⟩ * g - 1 ∈ P.asIdeal)
    (htrans : Transcendental k
      (componentCoordinate P ⟨0, hm⟩)) :
    HasNormalizedCompatibleVisibleFrame P hm := by
  let i : Fin m := ⟨0, hm⟩
  let K := ComponentFractionField P
  obtain ⟨E, V, hEV, hVdvr, hxV, htransE, hxm, hEfin, hkaehler, halgAll⟩ :=
    Stafford38.Geometry.LaneC.divisorialVisibleFrameExistence
      k K m (componentCoordinate P) i
        (componentCoordinate_adjoin_eq_top P) htrans
  letI : IsLocalRing V.toSubring := hVdvr.toIsLocalRing
  letI : Algebra E V.toSubring :=
    (Stafford38.Geometry.LaneC.coeffHom E V hEV).toAlgebra
  letI : Algebra k V.toSubring :=
    (Stafford38.Geometry.LaneC.groundHom E V hEV).toAlgebra
  letI : Algebra V.toSubring K := V.toSubring.subtype.toAlgebra
  let : SMul V.toSubring K := V.toSubring.subtype.toAlgebra.toSMul
  let : SMul k V.toSubring :=
    (Stafford38.Geometry.LaneC.groundHom E V hEV).toAlgebra.toSMul
  let : SMul k K := (inferInstance : Algebra k K).toSMul
  letI : IsScalarTower k V.toSubring K :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap k K c = (algebraMap k E c : K)
      exact IsScalarTower.algebraMap_apply k E K c
  letI : Module.Finite V.toSubring (Ω[V.toSubring⁄k]) := hkaehler
  let W : Data k K (componentCoordinate P i) :=
    retainedDataOfValuation E V hEV hVdvr (componentCoordinate P i) hxV
      htransE hxm hEfin
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
    W.ambientAlgebra
  obtain ⟨chart, qraw, scale, hscale, hchartRaw, hqraw⟩ :=
    exists_normalized_projective_lift V (componentProjectivePoint P)
      ⟨0, by simp [componentProjectivePoint]⟩
  let q : Fin (m + 1) → V.toSubring := fun a =>
    ⟨qraw a, (qraw a).property⟩
  have hchart : q chart = 1 := by
    apply Subtype.ext
    exact congrArg Subtype.val hchartRaw
  have hq : ∀ a, (q a : K) = scale * componentProjectivePoint P a := by
    intro a
    exact hqraw a
  have hq0 : q 0 ≠ 0 := by
    intro hzero
    apply hscale
    have h := hq 0
    rw [hzero] at h
    simpa [componentProjectivePoint] using h.symm
  let xV : V.toSubring := ⟨componentCoordinate P i, hxV⟩
  have hratioV : q (Fin.succ i) = q 0 * xV := by
    apply Subtype.ext
    change (q (Fin.succ i) : K) = (q 0 : K) * componentCoordinate P i
    rw [hq, hq]
    simp [componentProjectivePoint]
  have hq0nonunit : ¬ IsUnit (q 0) := by
    obtain ⟨g, hg⟩ := hunit
    let F := K
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField) F :=
      W.ambientAlgebra
    let : SMul W.coefficientField (CoordinateZeroLocalRing W.coefficientField) :=
      (inferInstance : Algebra W.coefficientField
        (CoordinateZeroLocalRing W.coefficientField)).toSMul
    let : SMul (CoordinateZeroLocalRing W.coefficientField) F := W.ambientAlgebra.toSMul
    let : SMul W.coefficientField F :=
      (inferInstance : Algebra W.coefficientField F).toSMul
    letI : IsScalarTower W.coefficientField
        (CoordinateZeroLocalRing W.coefficientField) F := W.coefficientTower
    let phi : MvPolynomial (Fin m) k →+* F :=
      (algebraMap (MvPolynomial (Fin m) k ⧸ P.asIdeal) F).comp
        (Ideal.Quotient.mk P.asIdeal)
    have hphiC : phi.comp MvPolynomial.C = algebraMap k F := by
      ext c
      exact IsScalarTower.algebraMap_apply k
        (MvPolynomial (Fin m) k ⧸ P.asIdeal) F c
    have hphiX : ∀ j, phi (MvPolynomial.X j) = componentCoordinate P j := by
      intro j
      rfl
    have hpoly : phi g = MvPolynomial.eval₂ (algebraMap k F)
        (fun j ↦ componentCoordinate P j) g := by
      rw [MvPolynomial.map_mvPolynomial_eq_eval₂ phi g]
      change MvPolynomial.eval₂Hom (phi.comp MvPolynomial.C)
          (fun j ↦ phi (MvPolynomial.X j)) g =
        MvPolynomial.eval₂Hom (algebraMap k F)
          (fun j ↦ componentCoordinate P j) g
      apply MvPolynomial.eval₂Hom_congr hphiC
      · funext j
        exact hphiX j
      · rfl
    have hinverse : componentCoordinate P i *
        MvPolynomial.eval₂ (algebraMap k F)
          (fun j ↦ componentCoordinate P j) g = 1 := by
      have hzero : phi (MvPolynomial.X i * g - 1) = 0 := by
        have hmk : Ideal.Quotient.mk P.asIdeal
            (MvPolynomial.X i * g - 1) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr hg
        simpa [phi] using (congrArg
          (algebraMap (MvPolynomial (Fin m) k ⧸ P.asIdeal) F) hmk)
      rw [map_sub, map_mul, map_one, sub_eq_zero, hphiX, hpoly] at hzero
      exact hzero
    let coeff : k →+* V :=
      (relativeCoefficientMap W.coefficientField W.place).comp
        (algebraMap k W.coefficientField)
    have hcoeff : W.place.valuation.toSubring.subtype.comp coeff =
        algebraMap k F := by
      ext c
      change ((relativeCoefficientMap W.coefficientField W.place
        (algebraMap k W.coefficientField c) : V) : F) = algebraMap k F c
      calc
        ((relativeCoefficientMap W.coefficientField W.place
            (algebraMap k W.coefficientField c) : V) : F) =
            algebraMap W.coefficientField F
              (algebraMap k W.coefficientField c) :=
          DFunLike.congr_fun
            (relativeCoefficientMap_commutes W.coefficientField W.place)
            (algebraMap k W.coefficientField c)
        _ = algebraMap k F c :=
          IsScalarTower.algebraMap_apply k W.coefficientField F c
    exact normalized_denominator_nonunit_of_polynomial_inverse
      (V := W.place.valuation) (coeff := coeff) hcoeff
      (x := fun j ↦ componentCoordinate P j)
      (qzero := q 0) (q := fun j ↦ q (Fin.succ j)) (scale := scale)
      (i := i) (parameter := W.place.parameter) (g := g)
      (by simpa [componentProjectivePoint] using hq 0)
      (by intro j; simpa [componentProjectivePoint] using hq (Fin.succ j))
      W.parameter_eq_coordinate W.place.parameter_nonunit hinverse
  have halg := halgAll scale q hq ⟨chart, hchart⟩ hq0nonunit
  have hchart_ne : chart ≠ 0 := by
    intro hzero
    apply hq0nonunit
    rw [← hzero, hchart]
    exact isUnit_one
  obtain ⟨j₀, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hchart_ne
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V.toSubring
  have hq0max : q 0 ∈ maximalIdeal V.toSubring := by
    apply (IsLocalRing.mem_maximalIdeal (q 0)).2
    exact mem_nonunits_iff.mpr hq0nonunit
  have hxV_ne : xV ≠ 0 := by
    intro hx0
    apply htransE
    have hx0K : componentCoordinate P i = 0 := congrArg Subtype.val hx0
    exact hx0K ▸ isAlgebraic_zero
  obtain ⟨a, e, b, u₀, ur, u₁, ha, he, hb, hab,
      hq0factor, hparameterFactor, hu₁, hq1factor⟩ :=
    exists_uniformizer_strict_orderGap t ht (q 0) xV
      (q (Fin.succ i)) hq0 hxV_ne hq0max hxm hratioV
  let Q : Fin m → V.toSubring := fun j => q (Fin.succ j)
  have hQj₀ : Q j₀ = 1 := hchart
  have hq0frame : q 0 = t ^ a * (u₀ : V.toSubring) := by
    simpa [mul_comm] using hq0factor
  have hq1frame : q (Fin.succ i) = t ^ (a + e) * (u₁ : V.toSubring) := by
    simpa [hb, mul_comm] using hq1factor
  obtain ⟨D, hD0, hD1, hDt, hDu, hDw, hDQ, hDa, hDe, hDj, hDW⟩ :=
    exists_visibleDivisorFrame_of_kaehler_image
      (k := k) (F := K) (q 0) (q (Fin.succ i)) t
        (u₀ : V.toSubring) (u₁ : V.toSubring) Q a e j₀
        ht.maximalIdeal_eq ht.ne_zero u₀.isUnit
        (Nat.one_le_iff_ne_zero.mpr ha.ne')
        (Nat.one_le_iff_ne_zero.mpr he.ne') hq0frame hq1frame hQj₀ halg
  refine ⟨W, Fin.succ j₀, q, scale, hscale, hchart, hq0, hq, ?_, ?_⟩
  · apply Subtype.ext
    have hv := congrArg Subtype.val hratioV
    change (q (Fin.succ ⟨0, hm⟩) : K) =
      (q 0 : K) * componentCoordinate P ⟨0, hm⟩ at hv
    calc
      (q (Fin.succ ⟨0, hm⟩) : K) =
          (q 0 : K) * componentCoordinate P ⟨0, hm⟩ := hv
      _ = (q 0 : K) * (W.place.parameter : K) := by
        rw [W.parameter_eq_coordinate]
  · exact ⟨D, hD0, hD1, fun j => by rw [hDQ]⟩


end

end Stafford38.Geometry.GeneralDivisorialVisibleFrame
