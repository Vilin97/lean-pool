/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.DivisorialVisibleFrameStageAssembly
import LeanPool.Stafford38.Stafford38.Geometry.ExactVisibleDivisorFrameInterface
import LeanPool.Stafford38.Stafford38.Geometry.KaehlerDVRVisibility
import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveDivisorOrderGap
import LeanPool.Stafford38.Stafford38.Geometry.RelativeRetainedBoundaryPlace

/-!
Existence of a divisorial frame satisfying the exact visibility interface.
-/

namespace Stafford38.Geometry.ExactDivisorialVisibleFrameExistence

open IsLocalRing Polynomial
open Stafford38
open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalBaseVariety
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.ComponentProjectiveOrder
open Stafford38.Geometry.DivisorTangentLattice
open Stafford38.Geometry.KaehlerDVRVisibility
open Stafford38.Geometry.ProjectiveDivisorOrderGap
open Stafford38.Geometry.ProjectiveValuationNormalization
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedDVR
open Stafford38.Geometry.ExactVisibleDivisorFrameInterface
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence

noncomputable section


universe u

open Stafford38.Geometry.AffineComponentCoordinateSplit

/-- The affine coordinates generate the function field of a prime component.
This is the exact generation hypothesis consumed by the lane-C stage
assembly. -/
theorem componentCoordinate_adjoin_eq_top
    {k : Type u} [Field k] {m : ℕ}
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    IntermediateField.adjoin k (Set.range (componentCoordinate P)) = ⊤ := by
  let R := MvPolynomial (Fin m) k ⧸ P.asIdeal
  let K := FractionRing R
  let L : IntermediateField k K :=
    IntermediateField.adjoin k (Set.range (componentCoordinate P))
  have hpoly (p : MvPolynomial (Fin m) k) :
      algebraMap R K (Ideal.Quotient.mk P.asIdeal p) ∈ L := by
    induction p using MvPolynomial.induction_on with
    | C c =>
        rw [← MvPolynomial.algebraMap_eq,
          Ideal.Quotient.mk_algebraMap,
          ← IsScalarTower.algebraMap_apply k R K]
        exact L.algebraMap_mem c
    | add p q hp hq =>
        rw [map_add, map_add]
        exact L.add_mem hp hq
    | mul_X p i hp =>
        rw [map_mul, map_mul]
        apply L.mul_mem hp
        exact IntermediateField.subset_adjoin k _ ⟨i, rfl⟩
  have hquot (z : R) : algebraMap R K z ∈ L := by
    refine Quotient.inductionOn z ?_
    intro p
    exact hpoly p
  apply top_unique
  intro z _
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R z
  rw [← hab]
  exact L.div_mem (hquot a) (hquot b)

theorem coordinateZeroLocal_maximalIdeal_eq_span (E : Type u) [Field E] :
    maximalIdeal (CoordinateZeroLocalRing E) =
      Ideal.span
        {algebraMap (Polynomial E) (CoordinateZeroLocalRing E) Polynomial.X} := by
  calc
    maximalIdeal (CoordinateZeroLocalRing E) =
        Ideal.map (algebraMap (Polynomial E) (CoordinateZeroLocalRing E))
          (coordinateZeroPrime E) :=
      (IsLocalization.AtPrime.map_eq_maximalIdeal
        (coordinateZeroPrime E) (CoordinateZeroLocalRing E)).symm
    _ = Ideal.map (algebraMap (Polynomial E) (CoordinateZeroLocalRing E))
          (Ideal.span {Polynomial.X}) := rfl
    _ = Ideal.span
          {algebraMap (Polynomial E) (CoordinateZeroLocalRing E) Polynomial.X} := by
      rw [Ideal.map_span, Set.image_singleton]

/-- The coordinate-zero local ring maps to a valuation ring that contains
the coefficient field and the selected element in its maximal ideal. -/
def coordinateZeroLocalFactor
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (E : IntermediateField k K)
    (V : ValuationSubring K) [IsLocalRing V.toSubring]
    (hEV : ∀ z : E, (z : K) ∈ V.toSubring)
    (x : K) (hxV : x ∈ V.toSubring)
    (hxm : (⟨x, hxV⟩ : V.toSubring) ∈ maximalIdeal V.toSubring) :
    CoordinateZeroLocalRing E →+* V.toSubring := by
  let c : E →+* V.toSubring :=
    Stafford38.Geometry.LaneC.coeffHom E V hEV
  let xV : V.toSubring := ⟨x, hxV⟩
  let g : Polynomial E →+* V.toSubring := Polynomial.eval₂RingHom c xV
  exact IsLocalization.lift (S := CoordinateZeroLocalRing E)
    (M := (coordinateZeroPrime E).primeCompl) (g := g) fun p ↦ by
      have hp0 : (p : Polynomial E).coeff 0 ≠ 0 := by
        intro hp0
        apply p.property
        change (p : Polynomial E) ∈ Ideal.span {Polynomial.X}
        rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]
        exact hp0
      have hcunit : IsUnit (c ((p : Polynomial E).coeff 0)) :=
        (isUnit_iff_ne_zero.mpr hp0).map c
      apply (residue_ne_zero_iff_isUnit (g (p : Polynomial E))).mp
      have hresx : residue V.toSubring xV = 0 :=
        (residue_eq_zero_iff xV).mpr hxm
      have hresconst : residue V.toSubring
          (c ((p : Polynomial E).coeff 0)) ≠ 0 :=
        (residue_ne_zero_iff_isUnit
          (c ((p : Polynomial E).coeff 0))).mpr hcunit
      have hdecomp := Polynomial.X_mul_divX_add (p : Polynomial E)
      have heval : residue V.toSubring (g (p : Polynomial E)) =
          residue V.toSubring (c ((p : Polynomial E).coeff 0)) := by
        calc
          residue V.toSubring (g (p : Polynomial E)) =
              residue V.toSubring
                (g (Polynomial.X * Polynomial.divX (p : Polynomial E) +
                  Polynomial.C ((p : Polynomial E).coeff 0))) :=
            congrArg (fun z ↦ residue V.toSubring (g z)) hdecomp.symm
          _ = residue V.toSubring (c ((p : Polynomial E).coeff 0)) := by
            rw [map_add, map_mul]
            change residue V.toSubring (Polynomial.eval₂ c xV Polynomial.X) *
                residue V.toSubring
                  (Polynomial.eval₂ c xV (Polynomial.divX (p : Polynomial E))) +
                residue V.toSubring
                  (Polynomial.eval₂ c xV
                    (Polynomial.C ((p : Polynomial E).coeff 0))) = _
            rw [Polynomial.eval₂_X, Polynomial.eval₂_C, hresx,
              zero_mul, zero_add]
      rw [heval]
      exact hresconst

theorem coordinateZeroLocalFactor_map_X
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (E : IntermediateField k K)
    (V : ValuationSubring K) [IsLocalRing V.toSubring]
    (hEV : ∀ z : E, (z : K) ∈ V.toSubring)
    (x : K) (hxV : x ∈ V.toSubring)
    (hxm : (⟨x, hxV⟩ : V.toSubring) ∈ maximalIdeal V.toSubring) :
    coordinateZeroLocalFactor E V hEV x hxV hxm
        (algebraMap (Polynomial E) (CoordinateZeroLocalRing E) Polynomial.X) =
      (⟨x, hxV⟩ : V.toSubring) := by
  rw [coordinateZeroLocalFactor, IsLocalization.lift_eq]
  exact Polynomial.eval₂_X _ _

theorem coordinateZeroLocalFactor_isLocal
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (E : IntermediateField k K)
    (V : ValuationSubring K) [IsLocalRing V.toSubring]
    (hEV : ∀ z : E, (z : K) ∈ V.toSubring)
    (x : K) (hxV : x ∈ V.toSubring)
    (hxm : (⟨x, hxV⟩ : V.toSubring) ∈ maximalIdeal V.toSubring) :
    IsLocalHom (coordinateZeroLocalFactor E V hEV x hxV hxm) := by
  let f := coordinateZeroLocalFactor E V hEV x hxV hxm
  apply (IsLocalRing.local_hom_TFAE f).out 4 1 |>.mp
  intro z hz
  rw [coordinateZeroLocal_maximalIdeal_eq_span,
    Ideal.mem_span_singleton] at hz
  obtain ⟨a, rfl⟩ := hz
  change f
      (algebraMap (Polynomial E) (CoordinateZeroLocalRing E) Polynomial.X * a) ∈
    maximalIdeal V.toSubring
  rw [map_mul, coordinateZeroLocalFactor_map_X E]
  exact Ideal.mul_mem_right _ _ hxm

theorem coordinateZeroLocalFactor_residue_finite
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (E : IntermediateField k K) (V : ValuationSubring K)
    [IsLocalRing V.toSubring]
    (hEV : ∀ z : E, (z : K) ∈ V.toSubring)
    (x : K) (hxV : x ∈ V.toSubring)
    (hxm : (⟨x, hxV⟩ : V.toSubring) ∈ maximalIdeal V.toSubring)
    (hfinite :
      letI : Algebra E V.toSubring :=
        (Stafford38.Geometry.LaneC.coeffHom E V hEV).toAlgebra
      Module.Finite E (ResidueField V.toSubring)) :
    let f := coordinateZeroLocalFactor E V hEV x hxV hxm
    let hf : IsLocalHom f :=
      coordinateZeroLocalFactor_isLocal E V hEV x hxV hxm
    ResidueExtensionFinite f hf := by
  let f := coordinateZeroLocalFactor E V hEV x hxV hxm
  let hf : IsLocalHom f :=
    coordinateZeroLocalFactor_isLocal E V hEV x hxV hxm
  let : Algebra E V.toSubring :=
    (Stafford38.Geometry.LaneC.coeffHom E V hEV).toAlgebra
  let : Module.Finite E (ResidueField V.toSubring) := hfinite
  let : Algebra (CoordinateZeroLocalRing E) V.toSubring := f.toAlgebra
  let : IsLocalHom (algebraMap (CoordinateZeroLocalRing E) V.toSubring) := hf
  let e₁ : E ≃+* ResidueField (CoordinateZeroLocalRing E) :=
    (coordinateResidueEquiv E).symm
  let e₂ : ResidueField V.toSubring ≃+* ResidueField V.toSubring :=
    RingEquiv.refl _
  have he₁ (z : E) : e₁ z =
      algebraMap E (ResidueField (CoordinateZeroLocalRing E)) z := by
    apply (coordinateResidueEquiv E).injective
    simp only [e₁, RingEquiv.apply_symm_apply,
      coordinateResidueEquiv_algebraMap]
  have hcompat :
      (algebraMap (ResidueField (CoordinateZeroLocalRing E))
          (ResidueField V.toSubring)).comp e₁.toRingHom =
        e₂.toRingHom.comp (algebraMap E (ResidueField V.toSubring)) := by
    ext z
    rw [RingHom.comp_apply, RingHom.comp_apply]
    change algebraMap (ResidueField (CoordinateZeroLocalRing E))
        (ResidueField V.toSubring) (e₁ z) =
      e₂ (algebraMap E (ResidueField V.toSubring) z)
    rw [he₁]
    change residue V.toSubring
        (f (algebraMap E (CoordinateZeroLocalRing E) z)) =
      residue V.toSubring
        (Stafford38.Geometry.LaneC.coeffHom E V hEV z)
    dsimp only [f]
    rw [IsScalarTower.algebraMap_apply E (Polynomial E)
      (CoordinateZeroLocalRing E) z]
    rw [coordinateZeroLocalFactor, IsLocalization.lift_eq]
    simp
  change Module.Finite (ResidueField (CoordinateZeroLocalRing E))
    (ResidueField V.toSubring)
  exact Module.Finite.of_equiv_equiv e₁ e₂ hcompat

/-- Package the particular DVR produced by the stage assembly as retained
boundary data, without replacing its parameter by a uniformizer. -/
def retainedDataOfValuation
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (E : IntermediateField k K) (V : ValuationSubring K)
    (hEV : ∀ z : E, (z : K) ∈ V.toSubring)
    (hVdvr : IsDiscreteValuationRing V.toSubring)
    (x : K) (hxV : x ∈ V.toSubring)
    (htrans : Transcendental E x)
    (hxm : (⟨x, hxV⟩ : V.toSubring) ∈ maximalIdeal V.toSubring)
    (hfinite :
      letI : IsLocalRing V.toSubring := hVdvr.toIsLocalRing
      letI : Algebra E V.toSubring :=
        (Stafford38.Geometry.LaneC.coeffHom E V hEV).toAlgebra
      Module.Finite E (ResidueField V.toSubring)) : Data k K x := by
  letI : IsLocalRing V.toSubring := hVdvr.toIsLocalRing
  let xV : V.toSubring := ⟨x, hxV⟩
  let f : CoordinateZeroLocalRing E →+* V.toSubring :=
    coordinateZeroLocalFactor E V hEV x hxV hxm
  let hf : IsLocalHom f :=
    coordinateZeroLocalFactor_isLocal E V hEV x hxV hxm
  let ambient : Algebra (CoordinateZeroLocalRing E) K :=
    (V.toSubring.subtype.comp f).toAlgebra
  letI : Algebra (CoordinateZeroLocalRing E) K := ambient
  have tower : IsScalarTower E (CoordinateZeroLocalRing E) K := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change (z : K) =
      ((f (algebraMap E (CoordinateZeroLocalRing E) z) : V.toSubring) : K)
    rw [IsScalarTower.algebraMap_apply E (Polynomial E)
      (CoordinateZeroLocalRing E) z]
    dsimp only [f]
    rw [coordinateZeroLocalFactor, IsLocalization.lift_eq]
    simp [Stafford38.Geometry.LaneC.coeffHom]
  have coordinate_eq :
      algebraMap (CoordinateZeroLocalRing E) K
          (algebraMap (Polynomial E) (CoordinateZeroLocalRing E) Polynomial.X) = x := by
    change ((f
      (algebraMap (Polynomial E) (CoordinateZeroLocalRing E) Polynomial.X) :
        V.toSubring) : K) = x
    rw [coordinateZeroLocalFactor_map_X E]
  have xV_ne : xV ≠ 0 := by
    intro hx0
    apply htrans
    have hx0K : x = 0 := congrArg Subtype.val hx0
    exact hx0K ▸ isAlgebraic_zero
  have xV_nonunit : ¬ IsUnit xV := by
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    exact hxm
  have hresfinite : ResidueExtensionFinite f hf :=
    coordinateZeroLocalFactor_residue_finite E V hEV x hxV hxm hfinite
  let place : RetainedDVRPlace (CoordinateZeroLocalRing E) (L := K)
      (algebraMap (Polynomial E) (CoordinateZeroLocalRing E) Polynomial.X) :=
    { valuation := V
      isDiscrete := hVdvr
      parameter := xV
      parameter_eq := coordinate_eq.symm
      parameter_ne := xV_ne
      parameter_nonunit := xV_nonunit
      factor := f
      factor_commutes := rfl
      factor_isLocal := hf
      residue_finite := hresfinite }
  exact
    { coefficientField := E
      coordinate_transcendental := htrans
      ambientAlgebra := ambient
      coefficientTower := tower
      coordinate_eq := coordinate_eq
      place := place }

/-- The stage-assembly place, its normalized projective column, and the
Kähler image together discharge the exact residual.  The element `t` below
is a separately chosen DVR uniformizer; the retained parameter remains the
selected affine coordinate and may have higher order. -/
theorem exactDivisorialVisibleFrameExistence :
    ExactDivisorialVisibleFrameExistence.{u} := by
  intro k _ _ _ n N d hn hdisjoint P hP htrans
  let i : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let K := ComponentFractionField P
  obtain ⟨E, V, hEV, hVdvr, hxV, htransE, hxm, hEfin, hkaehler, halgAll⟩ :=
    Stafford38.Geometry.LaneC.divisorialVisibleFrameExistence
      k K (n + 1) (componentCoordinate P) i
        (componentCoordinate_adjoin_eq_top P) htrans
  let : IsLocalRing V.toSubring := hVdvr.toIsLocalRing
  let : Algebra E V.toSubring :=
    (Stafford38.Geometry.LaneC.coeffHom E V hEV).toAlgebra
  let : Algebra k V.toSubring :=
    (Stafford38.Geometry.LaneC.groundHom E V hEV).toAlgebra
  let : Algebra V.toSubring K := V.toSubring.subtype.toAlgebra
  let : SMul V.toSubring K := V.toSubring.subtype.toAlgebra.toSMul
  let : SMul k V.toSubring :=
    (Stafford38.Geometry.LaneC.groundHom E V hEV).toAlgebra.toSMul
  let : SMul k K := (inferInstance : Algebra k K).toSMul
  let : IsScalarTower k V.toSubring K :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap k K c = (algebraMap k E c : K)
      exact IsScalarTower.algebraMap_apply k E K c
  let : Module.Finite V.toSubring (Ω[V.toSubring⁄k]) := hkaehler
  let W : Data k K (componentCoordinate P i) :=
    retainedDataOfValuation E V hEV hVdvr (componentCoordinate P i) hxV
      htransE hxm hEfin
  let : Algebra (CoordinateZeroLocalRing W.coefficientField) K :=
    W.ambientAlgebra
  obtain ⟨chart, qraw, scale, hscale, hchartRaw, hqraw⟩ :=
    exists_normalized_projective_lift V (componentProjectivePoint P)
      ⟨0, by simp [componentProjectivePoint]⟩
  let q : Fin (n + 1 + 1) → V.toSubring := fun a =>
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
  have hBP :
      reducedOrderBaseIdeal k
          (canonicalRightIdeal (presentedCoordinate k n) d N) ≤ P.asIdeal :=
    hP.1.2
  have hq0nonunit : ¬ IsUnit (q 0) :=
    normalizedComponentProjectivePoint_zero_nonunit
      (canonicalRightIdeal (presentedCoordinate k n) d N) i hdisjoint P hBP
      W q scale hq
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
  let Q : Fin (n + 1) → V.toSubring := fun j => q (Fin.succ j)
  have hQj₀ : Q j₀ = 1 := hchart
  have hq0frame : q 0 = t ^ a * (u₀ : V.toSubring) := by
    simpa [mul_comm] using hq0factor
  have hq1frame :
      q (Fin.succ i) = t ^ (a + e) * (u₁ : V.toSubring) := by
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
    change (q (Fin.succ ⟨0, Nat.zero_lt_succ n⟩) : K) =
      (q 0 : K) * componentCoordinate P ⟨0, Nat.zero_lt_succ n⟩ at hv
    calc
      (q (Fin.succ ⟨0, Nat.zero_lt_succ n⟩) : K) =
          (q 0 : K) * componentCoordinate P ⟨0, Nat.zero_lt_succ n⟩ := hv
      _ = (q 0 : K) * (W.place.parameter : K) := by
        rw [W.parameter_eq_coordinate]
  · exact ⟨D, hD0, hD1, fun j => by rw [hDQ]⟩

/-- Trust-zero production of the exact higher-dimensional visible-frame
input used by the terminal lane-C consumer. -/
theorem higherDimensionalCanonicalVisibleDivisorFrameProduction :
    HigherDimensionalCanonicalVisibleDivisorFrameProduction.{u} :=
  higherDimensionalCanonicalVisibleDivisorFrameProduction_of_exactResidual
    exactDivisorialVisibleFrameExistence


end

end Stafford38.Geometry.ExactDivisorialVisibleFrameExistence
