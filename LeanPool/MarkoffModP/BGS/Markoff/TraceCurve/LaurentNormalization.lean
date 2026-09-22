/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.AlgebraicGeometry.SpecRingEquiv
import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.ChartLocalization
import Mathlib.RingTheory.Localization.Integral

/-!
# Normalized Laurent overlap transitions

This module lifts the explicit Laurent chart transitions to integral closures in the corresponding
fraction fields.  The lift is constructed directly: integrality is transported simultaneously
along the coordinate-ring equivalence and its induced fraction-field equivalence.  In particular,
no unproved `smooth implies normal` bridge is used.

The final cocycle is proved first in the fraction fields and then in the integral closures.  Its
domain hypotheses are precisely the domain instances obtained from the already-proved
irreducibility of the two affine chart equations.
-/

namespace BGS.Markoff

open AlgebraicGeometry

noncomputable section

section IntegralClosureTransport

variable {K A B C : Type*} [Field K]
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra K A] [Algebra K B] [Algebra K C]
variable [IsDomain A] [IsDomain B] [IsDomain C]

omit [IsDomain A] [IsDomain B] in
private theorem fractionRingEquiv_maps_integral
    (e : A ≃ₐ[K] B) (x : integralClosure A (FractionRing A)) :
    IsIntegral B
      ((IsFractionRing.algEquivOfAlgEquiv
        (K := FractionRing A) (L := FractionRing B) e) (x : FractionRing A)) := by
  apply IsIntegral.map_of_comp_eq (R := A) (S := FractionRing A)
    (T := B) (U := FractionRing B) e.toRingEquiv.toRingHom
    (IsFractionRing.algEquivOfAlgEquiv
      (K := FractionRing A) (L := FractionRing B) e).toRingEquiv.toRingHom
  · ext a
    exact (IsFractionRing.algEquivOfAlgEquiv_algebraMap
      (K := FractionRing A) (L := FractionRing B) e a).symm
  · exact x.property

/-- An equivalence of domain algebras transports their integral closures in their fraction fields. -/
def integralClosureFractionRingEquiv (e : A ≃ₐ[K] B) :
    integralClosure A (FractionRing A) ≃+*
      integralClosure B (FractionRing B) where
  toFun x := ⟨(IsFractionRing.algEquivOfAlgEquiv
      (K := FractionRing A) (L := FractionRing B) e) (x : FractionRing A),
    fractionRingEquiv_maps_integral e x⟩
  invFun y := ⟨(IsFractionRing.algEquivOfAlgEquiv
      (K := FractionRing B) (L := FractionRing A) e.symm) (y : FractionRing B),
    fractionRingEquiv_maps_integral e.symm y⟩
  left_inv x := by
    ext
    exact (IsFractionRing.algEquivOfAlgEquiv
      (K := FractionRing A) (L := FractionRing B) e).symm_apply_apply x
  right_inv y := by
    ext
    exact (IsFractionRing.algEquivOfAlgEquiv
      (K := FractionRing A) (L := FractionRing B) e).apply_symm_apply y
  map_add' x y := by
    ext
    exact map_add _ _ _
  map_mul' x y := by
    ext
    exact map_mul _ _ _

omit [IsDomain A] [IsDomain B] in
@[simp]
theorem integralClosureFractionRingEquiv_coe (e : A ≃ₐ[K] B)
    (x : integralClosure A (FractionRing A)) :
    ((integralClosureFractionRingEquiv e x :
      integralClosure B (FractionRing B)) : FractionRing B) =
      (IsFractionRing.algEquivOfAlgEquiv
        (K := FractionRing A) (L := FractionRing B) e) (x : FractionRing A) := rfl

omit [IsDomain A] [IsDomain B] in
/-- The lifted integral-closure equivalence extends the original coordinate-ring equivalence. -/
theorem integralClosureFractionRingEquiv_comp_algebraMap (e : A ≃ₐ[K] B) :
    (integralClosureFractionRingEquiv e).toRingHom.comp
        (algebraMap A (integralClosure A (FractionRing A))) =
      (algebraMap B (integralClosure B (FractionRing B))).comp e.toRingHom := by
  apply DFunLike.ext _ _
  intro a
  apply Subtype.ext
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap
    (K := FractionRing A) (L := FractionRing B) e a

omit [IsDomain A] [IsDomain B] in
@[simp]
theorem integralClosureFractionRingEquiv_symm (e : A ≃ₐ[K] B) :
    (integralClosureFractionRingEquiv e).symm =
      integralClosureFractionRingEquiv e.symm := rfl

omit [IsDomain B] in
/-- Passing to fraction fields respects composition of algebra equivalences. -/
theorem fractionRingEquiv_trans (e : A ≃ₐ[K] B) (f : B ≃ₐ[K] C) :
    (IsFractionRing.algEquivOfAlgEquiv
      (K := FractionRing A) (L := FractionRing B) e).trans
        (IsFractionRing.algEquivOfAlgEquiv
          (K := FractionRing B) (L := FractionRing C) f) =
      IsFractionRing.algEquivOfAlgEquiv
        (K := FractionRing A) (L := FractionRing C) (e.trans f) := by
  apply AlgEquiv.ext
  intro x
  have h :
      ((IsFractionRing.algEquivOfAlgEquiv
        (K := FractionRing A) (L := FractionRing B) e).trans
          (IsFractionRing.algEquivOfAlgEquiv
            (K := FractionRing B) (L := FractionRing C) f)).toRingEquiv.toRingHom =
        (IsFractionRing.algEquivOfAlgEquiv
          (K := FractionRing A) (L := FractionRing C) (e.trans f)).toRingEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro a
    simp
  exact RingHom.congr_fun h x

omit [IsDomain B] in
/-- Transport of integral closures respects composition. -/
theorem integralClosureFractionRingEquiv_trans
    (e : A ≃ₐ[K] B) (f : B ≃ₐ[K] C) :
    (integralClosureFractionRingEquiv e).trans
        (integralClosureFractionRingEquiv f) =
      integralClosureFractionRingEquiv (e.trans f) := by
  ext x
  change
    ((IsFractionRing.algEquivOfAlgEquiv
      (K := FractionRing A) (L := FractionRing B) e).trans
        (IsFractionRing.algEquivOfAlgEquiv
          (K := FractionRing B) (L := FractionRing C) f)) x = _
  rw [fractionRingEquiv_trans]
  rfl

end IntegralClosureTransport

section IntegralClosureLocalization

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The canonical map from a principal open of an integral domain to the corresponding principal
open of its normalization. -/
def integralClosureAwayMap (f : R) :
    Localization.Away f →+*
      Localization.Away (algebraMap R (integralClosure R (FractionRing R)) f) := by
  letI : IsLocalization.Away
      ((Algebra.ofId R (integralClosure R (FractionRing R))) f)
      (Localization.Away (algebraMap R (integralClosure R (FractionRing R)) f)) := by
    simpa using (inferInstance : IsLocalization.Away
      (algebraMap R (integralClosure R (FractionRing R)) f)
      (Localization.Away (algebraMap R (integralClosure R (FractionRing R)) f)))
  exact (IsLocalization.Away.mapₐ
    (Localization.Away f)
    (Localization.Away (algebraMap R (integralClosure R (FractionRing R)) f))
    (Algebra.ofId R (integralClosure R (FractionRing R))) f).toRingHom

/-- The localization comparison for normalization, bundled with the square that identifies its
restriction on the original principal open.  Keeping the square in the data prevents the
normalization chart transition from being used without its compatibility with the raw chart. -/
structure IntegralClosureAwayComparison (f : R) where
  equiv :
    Localization.Away (algebraMap R (integralClosure R (FractionRing R)) f) ≃+*
      integralClosure (Localization.Away f) (FractionRing (Localization.Away f))
  equiv_comp_map : equiv.toRingHom.comp (integralClosureAwayMap f) =
    algebraMap (Localization.Away f)
      (integralClosure (Localization.Away f) (FractionRing (Localization.Away f)))

/-- Normalizing an integral domain and then restricting to a nonempty principal open agrees with
normalizing that principal open in its own fraction field, compatibly with the raw principal open.

The construction makes all comparison maps explicit.  The fraction field of `R` is first given
its compatible `Localization.Away f`-algebra structure.  Mathlib's
`IsLocalization.Away.integralClosure` then identifies the intermediate integral closure as a
localization of `integralClosure R (FractionRing R)`, and `FractionRing.algEquiv` compares the
intermediate ambient field with the canonical fraction field of `Localization.Away f`. -/
def integralClosureAwayComparison (f : R) (hf : f ≠ 0) :
    IntegralClosureAwayComparison f := by
  let Rf := Localization.Away f
  let F := FractionRing R
  let N := integralClosure R F
  have hfF : algebraMap R F f ≠ 0 :=
    (map_ne_zero_iff (algebraMap R F) (FaithfulSMul.algebraMap_injective R F)).mpr hf
  have hfUnit : IsUnit (algebraMap R F f) := isUnit_iff_ne_zero.mpr hfF
  let phi : Rf →ₐ[R] F :=
    IsLocalization.Away.liftAlgHom f (f := Algebra.ofId R F) hfUnit
  letI : Algebra Rf F := phi.toRingHom.toAlgebra
  letI : IsScalarTower R Rf F := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (phi.commutes r).symm)
  letI : IsFractionRing Rf F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers f) Rf F
  let T := integralClosure Rf F
  let Nf := integralClosure Rf (FractionRing Rf)
  let fracEquiv : FractionRing Rf ≃ₐ[Rf] F := FractionRing.algEquiv Rf F
  let psi : N →+* T :=
    { toFun := fun x ↦ ⟨(x : F), x.property.tower_top⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  letI : Algebra N T := psi.toAlgebra
  letI : IsScalarTower N T F := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R N T := IsScalarTower.of_algebraMap_eq' (by
    ext r
    rfl)
  letI : IsLocalization.Away (algebraMap R F f) F :=
    IsLocalization.away_of_isUnit_of_bijective F hfUnit Function.bijective_id
  letI : IsLocalization.Away (algebraMap R N f) T :=
    IsLocalization.Away.integralClosure (S := F) (Rf := Rf) (Sf := F) f
  let localizationEquiv : Localization.Away (algebraMap R N f) ≃ₐ[N] T :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap R N f))
      (Localization.Away (algebraMap R N f)) T
  let ambientFieldEquiv : T ≃+* Nf :=
    (fracEquiv.mapIntegralClosure).symm.toRingEquiv
  let e := localizationEquiv.toRingEquiv.trans ambientFieldEquiv
  refine ⟨e, ?_⟩
  apply IsLocalization.ringHom_ext (M := Submonoid.powers f)
  ext r
  simp [e, localizationEquiv, ambientFieldEquiv, integralClosureAwayMap]
  apply_fun fracEquiv
  have hmap (x : T) :
      fracEquiv ↑(fracEquiv.mapIntegralClosure.symm x) = (x : F) := by
    exact congrArg Subtype.val (fracEquiv.mapIntegralClosure.apply_symm_apply x)
  rw [hmap]
  rw [show
    (algebraMap R (Localization.Away (algebraMap R N f))) r =
      (algebraMap N (Localization.Away (algebraMap R N f))) ((algebraMap R N) r) by
        simpa using
          (IsScalarTower.algebraMap_apply R N
            (Localization.Away (algebraMap R N f)) r)]
  rw [localizationEquiv.commutes]
  rw [fracEquiv.commutes]
  change
    algebraMap T F (algebraMap N T (algebraMap R N r)) =
      algebraMap Rf F (algebraMap R Rf r)
  rw [← IsScalarTower.algebraMap_apply N T F]
  rw [← IsScalarTower.algebraMap_apply R N F]
  rw [← IsScalarTower.algebraMap_apply R Rf F]

/-- The ring equivalence underlying `integralClosureAwayComparison`. -/
def integralClosureAwayEquiv (f : R) (hf : f ≠ 0) :
    Localization.Away (algebraMap R (integralClosure R (FractionRing R)) f) ≃+*
      integralClosure (Localization.Away f) (FractionRing (Localization.Away f)) :=
  (integralClosureAwayComparison f hf).equiv

/-- The localization equivalence carries the canonical raw-to-normalized principal-open map to
the canonical normalization map of the raw principal open. -/
theorem integralClosureAwayEquiv_comp_map (f : R) (hf : f ≠ 0) :
    (integralClosureAwayEquiv f hf).toRingHom.comp (integralClosureAwayMap f) =
      algebraMap (Localization.Away f)
        (integralClosure (Localization.Away f) (FractionRing (Localization.Away f))) :=
  (integralClosureAwayComparison f hf).equiv_comp_map

end IntegralClosureLocalization

section TraceCoverCharts

variable {K : Type*} [Field K]

/-- Coordinate ring of the affine normalization, before passing to `Spec`. -/
abbrev WeightedSplitTraceAffineNormalizationRing
    (alpha beta : K) (d e : ℕ) :=
  integralClosure (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
    (FractionRing (WeightedSplitTraceAffineCoordinateRing alpha beta d e))

/-- Normalization ring of the common Laurent overlap of a trace-cover affine chart. -/
abbrev WeightedSplitTraceLaurentNormalizationRing
    (alpha beta : K) (d e : ℕ) :=
  integralClosure (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)
    (FractionRing (WeightedSplitTraceLaurentCoordinateRing alpha beta d e))

/-- Irreducibility and positivity ensure that localizing away from the coordinate product is a
genuine nonzero open.  The proof exposes the two possible coordinate-axis divisors and rules them
out by evaluation at `(0, 1)` and `(1, 0)`. -/
theorem weightedSplitTraceAffineCoordinateProduct_ne_zero_of_irreducible
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) :
    weightedSplitTraceAffineCoordinateProduct alpha beta d e ≠ 0 := by
  intro hzero
  have hmul : MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) ∈
      Ideal.span {splitTraceCoverPolynomial alpha beta d e} := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [Ideal.mem_span_singleton] at hmul
  rcases h.prime.dvd_mul.mp hmul with hx | hy
  · have ha := h.prime.associated_of_dvd (MvPolynomial.X_prime (i := (0 : Fin 2))) hx
    have hamap := ha.map (MvPolynomial.eval ![0, 1])
    simp [eval_splitTraceCoverPolynomial, hd.ne'] at hamap
  · have ha := h.prime.associated_of_dvd (MvPolynomial.X_prime (i := (1 : Fin 2))) hy
    have hamap := ha.map (MvPolynomial.eval ![1, 0])
    simp [eval_splitTraceCoverPolynomial, he.ne', hbeta] at hamap

/-- The Laurent coordinate ring is a domain once irreducibility proves that its affine source is
a domain and the preceding theorem proves that the inverted coordinate product is nonzero. -/
theorem weightedSplitTraceLaurentCoordinateRing_isDomain
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) :
    IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) := by
  let : IsDomain (WeightedSplitTraceAffineCoordinateRing alpha beta d e) :=
    weightedSplitTraceAffineCoordinateRing_isDomain alpha beta d e h
  exact IsLocalization.Away.isDomain
    (S := WeightedSplitTraceLaurentCoordinateRing alpha beta d e)
    (weightedSplitTraceAffineCoordinateProduct_ne_zero_of_irreducible
      alpha beta d e hd he hbeta h)

/-- The normalized Laurent overlap is the principal open of the affine normalization obtained by
inverting the original coordinate product.  Both the affine-domain and nonempty-open hypotheses
are discharged from irreducibility and positivity. -/
def weightedSplitTraceAffineNormalizationLaurentOpenEquiv_of_irreducible
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) :
    Localization.Away
        (algebraMap (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
          (WeightedSplitTraceAffineNormalizationRing alpha beta d e)
          (weightedSplitTraceAffineCoordinateProduct alpha beta d e)) ≃+*
      WeightedSplitTraceLaurentNormalizationRing alpha beta d e := by
  letI : IsDomain (WeightedSplitTraceAffineCoordinateRing alpha beta d e) :=
    weightedSplitTraceAffineCoordinateRing_isDomain alpha beta d e h
  exact integralClosureAwayEquiv
    (weightedSplitTraceAffineCoordinateProduct alpha beta d e)
    (weightedSplitTraceAffineCoordinateProduct_ne_zero_of_irreducible
      alpha beta d e hd he hbeta h)

/-- Scheme-level form of the normalized principal-open comparison. -/
def weightedSplitTraceAffineNormalizationLaurentOpenSchemeIso_of_irreducible
    (alpha beta : K) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e)) :
    Spec (CommRingCat.of (WeightedSplitTraceLaurentNormalizationRing alpha beta d e)) ≅
      Spec (CommRingCat.of (Localization.Away
        (algebraMap (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
          (WeightedSplitTraceAffineNormalizationRing alpha beta d e)
          (weightedSplitTraceAffineCoordinateProduct alpha beta d e)))) :=
  BGS.specIsoOfRingEquiv
    (weightedSplitTraceAffineNormalizationLaurentOpenEquiv_of_irreducible
      alpha beta d e hd he hbeta h)

variable (alpha beta : K) (d e : ℕ)
variable [IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)]
variable [IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e)]

/-- The first-coordinate inversion lifted to the normalized Laurent overlap. -/
def weightedSplitTraceLeftInversionLaurentNormalizationEquiv :
    WeightedSplitTraceLaurentNormalizationRing alpha beta d e ≃+*
      WeightedSplitTraceLaurentNormalizationRing alpha beta d e :=
  integralClosureFractionRingEquiv
    (weightedSplitTraceLeftInversionLaurentEquiv alpha beta d e)

/-- The second-coordinate inversion lifted to the normalized Laurent overlap. -/
def weightedSplitTraceRightInversionLaurentNormalizationEquiv :
    WeightedSplitTraceLaurentNormalizationRing beta alpha d e ≃+*
      WeightedSplitTraceLaurentNormalizationRing alpha beta d e :=
  integralClosureFractionRingEquiv
    (weightedSplitTraceRightInversionLaurentEquiv alpha beta d e)

omit [IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)]
  [IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e)] in
/-- The coordinate-ring transition equivalences satisfy the same square cocycle as their maps. -/
theorem weightedSplitTraceLaurentInversionEquivs_commute :
    (weightedSplitTraceRightInversionLaurentEquiv alpha beta d e).trans
        (weightedSplitTraceLeftInversionLaurentEquiv alpha beta d e) =
      (weightedSplitTraceLeftInversionLaurentEquiv beta alpha d e).trans
        (weightedSplitTraceRightInversionLaurentEquiv alpha beta d e) := by
  apply AlgEquiv.ext
  intro x
  exact DFunLike.congr_fun
    (weightedSplitTraceLaurentInversions_commute alpha beta d e) x

/-- The lifted normalization transitions satisfy the required square cocycle. -/
theorem weightedSplitTraceLaurentNormalizationInversions_commute :
    (weightedSplitTraceRightInversionLaurentNormalizationEquiv alpha beta d e).trans
        (weightedSplitTraceLeftInversionLaurentNormalizationEquiv alpha beta d e) =
      (weightedSplitTraceLeftInversionLaurentNormalizationEquiv beta alpha d e).trans
        (weightedSplitTraceRightInversionLaurentNormalizationEquiv alpha beta d e) := by
  simp only [weightedSplitTraceRightInversionLaurentNormalizationEquiv,
    weightedSplitTraceLeftInversionLaurentNormalizationEquiv]
  rw [integralClosureFractionRingEquiv_trans,
    integralClosureFractionRingEquiv_trans,
    weightedSplitTraceLaurentInversionEquivs_commute]

omit [IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)]
  [IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e)] in
/-- The normalization cocycle with its domain instances explicitly discharged by the two affine
irreducibility theorems.  This is the upstream-to-downstream wiring used by the geometric charts. -/
theorem weightedSplitTraceLaurentNormalizationInversions_commute_of_irreducible
    (hd : 0 < d) (he : 0 < e) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (h : Irreducible (splitTraceCoverPolynomial alpha beta d e))
    (hswap : Irreducible (splitTraceCoverPolynomial beta alpha d e)) :
    letI : IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) :=
      weightedSplitTraceLaurentCoordinateRing_isDomain alpha beta d e hd he hbeta h
    letI : IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e) :=
      weightedSplitTraceLaurentCoordinateRing_isDomain beta alpha d e hd he halpha hswap
    (weightedSplitTraceRightInversionLaurentNormalizationEquiv alpha beta d e).trans
        (weightedSplitTraceLeftInversionLaurentNormalizationEquiv alpha beta d e) =
      (weightedSplitTraceLeftInversionLaurentNormalizationEquiv beta alpha d e).trans
        (weightedSplitTraceRightInversionLaurentNormalizationEquiv alpha beta d e) := by
  let : IsDomain (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) :=
    weightedSplitTraceLaurentCoordinateRing_isDomain alpha beta d e hd he hbeta h
  let : IsDomain (WeightedSplitTraceLaurentCoordinateRing beta alpha d e) :=
    weightedSplitTraceLaurentCoordinateRing_isDomain beta alpha d e hd he halpha hswap
  exact weightedSplitTraceLaurentNormalizationInversions_commute alpha beta d e

/-- Scheme isomorphism on the normalized overlap induced by first-coordinate inversion. -/
def weightedSplitTraceLeftInversionLaurentNormalizationSchemeIso :
    Spec (CommRingCat.of (WeightedSplitTraceLaurentNormalizationRing alpha beta d e)) ≅
      Spec (CommRingCat.of (WeightedSplitTraceLaurentNormalizationRing alpha beta d e)) :=
  BGS.specIsoOfRingEquiv
    (weightedSplitTraceLeftInversionLaurentNormalizationEquiv alpha beta d e)

/-- Contravariant scheme isomorphism on normalized overlaps induced by second-coordinate inversion. -/
def weightedSplitTraceRightInversionLaurentNormalizationSchemeIso :
    Spec (CommRingCat.of (WeightedSplitTraceLaurentNormalizationRing alpha beta d e)) ≅
      Spec (CommRingCat.of (WeightedSplitTraceLaurentNormalizationRing beta alpha d e)) :=
  BGS.specIsoOfRingEquiv
    (weightedSplitTraceRightInversionLaurentNormalizationEquiv alpha beta d e)

section ConjugatedPrincipalOpenTransitions

universe u

variable {OA OB : Type u} [CommRing OA] [CommRing OB]

/-- Transport first-coordinate inversion from the normalized Laurent ring to any explicitly
identified principal-open ring model. -/
def conjugatedLeftNormalizationOpenEquiv
    (openEquiv : OA ≃+* WeightedSplitTraceLaurentNormalizationRing alpha beta d e) :
    OA ≃+* OA :=
  openEquiv.trans
    ((weightedSplitTraceLeftInversionLaurentNormalizationEquiv alpha beta d e).trans
      openEquiv.symm)

/-- Transport second-coordinate inversion between two explicitly identified principal-open ring
models. -/
def conjugatedRightNormalizationOpenEquiv
    (openEquiv : OA ≃+* WeightedSplitTraceLaurentNormalizationRing alpha beta d e)
    (swappedOpenEquiv : OB ≃+* WeightedSplitTraceLaurentNormalizationRing beta alpha d e) :
    OB ≃+* OA :=
  swappedOpenEquiv.trans
    ((weightedSplitTraceRightInversionLaurentNormalizationEquiv alpha beta d e).trans
      openEquiv.symm)

/-- Conjugating by arbitrary principal-open identifications preserves the normalization cocycle. -/
theorem conjugatedNormalizationOpenInversions_commute
    (openEquiv : OA ≃+* WeightedSplitTraceLaurentNormalizationRing alpha beta d e)
    (swappedOpenEquiv : OB ≃+* WeightedSplitTraceLaurentNormalizationRing beta alpha d e) :
    (conjugatedRightNormalizationOpenEquiv alpha beta d e openEquiv swappedOpenEquiv).trans
        (conjugatedLeftNormalizationOpenEquiv alpha beta d e openEquiv) =
      (conjugatedLeftNormalizationOpenEquiv beta alpha d e swappedOpenEquiv).trans
        (conjugatedRightNormalizationOpenEquiv alpha beta d e openEquiv swappedOpenEquiv) := by
  ext x
  simp only [conjugatedRightNormalizationOpenEquiv, conjugatedLeftNormalizationOpenEquiv,
    RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  exact congrArg openEquiv.symm
    (DFunLike.congr_fun
      (weightedSplitTraceLaurentNormalizationInversions_commute alpha beta d e)
      (swappedOpenEquiv x))

/-- Scheme automorphism of a principal-open model induced by first-coordinate inversion. -/
def conjugatedLeftNormalizationOpenSchemeIso
    (openEquiv : OA ≃+* WeightedSplitTraceLaurentNormalizationRing alpha beta d e) :
    Spec (CommRingCat.of OA) ≅ Spec (CommRingCat.of OA) :=
  BGS.specIsoOfRingEquiv
    (conjugatedLeftNormalizationOpenEquiv alpha beta d e openEquiv)

/-- Contravariant scheme isomorphism of principal-open models induced by second-coordinate
inversion. -/
def conjugatedRightNormalizationOpenSchemeIso
    (openEquiv : OA ≃+* WeightedSplitTraceLaurentNormalizationRing alpha beta d e)
    (swappedOpenEquiv : OB ≃+* WeightedSplitTraceLaurentNormalizationRing beta alpha d e) :
    Spec (CommRingCat.of OA) ≅ Spec (CommRingCat.of OB) :=
  BGS.specIsoOfRingEquiv
    (conjugatedRightNormalizationOpenEquiv alpha beta d e
      openEquiv swappedOpenEquiv)

end ConjugatedPrincipalOpenTransitions

end TraceCoverCharts

end

end BGS.Markoff
