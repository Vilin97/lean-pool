/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.EllipticCurve.Instances
public import Mathlib.RingTheory.Unramified.Dedekind
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Etale.StandardEtale

/-!
# The affine coordinate ring of an elliptic curve is Dedekind

The Weierstrass equation is monic in both affine coordinates.  At every prime of its
coordinate ring, nonsingularity says that one of the two partial derivatives is a unit.
Using the corresponding coordinate realizes the local algebra as unramified over a
localization of a polynomial PID, so its maximal ideal is principal and the local ring is a DVR.

The main result is the `IsDedekindDomain W.CoordinateRing` instance.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {k : Type*} [Field k]

/-- The Weierstrass equation viewed as a monic cubic in the `X`-coordinate. -/
noncomputable def xPolynomial (W : WeierstrassCurve.Affine k) : k[X][Y] :=
  Cubic.toPoly
    ⟨1, C W.a₂, C W.a₄ - C W.a₁ * X,
      C W.a₆ - X ^ 2 - C W.a₃ * X⟩

lemma xPolynomial_eq_neg_swap (W : WeierstrassCurve.Affine k) :
    xPolynomial W = -Polynomial.Bivariate.swap W.polynomial := by
  rw [xPolynomial, polynomial, Cubic.toPoly]
  simp only [map_add, map_sub, map_mul, map_pow, map_one, one_mul,
    Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_C,
    Polynomial.map_C, Polynomial.map_X]
  ring

lemma xPolynomial_monic (W : WeierstrassCurve.Affine k) : (xPolynomial W).Monic := by
  rw [xPolynomial]
  exact Cubic.monic_of_a_eq_one'

/-- Swapping the two polynomial variables identifies the monic `X`-presentation with the
affine coordinate ring. -/
noncomputable def xAdjoinRootEquiv (W : WeierstrassCurve.Affine k) :
    AdjoinRoot (xPolynomial W) ≃ₐ[k] W.CoordinateRing :=
  { Ideal.quotientEquiv
      (Ideal.span {xPolynomial W}) (Ideal.span {W.polynomial})
      Polynomial.Bivariate.swap.toRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton, xPolynomial_eq_neg_swap,
        map_neg, Ideal.span_singleton_neg]
      exact congrArg (fun p => Ideal.span ({p} : Set k[X][Y]))
        (Polynomial.Bivariate.swap_swap_apply W.polynomial).symm) with
    commutes' := fun r => by
      rw [IsScalarTower.algebraMap_apply k k[X] (AdjoinRoot (xPolynomial W)),
        IsScalarTower.algebraMap_apply k k[X] W.CoordinateRing]
      change (Ideal.quotientEquiv _ _ Polynomial.Bivariate.swap.toRingEquiv _)
        (Ideal.Quotient.mk _ (C (C r))) = Ideal.Quotient.mk _ (C (C r))
      rw [Ideal.quotientEquiv_mk]
      exact congrArg (Ideal.Quotient.mk (Ideal.span {W.polynomial}))
        (Polynomial.Bivariate.swap_C_C r) }


lemma xAdjoinRootEquiv_mk (W : WeierstrassCurve.Affine k) (q : k[X][Y]) :
    xAdjoinRootEquiv W (AdjoinRoot.mk (xPolynomial W) q) =
      CoordinateRing.mk W (Polynomial.Bivariate.swap q) := by
  rfl

noncomputable instance instIsDomainXAdjoinRoot (W : WeierstrassCurve.Affine k) :
    IsDomain (AdjoinRoot (xPolynomial W)) :=
  (xAdjoinRootEquiv W).injective.isDomain (xAdjoinRootEquiv W).toRingHom

lemma coordinate_mk_eq_eval₂ (W : WeierstrassCurve.Affine k) (q : k[X][Y]) :
    CoordinateRing.mk W q =
      eval₂ (eval₂RingHom (algebraMap k W.CoordinateRing)
        (CoordinateRing.mk W (C X))) (CoordinateRing.mk W Y) q := by
  change (CoordinateRing.mk W) q =
    (eval₂RingHom (eval₂RingHom (algebraMap k W.CoordinateRing)
      (CoordinateRing.mk W (C X))) (CoordinateRing.mk W Y)) q
  apply congrArg (fun f : k[X][Y] →+* W.CoordinateRing => f q)
  apply Polynomial.ringHom_ext
  · intro p
    rw [AdjoinRoot.mk_C]
    change (AdjoinRoot.of W.polynomial) p =
      eval₂ (eval₂RingHom (algebraMap k W.CoordinateRing)
        (CoordinateRing.mk W (C X))) (CoordinateRing.mk W Y) (C p)
    rw [eval₂_C]
    apply congrArg (fun f : k[X] →+* W.CoordinateRing => f p)
    apply Polynomial.ringHom_ext
    · intro a
      simp [CoordinateRing.mk,
        IsScalarTower.algebraMap_apply k k[X] W.CoordinateRing]
    · simp [CoordinateRing.mk]
  · simp [CoordinateRing.mk]

lemma coordinate_polynomialX_eval (W : WeierstrassCurve.Affine k) :
    (W⁄W.CoordinateRing).polynomialX.evalEval
      (CoordinateRing.mk W (C X)) (CoordinateRing.mk W Y) =
        CoordinateRing.mk W W.polynomialX := by
  change (W.map (algebraMap k W.CoordinateRing)).polynomialX.evalEval _ _ = _
  rw [map_polynomialX]
  rw [← Polynomial.eval₂_eval₂RingHom_apply]
  exact (coordinate_mk_eq_eval₂ W W.polynomialX).symm

lemma coordinate_polynomialY_eval (W : WeierstrassCurve.Affine k) :
    (W⁄W.CoordinateRing).polynomialY.evalEval
      (CoordinateRing.mk W (C X)) (CoordinateRing.mk W Y) =
        CoordinateRing.mk W W.polynomialY := by
  change (W.map (algebraMap k W.CoordinateRing)).polynomialY.evalEval _ _ = _
  rw [map_polynomialY]
  rw [← Polynomial.eval₂_eval₂RingHom_apply]
  exact (coordinate_mk_eq_eval₂ W W.polynomialY).symm

lemma coordinate_equation (W : WeierstrassCurve.Affine k) :
    (W⁄W.CoordinateRing).Equation
      (CoordinateRing.mk W (C X)) (CoordinateRing.mk W Y) := by
  rw [equation_iff]
  have h : CoordinateRing.mk W W.polynomial = 0 := AdjoinRoot.mk_self
  simp only [polynomial, map_add, map_sub, map_mul, map_pow] at h
  convert sub_eq_zero.mp h using 1 <;>
    simp [WeierstrassCurve.baseChange, WeierstrassCurve.map,
      IsScalarTower.algebraMap_apply k k[X] W.CoordinateRing]; ring

lemma derivative_polynomial_eq (W : WeierstrassCurve.Affine k) :
    W.polynomial.derivative = W.polynomialY := by
  rw [polynomial, polynomialY]
  simp only [derivative_add, derivative_sub, derivative_pow, derivative_X,
    derivative_mul, derivative_C, zero_mul]
  norm_num
  have h2 : (2 : k[X]) = C (2 : k) := (map_ofNat C 2).symm
  exact h2

lemma xPolynomial_derivative_eq (W : WeierstrassCurve.Affine k) :
    (xPolynomial W).derivative = -Polynomial.Bivariate.swap W.polynomialX := by
  rw [xPolynomial, polynomialX, Cubic.toPoly]
  simp only [derivative_add, derivative_pow, derivative_X,
    derivative_mul, derivative_C, zero_mul, add_zero]
  simp only [map_ofNat, C_1, one_mul, map_add, map_sub, map_mul, map_pow,
    Polynomial.Bivariate.swap_C, Polynomial.Bivariate.swap_Y,
    Polynomial.map_C, Polynomial.map_X]
  norm_num
  have h2 : (2 : k[X][Y]) = C (2 : k[X]) := (map_ofNat C 2).symm
  have h3 : (3 : k[X][Y]) = C (3 : k[X]) := (map_ofNat C 3).symm
  rw [h2, h3]
  ring

lemma xAdjoinRootEquiv_neg_swap_polynomialX (W : WeierstrassCurve.Affine k) :
    xAdjoinRootEquiv W (AdjoinRoot.mk (xPolynomial W)
      (-Polynomial.Bivariate.swap W.polynomialX)) =
      -CoordinateRing.mk W W.polynomialX := by
  have hcore : xAdjoinRootEquiv W
      (AdjoinRoot.mk (xPolynomial W) (Polynomial.Bivariate.swap W.polynomialX)) =
        CoordinateRing.mk W W.polynomialX := by
    rw [xAdjoinRootEquiv_mk, Polynomial.Bivariate.swap_swap_apply]
  calc
    xAdjoinRootEquiv W
        (AdjoinRoot.mk (xPolynomial W) (-Polynomial.Bivariate.swap W.polynomialX)) =
      xAdjoinRootEquiv W
        (-(AdjoinRoot.mk (xPolynomial W) (Polynomial.Bivariate.swap W.polynomialX))) := by
          rw [map_neg]
    _ = -xAdjoinRootEquiv W
        (AdjoinRoot.mk (xPolynomial W) (Polynomial.Bivariate.swap W.polynomialX)) := map_neg _ _
    _ = -CoordinateRing.mk W W.polynomialX := congrArg Neg.neg hcore

lemma coordinate_derivatives_not_both_mem (W : WeierstrassCurve.Affine k) [W.IsElliptic]
    (P : Ideal W.CoordinateRing) [P.IsPrime] :
    CoordinateRing.mk W W.polynomialX ∉ P ∨ CoordinateRing.mk W W.polynomialY ∉ P := by
  let L := P.ResidueField
  let f : W.CoordinateRing →+* L := algebraMap W.CoordinateRing L
  let x : L := algebraMap W.CoordinateRing L (CoordinateRing.mk W (C X))
  let y : L := algebraMap W.CoordinateRing L (CoordinateRing.mk W Y)
  let : (W⁄W.CoordinateRing).IsElliptic := by
    change (W.map (algebraMap k W.CoordinateRing)).IsElliptic
    infer_instance
  let : ((W⁄W.CoordinateRing).map f).IsElliptic := by infer_instance
  have hEq : ((W⁄W.CoordinateRing).map f).Equation x y := by
    simpa [x, y, f] using (coordinate_equation W).map f
  have hns : ((W⁄W.CoordinateRing).map f).Nonsingular x y :=
    (((W⁄W.CoordinateRing).map f).equation_iff_nonsingular).mp hEq
  rw [Nonsingular] at hns
  rcases hns.2 with hx | hy
  · left
    intro hmem
    apply hx
    rw [map_polynomialX, map_mapRingHom_evalEval, coordinate_polynomialX_eval]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hmem
  · right
    intro hmem
    apply hy
    rw [map_polynomialY, map_mapRingHom_evalEval, coordinate_polynomialY_eval]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hmem

end WeierstrassCurve.Affine

namespace AdjoinRoot

variable {R : Type*} [CommRing R]

theorem isUnramifiedAt_of_monic_derivative_not_mem (f : R[X]) (hf : f.Monic)
    (P : Ideal (AdjoinRoot f)) [P.IsPrime]
    (hP : AdjoinRoot.mk f f.derivative ∉ P) :
    Algebra.IsUnramifiedAt R P := by
  let Q : StandardEtalePair R :=
    ⟨f, hf, f.derivative, 1, 0, 1, by simp⟩
  have hfu : Algebra.FormallyUnramified R
      (Localization.Away (AdjoinRoot.mk f f.derivative)) := by
    exact Algebra.FormallyUnramified.of_equiv Q.equivAwayAdjoinRoot
  have hopen := (Algebra.basicOpen_subset_unramifiedLocus_iff (R := R)
    (A := AdjoinRoot f) (f := AdjoinRoot.mk f f.derivative)).mpr hfu
  have hmem : (⟨P, inferInstance⟩ : PrimeSpectrum (AdjoinRoot f)) ∈
      PrimeSpectrum.basicOpen (AdjoinRoot.mk f f.derivative) := by
    simpa using hP
  exact hopen hmem

theorem isDiscreteValuationRing_atPrime_of_derivative_not_mem
    [IsNoetherianRing R] [IsPrincipalIdealRing R]
    (f : R[X]) (hf : f.Monic) [IsDomain (AdjoinRoot f)]
    (P : Ideal (AdjoinRoot f)) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hP : AdjoinRoot.mk f f.derivative ∉ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  let : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  let : IsNoetherianRing (AdjoinRoot f) := IsNoetherianRing.of_finite R _
  let : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  let : Algebra.IsUnramifiedAt R P :=
    isUnramifiedAt_of_monic_derivative_not_mem f hf P hP
  let p := P.under R
  let := Localization.AtPrime.algebraOfLiesOver p P
  have hmap : p.map (algebraMap R (Localization.AtPrime P)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    ((Algebra.isUnramifiedAt_iff_map_eq R p P).mp inferInstance).2
  have : p.IsPrincipal := IsPrincipalIdealRing.principal p
  have hprincipal : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsPrincipal := by
    rw [← hmap]
    infer_instance
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P)
    (IsLocalization.AtPrime.not_isField (AdjoinRoot f) hP0
      (Localization.AtPrime P))).out 4 0).mp hprincipal

theorem isDiscreteValuationRing_atPrime_of_derivative_eq_not_mem
    [IsNoetherianRing R] [IsPrincipalIdealRing R]
    (f : R[X]) (hf : f.Monic) [IsDomain (AdjoinRoot f)]
    (q : R[X]) (hder : f.derivative = q)
    (P : Ideal (AdjoinRoot f)) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hP : AdjoinRoot.mk f q ∉ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  apply isDiscreteValuationRing_atPrime_of_derivative_not_mem f hf P hP0
  rwa [hder]

end AdjoinRoot

namespace IsDiscreteValuationRing

theorem of_ringEquiv_of_not_isField {A B : Type*}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsLocalRing B]
    (e : A ≃+* B) (hB : ¬IsField B) : IsDiscreteValuationRing B := by
  let : IsPrincipalIdealRing B :=
    { principal := fun I => by
        let J := I.comap e.toRingHom
        have : J.IsPrincipal := IsPrincipalIdealRing.principal J
        have hJI : J.map e.toRingHom = I :=
          Ideal.map_comap_eq_self_of_equiv e I
        rw [← hJI]
        infer_instance }
  exact { not_a_field' := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hB }

theorem atPrime_of_comap_ringEquiv {A B : Type*}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    (e : A ≃+* B) (P : Ideal B) [P.IsPrime] (hP0 : P ≠ ⊥)
    [IsDiscreteValuationRing (Localization.AtPrime (P.comap e.toRingHom))] :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  have hmon : Submonoid.map e.toMonoidHom (P.comap e.toRingHom).primeCompl =
      P.primeCompl := e.map_primeCompl_comap_eq P
  let eLoc : Localization.AtPrime (P.comap e.toRingHom) ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv
      (M := (P.comap e.toRingHom).primeCompl) (T := P.primeCompl)
      _ _ e hmon
  exact of_ringEquiv_of_not_isField eLoc
    (IsLocalization.AtPrime.not_isField B hP0 _)

end IsDiscreteValuationRing

private theorem not_mem_comap_of_image_eq {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (P : Ideal B) (x : A) (y : B) (hxy : e x = y) (hy : y ∉ P) :
    x ∉ P.comap e.toRingHom := by
  intro hx
  exact hy (hxy ▸ hx)

namespace WeierstrassCurve.Affine.CoordinateRing

variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]

omit [WeierstrassCurve.IsElliptic W] in
theorem isDiscreteValuationRing_atPrime_of_polynomialY_not_mem
    (P : Ideal W.CoordinateRing) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hY : CoordinateRing.mk W W.polynomialY ∉ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  apply AdjoinRoot.isDiscreteValuationRing_atPrime_of_derivative_not_mem
    W.polynomial W.monic_polynomial P hP0
  rwa [derivative_polynomial_eq]

omit [WeierstrassCurve.IsElliptic W] in
theorem x_comap_ne_bot (P : Ideal W.CoordinateRing) (hP0 : P ≠ ⊥) :
    P.comap (xAdjoinRootEquiv W).toRingHom ≠ ⊥ := by
  intro hQ
  apply hP0
  have hmap : (P.comap (xAdjoinRootEquiv W).toRingHom).map
      (xAdjoinRootEquiv W).toRingHom = P :=
    Ideal.map_comap_eq_self_of_equiv (xAdjoinRootEquiv W).toRingEquiv P
  rw [← hmap, hQ, Ideal.map_bot]

omit [WeierstrassCurve.IsElliptic W] in
theorem isDiscreteValuationRing_atPrime_x_comap
    (P : Ideal W.CoordinateRing) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hX : CoordinateRing.mk W W.polynomialX ∉ P) :
    IsDiscreteValuationRing
      (Localization.AtPrime (P.comap (xAdjoinRootEquiv W).toRingHom)) := by
  let : (P.comap (xAdjoinRootEquiv W).toRingHom).IsPrime :=
    Ideal.IsPrime.comap (xAdjoinRootEquiv W).toRingHom
  exact AdjoinRoot.isDiscreteValuationRing_atPrime_of_derivative_eq_not_mem
    (xPolynomial W) (xPolynomial_monic W)
    (-Polynomial.Bivariate.swap W.polynomialX) (xPolynomial_derivative_eq W)
    (P.comap (xAdjoinRootEquiv W).toRingHom) (x_comap_ne_bot W P hP0)
    (not_mem_comap_of_image_eq (xAdjoinRootEquiv W).toRingEquiv P _ _
      (xAdjoinRootEquiv_neg_swap_polynomialX W) (by simpa using hX))

omit [WeierstrassCurve.IsElliptic W] in
theorem isDiscreteValuationRing_atPrime_of_polynomialX_not_mem
    (P : Ideal W.CoordinateRing) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hX : CoordinateRing.mk W W.polynomialX ∉ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  let : IsDiscreteValuationRing
      (Localization.AtPrime (P.comap (xAdjoinRootEquiv W).toRingHom)) :=
    isDiscreteValuationRing_atPrime_x_comap W P hP0 hX
  exact IsDiscreteValuationRing.atPrime_of_comap_ringEquiv
    (xAdjoinRootEquiv W).toRingEquiv P hP0

theorem isDedekindDomain : IsDedekindDomain W.CoordinateRing := by
  have : IsNoetherianRing W.CoordinateRing := IsNoetherianRing.of_finite k[X] _
  refine isDedekindDomain_iff_isDiscreteValuationRing_atPrime.mpr ⟨inferInstance, ?_⟩
  intro P hP0 hPprime
  rcases coordinate_derivatives_not_both_mem W P with hX | hY
  · exact isDiscreteValuationRing_atPrime_of_polynomialX_not_mem W P hP0 hX
  · exact isDiscreteValuationRing_atPrime_of_polynomialY_not_mem W P hP0 hY

noncomputable instance instIsDedekindDomainCoordinateRing :
    IsDedekindDomain W.CoordinateRing := isDedekindDomain W

end WeierstrassCurve.Affine.CoordinateRing
