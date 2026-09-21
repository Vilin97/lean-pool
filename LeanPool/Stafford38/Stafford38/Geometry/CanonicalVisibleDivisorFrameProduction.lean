/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.CanonicalNonconstantFiniteGradientProduction
import LeanPool.Stafford38.Stafford38.Geometry.GenericPointKaehlerConormal
import LeanPool.Stafford38.Stafford38.Geometry.RetainedPlaceConormalTransport

/-!
# Lane C reduced to a visible divisor frame

The finite-gradient interface of lane C asks, on every minimal component
whose distinguished coordinate is transcendental, for one finite-gradient
boundary certificate over some field extension.  This file reduces that
interface to a single geometric statement: the existence of a retained
boundary place whose normalized homogeneous coordinate column carries a
*visible divisor frame* in the sense of `DivisorTangentLattice`.

Everything downstream is trust-zero:

* the lattice lemma turns the visible frame into a Kähler relation with
  coefficients divisible by `t^(a+e-1)`;
* the generic-point bridge turns that relation into affine conormal
  membership at the generic point;
* the retained-place transport carries it to the completed residue field,
  supplies the projective zeroth entry, and produces the one-row datum;
* the existing adapter extracts the finite-gradient certificate.

Nothing here constructs the place or the frame.  The producer statement
`HigherDimensionalCanonicalVisibleDivisorFrameProduction` is the exact
remaining geometric input of lane C.
-/

namespace Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction

open Stafford38
open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalBaseVariety
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.CharacteristicInitialIdeal
open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.AsymptoticDivisorExistence
open Stafford38.Geometry.CanonicalNonconstantFiniteGradientProduction
open Stafford38.Geometry.CanonicalNonconstantFiniteGradientProductionProof
open Stafford38.Geometry.ComponentFunctionFieldBoundary
open Stafford38.Geometry.ComponentProjectiveClosure
open Stafford38.Geometry.DivisorTangentLattice
open Stafford38.Geometry.FiniteGradientResidueExtension
open Stafford38.Geometry.GenericPointKaehlerConormal
open Stafford38.Geometry.RelativeCoefficientDVR
open Stafford38.Geometry.RelativeRetainedBoundaryPlace
open Stafford38.Geometry.RetainedGroundMapIdentification
open Stafford38.Geometry.RetainedPlaceConormalTransport
open Stafford38.Geometry.RetainedProjectiveCompletion
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open IsLocalRing

noncomputable section

universe u


variable {k : Type u} [Field k] {m : ℕ}

/-! ## Conormal transfer from a minimal prime to the radical ideal -/

section Transfer

open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation

variable {F : Type*} [Field F]

theorem differentialCovector_mul (y : Fin m → F) (p q : MvPolynomial (Fin m) F) :
    differentialCovector y (p * q) =
      MvPolynomial.eval y q • differentialCovector y p +
        MvPolynomial.eval y p • differentialCovector y q := by
  apply LinearMap.ext
  intro v
  change (∑ i, differentialAt y (p * q) i * v i) =
    MvPolynomial.eval y q * (∑ i, differentialAt y p i * v i) +
      MvPolynomial.eval y p * (∑ i, differentialAt y q i * v i)
  simp only [differentialAt, MvPolynomial.pderiv_mul, map_add, map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

theorem differentialCovector_add (y : Fin m → F) (p q : MvPolynomial (Fin m) F) :
    differentialCovector y (p + q) = differentialCovector y p + differentialCovector y q := by
  apply LinearMap.ext
  intro v
  change (∑ i, differentialAt y (p + q) i * v i) =
    (∑ i, differentialAt y p i * v i) + ∑ i, differentialAt y q i * v i
  simp only [differentialAt, map_add, add_mul, Finset.sum_add_distrib]

theorem differentialCovector_zero (y : Fin m → F) :
    differentialCovector y (0 : MvPolynomial (Fin m) F) = 0 := by
  apply LinearMap.ext
  intro v
  change (∑ i, differentialAt y 0 i * v i) = 0
  simp [differentialAt]

/-- For a radical ideal `I` and a minimal prime `P` of `I`, every element of
`P` becomes an element of `I` after multiplication by an element outside `P`.
The multiplier is a product of elements of the other minimal primes. -/
theorem exists_mul_mem_of_mem_minimalPrimes_of_isRadical
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {I P : Ideal R} (hI : I.IsRadical) (hP : P ∈ I.minimalPrimes)
    {f : R} (hf : f ∈ P) : ∃ s ∉ P, s * f ∈ I := by
  classical
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R I
  set T := hfin.toFinset.erase P with hT
  have hchoice : ∀ Q ∈ T, ∃ s ∈ Q, s ∉ P := by
    intro Q hQ
    rw [hT, Finset.mem_erase, hfin.mem_toFinset] at hQ
    by_contra hcon
    push_neg at hcon
    exact hQ.1 (le_antisymm hcon (hP.2 hQ.2.1 hcon))
  choose s hsQ hsP using hchoice
  refine ⟨∏ Q ∈ T.attach, s Q.1 Q.2, ?_, ?_⟩
  · intro h
    obtain ⟨Q, -, hQ⟩ := (hP.1.1.prod_mem_iff).1 h
    exact hsP Q.1 Q.2 hQ
  · rw [← hI.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro Q hQ
    by_cases hQP : Q = P
    · subst hQP
      exact Ideal.mul_mem_left _ _ hf
    · have hQT : Q ∈ T := by
        rw [hT, Finset.mem_erase, hfin.mem_toFinset]
        exact ⟨hQP, hQ⟩
      refine Ideal.mul_mem_right _ _ ?_
      exact Ideal.mem_of_dvd _
        (Finset.dvd_prod_of_mem (fun Q : T ↦ s Q.1 Q.2) (Finset.mem_attach _ ⟨Q, hQT⟩))
        (hsQ Q hQT)

/-- At a point whose vanishing ideal is exactly the minimal prime `P` of `I`,
the equation-defined conormal space of `P` is contained in that of `I`. -/
theorem affineConormalSpace_map_minimalPrime_le [Algebra k F]
    (I P : Ideal (MvPolynomial (Fin m) k)) (hI : I.IsRadical) (hP : P ∈ I.minimalPrimes)
    (y : Fin m → F)
    (hy : ∀ f, MvPolynomial.eval y (MvPolynomial.map (algebraMap k F) f) = 0 ↔ f ∈ P) :
    affineConormalSpace y (P.map (MvPolynomial.map (algebraMap k F))) ≤
      affineConormalSpace y (I.map (MvPolynomial.map (algebraMap k F))) := by
  classical
  rw [affineConormalSpace_eq_equationCovectorSpan, affineConormalSpace_eq_equationCovectorSpan]
  set S := equationCovectorSpan y (I.map (MvPolynomial.map (algebraMap k F)))
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨f', hf'⟩, rfl⟩
  show differentialCovector y f' ∈ S
  have key : MvPolynomial.eval y f' = 0 ∧ differentialCovector y f' ∈ S := by
    refine Submodule.span_induction (p := fun x _ ↦
      MvPolynomial.eval y x = 0 ∧ differentialCovector y x ∈ S) ?_ ?_ ?_ ?_ hf'
    · rintro _ ⟨f, hf, rfl⟩
      refine ⟨(hy f).2 hf, ?_⟩
      obtain ⟨g, hgP, hfg⟩ := exists_mul_mem_of_mem_minimalPrimes_of_isRadical hI hP hf
      have hg : MvPolynomial.eval y (MvPolynomial.map (algebraMap k F) g) ≠ 0 :=
        fun h ↦ hgP ((hy g).1 h)
      have hprod : differentialCovector y
          (MvPolynomial.map (algebraMap k F) (g * f)) ∈ S :=
        Submodule.subset_span ⟨⟨_, Ideal.mem_map_of_mem _ hfg⟩, rfl⟩
      rw [map_mul, differentialCovector_mul, (hy f).2 hf, zero_smul, zero_add] at hprod
      have := S.smul_mem (MvPolynomial.eval y (MvPolynomial.map (algebraMap k F) g))⁻¹ hprod
      rwa [smul_smul, inv_mul_cancel₀ hg, one_smul] at this
    · exact ⟨by simp, by rw [differentialCovector_zero]; exact S.zero_mem⟩
    · rintro x y' _ _ ⟨hx0, hx⟩ ⟨hy0, hy'⟩
      exact ⟨by rw [map_add, hx0, hy0, add_zero],
        by rw [differentialCovector_add]; exact S.add_mem hx hy'⟩
    · rintro p x _ ⟨hx0, hx⟩
      refine ⟨by rw [smul_eq_mul, map_mul, hx0, mul_zero], ?_⟩
      rw [smul_eq_mul, differentialCovector_mul, hx0, zero_smul, zero_add]
      exact S.smul_mem _ hx
  exact key.2

end Transfer

/-- A retained boundary place on a component together with a normalized
projective column and a visible divisor frame attached to it. -/
def HasVisibleDivisorFrame
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (hm : 0 < m)
    [CharZero k] : Prop :=
  ∃ W : Data k (ComponentFractionField P) (componentCoordinate P ⟨0, hm⟩),
    letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
        (ComponentFractionField P) := W.ambientAlgebra
    let V := W.place.valuation.toSubring
    letI : IsDiscreteValuationRing V := W.place.isDiscrete
    ∃ (q : Fin (m + 1) → V) (scale : ComponentFractionField P),
      q 0 ≠ 0 ∧
      (∀ a, (q a : ComponentFractionField P) =
        scale * componentProjectivePoint P a) ∧
      q (Fin.succ ⟨0, hm⟩) = q 0 * W.place.parameter ∧
      ∃ D : VisibleDivisorFrame (V := V)
        (KaehlerDifferential.D k (ComponentFractionField P)) (Fin m),
        D.Q₀ = q 0 ∧ D.Q₁ = q (Fin.succ ⟨0, hm⟩) ∧ ∀ j, D.Q j = q (Fin.succ j)

/-- The generic-point bridge instantiated on a component: its statement is
the `hbridge` hypothesis of the retained-place transport. -/
theorem component_kaehler_bridge (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (xi : Fin m → ComponentFractionField P)
    (h : ∑ j, xi j • KaehlerDifferential.D k (ComponentFractionField P)
      (componentCoordinate P j) = 0) :
    Stafford38.Geometry.AffineConormalSpan.coordinateCovector xi ∈
      Stafford38.Geometry.AffineConormalSpan.affineConormalSpace (componentCoordinate P)
        (P.asIdeal.map (MvPolynomial.map
          (algebraMap k (ComponentFractionField P)))) := by
  haveI : P.asIdeal.IsPrime := P.isPrime
  exact coordinateCovector_mem_affineConormalSpace_of_kaehler_sum_eq_zero
    (I := P.asIdeal) (F := ComponentFractionField P) xi h

/-- A visible divisor frame on a component yields a finite-gradient boundary
certificate over the residue field of its place, for the radical ideal of
which the component is a minimal prime. -/
theorem exists_finiteGradientBoundaryCertificateOver_of_hasVisibleDivisorFrame
    [CharZero k]
    (I : Ideal (MvPolynomial (Fin m) k)) (hI : I.IsRadical)
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (hP : P.asIdeal ∈ I.minimalPrimes)
    (hm : 0 < m) (h : HasVisibleDivisorFrame P hm) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      Nonempty (FiniteGradientBoundaryCertificateOver (k := k) (K := K) m hm I) := by
  classical
  obtain ⟨W, q, scale, hq0, hq, hratio, D, hQ₀, hQ₁, hQ⟩ := h
  letI : Algebra (CoordinateZeroLocalRing W.coefficientField)
      (ComponentFractionField P) := W.ambientAlgebra
  let V := W.place.valuation.toSubring
  letI : IsDiscreteValuationRing V := W.place.isDiscrete
  letI : Algebra W.coefficientField V :=
    (relativeCoefficientMap W.coefficientField W.place).toAlgebra
  letI : Algebra k (ResidueField V) := retainedResidueGroundAlgebra P ⟨0, hm⟩ W
  -- The generic point kills exactly the minimal prime.
  have hy : ∀ f, MvPolynomial.eval (componentCoordinate P)
      (MvPolynomial.map (algebraMap k (ComponentFractionField P)) f) = 0 ↔ f ∈ P.asIdeal := by
    intro f
    rw [MvPolynomial.eval_map, ← componentAffineGenericPointMap_eq_eval₂,
      ← RingHom.mem_ker, componentAffineGenericPointMap_ker]
  have hbridge : ∀ xi : Fin m → ComponentFractionField P,
      ∑ j, xi j • KaehlerDifferential.D k (ComponentFractionField P)
        (componentCoordinate P j) = 0 →
      Stafford38.Geometry.AffineConormalSpan.coordinateCovector xi ∈
        Stafford38.Geometry.AffineConormalSpan.affineConormalSpace (componentCoordinate P)
          (I.map (MvPolynomial.map (algebraMap k (ComponentFractionField P)))) :=
    fun xi hxi ↦ affineConormalSpace_map_minimalPrime_le I P.asIdeal hI hP _ hy
      (component_kaehler_bridge P xi hxi)
  have hq0F : (q 0 : ComponentFractionField P) ≠ 0 := fun h ↦ hq0 (Subtype.ext h)
  have hIy : ∀ g ∈ I,
      MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
        (componentCoordinate P) g = 0 := by
    intro g hg
    rw [← componentAffineGenericPointMap_eq_eval₂]
    exact componentAffineGenericPointMap_eq_zero_of_mem P (hP.1.2 hg)
  let : SMul V (ComponentFractionField P) :=
    (inferInstance : Algebra V (ComponentFractionField P)).toSMul
  let : SMulCommClass k V (ComponentFractionField P) := ⟨fun a b c ↦ by
    simp only [Algebra.smul_def]
    ring⟩
  obtain ⟨R⟩ := regularizedOneRowConormalData_of_transport hm I (componentCoordinate P)
    hIy Subtype.val_injective (retainedToCompletedPowerSeries W)
    (retainedToCompletedPowerSeries_injective W)
    (retainedToCompletedPowerSeries_constantCoeff_eq_zero_of_nonunit W)
    (retainedLaurentLift P ⟨0, hm⟩ W)
    (retainedLaurentLift_algebraMap P ⟨0, hm⟩ W)
    (retainedLaurentLift_comp_algebraMap P ⟨0, hm⟩ W)
    q hq0 (componentCoordinate_eq_div P (fun a ↦ (q a : ComponentFractionField P))
      scale hq hq0F)
    W.place.parameter hratio D hQ₀ hQ₁ hQ hbridge
  exact ⟨ResidueField V, inferInstance, inferInstance,
    finiteGradientBoundaryCertificateOver_of_regularizedOneRowConormalData hm I _ R⟩

/-- The reduced lane C input: every relevant transcendental component carries
a retained place with a visible divisor frame. -/
def HigherDimensionalCanonicalVisibleDivisorFrameProduction : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (n N : ℕ) (d : PresentedWeyl k (n + 1)),
    0 < n →
    Disjoint
      (orderCharacteristicSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N))
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1)))) →
    ∀ P : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k),
      P.asIdeal ∈
        (reducedOrderBaseIdeal k
          (canonicalRightIdeal (presentedCoordinate k n) d N)).minimalPrimes →
      Transcendental k (componentCoordinate P ⟨0, Nat.zero_lt_succ n⟩) →
      HasVisibleDivisorFrame P (Nat.zero_lt_succ n)

/-- The visible-frame producer discharges the finite-gradient interface. -/
theorem higherDimensionalCanonicalResidueExtensionNonconstantFiniteGradientProduction_of_visibleDivisorFrame
    (h : HigherDimensionalCanonicalVisibleDivisorFrameProduction.{u}) :
    HigherDimensionalCanonicalResidueExtensionNonconstantFiniteGradientProduction.{u} := by
  intro k _ _ _ n N d hn hdisjoint P hP htrans
  exact exists_finiteGradientBoundaryCertificateOver_of_hasVisibleDivisorFrame _
    (reducedOrderBaseIdeal_isRadical k (canonicalRightIdeal (presentedCoordinate k n) d N))
    P hP (Nat.zero_lt_succ n) (h k n N d hn hdisjoint P hP htrans)


end

end Stafford38.Geometry.CanonicalVisibleDivisorFrameProduction
