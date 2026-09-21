/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import LeanPool.Stafford38.Stafford38.Geometry.GeneralConormalContainment
import LeanPool.Stafford38.Stafford38.Geometry.ConormalPrincipalOpenDensity
import LeanPool.Stafford38.Stafford38.Geometry.SmoothAffineConormal
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
Containment of a component’s conormal closure in the ambient characteristic variety.
-/

namespace Stafford38.Geometry.GeneralComponentConormalContainment

open Stafford38
open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.ConormalPrincipalOpenDensity
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.GeneralConormalContainment
open Stafford38.Geometry.SmoothAffineConormal
open Stafford38.WeylFiltration

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}

omit [IsAlgClosed k] [CharZero k] in
private theorem differentialCovector_mul (y : Fin n → k)
    (p q : MvPolynomial (Fin n) k) :
    differentialCovector y (p * q) =
      MvPolynomial.eval y q • differentialCovector y p +
        MvPolynomial.eval y p • differentialCovector y q := by
  apply LinearMap.ext
  intro v
  change (∑ i, differentialAt y (p * q) i * v i) =
    MvPolynomial.eval y q * (∑ i, differentialAt y p i * v i) +
      MvPolynomial.eval y p * (∑ i, differentialAt y q i * v i)
  simp only [differentialAt, MvPolynomial.pderiv_mul, map_add, map_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

omit [IsAlgClosed k] [CharZero k] in
private theorem exists_separator
    (I P : Ideal (MvPolynomial (Fin n) k))
    (hI : I.IsRadical) (hP : P ∈ I.minimalPrimes) :
    ∃ f ∉ P, ∀ h ∈ P, f * h ∈ I := by
  classical
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing
    (MvPolynomial (Fin n) k) I
  set T := hfin.toFinset.erase P with hT
  have hchoice : ∀ Q ∈ T, ∃ s ∈ Q, s ∉ P := by
    intro Q hQ
    rw [hT, Finset.mem_erase, hfin.mem_toFinset] at hQ
    by_contra hcon
    push Not at hcon
    exact hQ.1 (le_antisymm hcon (hP.2 hQ.2.1 hcon))
  choose s hsQ hsP using hchoice
  let f := ∏ Q ∈ T.attach, s Q.1 Q.2
  have hfP : f ∉ P := by
    intro hf
    obtain ⟨Q, -, hQ⟩ := (hP.1.1.prod_mem_iff).1 hf
    exact hsP Q.1 Q.2 hQ
  refine ⟨f, hfP, ?_⟩
  intro h hp
  rw [← hI.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
  intro Q hQ
  by_cases hQP : Q = P
  · subst hQP
    exact Ideal.mul_mem_left _ _ hp
  · have hQT : Q ∈ T := by
      rw [hT, Finset.mem_erase, hfin.mem_toFinset]
      exact ⟨hQP, hQ⟩
    refine Ideal.mul_mem_right _ _ ?_
    exact Ideal.mem_of_dvd _
      (Finset.dvd_prod_of_mem (fun Q : T ↦ s Q.1 Q.2)
        (Finset.mem_attach _ ⟨Q, hQT⟩))
      (hsQ Q hQT)

theorem equationConormalClosure_minimalPrime_subset_zeroLocus
    (J : Ideal (SymbolRing k n))
    (hJrad : J.IsRadical)
    (hhom : J.IsHomogeneous (orderDecomposition (k := k) (n := n)))
    (hJpoisson : IsBaseRelativePoisson J)
    (P : Ideal (MvPolynomial (Fin n) k))
    (hP : P ∈ (J.comap baseLift).minimalPrimes) :
    equationConormalClosure P ⊆ MvPolynomial.zeroLocus k J := by
  let I : Ideal (MvPolynomial (Fin n) k) :=
    J.comap (baseLift (k := k) (n := n)).toRingHom
  have hIrad : I.IsRadical := by
    exact Ideal.IsRadical.comap
      (f := (baseLift (k := k) (n := n)).toRingHom) hJrad
  change P ∈ I.minimalPrimes at hP
  obtain ⟨f, hfP, hfp⟩ := exists_separator I P hIrad hP
  let S : Set (Fin n → k) := {y | y ∈ MvPolynomial.zeroLocus k P ∧
    MvPolynomial.eval y f ≠ 0}
  have hS : S ⊆ MvPolynomial.zeroLocus k P := by
    intro y hy
    exact hy.1
  have hopen : ∀ y : Fin n → k, y ∈ MvPolynomial.zeroLocus k P →
      MvPolynomial.eval y f ≠ 0 → y ∈ S := by
    intro y hy hfy
    exact ⟨hy, hfy⟩
  have hrestricted :
      ConormalPrincipalOpenDensity.restrictedEquationConormalLocus P S ⊆
        MvPolynomial.zeroLocus k J := by
    intro q hq
    let y : Fin n → k := fun i ↦ q (Sum.inl i)
    let ξ : Fin n → k := fun i ↦ q (Sum.inr i)
    have hyP : y ∈ MvPolynomial.zeroLocus k P := hq.2.1
    have hfy : MvPolynomial.eval y f ≠ 0 := hq.2.2
    have hyI : ∀ g ∈ I, MvPolynomial.eval y g = 0 := by
      intro g hg
      exact hq.1.1 g (hP.1.2 hg)
    have hinc : affineConormalSpace y P ≤ affineConormalSpace y I := by
      rw [affineConormalSpace_eq_equationCovectorSpan y P,
        affineConormalSpace_eq_equationCovectorSpan y I]
      apply Submodule.span_le.2
      intro z hz
      rcases hz with ⟨h', rfl⟩
      rcases h' with ⟨h, hh⟩
      obtain hfh := hfp h hh
      have hgen : differentialCovector y (f * h) ∈
          equationCovectorSpan y I := by
        apply Submodule.subset_span
        exact ⟨⟨f * h, hfh⟩, rfl⟩
      have hevalh : MvPolynomial.eval y h = 0 := hq.1.1 h hh
      rw [differentialCovector_mul, hevalh, zero_smul, zero_add] at hgen
      have hscaled := (equationCovectorSpan y I).smul_mem
        (MvPolynomial.eval y f)⁻¹ hgen
      rw [smul_smul, inv_mul_cancel₀ hfy, one_smul] at hscaled
      exact hscaled
    have hxiI : coordinateCovector ξ ∈ affineConormalSpace y I :=
      hinc hq.1.2
    have hqI : q ∈ equationConormalLocus I := ⟨hyI, hxiI⟩
    exact (GeneralConormalContainment.equationConormalLocus_subset_zeroLocus
        J hJpoisson (fun z hz ↦
        zeroSection_commonZero_of_isHomogeneous J hhom z hz)) hqI
  have hclosure := equationConormalClosure_restricted_eq P hP.1.1 f hfP S hopen
  intro q hq
  apply (zeroLocus_vanishingIdeal_mono_of_subset_zeroLocus
    (ConormalPrincipalOpenDensity.restrictedEquationConormalLocus P S)
    J hrestricted)
  rw [hclosure]
  exact hq

theorem smoothConormalClosure_minimalPrime_subset_zeroLocus
    (J : Ideal (SymbolRing k n))
    (hJrad : J.IsRadical)
    (hhom : J.IsHomogeneous (orderDecomposition (k := k) (n := n)))
    (hJpoisson : IsBaseRelativePoisson J)
    (P : Ideal (MvPolynomial (Fin n) k))
    (hP : P ∈ (J.comap baseLift).minimalPrimes) :
    MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (restrictedEquationConormalLocus P {y | SmoothAffinePoint P y})) ⊆
      MvPolynomial.zeroLocus k J := by
  rw [equationConormalClosure_smoothAffine_eq P hP.1.1]
  exact equationConormalClosure_minimalPrime_subset_zeroLocus
    J hJrad hhom hJpoisson P hP


end

end Stafford38.Geometry.GeneralComponentConormalContainment
