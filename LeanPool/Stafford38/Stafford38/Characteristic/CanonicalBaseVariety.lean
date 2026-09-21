/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalAxisAvoidanceConsumer
import LeanPool.Stafford38.Stafford38.Characteristic.BaseZeroSection
import LeanPool.Stafford38.Stafford38.Characteristic.ReducedSupportIdeal
import Mathlib.RingTheory.Nullstellensatz

/-!
# The affine base variety feeding the asymptotic argument

Over an algebraically closed field, nonempty order-characteristic support
forces the contracted reduced base ideal to have a rational point.  If the
support avoids the distinguished coordinate hyperplane, every such base point
has nonzero distinguished coordinate.  These are exactly the affine premises
of the remaining projective-boundary theorem.
-/

namespace Stafford38.Characteristic.CanonicalBaseVariety

open Stafford38
open Stafford38.Characteristic
open Stafford38.Characteristic.BaseZeroSection
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

omit [IsAlgClosed k] in
/-- A nonempty reduced order support makes its contracted base ideal proper. -/
theorem reducedOrderBaseIdeal_ne_top_of_support_nonempty
    (I : RightIdeal (PresentedWeyl k n))
    (hsupp : (orderCharacteristicSupport k I).Nonempty) :
    reducedOrderBaseIdeal k I ≠ ⊤ := by
  rintro htop
  rcases hsupp with ⟨p, hp⟩
  have hpReduced : p ∈ PrimeSpectrum.zeroLocus
      (reducedOrderSupportIdeal k I : Set (SymbolRing k n)) := by
    rw [← orderCharacteristicSupport_eq_zeroLocus_reduced k I]
    exact hp
  rw [PrimeSpectrum.mem_zeroLocus] at hpReduced
  have honeBase : (1 : MvPolynomial (Fin n) k) ∈
      reducedOrderBaseIdeal k I := by rw [htop]; exact Submodule.mem_top
  have honeReduced : (1 : SymbolRing k n) ∈
      reducedOrderSupportIdeal k I := by
    simpa [baseLift] using
      (mem_reducedOrderBaseIdeal_iff k I 1).mp honeBase
  exact p.2.ne_top
    ((Ideal.eq_top_iff_one p.asIdeal).2 (hpReduced honeReduced))

/-- Over an algebraically closed field, nonempty support therefore produces a
ground-field point of the contracted base zero set. -/
theorem exists_reducedOrderBaseZero_of_support_nonempty
    (I : RightIdeal (PresentedWeyl k n))
    (hsupp : (orderCharacteristicSupport k I).Nonempty) :
    ∃ y : Fin n → k,
      ∀ f ∈ reducedOrderBaseIdeal k I, MvPolynomial.eval y f = 0 := by
  let B := reducedOrderBaseIdeal k I
  obtain ⟨M, hMmax, hBM⟩ :=
    Ideal.exists_le_maximal B
      (reducedOrderBaseIdeal_ne_top_of_support_nonempty I hsupp)
  obtain ⟨y, hMy⟩ :=
    MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hMmax
  refine ⟨y, ?_⟩
  intro f hf
  have hfM : f ∈ M := hBM hf
  rw [hMy, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hfM
  exact hfM

omit [IsAlgClosed k] in
/-- If support avoids the coordinate-zero prime locus, every point of the
contracted base variety has nonzero distinguished coordinate. -/
theorem coordinate_ne_zero_of_baseZero_of_support_disjoint
    (I : RightIdeal (PresentedWeyl k n)) (i : Fin n)
    (hdisjoint : Disjoint
      (orderCharacteristicSupport k I)
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl i)} : Set (SymbolRing k n))))
    (y : Fin n → k)
    (hy : ∀ f ∈ reducedOrderBaseIdeal k I, MvPolynomial.eval y f = 0) :
    y i ≠ 0 := by
  intro hyi
  let q : PhaseVar n → k := zeroSectionPoint y
  let p : PrimeSpectrum (SymbolRing k n) := MvPolynomial.pointToPoint q
  have hzero : ∀ P ∈ reducedOrderSupportIdeal k I,
      MvPolynomial.eval q P = 0 := by
    exact zeroSection_mem_of_mem_reducedOrderBaseZeroSet k I y hy
  have hpSupport : p ∈ orderCharacteristicSupport k I := by
    rw [orderCharacteristicSupport_eq_zeroLocus_reduced]
    rw [PrimeSpectrum.mem_zeroLocus]
    intro P hP
    change P ∈ MvPolynomial.vanishingIdeal k {q}
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hzero P hP
  have hpCoordinate : p ∈ PrimeSpectrum.zeroLocus
      ({MvPolynomial.X (.inl i)} : Set (SymbolRing k n)) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    intro P hP
    change P ∈ MvPolynomial.vanishingIdeal k {q}
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff,
      Set.mem_singleton_iff.mp hP]
    simp [q, zeroSectionPoint, hyi]
  exact Set.disjoint_left.mp hdisjoint hpSupport hpCoordinate

/-- The two affine hypotheses required by the asymptotic boundary theorem:
the base zero set is inhabited and lies in the principal open `X_i ≠ 0`. -/
theorem exists_baseZero_and_all_coordinate_ne_zero
    (I : RightIdeal (PresentedWeyl k n)) (i : Fin n)
    (hdisjoint : Disjoint
      (orderCharacteristicSupport k I)
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl i)} : Set (SymbolRing k n))))
    (hsupp : (orderCharacteristicSupport k I).Nonempty) :
    (∃ y : Fin n → k,
      ∀ f ∈ reducedOrderBaseIdeal k I, MvPolynomial.eval y f = 0) ∧
    (∀ y : Fin n → k,
      (∀ f ∈ reducedOrderBaseIdeal k I, MvPolynomial.eval y f = 0) →
      y i ≠ 0) := by
  refine ⟨exists_reducedOrderBaseZero_of_support_nonempty I hsupp, ?_⟩
  intro y hy
  exact coordinate_ne_zero_of_baseZero_of_support_disjoint I i hdisjoint y hy


end

end Stafford38.Characteristic.CanonicalBaseVariety
