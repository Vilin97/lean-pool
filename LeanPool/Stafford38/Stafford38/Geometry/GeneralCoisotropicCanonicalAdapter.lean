/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.GradedAlgebra.Radical
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalGabberInvolutivityInterface
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalLaurentSymbolControl
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalUnitCoordinatePreimage
import LeanPool.Stafford38.Stafford38.Characteristic.GabberGlobalAssembly
import LeanPool.Stafford38.Stafford38.Characteristic.InitialIdealHomogeneous
import LeanPool.Stafford38.Stafford38.Characteristic.ReducedSupportIdeal
import LeanPool.Stafford38.Stafford38.Characteristic.ZeroSectionContainment
import LeanPool.Stafford38.Stafford38.CanonicalSupportVanishingReduction
import LeanPool.Stafford38.Stafford38.Geometry.FibreConicalVanishingIdeal
import LeanPool.Stafford38.Stafford38.Geometry.GeneralCoisotropicSets

/-!
# Adapter from canonical order support to the arbitrary coisotropic theorem

The canonical order support is presented on the prime spectrum, while the
general exclusion theorem is stated for field-valued phase points.  This file
performs that change of presentation at the reduced order-support ideal.  The
canonical support-avoidance input supplies the coordinate hypothesis, and the
Gabber involutivity result supplies the self-involutivity of the same radical
ideal.

This adapter is deliberately separate from the canonical support assembly, so
the general theorem can be integrated there without an import cycle.
-/

namespace Stafford38.Geometry.GeneralCoisotropicCanonicalAdapter

open Stafford38
open Stafford38.CanonicalSupportVanishingReduction
open Stafford38.CanonicalUnitCoordinatePreimage
open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.CharacteristicInitialIdeal
open Stafford38.Characteristic.CanonicalLaurentSymbolControl
open Stafford38.Characteristic.CanonicalBaseVariety
open Stafford38.Characteristic.GabberGlobalAssembly
open Stafford38.CharacteristicInitialIdealHomogeneous
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.Characteristic.ZeroSectionContainment
open Stafford38.Characteristic.PostScalarExtensionPoisson
open Stafford38.CharacteristicHomogeneousChart
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.FibreConicalVanishingIdeal
open Stafford38.Geometry.GeneralCoisotropicSets
open Stafford38.Geometry.ConormalAxisContradiction
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.WeylEulerResidue
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBWMonicBridge
open Stafford38.EulerSurjectivity

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]

/-- The order-weight grading used by the general coisotropic adapter. -/
local instance orderGradedAlgebraInstance {n : ℕ} :
    GradedAlgebra
      (MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n)) :=
  MvPolynomial.weightedGradedAlgebra k (@orderWeight n)

omit [IsAlgClosed k] [CharZero k] in
private theorem orderInitialIdeal_isHomogeneous
    {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) :
    (orderInitialIdeal k I).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n)) := by
  intro d P hP
  exact CharacteristicFilteredQuotient.coe_mem_orderInitialIdeal_of_mem_orderSymbolRelation k I d
    (DirectSum.decompose
      (MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n)) P d)
    (decompose_mem_orderSymbolRelation_of_mem_orderInitialIdeal
      k I P hP d)

omit [IsAlgClosed k] [CharZero k] in
private theorem zeroLocus_isFibreConical_of_isHomogeneous
    {n : ℕ} (J : Ideal (SymbolRing k n))
    (hhom : J.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n))) :
    IsFibreConical (MvPolynomial.zeroLocus k J) := by
  intro q hq a ha
  let y : Fin n → k := fun i => q (.inl i)
  let ξ : Fin n → k := fun i => q (.inr i)
  have hqsplit : q = Sum.elim y ξ := by
    funext i
    rcases i with i | i <;> rfl
  have hline (f : SymbolRing k n) (hf : f ∈ J) :
      fibreLinePolynomial y ξ f = 0 := by
    apply Polynomial.ext
    intro d
    rw [coeff_fibreLinePolynomial_eq_eval_weightedHomogeneousComponent]
    rw [← hqsplit]
    exact (MvPolynomial.mem_zeroLocus_iff.mp hq) _ (hhom d hf)
  intro f hf
  have heval := eval_fibreLinePolynomial y ξ f a
  rw [hline f hf, Polynomial.eval_zero] at heval
  simpa [y, ξ] using heval.symm

/-! The canonical reduced support ideal is an admissible input to the
general coisotropic exclusion theorem.  The only geometric fact used here is
Gabber's involutivity of the radical associated graded annihilator; its
base-relative fragment is obtained by restricting the first bracket entry to
the base polynomial subring. -/

theorem algebraicallyClosedCanonicalSupportVanishing_of_generalCoisotropic
    (hunit : CanonicalStrictUnitCoordinatePreimage.{u}) :
    AlgebraicallyClosedCanonicalSupportVanishing.{u} := by
  intro k _ _ _ n N d hN hd
  let I := canonicalRightIdeal (presentedCoordinate k n) d N
  let J : Ideal (SymbolRing k (n + 1)) := reducedOrderSupportIdeal k I
  have hdisjoint : Disjoint
      (orderCharacteristicSupport k I)
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1)))) := by
    exact canonical_orderCharacteristicSupport_disjoint_coordinate_zeroLocus_of_strictUnit
      k n N (hunit k n N d hN hd)
  by_contra hsupp
  have hnonempty : (orderCharacteristicSupport k I).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hsupp
  have hproper : J ≠ ⊤ := by
    intro htop
    obtain ⟨p, hp⟩ := hnonempty
    have hpzero : p ∈ PrimeSpectrum.zeroLocus J := by
      rw [← orderCharacteristicSupport_eq_zeroLocus_reduced k I]
      exact hp
    rw [htop] at hpzero
    simpa using hpzero
  have hrad : J.IsRadical := by
    simpa only [J] using reducedOrderSupportIdeal_isRadical k I
  have hhom : J.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule k
        (@orderWeight (n + 1))) := by
    simpa only [J, reducedOrderSupportIdeal] using
      (orderInitialIdeal_isHomogeneous (k := k) I).radical
  have hinv : IsInvolutive J := by
    change IsInvolutive (orderInitialIdeal k I).radical
    rw [← annihilator_orderAssociatedGradedModule]
    exact associatedGraded_radical_isInvolutive (k := k) I
  have hW : IsFibreConical (MvPolynomial.zeroLocus k J) :=
    zeroLocus_isFibreConical_of_isHomogeneous J hhom
  have hnonemptyW : (MvPolynomial.zeroLocus k J).Nonempty := by
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hproper
    obtain ⟨q, hqM⟩ :=
      MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hM
    refine ⟨q, ?_⟩
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro f hf
    have hfM : f ∈ M := hJM hf
    rw [hqM, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hfM
    exact hfM
  have hpoissonW : ∀ f ∈ MvPolynomial.vanishingIdeal k
      (MvPolynomial.zeroLocus k J),
      ∀ g ∈ MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k J),
        poissonBracket f g ∈ MvPolynomial.vanishingIdeal k
          (MvPolynomial.zeroLocus k J) := by
    intro f hf g hg
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hf hg ⊢
    exact Ideal.le_radical (hinv f (hrad hf) g (hrad hg))
  obtain ⟨P, hP⟩ := exists_canonical_fibrePolynomial n N hd
  have hPinitial : fibreLift P ∈ J := by
    apply orderInitialIdeal_le_reducedOrderSupportIdeal k I
    rw [hP]
    exact canonical_orderPrincipalComponent_mem_initialIdeal k n N hd
  have hPaxis : MvPolynomial.eval
      (fun i : Fin (n + 1) =>
        if i = ⟨0, Nat.zero_lt_succ n⟩ then (1 : k) else 0) P = 1 := by
    have hcanonical := canonical_orderPrincipalComponent_eval_pureMomentumAxis
      n N hd
    rw [← hP] at hcanonical
    have heval := eval₂_fibreLift (K := k) P
      (fun _ : Fin (n + 1) => (0 : k))
      (fun i : Fin (n + 1) =>
        if i = ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0)
    have hsplit : Sum.elim (fun _ : Fin (n + 1) => (0 : k))
        (fun i : Fin (n + 1) =>
          if i = ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) =
        axisPoint k (.inr (0 : Fin (n + 1))) := by
      funext i
      rcases i with i | i
      · simp [axisPoint]
      · simp [axisPoint, Sum.inr.injEq] <;> rfl
    rw [hsplit] at heval
    simpa only [← MvPolynomial.aeval_def, MvPolynomial.aeval_eq_eval] using
      heval.symm.trans hcanonical
  obtain ⟨q, hq, hqcoord⟩ :=
    exists_zero_base_coordinate_of_isFibreConical
      (k := k) (m := n + 1) (Nat.zero_lt_succ n)
      (MvPolynomial.zeroLocus k J) hnonemptyW ⟨J, rfl⟩ hW hpoissonW P
      (by
        rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]
        exact Ideal.le_radical hPinitial)
      (by rw [hPaxis]; exact one_ne_zero)
  have hqSupport : MvPolynomial.pointToPoint q ∈
      orderCharacteristicSupport k I := by
    rw [orderCharacteristicSupport_eq_zeroLocus_reduced k I,
      PrimeSpectrum.mem_zeroLocus]
    intro f hf
    change f ∈ MvPolynomial.vanishingIdeal k {q}
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact (MvPolynomial.mem_zeroLocus_iff.mp hq) f hf
  have hqCoordinate : MvPolynomial.pointToPoint q ∈
      PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1))) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    intro f hf
    change f ∈ MvPolynomial.vanishingIdeal k {q}
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff,
      Set.mem_singleton_iff.mp hf]
    simpa using hqcoord
  exact Set.disjoint_left.mp hdisjoint hqSupport hqCoordinate

end
end Stafford38.Geometry.GeneralCoisotropicCanonicalAdapter
