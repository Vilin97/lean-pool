/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalLaurentSymbolControl
import LeanPool.Stafford38.Stafford38.Geometry.FiniteGradientResidueExtension
import LeanPool.Stafford38.Stafford38.Geometry.OneVariableAmbientConormal

/-!
# Canonical geometry over the boundary residue field

The residue field `K` of a projective boundary divisor need not equal the
ground field `k`.  The completed arc therefore lives in `K[[t]]`, while the
canonical Weyl operator, its principal symbol, and the contracted base ideal
remain defined over `k`.

This file repairs the terminal rank split at that interface.  In ambient rank
one the existing direct argument stays over `k`.  In higher rank the producer
is allowed to choose an arbitrary extension field `K/k` and returns the
Laurent conormal point actually consumed by the symbol contradiction.  It may
obtain that point directly from a constant-coordinate component or from a
completed boundary chart.  Symbol vanishing is requested over the same chosen
extension, and the contradiction is completed there.  No map `K → k`
occurs.

The results are conditional assemblers.  They do not produce the
higher-dimensional conormal axis, prove post-extension Poisson/Gabber
integrability, prove noncharacteristic restriction, or prove the canonical
coordinate-preimage hypothesis.
-/

namespace Stafford38.Geometry.CanonicalResidueExtensionAssembly

open Stafford38
open Stafford38.CanonicalAxisAvoidanceConsumer
open Stafford38.CanonicalSupportVanishingReduction
open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalLaurentSymbolControl
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.CharacteristicInitialIdeal
open Stafford38.CharacteristicHomogeneousChart
open Stafford38.CanonicalUnitCoordinatePreimage
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.ConormalAxisContradiction
open Stafford38.Geometry.FiniteGradientResidueExtension
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.LaurentConormalResidueExtension
open Stafford38.Geometry.OneVariableAmbientConormal
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryRetractionSpecialization
open Stafford38.WeylEulerResidue
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBWMonicBridge

noncomputable section

universe u

/-! ## Exact conditional inputs -/

/-- Symbol control after extension to the Laurent field of an arbitrary
residue extension `K/k`.

This is the exact geometric-support input used below.  It is deliberately not
called a theorem of Gabber: a caller must still prove it for the concrete
canonical quotient and the particular extension selected by boundary
geometry. -/
def CanonicalResidueExtensionSymbolControl : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (K : Type u) [Field K] [Algebra k K]
    (n N : ℕ) (d : PresentedWeyl k (n + 1)),
    0 < N → IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d →
      ∃ P : MvPolynomial (Fin (n + 1)) k,
        fibreLift P = presentedPrincipalComponent k orderWeight N d ∧
        ∀ q ∈ groundEquationConormalLocus (k := k) (K := K)
            (reducedOrderBaseIdeal k
              (canonicalRightIdeal (presentedCoordinate k n) d N)),
          MvPolynomial.eval₂ (groundLaurentMap (k := k) (K := K)) q
            (fibreLift P) = 0

/-- Higher-dimensional production of the exact conormal-axis endpoint used by
the symbol contradiction, over its natural existential residue extension.

The strict inequality excludes ambient rank one, which is handled directly.
In higher rank this interface deliberately does not prescribe how the point is
produced: the constant-coordinate branch may take `K = k`, while the
nonconstant branch may extract it from a completed boundary chart over a
genuine residue extension. -/
def HigherDimensionalCanonicalResidueExtensionConormalAxisProduction : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (n N : ℕ) (d : PresentedWeyl k (n + 1)),
    0 < n →
    0 < N →
    IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d →
    Disjoint
      (orderCharacteristicSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N))
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1)))) →
    (orderCharacteristicSupport k
      (canonicalRightIdeal (presentedCoordinate k n) d N)).Nonempty →
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (y : Fin (n + 1) → LaurentSeries K)
      (xi : Fin (n + 1) → PowerSeries K),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries K) (LaurentSeries K) (xi i)) ∈
        groundEquationConormalLocus (k := k) (K := K)
          (reducedOrderBaseIdeal k
            (canonicalRightIdeal (presentedCoordinate k n) d N)) ∧
      residueColumn xi =
        (fun i : Fin (n + 1) ↦
          if i = ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0)

/-! ## One chart gives the terminal contradiction over `K` -/

/-- The canonical principal symbol evaluates to one on the pure first-fibre
axis before and after extension from `k` to `K`. -/
theorem canonical_fibrePolynomial_eval_extensionAxis
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n N : ℕ} {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (P : MvPolynomial (Fin (n + 1)) k)
    (hP : fibreLift P = presentedPrincipalComponent k orderWeight N d) :
    MvPolynomial.eval₂ (algebraMap k K)
        (fun i : Fin (n + 1) ↦
          if i = ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) P = 1 := by
  have hcanonical :=
    canonical_orderPrincipalComponent_eval_pureMomentumAxis n N hd
  have hsplit :
      Sum.elim (fun _ : Fin (n + 1) ↦ (0 : k))
          (fun i : Fin (n + 1) ↦
            if i = ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) =
        axisPoint k (.inr (0 : Fin (n + 1))) := by
    funext i
    rcases i with i | i
    · simp [axisPoint]
    · (simp [axisPoint]; rfl)
  rw [← hP] at hcanonical
  have heval := eval₂_fibreLift (K := k) P
    (fun _ : Fin (n + 1) ↦ (0 : k))
    (fun i : Fin (n + 1) ↦
      if i = ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0)
  rw [hsplit] at heval
  have hground : MvPolynomial.eval
      (fun i : Fin (n + 1) ↦
        if i = ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) P = 1 := by
    simpa only [← MvPolynomial.aeval_def, MvPolynomial.aeval_eq_eval] using
      heval.symm.trans hcanonical
  rw [eval₂_extensionAxis_eq_algebraMap_eval_axis
    (K := K) (Nat.zero_lt_succ n) P, hground]
  exact map_one (algebraMap k K)

/-- A residue-extension completed chart, together with canonical symbol
vanishing over the same Laurent field, is contradictory.  The conclusion is
proved in `K`; no residue-field descent or retraction is used. -/
theorem false_of_canonical_completedProjectiveBoundaryChartOver
    {k K : Type u} [Field k] [CharZero k]
    [Field K] [Algebra k K]
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (P : MvPolynomial (Fin (n + 1)) k)
    (hP : fibreLift P = presentedPrincipalComponent k orderWeight N d)
    (W : CompletedProjectiveBoundaryChartOver
      (k := k) (K := K) (n + 1) (Nat.zero_lt_succ n)
      (reducedOrderBaseIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N)))
    (hvanishes :
      ∀ q ∈ groundEquationConormalLocus (k := k) (K := K)
          (reducedOrderBaseIdeal k
            (canonicalRightIdeal (presentedCoordinate k n) d N)),
        MvPolynomial.eval₂ (groundLaurentMap (k := k) (K := K)) q
          (fibreLift P) = 0) : False := by
  let : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap k K).injective
  obtain ⟨y, xi, hgeneric, hresidue⟩ :=
    exists_conormalAxis_of_completedProjectiveBoundaryChartOver
      (k := k) (K := K) (Nat.zero_lt_succ n)
      (reducedOrderBaseIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N)) W
  exact false_of_ground_fibreOnly_symbol_one_on_residue_and_vanishing
    (k := k) (K := K)
    (reducedOrderBaseIdeal k
      (canonicalRightIdeal (presentedCoordinate k n) d N))
    P
    (fun i : Fin (n + 1) ↦
      if i = ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0)
    y xi hgeneric hresidue hvanishes
    (canonical_fibrePolynomial_eval_extensionAxis
      (K := K) hd P hP)

/-! ## Rank-split terminal assembly -/

/-- Conditional support vanishing with the corrected coefficient fields.

The rank-one branch uses the existing direct ambient conormal theorem over
`k`.  In the successor branch, conormal-axis production chooses `K/k`; symbol
control and that point are then consumed over precisely that `K`.  The theorem
never specializes a `K`-valued point to `k[[t]]`. -/
theorem algebraicallyClosedCanonicalSupportVanishing_of_residueExtension_rankSplit
    (hunit : CanonicalStrictUnitCoordinatePreimage.{u})
    (hcontrol : CanonicalResidueExtensionSymbolControl.{u})
    (hproduction :
      HigherDimensionalCanonicalResidueExtensionConormalAxisProduction.{u}) :
    AlgebraicallyClosedCanonicalSupportVanishing.{u} := by
  intro k _ _ _ n N d hN hd
  let I := canonicalRightIdeal (presentedCoordinate k n) d N
  have hdisjoint : Disjoint
      (orderCharacteristicSupport k I)
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1)))) :=
    canonical_orderCharacteristicSupport_disjoint_coordinate_zeroLocus_of_strictUnit
      k n N (hunit k n N d hN hd)
  by_contra hsupp
  have hnonempty : (orderCharacteristicSupport k I).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hsupp
  cases n with
  | zero =>
      obtain ⟨P, hP, hvanishes⟩ := hcontrol k k 0 N d hN hd
      obtain ⟨y, xi, hgeneric, hresidue⟩ :=
        exists_canonical_rankOne_laurentConormalAxis I hdisjoint hnonempty
      apply false_of_ground_fibreOnly_symbol_one_on_residue_and_vanishing
        (k := k) (K := k) (reducedOrderBaseIdeal k I) P
          (fun _ : Fin 1 ↦ (1 : k)) y xi
      · simpa [groundEquationConormalLocus, groundPolynomialMap,
          groundLaurentMap, scalarPolynomialMap] using hgeneric
      · exact hresidue
      · exact hvanishes
      · have haxis := canonical_fibrePolynomial_eval_extensionAxis
          (K := k) hd P hP
        have hfun : (fun _ : Fin 1 ↦ (1 : k)) =
            (fun i : Fin 1 ↦
              if i = ⟨0, Nat.zero_lt_succ 0⟩ then 1 else 0) := by
          funext i
          fin_cases i
          simp
        rw [hfun]
        exact haxis
  | succ n =>
      obtain ⟨K, fieldK, algebraK, y, xi, hgeneric, hresidue⟩ :=
        hproduction k (n + 1) N d (Nat.zero_lt_succ n)
          hN hd hdisjoint hnonempty
      let : Field K := fieldK
      let : Algebra k K := algebraK
      obtain ⟨P, hP, hvanishes⟩ :=
        hcontrol k K (n + 1) N d hN hd
      exact false_of_ground_fibreOnly_symbol_one_on_residue_and_vanishing
        (k := k) (K := K)
        (reducedOrderBaseIdeal k
          (canonicalRightIdeal (presentedCoordinate k (n + 1)) d N))
        P
        (fun i : Fin ((n + 1) + 1) ↦
          if i = ⟨0, Nat.zero_lt_succ (n + 1)⟩ then 1 else 0)
        y xi hgeneric hresidue hvanishes
        (canonical_fibrePolynomial_eval_extensionAxis
          (K := K) hd P hP)


end

end Stafford38.Geometry.CanonicalResidueExtensionAssembly
