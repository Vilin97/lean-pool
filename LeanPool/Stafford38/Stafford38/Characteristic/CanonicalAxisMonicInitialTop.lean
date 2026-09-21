/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.AssociatedGradedFinite
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalUnitPreimageFromInitialTop
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredQuotientReesAction
import LeanPool.Stafford38.Stafford38.Characteristic.HyperplaneRestriction
import LeanPool.Stafford38.Stafford38.Weyl.QuotientTransport

/-!
# The exact Rees--Koszul form of canonical axis cancellation

For the canonical quotient `Q = A / (dA + x^N dA)`, PBW monicity already
makes right multiplication by `x` surjective on `Q`.  This is the vanishing
of ordinary degree-zero restriction.

The requested axis-monic initial-ideal theorem is stronger: it says that the
same one-element Koszul restriction vanishes after passing to the actual
order-associated graded module, equivalently after specialization of the
order-Rees module.  This file proves that equivalence literally.  Thus the
remaining bridge is strict Rees--Koszul base change for this canonical
quotient; ordinary quotient surjectivity is not silently promoted to it.

No D-module theorem, noncharacteristic pullback theorem, or project axiom is
used here.
-/

namespace Stafford38.CanonicalAxisMonicInitialTop

open Stafford38.CanonicalUnitCoordinatePreimage
open Stafford38.CanonicalUnitPreimageFromInitialTop
open Stafford38.Characteristic
open Stafford38.Characteristic.AssociatedGradedFinite
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicFilteredQuotientReesAction
open Stafford38.CharacteristicInitialIdeal
open Stafford38.EulerSurjectivity
open AlgebraicAnalysis.HyperplaneRestriction
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylQuotientTransport

noncomputable section

universe u

variable (k : Type u) [Field k] [Algebra ℚ k]

private abbrev CanonicalIdeal (n N : ℕ)
    (d : PresentedWeyl k (n + 1)) :=
  canonicalRightIdeal (presentedCoordinate k n) d N

/-- The distinguished base-coordinate symbol. -/
private abbrev AxisCoordinate (n : ℕ) : SymbolRing k (n + 1) :=
  MvPolynomial.X (.inl (0 : Fin (n + 1)))

/-- Zeroth Koszul homology of the distinguished coordinate on the actual
order-associated graded canonical quotient.  Through the exact Rees special
fibre constructed elsewhere, this is the specialized Rees restriction. -/
abbrev CanonicalGradedCoordinateKoszulH0 (n N : ℕ)
    (d : PresentedWeyl k (n + 1)) :=
  Restriction
    (R := SymbolRing k (n + 1))
    (M := OrderAssociatedGradedModule k (CanonicalIdeal k n N d))
    (AxisCoordinate k n)

/-- Ordinary zeroth Koszul homology of the coordinate on the canonical
filtered quotient, before Rees specialization. -/
abbrev CanonicalOrdinaryCoordinateKoszulH0 (n N : ℕ)
    (d : PresentedWeyl k (n + 1)) :=
  FilteredRightQuotient k (CanonicalIdeal k n N d) ⧸
    LinearMap.range
      (filteredRightMul k (CanonicalIdeal k n N d)
        (presentedCoordinate k n))

/-- The initial-ideal target is exactly surjectivity of coordinate
multiplication on the actual order-associated graded module.  Cyclicity is
used in both directions, and the annihilator is the literal order initial
ideal. -/
theorem canonical_orderInitialIdeal_sup_coordinate_eq_top_iff_graded_surjective
    (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    orderInitialIdeal k (CanonicalIdeal k n N d) ⊔
          Ideal.span {AxisCoordinate k n} = ⊤ ↔
      Function.Surjective
        (fun q : OrderAssociatedGradedModule k (CanonicalIdeal k n N d) ↦
          AxisCoordinate k n • q) := by
  classical
  let I := CanonicalIdeal k n N d
  let X := AxisCoordinate k n
  let g := orderAssociatedGradedGenerator k I
  constructor
  · intro htop q
    obtain ⟨P, rfl⟩ := exists_smul_orderAssociatedGradedGenerator k I q
    have hone : (1 : SymbolRing k (n + 1)) ∈
        orderInitialIdeal k I ⊔ Ideal.span {X} := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨j, hj, s, hs, hjs⟩ := Submodule.mem_sup.mp hone
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hs
    have hjg : j • g = 0 :=
      (smul_orderAssociatedGradedGenerator_eq_zero_iff k I j).2 hj
    have hsg : s • g = g := by
      calc
        s • g = (j + s) • g := by rw [add_smul, hjg, zero_add]
        _ = 1 • g := congrArg (fun r : SymbolRing k (n + 1) => r • g) hjs
        _ = g := one_smul _ _
    refine ⟨(P * a) • g, ?_⟩
    calc
      X • ((P * a) • g) = (X * (P * a)) • g := by rw [smul_smul]
      _ = (P * s) • g := by rw [ha]; ring
      _ = P • (s • g) := by rw [smul_smul]
      _ = P • g := by rw [hsg]
  · intro hsurj
    obtain ⟨q, hq⟩ := hsurj
      (orderAssociatedGradedGenerator k I)
    obtain ⟨P, hP⟩ := exists_smul_orderAssociatedGradedGenerator k I q
    have hq' : X • (P • orderAssociatedGradedGenerator k I) =
        orderAssociatedGradedGenerator k I := by
      rw [hP]
      simpa [X, I] using hq
    have hkill : (X * P - 1) • orderAssociatedGradedGenerator k I = 0 := by
      rw [sub_smul, mul_smul, hq', one_smul, sub_self]
    have hrel : X * P - 1 ∈ orderInitialIdeal k I :=
      (smul_orderAssociatedGradedGenerator_eq_zero_iff k I (X * P - 1)).1
        hkill
    apply (Ideal.eq_top_iff_one _).2
    rw [show (1 : SymbolRing k (n + 1)) = -(X * P - 1) + X * P by ring]
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left ((orderInitialIdeal k I).neg_mem hrel)
    · apply Submodule.mem_sup_right
      exact (Ideal.span {X}).mul_mem_right P
        (Ideal.subset_span (Set.mem_singleton X))

/-- Exact Koszul formulation of the requested theorem: the initial ideal and
the coordinate generate one iff the specialized one-coordinate Koszul
`H₀` is zero. -/
theorem canonical_orderInitialIdeal_sup_coordinate_eq_top_iff_koszulH0_subsingleton
    (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    orderInitialIdeal k (CanonicalIdeal k n N d) ⊔
          Ideal.span {AxisCoordinate k n} = ⊤ ↔
      Subsingleton (CanonicalGradedCoordinateKoszulH0 k n N d) := by
  rw [canonical_orderInitialIdeal_sup_coordinate_eq_top_iff_graded_surjective]
  exact (restriction_subsingleton_iff_smul_surjective
    (R := SymbolRing k (n + 1))
    (M := OrderAssociatedGradedModule k (CanonicalIdeal k n N d))
    (x := AxisCoordinate k n)).symm

/-- Monicity already kills ordinary coordinate restriction on the literal
canonical right quotient.  This is the source side of the still-missing
strict Rees--Koszul base-change theorem. -/
theorem canonical_ordinary_coordinate_surjective_of_axisMonic
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    Function.Surjective
      (rightMul (CanonicalIdeal k n N d) (presentedCoordinate k n)) :=
  presentedCanonicalRightQuotient_rightMul_coordinate_surjective n N hd

/-- The filtered additive model and the literal regular-right-module quotient
intertwine their written right coordinate actions. -/
theorem filteredRightQuotientEquivRightQuotient_coordinate
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (q : FilteredRightQuotient k (CanonicalIdeal k n N d)) :
    filteredRightQuotientEquivRightQuotient k (CanonicalIdeal k n N d)
        (filteredRightMul k (CanonicalIdeal k n N d)
          (presentedCoordinate k n) q) =
      rightMul (CanonicalIdeal k n N d) (presentedCoordinate k n)
        (filteredRightQuotientEquivRightQuotient k
          (CanonicalIdeal k n N d) q) := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro z
  rfl

/-- PBW monicity makes the ordinary one-coordinate Koszul `H₀` literally
zero.  The requested initial-top theorem is the assertion that this remains
true after passing to the order-Rees special fibre. -/
theorem canonical_ordinary_coordinateKoszulH0_subsingleton_of_axisMonic
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    Subsingleton (CanonicalOrdinaryCoordinateKoszulH0 k n N d) := by
  rw [Submodule.Quotient.subsingleton_iff]
  apply top_unique
  intro q hq
  let e := filteredRightQuotientEquivRightQuotient k
    (CanonicalIdeal k n N d)
  obtain ⟨r, hr⟩ :=
    canonical_ordinary_coordinate_surjective_of_axisMonic k n N hd (e q)
  refine ⟨e.symm r, ?_⟩
  apply e.injective
  rw [filteredRightQuotientEquivRightQuotient_coordinate]
  simpa [e] using hr

/-- The initial-top statement and the existing strict unit predecessor are
equivalent for the literal canonical quotient. -/
theorem canonical_orderInitialIdeal_sup_coordinate_eq_top_iff_strictUnit
    (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    orderInitialIdeal k (CanonicalIdeal k n N d) ⊔
          Ideal.span {AxisCoordinate k n} = ⊤ ↔
      StrictUnitCoordinatePreimage k n N d := by
  constructor
  · exact fun h ↦
      strictUnitCoordinatePreimage_of_orderInitialIdeal_sup_coordinate_eq_top
        k n N h
  · exact fun h ↦
      canonical_orderInitialIdeal_sup_coordinate_eq_top_of_strictUnit
        k n N h


end

end Stafford38.CanonicalAxisMonicInitialTop
