/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalAxisMonicInitialTop
public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalUnitPreimageFromInitialTop
public import LeanPool.Stafford38.Stafford38.Characteristic.TransposedFilteredModuleSupport


/-!
# The specialized noncharacteristic boundary for the canonical quotient

This file closes all algebraic transport around the coordinate-hyperplane
noncharacteristic step.  For the canonical quotient it proves that ordinary
coordinate multiplication is surjective after right-to-left transposition,
that transposition fixes the coordinate hyperplane in symbol space, and that
the desired support exclusion is equivalent to surjectivity on the actual
associated graded module.

The final implication from ordinary surjectivity and the monic normal symbol
to associated-graded surjectivity is not available in Mathlib: it is the
specialized strict noncharacteristic inverse-image theorem.  No substitute
for that theorem is assumed here.
-/

@[expose] public section

namespace Stafford38.SpecializedNoncharacteristicEquality

open Stafford38.CanonicalAxisMonicInitialTop
open Stafford38.CanonicalUnitPreimageFromInitialTop
open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicInitialIdeal
open Stafford38.CharacteristicTransposedFilteredModuleSupport
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylQuotientTransport
open Stafford38.WeylTransposition
open Stafford38.WeylTranspositionFiltration

noncomputable section

universe u

variable (k : Type u) [Field k]

private abbrev CanonicalIdeal (n N : ℕ)
    (d : PresentedWeyl k (n + 1)) :=
  presentedCanonicalRightIdeal (k := k) n N d

private abbrev AxisCoordinate (n : ℕ) : SymbolRing k (n + 1) :=
  MvPolynomial.X (.inl (0 : Fin (n + 1)))

private abbrev AxisZeroLocus (n : ℕ) :
    Set (PrimeSpectrum (SymbolRing k (n + 1))) :=
  PrimeSpectrum.zeroLocus ({AxisCoordinate k n} :
    Set (SymbolRing k (n + 1)))

/-! ## Ordinary transposed restriction -/

/-- In the transposed left canonical quotient, left multiplication by the
distinguished coordinate is the original right-coordinate action. -/
theorem transposedCanonical_coordinate_smul_eq_rightMul
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (q : TransposedFilteredRightQuotient k (CanonicalIdeal k n N d)) :
    (presentedCoordinate k n • q).toRightQuotient =
      rightMul (CanonicalIdeal k n N d) (presentedCoordinate k n)
        q.toRightQuotient := by
  rcases q with ⟨q⟩
  change rightMul (CanonicalIdeal k n N d)
      (transpose k (n + 1) (presentedCoordinate k n)) q = _
  rw [show presentedCoordinate k n = coordinate k (n + 1) 0 from rfl,
    transpose_coordinate]

/-- PBW monicity already kills ordinary degree-zero restriction of the
transposed left module: coordinate multiplication is onto. -/
theorem transposedCanonical_coordinate_smul_surjective
    [Algebra ℚ k] (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    Function.Surjective
      (fun q : TransposedFilteredRightQuotient k (CanonicalIdeal k n N d) ↦
        presentedCoordinate k n • q) := by
  intro q
  obtain ⟨r, hr⟩ :=
    presentedCanonicalRightQuotient_rightMul_coordinate_surjective
      (k := k) n N hd q.toRightQuotient
  refine ⟨TransposedFilteredRightQuotient.mk r, ?_⟩
  apply (transposedFilteredRightQuotientEquiv k
    (CanonicalIdeal k n N d)).injective
  change (presentedCoordinate k n •
      TransposedFilteredRightQuotient.mk r).toRightQuotient =
    q.toRightQuotient
  rw [transposedCanonical_coordinate_smul_eq_rightMul]
  exact hr

/-! ## Symbol-space invariance -/

theorem symbolTransposition_axisCoordinate (n : ℕ) :
    symbolTransposition k (AxisCoordinate k n) = AxisCoordinate k n := by
  simp [AxisCoordinate]

/-- The induced involution on the prime spectrum is literally involutive. -/
theorem primeComap_symbolTransposition_involutive
    {n : ℕ} (p : PrimeSpectrum (SymbolRing k n)) :
    PrimeSpectrum.comap
        (symbolTranspositionEquiv k).toRingEquiv.toRingHom
        (PrimeSpectrum.comap
          (symbolTranspositionEquiv k).toRingEquiv.toRingHom p) = p := by
  rw [← PrimeSpectrum.comap_comp_apply]
  have hcomp :
      (symbolTranspositionEquiv k).toRingEquiv.toRingHom.comp
          (symbolTranspositionEquiv k).toRingEquiv.toRingHom =
        RingHom.id (SymbolRing k n) := by
    apply RingHom.ext
    intro P
    change symbolTransposition k (symbolTransposition k P) = P
    exact AlgHom.congr_fun (symbolTransposition_comp_self k) P
  rw [hcomp]
  rfl

/-- Momentum-sign substitution fixes the coordinate hyperplane. -/
theorem axisZeroLocus_preimage_symbolTransposition (n : ℕ) :
    PrimeSpectrum.comap
        (symbolTranspositionEquiv k).toRingEquiv.toRingHom ⁻¹'
        AxisZeroLocus k n =
      AxisZeroLocus k n := by
  ext p
  simp only [Set.mem_preimage, AxisZeroLocus,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
  change (symbolTranspositionEquiv k).toRingEquiv.toRingHom
      (AxisCoordinate k n) ∈ p.asIdeal ↔
    AxisCoordinate k n ∈ p.asIdeal
  change symbolTransposition k (AxisCoordinate k n) ∈ p.asIdeal ↔
    AxisCoordinate k n ∈ p.asIdeal
  rw [symbolTransposition_axisCoordinate]

private theorem disjoint_preimage_iff_of_involution_of_invariant
    {X : Type*} (f : X → X) (hf : ∀ x, f (f x) = x)
    (A B : Set X) (hB : f ⁻¹' B = B) :
    Disjoint (f ⁻¹' A) B ↔ Disjoint A B := by
  rw [Set.disjoint_left, Set.disjoint_left]
  constructor
  · intro h x hxA hxB
    have hxpre : f x ∈ f ⁻¹' A := by
      change f (f x) ∈ A
      rwa [hf]
    have hxfb : f x ∈ B := by
      have := Set.ext_iff.mp hB x
      exact this.mpr hxB
    exact h hxpre hxfb
  · intro h x hxpre hxB
    have hfxB : f x ∈ B := by
      have := Set.ext_iff.mp hB x
      exact this.mpr hxB
    exact h hxpre hfxB

/-- Consequently, support exclusion from the coordinate hyperplane is
unchanged by the right-to-left symbol transposition. -/
theorem transposedSupport_disjoint_axis_iff
    (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    Disjoint
        (transposedOrderAssociatedGradedSupport k (CanonicalIdeal k n N d))
        (AxisZeroLocus k n) ↔
      Disjoint
        (Module.support (SymbolRing k (n + 1))
          (OrderAssociatedGradedModule k (CanonicalIdeal k n N d)))
        (AxisZeroLocus k n) := by
  rw [transposedOrderAssociatedGradedSupport_eq_preimage]
  apply disjoint_preimage_iff_of_involution_of_invariant
  · exact primeComap_symbolTransposition_involutive k
  · exact axisZeroLocus_preimage_symbolTransposition k n

/-! ## Exact remaining strictness boundary -/

private theorem disjoint_zeroLocus_singleton_iff_sup_eq_top
    {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
    Disjoint (PrimeSpectrum.zeroLocus I)
        (PrimeSpectrum.zeroLocus ({x} : Set R)) ↔
      I ⊔ Ideal.span {x} = ⊤ := by
  rw [Set.disjoint_iff_inter_eq_empty,
    ← PrimeSpectrum.zeroLocus_span ({x} : Set R),
    ← PrimeSpectrum.zeroLocus_sup,
    PrimeSpectrum.zeroLocus_empty_iff_eq_top]

/-- Since symbol transposition fixes the base coordinate, coordinate
surjectivity on the transposed associated graded module is equivalent to the
same statement on the original associated graded module. -/
theorem transposedGradedCoordinate_surjective_iff
    (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    Function.Surjective
        (fun q : TransposedOrderAssociatedGradedModule k
            (CanonicalIdeal k n N d) ↦ AxisCoordinate k n • q) ↔
      Function.Surjective
        (fun q : OrderAssociatedGradedModule k (CanonicalIdeal k n N d) ↦
          AxisCoordinate k n • q) := by
  constructor
  · intro h q
    obtain ⟨r, hr⟩ := h (TransposedOrderAssociatedGradedModule.mk q)
    refine ⟨r.toOrderAssociatedGradedModule, ?_⟩
    have hr' := congrArg
      TransposedOrderAssociatedGradedModule.toOrderAssociatedGradedModule hr
    simpa only [transposedSymbol_smul, symbolTransposition_axisCoordinate]
      using hr'
  · intro h q
    obtain ⟨r, hr⟩ := h q.toOrderAssociatedGradedModule
    refine ⟨TransposedOrderAssociatedGradedModule.mk r, ?_⟩
    apply (transposedOrderAssociatedGradedEquiv k
      (CanonicalIdeal k n N d)).injective
    change TransposedOrderAssociatedGradedModule.toOrderAssociatedGradedModule
        (AxisCoordinate k n •
          TransposedOrderAssociatedGradedModule.mk r) =
      q.toOrderAssociatedGradedModule
    simpa only [transposedSymbol_smul, symbolTransposition_axisCoordinate]
      using hr

/-- For the canonical quotient, hyperplane support exclusion is exactly
surjectivity of the coordinate on the actual associated graded module. -/
theorem canonicalSupport_disjoint_axis_iff_gradedCoordinate_surjective
     (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    Disjoint
        (Module.support (SymbolRing k (n + 1))
          (OrderAssociatedGradedModule k (CanonicalIdeal k n N d)))
        (AxisZeroLocus k n) ↔
      Function.Surjective
        (fun q : OrderAssociatedGradedModule k (CanonicalIdeal k n N d) ↦
          AxisCoordinate k n • q) := by
  have hsupp :
      Module.support (SymbolRing k (n + 1))
          (OrderAssociatedGradedModule k (CanonicalIdeal k n N d)) =
        PrimeSpectrum.zeroLocus
          (orderInitialIdeal k (CanonicalIdeal k n N d)) := by
    rw [Module.support_eq_zeroLocus,
      annihilator_orderAssociatedGradedModule]
  rw [hsupp]
  exact (disjoint_zeroLocus_singleton_iff_sup_eq_top
    (orderInitialIdeal k (CanonicalIdeal k n N d))
    (AxisCoordinate k n)).trans
      (canonical_orderInitialIdeal_sup_coordinate_eq_top_iff_graded_surjective
        k n N d)

/-- Fully transposed form of the exact boundary.  This is the strongest
specialized equality obtainable from the current local and Mathlib APIs:
the desired support exclusion is equivalent to strict associated-graded
coordinate surjectivity, while ordinary coordinate surjectivity was proved
above from monicity. -/
theorem transposedSupport_disjoint_axis_iff_gradedCoordinate_surjective
     (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    Disjoint
        (transposedOrderAssociatedGradedSupport k (CanonicalIdeal k n N d))
        (AxisZeroLocus k n) ↔
      Function.Surjective
        (fun q : OrderAssociatedGradedModule k (CanonicalIdeal k n N d) ↦
          AxisCoordinate k n • q) := by
  rw [transposedSupport_disjoint_axis_iff]
  exact canonicalSupport_disjoint_axis_iff_gradedCoordinate_surjective
    k n N d

/-- Left-module form consumed directly by the missing specialized
noncharacteristic theorem. -/
theorem transposedSupport_disjoint_axis_iff_transposedGradedCoordinate_surjective
     (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    Disjoint
        (transposedOrderAssociatedGradedSupport k (CanonicalIdeal k n N d))
        (AxisZeroLocus k n) ↔
      Function.Surjective
        (fun q : TransposedOrderAssociatedGradedModule k
            (CanonicalIdeal k n N d) ↦ AxisCoordinate k n • q) :=
  (transposedSupport_disjoint_axis_iff_gradedCoordinate_surjective
    k n N d).trans (transposedGradedCoordinate_surjective_iff k n N d).symm

/-- The project-specific algebraic suffix after the noncharacteristic theorem:
transposed support avoidance produces the canonical order-zero predecessor of
the quotient unit.  No D-module theorem is used in this conversion. -/
theorem strictUnitCoordinatePreimage_of_transposedSupport_disjoint_axis
     (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (havoid : Disjoint
      (transposedOrderAssociatedGradedSupport k (CanonicalIdeal k n N d))
      (AxisZeroLocus k n)) :
    Stafford38.CanonicalUnitCoordinatePreimage.StrictUnitCoordinatePreimage
      k n N d := by
  have horiginal :=
    (transposedSupport_disjoint_axis_iff k n N d).mp havoid
  have hzero : Disjoint
      (PrimeSpectrum.zeroLocus
        (orderInitialIdeal k (CanonicalIdeal k n N d)))
      (AxisZeroLocus k n) := by
    rw [Module.support_eq_zeroLocus,
      annihilator_orderAssociatedGradedModule] at horiginal
    exact horiginal
  have htop : orderInitialIdeal k (CanonicalIdeal k n N d) ⊔
      Ideal.span {AxisCoordinate k n} = ⊤ :=
    (disjoint_zeroLocus_singleton_iff_sup_eq_top
      (orderInitialIdeal k (CanonicalIdeal k n N d))
      (AxisCoordinate k n)).mp hzero
  exact strictUnitCoordinatePreimage_of_orderInitialIdeal_sup_coordinate_eq_top
    k n N htop


end

end Stafford38.SpecializedNoncharacteristicEquality
