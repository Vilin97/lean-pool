/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.FibreConicalVanishingIdeal
import LeanPool.Stafford38.Stafford38.Geometry.GeneralCoisotropicExclusion

/-!
# Coisotropic sets and their vanishing ideals

Closed affine sets are represented as common zero loci of polynomial ideals.
The vanishing ideal is radical, and its base contraction describes the base
projection of a closed fibre-conical set.
-/

namespace Stafford38.Geometry.GeneralCoisotropicSets

open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.ConormalPrincipalOpenDensity
open Stafford38.Geometry.GeneralConormalContainment
open Stafford38.Geometry.GeneralComponentConormalContainment
open Stafford38.Geometry.GeneralCoisotropicExclusion
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.SmoothAffineConormal

noncomputable section

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}

omit [IsAlgClosed k] [CharZero k] in
theorem vanishingIdeal_isRadical (W : Set (PhaseVar n → k)) :
    (MvPolynomial.vanishingIdeal k W).IsRadical := by
  intro p hp
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hp
  intro q hq
  have h := hm q hq
  simpa only [map_pow] using eq_zero_of_pow_eq_zero
    (show (MvPolynomial.aeval q p) ^ m = 0 by simpa only [map_pow] using h)

omit [IsAlgClosed k] [CharZero k] in
theorem zeroLocus_vanishingIdeal_of_algebraic_closed
    (W : Set (PhaseVar n → k))
    (hclosed : ∃ L : Ideal (SymbolRing k n), W = MvPolynomial.zeroLocus k L) :
    MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k W) = W := by
  obtain ⟨L, rfl⟩ := hclosed
  apply Set.Subset.antisymm
  · exact MvPolynomial.zeroLocus_anti_mono (MvPolynomial.le_vanishingIdeal_zeroLocus L)
  · exact MvPolynomial.zeroLocus_vanishingIdeal_le _

omit [IsAlgClosed k] [CharZero k] in
theorem baseProjection_eq_zeroLocus_comap
    (W : Set (PhaseVar n → k))
    (hclosed : ∃ L : Ideal (SymbolRing k n), W = MvPolynomial.zeroLocus k L)
    (hhom : (MvPolynomial.vanishingIdeal k W).IsHomogeneous
      (orderDecomposition (k := k) (n := n))) :
    {y : Fin n → k | ∃ ξ : Fin n → k, Sum.elim y ξ ∈ W} =
      MvPolynomial.zeroLocus k ((MvPolynomial.vanishingIdeal k W).comap baseLift) := by
  ext y
  constructor
  · rintro ⟨ξ, hξ⟩ f hf
    have h := hf (Sum.elim y ξ) hξ
    simpa [baseLift, MvPolynomial.eval_rename, Function.comp_def] using h
  · intro hy
    refine ⟨0, ?_⟩
    rw [← zeroLocus_vanishingIdeal_of_algebraic_closed W hclosed]
    have hzero := zeroSection_commonZero_of_isHomogeneous
      (MvPolynomial.vanishingIdeal k W) hhom y hy
    have hpoint : Sum.elim y (fun _ : Fin n => (0 : k)) = zeroSectionPoint y := by
      funext i
      rcases i with i | i <;> rfl
    change Sum.elim y (fun _ : Fin n => (0 : k)) ∈
      MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k W)
    rw [hpoint]
    exact hzero

/-- For every minimal component of the base projection, the closure of its
smooth conormal bundle lies in the original closed fibre-conical coisotropic
set.  This is the set-level form of the component containment used in the
manuscript. -/
theorem smoothConormalClosure_minimalPrime_subset_of_isFibreConical
    (W : Set (PhaseVar n → k))
    (hclosed : ∃ L : Ideal (SymbolRing k n),
      W = MvPolynomial.zeroLocus k L)
    (hW : FibreConicalVanishingIdeal.IsFibreConical W)
    (hpoisson : ∀ f ∈ MvPolynomial.vanishingIdeal k W,
      ∀ g ∈ MvPolynomial.vanishingIdeal k W,
        poissonBracket f g ∈ MvPolynomial.vanishingIdeal k W)
    (P : Ideal (MvPolynomial (Fin n) k))
    (hP : P ∈ ((MvPolynomial.vanishingIdeal k W).comap baseLift).minimalPrimes) :
    MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (restrictedEquationConormalLocus P {y | SmoothAffinePoint P y})) ⊆ W := by
  let J : Ideal (SymbolRing k n) := MvPolynomial.vanishingIdeal k W
  have hrad : J.IsRadical := by
    simpa only [J] using vanishingIdeal_isRadical W
  have hhom : J.IsHomogeneous (orderDecomposition (k := k) (n := n)) := by
    simpa only [J] using
      FibreConicalVanishingIdeal.vanishingIdeal_isHomogeneous_of_isFibreConical W hW
  have hbasePoisson : IsBaseRelativePoisson J := by
    intro f hf g hg
    exact hpoisson (baseLift f) hf g hg
  rw [← zeroLocus_vanishingIdeal_of_algebraic_closed W hclosed]
  exact smoothConormalClosure_minimalPrime_subset_zeroLocus
    J hrad hhom hbasePoisson P hP

/-- A nonempty closed fibre-conical coisotropic set cannot avoid the distinguished
base-coordinate hyperplane while lying in a fibre polynomial hypersurface
transverse to the distinguished axis.

The ideal used by the argument is the actual vanishing ideal of `W`; its
radicality is automatic, fibre homogeneity is derived from `hW`, and
coisotropy means the exact self-involutivity condition `{I(W), I(W)} ⊆ I(W)`. -/
theorem exists_zero_base_coordinate_of_isFibreConical
    {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (W : Set (PhaseVar m → k))
    (hnonempty : W.Nonempty)
    (hclosed : ∃ L : Ideal (SymbolRing k m),
      W = MvPolynomial.zeroLocus k L)
    (hW : FibreConicalVanishingIdeal.IsFibreConical W)
    (hpoisson : ∀ f ∈ MvPolynomial.vanishingIdeal k W,
      ∀ g ∈ MvPolynomial.vanishingIdeal k W,
        poissonBracket f g ∈ MvPolynomial.vanishingIdeal k W)
    (P : MvPolynomial (Fin m) k)
    (hP : fibreLift P ∈ MvPolynomial.vanishingIdeal k W)
    (haxis : MvPolynomial.eval
      (fun i : Fin m => if i = ⟨0, hm⟩ then (1 : k) else 0) P ≠ 0) :
    ∃ q ∈ W, q (.inl ⟨0, hm⟩) = 0 := by
  let J : Ideal (SymbolRing k m) := MvPolynomial.vanishingIdeal k W
  have hproper : J ≠ ⊤ := by
    intro htop
    obtain ⟨q, hq⟩ := hnonempty
    have hqzero : q ∈ MvPolynomial.zeroLocus k J := by
      exact MvPolynomial.zeroLocus_vanishingIdeal_le W hq
    rw [htop] at hqzero
    simp at hqzero
  have hrad : J.IsRadical := by
    simpa only [J] using vanishingIdeal_isRadical W
  have hhom : J.IsHomogeneous (orderDecomposition (k := k) (n := m)) := by
    simpa only [J] using
      FibreConicalVanishingIdeal.vanishingIdeal_isHomogeneous_of_isFibreConical W hW
  have hbasePoisson : IsBaseRelativePoisson J := by
    intro f hf g hg
    exact hpoisson (baseLift f) hf g hg
  obtain ⟨q, hq, hqcoord⟩ := exists_zero_base_coordinate hm J hproper hrad hhom
    hbasePoisson P hP haxis
  refine ⟨q, ?_, hqcoord⟩
  rw [← zeroLocus_vanishingIdeal_of_algebraic_closed W hclosed]
  exact hq


end
end Stafford38.Geometry.GeneralCoisotropicSets
