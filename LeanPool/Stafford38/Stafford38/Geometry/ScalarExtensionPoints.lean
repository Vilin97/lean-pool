/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.Nullstellensatz
import LeanPool.Stafford38.Stafford38.Geometry.AffineConormalClosure

/-!
# Scalar extension and geometric points

This file gives the coefficient-extension bridge for the field-valued affine
geometry used by the characteristic-support and conormal arguments.  All
polynomial maps, ideal maps/comaps, and evaluation maps are displayed
explicitly.

For an ideal `J` over `k`, its geometric reduced extension is defined as the
radical of the extended ideal, not as the extension of `J.radical`.  The two
zero loci agree over every extension field.  No assertion that radicals,
closures, or ideal contractions commute with base change is made here.
-/

namespace Stafford38.Geometry.ScalarExtensionPoints

open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Characteristic.BaseZeroSection
open Stafford38.CharacteristicFilteredQuotient
open Stafford38.CharacteristicInitialIdeal
open Stafford38.CharacteristicInitialIdealHomogeneous
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylFiltration

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {σ : Type*} {n : ℕ}

/-- Coefficient extension on a multivariable polynomial ring. -/
def scalarPolynomialMap (σ : Type*) :
    MvPolynomial σ k →+* MvPolynomial σ K :=
  MvPolynomial.map (algebraMap k K)

/-- Coefficient extension is injective for a field extension. -/
theorem scalarPolynomialMap_injective (σ : Type*) :
    Function.Injective (scalarPolynomialMap (k := k) (K := K) σ) :=
  MvPolynomial.map_injective (algebraMap k K)
    (FaithfulSMul.algebraMap_injective k K)

/-- Evaluation of a coefficient-extended polynomial at a `K`-point is
exactly `eval₂` with the structure map on coefficients. -/
theorem eval_scalarPolynomialMap (q : σ → K) (f : MvPolynomial σ k) :
    MvPolynomial.eval q (scalarPolynomialMap (k := k) (K := K) σ f) =
      MvPolynomial.eval₂ (algebraMap k K) q f := by
  exact MvPolynomial.eval_map (algebraMap k K) q f

/-- Exact point semantics of ideal extension: a `K`-point kills the extended
ideal iff it kills the image of every member of the original ideal. -/
theorem mem_zeroLocus_map_iff
    (J : Ideal (MvPolynomial σ k)) (q : σ → K) :
    q ∈ MvPolynomial.zeroLocus K
        (J.map (scalarPolynomialMap (k := k) (K := K) σ)) ↔
      ∀ f ∈ J, MvPolynomial.eval₂ (algebraMap k K) q f = 0 := by
  constructor
  · intro hq f hf
    have h := hq
      (scalarPolynomialMap (k := k) (K := K) σ f)
      (Ideal.mem_map_of_mem
        (scalarPolynomialMap (k := k) (K := K) σ) hf)
    simpa [eval_scalarPolynomialMap] using h
  · intro hq
    rw [Ideal.map, MvPolynomial.zeroLocus_span]
    rintro _ ⟨f, hf, rfl⟩
    simpa [eval_scalarPolynomialMap] using hq f hf

/-- Polynomials over `k` vanishing on a set of `K`-points.  This is the
contraction of the ordinary `K`-valued vanishing ideal. -/
def extensionValuedVanishingIdeal (S : Set (σ → K)) :
    Ideal (MvPolynomial σ k) :=
  (MvPolynomial.vanishingIdeal K S).comap
    (scalarPolynomialMap (k := k) (K := K) σ)

theorem mem_extensionValuedVanishingIdeal_iff
    (S : Set (σ → K)) (f : MvPolynomial σ k) :
    f ∈ extensionValuedVanishingIdeal (k := k) (K := K) S ↔
      ∀ q ∈ S, MvPolynomial.eval₂ (algebraMap k K) q f = 0 := by
  simp [extensionValuedVanishingIdeal, eval_scalarPolynomialMap]

/-- Exact Galois bridge between ideal extension and vanishing on
extension-valued points. -/
theorem subset_zeroLocus_map_iff_le_extensionValuedVanishingIdeal
    (J : Ideal (MvPolynomial σ k)) (S : Set (σ → K)) :
    S ⊆ MvPolynomial.zeroLocus K
        (J.map (scalarPolynomialMap (k := k) (K := K) σ)) ↔
      J ≤ extensionValuedVanishingIdeal (k := k) (K := K) S := by
  constructor
  · intro h f hf
    rw [mem_extensionValuedVanishingIdeal_iff]
    intro q hq
    exact (mem_zeroLocus_map_iff J q).mp (h hq) f hf
  · intro h q hq
    rw [mem_zeroLocus_map_iff]
    intro f hf
    exact (mem_extensionValuedVanishingIdeal_iff S f).mp (h hf) q hq

/-- Taking a radical after scalar extension does not change the set of
`K`-valued zeros.  This does not identify that radical with the extension of
the ground-field radical. -/
theorem zeroLocus_radical (L : Ideal (MvPolynomial σ K)) :
    MvPolynomial.zeroLocus K L.radical = MvPolynomial.zeroLocus K L := by
  apply Set.Subset.antisymm
  · exact MvPolynomial.zeroLocus_anti_mono Ideal.le_radical
  · intro q hq f hf
    exact MvPolynomial.radical_le_vanishingIdeal_zeroLocus L hf q hq

/-- The reduced geometric extension of an ideal.  Reduction is deliberately
performed after coefficient extension. -/
def geometricRadicalExtension (J : Ideal (MvPolynomial σ k)) :
    Ideal (MvPolynomial σ K) :=
  (J.map (scalarPolynomialMap (k := k) (K := K) σ)).radical

/-- Exact geometric-point semantics of the reduced extension. -/
theorem mem_zeroLocus_geometricRadicalExtension_iff
    (J : Ideal (MvPolynomial σ k)) (q : σ → K) :
    q ∈ MvPolynomial.zeroLocus K
        (geometricRadicalExtension (k := k) (K := K) J) ↔
      ∀ f ∈ J, MvPolynomial.eval₂ (algebraMap k K) q f = 0 := by
  rw [geometricRadicalExtension, zeroLocus_radical,
    mem_zeroLocus_map_iff]

/-- Coefficient extension commutes with the explicit embedding of base
coordinates into phase space. -/
theorem scalarPolynomialMap_baseLift (f : MvPolynomial (Fin n) k) :
    scalarPolynomialMap (k := k) (K := K) (PhaseVar n) (baseLift f) =
      baseLift (scalarPolynomialMap (k := k) (K := K) (Fin n) f) := by
  exact MvPolynomial.map_rename (algebraMap k K) Sum.inl f

/-- The always-valid map/comap comparison for the base-coordinate square.
The orientation is important: extension of the old contraction is contained
in the contraction of the extended ideal.  The reverse inclusion would need
the flat Cartesian base-change/intersection theorem for this polynomial
square; no such equality is assumed. -/
theorem map_baseContraction_le_extendedBaseContraction
    (J : Ideal (SymbolRing k n)) :
    (J.comap
        (baseLift : MvPolynomial (Fin n) k →ₐ[k] SymbolRing k n).toRingHom).map
        (scalarPolynomialMap (k := k) (K := K) (Fin n)) ≤
      (J.map (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))).comap
        (baseLift : MvPolynomial (Fin n) K →ₐ[K] SymbolRing K n).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  change baseLift (scalarPolynomialMap (k := k) (K := K) (Fin n) f) ∈
    J.map (scalarPolynomialMap (k := k) (K := K) (PhaseVar n))
  rw [← scalarPolynomialMap_baseLift]
  exact Ideal.mem_map_of_mem
    (scalarPolynomialMap (k := k) (K := K) (PhaseVar n)) hf

/-- The corresponding comparison remains valid when the extended phase
ideal is reduced after base change. -/
theorem map_baseContraction_le_geometricBaseContraction
    (J : Ideal (SymbolRing k n)) :
    (J.comap
        (baseLift : MvPolynomial (Fin n) k →ₐ[k] SymbolRing k n).toRingHom).map
        (scalarPolynomialMap (k := k) (K := K) (Fin n)) ≤
      (geometricRadicalExtension (k := k) (K := K) J).comap
        (baseLift : MvPolynomial (Fin n) K →ₐ[K] SymbolRing K n).toRingHom := by
  exact (map_baseContraction_le_extendedBaseContraction J).trans
    (Ideal.comap_mono Ideal.le_radical)

/-- A phase point of an extended ideal projects to a point of the contraction
of that extended ideal. -/
theorem baseProjection_mem_zeroLocus_comap
    (L : Ideal (SymbolRing K n)) (q : PhaseVar n → K)
    (hq : q ∈ MvPolynomial.zeroLocus K L) :
    (fun i ↦ q (Sum.inl i)) ∈ MvPolynomial.zeroLocus K
      (L.comap
        (baseLift : MvPolynomial (Fin n) K →ₐ[K] SymbolRing K n).toRingHom) := by
  intro f hf
  have h := hq (baseLift f) hf
  change MvPolynomial.eval q (MvPolynomial.rename Sum.inl f) = 0 at h
  rw [MvPolynomial.eval_rename] at h
  exact h

/-- Consequently, a geometric point of the reduced extension projects to a
zero of the scalar extension of the original base contraction.  This is the
strong unconditional one-way base-contraction theorem. -/
theorem geometricSupport_baseProjection_mem_groundContractionZeroLocus
    (J : Ideal (SymbolRing k n)) (q : PhaseVar n → K)
    (hq : q ∈ MvPolynomial.zeroLocus K
      (geometricRadicalExtension (k := k) (K := K) J)) :
    (fun i ↦ q (Sum.inl i)) ∈ MvPolynomial.zeroLocus K
      ((J.comap
          (baseLift : MvPolynomial (Fin n) k →ₐ[k] SymbolRing k n).toRingHom).map
        (scalarPolynomialMap (k := k) (K := K) (Fin n))) := by
  apply MvPolynomial.zeroLocus_anti_mono
    (map_baseContraction_le_geometricBaseContraction J)
  exact baseProjection_mem_zeroLocus_comap
    (geometricRadicalExtension (k := k) (K := K) J) q hq

/-- Exact membership in the equation-defined conormal locus after extending
the equation ideal.  In particular, the base equations are evaluated by the
displayed `eval₂` map; no identification of closures across fields occurs. -/
theorem mem_equationConormalLocus_map_iff
    (I : Ideal (MvPolynomial (Fin n) k)) (q : PhaseVar n → K) :
    q ∈ equationConormalLocus
        (I.map (scalarPolynomialMap (k := k) (K := K) (Fin n))) ↔
      (∀ f ∈ I,
          MvPolynomial.eval₂ (algebraMap k K)
            (fun i ↦ q (Sum.inl i)) f = 0) ∧
        coordinateCovector (fun i ↦ q (Sum.inr i)) ∈
          affineConormalSpace (fun i ↦ q (Sum.inl i))
            (I.map (scalarPolynomialMap (k := k) (K := K) (Fin n))) := by
  rw [equationConormalLocus]
  constructor
  · intro h
    refine ⟨?_, h.2⟩
    exact (mem_zeroLocus_map_iff I (fun i ↦ q (Sum.inl i))).mp h.1
  · intro h
    refine ⟨?_, h.2⟩
    exact (mem_zeroLocus_map_iff I (fun i ↦ q (Sum.inl i))).mpr h.1

/-- Partial derivatives commute with coefficient extension, with the
evaluation map at a geometric point shown explicitly. -/
theorem differentialAt_scalarPolynomialMap
    (y : Fin n → K) (f : MvPolynomial (Fin n) k) (i : Fin n) :
    differentialAt y
        (scalarPolynomialMap (k := k) (K := K) (Fin n) f) i =
      MvPolynomial.eval₂ (algebraMap k K) y
        (MvPolynomial.pderiv i f) := by
  change MvPolynomial.eval y
      (MvPolynomial.pderiv i
        (MvPolynomial.map (algebraMap k K) f)) = _
  rw [MvPolynomial.pderiv_map, MvPolynomial.eval_map]

/-- Once a pointwise conormal containment has been proved over `K`, its
`K`-valued algebraic closure hull remains in the reduced geometric support.
Both closure and reduction are taken after base change. -/
theorem equationConormalClosure_map_subset_geometricRadicalExtension
    (I : Ideal (MvPolynomial (Fin n) k))
    (J : Ideal (SymbolRing k n))
    (h : equationConormalLocus
          (I.map (scalarPolynomialMap (k := k) (K := K) (Fin n))) ⊆
        MvPolynomial.zeroLocus K
          (geometricRadicalExtension (k := k) (K := K) J)) :
    equationConormalClosure
        (I.map (scalarPolynomialMap (k := k) (K := K) (Fin n))) ⊆
      MvPolynomial.zeroLocus K
        (geometricRadicalExtension (k := k) (K := K) J) := by
  exact zeroLocus_vanishingIdeal_mono_of_subset_zeroLocus
    (equationConormalLocus
      (I.map (scalarPolynomialMap (k := k) (K := K) (Fin n))) )
    (geometricRadicalExtension (k := k) (K := K) J) h

/-- The project-facing specialization: geometric reduction of the reduced
order-support ideal.  This is intentionally `radical (map ...)`. -/
def geometricReducedOrderSupportIdeal
    (W : RightIdeal (PresentedWeyl k n)) : Ideal (SymbolRing K n) :=
  geometricRadicalExtension (k := k) (K := K)
    (reducedOrderSupportIdeal k W)

/-- The actual base contraction of the post-base-change reduced support. -/
def geometricReducedOrderBaseIdeal
    (W : RightIdeal (PresentedWeyl k n)) :
    Ideal (MvPolynomial (Fin n) K) :=
  (geometricReducedOrderSupportIdeal (k := k) (K := K) W).comap
    (baseLift : MvPolynomial (Fin n) K →ₐ[K] SymbolRing K n).toRingHom

/-- Geometric points of the reduced order support are exactly the `K`-points
annihilating every ground-field reduced-support equation. -/
theorem mem_zeroLocus_geometricReducedOrderSupportIdeal_iff
    (W : RightIdeal (PresentedWeyl k n)) (q : PhaseVar n → K) :
    q ∈ MvPolynomial.zeroLocus K
        (geometricReducedOrderSupportIdeal (k := k) (K := K) W) ↔
      ∀ f ∈ reducedOrderSupportIdeal k W,
        MvPolynomial.eval₂ (algebraMap k K) q f = 0 := by
  exact mem_zeroLocus_geometricRadicalExtension_iff
    (reducedOrderSupportIdeal k W) q

/-- Fibre-zero specialization commutes with coefficient extension. -/
theorem scalarPolynomialMap_fibreZeroSpecialization
    (P : SymbolRing k n) :
    scalarPolynomialMap (k := k) (K := K) (Fin n)
        (fibreZeroSpecialization k P) =
      fibreZeroSpecialization K
        (scalarPolynomialMap (k := k) (K := K) (PhaseVar n) P) := by
  simp only [fibreZeroSpecialization, scalarPolynomialMap,
    MvPolynomial.map_bind₁]
  congr 1
  ext i
  rcases i with i | i <;> simp

private abbrev orderDecompositionExtension :=
  MvPolynomial.weightedHomogeneousSubmodule k (@orderWeight n)

local instance orderGradedAlgebraExtensionInstance :
    GradedAlgebra (orderDecompositionExtension (k := k) (n := n)) :=
  MvPolynomial.weightedGradedAlgebra k (@orderWeight n)

/-- A geometric zero of the actual contracted reduced support lifts to the
zero section of the actual geometric reduced support.  The proof transports
the ground-field degree-zero component through coefficient extension; it
does not identify the two base contractions. -/
theorem zeroSection_mem_of_mem_geometricReducedOrderBaseZeroSet
    (W : RightIdeal (PresentedWeyl k n)) (y : Fin n → K)
    (hy : ∀ f ∈ geometricReducedOrderBaseIdeal (k := k) (K := K) W,
      MvPolynomial.eval y f = 0) :
    zeroSectionPoint y ∈ MvPolynomial.zeroLocus K
      (geometricReducedOrderSupportIdeal (k := k) (K := K) W) := by
  rw [mem_zeroLocus_geometricReducedOrderSupportIdeal_iff]
  intro P hP
  obtain ⟨m, hm⟩ := (mem_reducedOrderSupportIdeal_iff k W P).mp hP
  let f := fibreZeroSpecialization k (P ^ m)
  have hcomponent :
      (DirectSum.decompose
          (orderDecompositionExtension (k := k) (n := n)) (P ^ m) 0 :
        SymbolRing k n) ∈ orderInitialIdeal k W :=
    coe_mem_orderInitialIdeal_of_mem_orderSymbolRelation k W 0
      (DirectSum.decompose
        (orderDecompositionExtension (k := k) (n := n)) (P ^ m) 0)
      (decompose_mem_orderSymbolRelation_of_mem_orderInitialIdeal
        k W (P ^ m) hm 0)
  have hbaseLift : baseLift f ∈ reducedOrderSupportIdeal k W := by
    rw [← zeroComponent_eq_baseLift_fibreZeroSpecialization]
    exact orderInitialIdeal_le_reducedOrderSupportIdeal k W hcomponent
  have hmapBase :
      scalarPolynomialMap (k := k) (K := K) (Fin n) f ∈
        geometricReducedOrderBaseIdeal (k := k) (K := K) W := by
    change baseLift
        (scalarPolynomialMap (k := k) (K := K) (Fin n) f) ∈
      geometricReducedOrderSupportIdeal (k := k) (K := K) W
    rw [← scalarPolynomialMap_baseLift]
    exact Ideal.le_radical
      (Ideal.mem_map_of_mem
        (scalarPolynomialMap (k := k) (K := K) (PhaseVar n)) hbaseLift)
  have hfy :
      MvPolynomial.eval y
        (scalarPolynomialMap (k := k) (K := K) (Fin n) f) = 0 :=
    hy _ hmapBase
  have heval :
      MvPolynomial.eval (zeroSectionPoint y)
        ((scalarPolynomialMap (k := k) (K := K) (PhaseVar n) P) ^ m) = 0 := by
    rw [← map_pow,
      ← eval_fibreZeroSpecialization K y
        (scalarPolynomialMap (k := k) (K := K) (PhaseVar n) (P ^ m)),
      ← scalarPolynomialMap_fibreZeroSpecialization]
    exact hfy
  have hp0 :
      MvPolynomial.eval (zeroSectionPoint y)
        (scalarPolynomialMap (k := k) (K := K) (PhaseVar n) P) = 0 := by
    exact (pow_eq_zero_iff'.mp (by simpa only [map_pow] using heval)).1
  simpa [eval_scalarPolynomialMap] using hp0

/-- Exact geometric conormal consumer for the scalar-extended reduced order
support.  The sole substantive hypothesis left to the caller is the
base-relative Poisson condition on the post-base-change radical ideal. -/
theorem equationConormalClosure_geometricReducedOrderBase_subset_support
    [CharZero K]
    (W : RightIdeal (PresentedWeyl k n))
    (hJ : IsBaseRelativePoisson
      (geometricReducedOrderSupportIdeal (k := k) (K := K) W)) :
    equationConormalClosure
        (geometricReducedOrderBaseIdeal (k := k) (K := K) W) ⊆
      MvPolynomial.zeroLocus K
        (geometricReducedOrderSupportIdeal (k := k) (K := K) W) := by
  apply zeroLocus_vanishingIdeal_mono_of_subset_zeroLocus
  intro q hq
  let y : Fin n → K := fun i ↦ q (Sum.inl i)
  let ξ : Fin n → K := fun i ↦ q (Sum.inr i)
  have hzero := zeroSection_mem_of_mem_geometricReducedOrderBaseZeroSet
    W y hq.1
  have hpoint := affineConormal_coordinatePoint_isCommonZero
    (geometricReducedOrderSupportIdeal (k := k) (K := K) W) hJ y
    hzero
    (geometricReducedOrderBaseIdeal (k := k) (K := K) W)
    (fun f ↦ f.2) ξ hq.2
  have hsplit : Sum.elim y ξ = q := by
    funext i
    rcases i with i | i <;> rfl
  rw [← hsplit]
  exact hpoint


end

end Stafford38.Geometry.ScalarExtensionPoints
