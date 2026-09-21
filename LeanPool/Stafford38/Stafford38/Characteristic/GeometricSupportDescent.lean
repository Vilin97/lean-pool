/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.MvPolynomial
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import LeanPool.Stafford38.Stafford38.Geometry.ScalarExtensionPoints

/-!
# Geometric points and support after algebraic closure

For finitely many polynomial variables over an arbitrary field, a proper
ideal has a common zero in the algebraic closure.  This file records the
result with the coefficient map and its map/comap consequences explicit.

The proof chooses a maximal ideal above the given ideal, uses Zariski's lemma
to make its residue field algebraic over the ground field, and embeds that
residue field into the algebraic closure.  It does not use characteristic
varieties, Gabber's theorem, or asymptotic geometry.
-/

namespace Stafford38.Characteristic.GeometricSupportDescent

open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Characteristic
open Stafford38.CharacteristicInitialIdeal
open Stafford38.WeylIteratedEquivalence
open Stafford38.EulerSurjectivity

noncomputable section

variable {k : Type*} [Field k]
variable {σ : Type*} [Finite σ]

/-- A proper ideal in a finite-variable polynomial ring has a common zero in
the algebraic closure of the coefficient field. -/
theorem exists_algebraicClosure_zero_of_ne_top
    (J : Ideal (MvPolynomial σ k)) (hJ : J ≠ ⊤) :
    ∃ q : σ → AlgebraicClosure k,
      q ∈ MvPolynomial.zeroLocus (AlgebraicClosure k)
        (J.map (scalarPolynomialMap
          (k := k) (K := AlgebraicClosure k) σ)) := by
  obtain ⟨M, hMmax, hJM⟩ := Ideal.exists_le_maximal J hJ
  let : M.IsMaximal := hMmax
  let Q := MvPolynomial σ k ⧸ M
  let : Field Q := Ideal.Quotient.field M
  let : Module.IsTorsionFree k Q :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (MvPolynomial.quotient_mk_comp_C_injective σ k M hMmax.ne_top)
  have hIntegral :
      RingHom.IsIntegral
        ((Ideal.Quotient.mk M).comp (MvPolynomial.C : k →+* MvPolynomial σ k)) :=
    MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing
      (Ideal.Quotient.mk M) Ideal.Quotient.mk_surjective
  let : Algebra.IsIntegral k Q := ⟨hIntegral⟩
  let : Algebra.IsAlgebraic k Q := Algebra.IsIntegral.isAlgebraic
  let φ : Q →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let q : σ → AlgebraicClosure k := fun i => φ (Ideal.Quotient.mk M (MvPolynomial.X i))
  refine ⟨q, (mem_zeroLocus_map_iff J q).2 ?_⟩
  intro f hf
  let ψ : MvPolynomial σ k →+* AlgebraicClosure k :=
    φ.toRingHom.comp (Ideal.Quotient.mk M)
  have hψ : ψ f = 0 := by
    change φ (Ideal.Quotient.mk M f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hJM hf), map_zero]
  have hcoeff : ψ.comp MvPolynomial.C =
      algebraMap k (AlgebraicClosure k) := by
    ext a
    change φ (Ideal.Quotient.mk M (MvPolynomial.C a)) =
      algebraMap k (AlgebraicClosure k) a
    rw [show Ideal.Quotient.mk M (MvPolynomial.C a) = algebraMap k Q a from rfl]
    exact φ.commutes a
  rw [MvPolynomial.map_mvPolynomial_eq_eval₂ ψ] at hψ
  rw [hcoeff] at hψ
  simpa [ψ, q] using hψ

/-- Over the algebraic closure, geometric emptiness is exactly the unit-ideal
condition on the original ground-field ideal. -/
theorem algebraicClosure_zeroLocus_eq_empty_iff
    (J : Ideal (MvPolynomial σ k)) :
    MvPolynomial.zeroLocus (AlgebraicClosure k)
        (J.map (scalarPolynomialMap
          (k := k) (K := AlgebraicClosure k) σ)) = ∅ ↔
      J = ⊤ := by
  constructor
  · intro hzero
    by_contra hJ
    obtain ⟨q, hq⟩ := exists_algebraicClosure_zero_of_ne_top J hJ
    rw [hzero] at hq
    exact hq
  · rintro rfl
    change MvPolynomial.zeroLocus (AlgebraicClosure k)
      ((⊤ : Ideal (MvPolynomial σ k)).map
        (scalarPolynomialMap
          (k := k) (K := AlgebraicClosure k) σ)) =
        (⊥ : Set (σ → AlgebraicClosure k))
    rw [Ideal.map_top, MvPolynomial.zeroLocus_top]

/-- Scalar extension to the algebraic closure reflects and preserves the
unit ideal for finite-variable polynomial rings. -/
theorem map_scalarPolynomialMap_eq_top_iff
    (J : Ideal (MvPolynomial σ k)) :
    J.map (scalarPolynomialMap
        (k := k) (K := AlgebraicClosure k) σ) = ⊤ ↔
      J = ⊤ := by
  constructor
  · intro hmap
    apply (algebraicClosure_zeroLocus_eq_empty_iff J).mp
    rw [hmap]
    exact MvPolynomial.zeroLocus_top
  · rintro rfl
    exact Ideal.map_top _

/-- A nonempty ground-field prime-spectrum zero locus yields a geometric
point after passing to the algebraic closure. -/
theorem exists_algebraicClosure_zero_of_mem_primeZeroLocus
    (J : Ideal (MvPolynomial σ k))
    (p : PrimeSpectrum (MvPolynomial σ k))
    (hp : p ∈ PrimeSpectrum.zeroLocus (J : Set (MvPolynomial σ k))) :
    ∃ q : σ → AlgebraicClosure k,
      q ∈ MvPolynomial.zeroLocus (AlgebraicClosure k)
        (J.map (scalarPolynomialMap
          (k := k) (K := AlgebraicClosure k) σ)) := by
  apply exists_algebraicClosure_zero_of_ne_top J
  intro hJ
  subst J
  exact p.2.ne_top (by simpa using hp)

/-- A geometric point gives a prime of the original polynomial ring by
contracting its evaluation kernel.  The displayed equality records the exact
map/comap orientation. -/
def groundPrimeOfAlgebraicClosurePoint (q : σ → AlgebraicClosure k) :
    PrimeSpectrum (MvPolynomial σ k) :=
  PrimeSpectrum.comap (scalarPolynomialMap
    (k := k) (K := AlgebraicClosure k) σ)
    (MvPolynomial.pointToPoint q)

theorem groundPrimeOfAlgebraicClosurePoint_asIdeal
    (q : σ → AlgebraicClosure k) :
    (groundPrimeOfAlgebraicClosurePoint (k := k) q).asIdeal =
      (MvPolynomial.vanishingIdeal (AlgebraicClosure k) {q}).comap
        (scalarPolynomialMap
          (k := k) (K := AlgebraicClosure k) σ) :=
  rfl

/-- Conversely, a geometric zero of the extended ideal contracts to a prime
of the ground polynomial ring containing the original ideal. -/
theorem groundPrimeOfAlgebraicClosurePoint_mem_zeroLocus
    (J : Ideal (MvPolynomial σ k)) (q : σ → AlgebraicClosure k)
    (hq : q ∈ MvPolynomial.zeroLocus (AlgebraicClosure k)
      (J.map (scalarPolynomialMap
        (k := k) (K := AlgebraicClosure k) σ))) :
    groundPrimeOfAlgebraicClosurePoint (k := k) q ∈
      PrimeSpectrum.zeroLocus (J : Set (MvPolynomial σ k)) := by
  rw [PrimeSpectrum.mem_zeroLocus]
  intro f hf
  change scalarPolynomialMap
      (k := k) (K := AlgebraicClosure k) σ f ∈
    MvPolynomial.vanishingIdeal (AlgebraicClosure k) {q}
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
  exact hq _ (Ideal.mem_map_of_mem _ hf)

/-- Thus nonemptiness of the prime-spectrum support and nonemptiness of the
algebraic-closure geometric zero locus are equivalent. -/
theorem primeZeroLocus_nonempty_iff_algebraicClosure_zeroLocus_nonempty
    (J : Ideal (MvPolynomial σ k)) :
    Set.Nonempty (PrimeSpectrum.zeroLocus (J : Set (MvPolynomial σ k))) ↔
      Set.Nonempty (MvPolynomial.zeroLocus (AlgebraicClosure k)
        (J.map (scalarPolynomialMap
          (k := k) (K := AlgebraicClosure k) σ))) := by
  constructor
  · rintro ⟨p, hp⟩
    exact exists_algebraicClosure_zero_of_mem_primeZeroLocus J p hp
  · rintro ⟨q, hq⟩
    exact ⟨groundPrimeOfAlgebraicClosurePoint (k := k) q,
      groundPrimeOfAlgebraicClosurePoint_mem_zeroLocus J q hq⟩

/-- Project-facing form: a proper order initial ideal has a geometric point
after coefficient extension to the algebraic closure. -/
theorem exists_algebraicClosure_orderInitialZero_of_ne_top
    {n : ℕ} (I : RightIdeal (PresentedWeyl k n))
    (hI : orderInitialIdeal k I ≠ ⊤) :
    ∃ q : PhaseVar n → AlgebraicClosure k,
      q ∈ MvPolynomial.zeroLocus (AlgebraicClosure k)
        ((orderInitialIdeal k I).map
          (scalarPolynomialMap
            (k := k) (K := AlgebraicClosure k) (PhaseVar n))) :=
  exists_algebraicClosure_zero_of_ne_top (orderInitialIdeal k I) hI

/-- The literal prime-spectrum order support is nonempty exactly when the
extended order initial ideal has an algebraic-closure-valued point. -/
theorem orderCharacteristicSupport_nonempty_iff_geometric_nonempty
    {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) :
    Set.Nonempty (orderCharacteristicSupport k I) ↔
      Set.Nonempty (MvPolynomial.zeroLocus (AlgebraicClosure k)
        ((orderInitialIdeal k I).map
          (scalarPolynomialMap
            (k := k) (K := AlgebraicClosure k) (PhaseVar n)))) := by
  rw [orderCharacteristicSupport_eq_zeroLocus]
  exact primeZeroLocus_nonempty_iff_algebraicClosure_zeroLocus_nonempty
    (orderInitialIdeal k I)

/-- Geometric emptiness over the algebraic closure descends all the way to
the unit order initial ideal and hence to empty prime-spectrum support. -/
theorem geometric_orderInitialZeroLocus_empty_iff_support_empty
    {n : ℕ} (I : RightIdeal (PresentedWeyl k n)) :
    MvPolynomial.zeroLocus (AlgebraicClosure k)
        ((orderInitialIdeal k I).map
          (scalarPolynomialMap
            (k := k) (K := AlgebraicClosure k) (PhaseVar n))) = ∅ ↔
      orderCharacteristicSupport k I = ∅ := by
  rw [algebraicClosure_zeroLocus_eq_empty_iff,
    orderCharacteristicSupport_eq_empty_iff]


end

end Stafford38.Characteristic.GeometricSupportDescent
