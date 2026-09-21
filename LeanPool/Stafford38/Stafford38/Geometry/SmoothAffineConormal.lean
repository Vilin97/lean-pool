/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.ConormalPrincipalOpenDensity
import LeanPool.Stafford38.Stafford38.Geometry.GenericSmoothOpen

/-!
# Density of the conormal over the smooth affine locus

For a prime affine variety over an algebraically closed field, its genuine
Mathlib smooth points contain a nonempty principal open.  Consequently the
equation conormal over those smooth points has the same algebraic closure as
the full equation conormal.
-/

namespace Stafford38.Geometry.SmoothAffineConormal

open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.ConormalPrincipalOpenDensity

noncomputable section

variable {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}

def SmoothAffinePoint (I : Ideal (MvPolynomial (Fin n) k))
    (y : Fin n → k) : Prop :=
  ∃ e : (MvPolynomial (Fin n) k ⧸ I) →ₐ[k] k,
    (∀ p, e (Ideal.Quotient.mk I p) = MvPolynomial.aeval y p) ∧
    let hprime : (RingHom.ker e.toRingHom).IsPrime := RingHom.ker_isPrime e
    (⟨RingHom.ker e.toRingHom, hprime⟩ :
      PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I)) ∈
      Algebra.smoothLocus k (MvPolynomial (Fin n) k ⧸ I)

theorem smoothAffinePoint_mem_zeroLocus
    (I : Ideal (MvPolynomial (Fin n) k)) :
    {y | SmoothAffinePoint I y} ⊆ MvPolynomial.zeroLocus k I := by
  intro y hy p hp
  obtain ⟨e, heval, _⟩ := hy
  have hmk : Ideal.Quotient.mk I p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hp
  rw [← heval p, hmk, map_zero]

theorem equationConormalClosure_smoothAffine_eq
    (I : Ideal (MvPolynomial (Fin n) k)) (hI : I.IsPrime) :
    MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k
          (restrictedEquationConormalLocus I {y | SmoothAffinePoint I y})) =
      equationConormalClosure I := by
  letI : I.IsPrime := hI
  letI : Algebra.FinitePresentation k (MvPolynomial (Fin n) k ⧸ I) :=
    Algebra.FinitePresentation.quotient I.fg_of_isNoetherianRing
  obtain ⟨fbar, hfbar, hsmooth⟩ := exists_nonzero_smooth_away_quotient I
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective fbar
  have hf : f ∉ I := by
    intro h
    exact hfbar (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  apply equationConormalClosure_restricted_eq I hI f hf
    {y | SmoothAffinePoint I y}
    (smoothAffinePoint_mem_zeroLocus I)
  intro y hyI hyf
  let e : (MvPolynomial (Fin n) k ⧸ I) →ₐ[k] k :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval y) (by
      intro p hp
      exact hyI p hp)
  refine ⟨e, ?_, ?_⟩
  · intro p
    simp [e]
  · have hopen : (⟨RingHom.ker e.toRingHom, RingHom.ker_isPrime e⟩ :
        PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I)) ∈
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk I f) := by
      rw [PrimeSpectrum.mem_basicOpen]
      intro hker
      have hezero : e (Ideal.Quotient.mk I f) = 0 := hker
      simp [e] at hezero
      exact hyf hezero
    exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hsmooth) hopen


end
end Stafford38.Geometry.SmoothAffineConormal
