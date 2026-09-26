/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import LeanPool.Stafford38.Stafford38.Geometry.SmoothAffineConormal


/-!
# Projective conormal directions

Only the polynomial criterion is recorded here.  This file does not identify
an asymptotic conormal variety with a projective closure.
-/

@[expose] public section

namespace Stafford38.Geometry.ProjectiveConormalDirections

open scoped LinearAlgebra.Projectivization
open Stafford38.Characteristic
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.SmoothAffineConormal

noncomputable section

variable {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}

/-- Projective points whose every nonzero representative annihilates a given polynomial. -/
def projectiveHomogeneousZeroLocus (P : MvPolynomial (Fin n) k) :
    Set (Projectivization k (Fin n → k)) :=
  {z | ∀ v : Fin n → k, ∀ hv : v ≠ 0,
    z = Projectivization.mk k v hv → MvPolynomial.eval v P = 0}

/-- The intersection of all homogeneous polynomial zero loci containing a projective set. -/
def projectiveHomogeneousClosure
    (T : Set (Projectivization k (Fin n → k))) :
    Set (Projectivization k (Fin n → k)) :=
  {z | ∀ P : MvPolynomial (Fin n) k, ∀ d : ℕ,
    P.IsHomogeneous d →
    T ⊆ projectiveHomogeneousZeroLocus P →
      z ∈ projectiveHomogeneousZeroLocus P}

/-- Nonzero covectors conormal to at least one smooth affine point of the ideal. -/
def smoothConormalDirectionSet
    (I : Ideal (MvPolynomial (Fin n) k)) :
    Set (Fin n → k) :=
  {ξ | ∃ y : Fin n → k,
    SmoothAffinePoint I y ∧ ξ ≠ 0 ∧
      coordinateCovector ξ ∈ affineConormalSpace y I}

/-- Covectors conormal to smooth affine points, including the zero covector. -/
def smoothConormalFibreProjection
    (I : Ideal (MvPolynomial (Fin n) k)) : Set (Fin n → k) :=
  {ξ | ∃ y : Fin n → k,
    SmoothAffinePoint I y ∧
      coordinateCovector ξ ∈ affineConormalSpace y I}

/-- The projective classes represented by nonzero vectors in a given set. -/
def projectivizedDirectionSet (T : Set (Fin n → k)) :
    Set (Projectivization k (Fin n → k)) :=
  {z | ∃ v, v ∈ T ∧ ∃ hv : v ≠ 0, z = Projectivization.mk k v hv}

omit [IsAlgClosed k] in
private theorem eval_smul_of_isHomogeneous
    (P : MvPolynomial (Fin n) k) (d : ℕ) (hP : P.IsHomogeneous d)
    (a : k) (v : Fin n → k) :
    MvPolynomial.eval (a • v) P = a ^ d * MvPolynomial.eval v P := by
  simp only [MvPolynomial.eval_eq']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hd : ∑ i, s i = d := by
    rw [← s.sum_fintype (fun _ c => c) (fun _ => rfl)]
    simpa [MvPolynomial.IsHomogeneous, Finsupp.weight_apply] using
      hP (MvPolynomial.mem_support_iff.mp hs)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hd]
  ring

omit [IsAlgClosed k] in
theorem mk_mem_projectiveHomogeneousClosure_of_fibre_zeroLocus
    (I : Ideal (MvPolynomial (Fin n) k)) (ξ : Fin n → k) (hξ : ξ ≠ 0)
    (hvan : ξ ∈ MvPolynomial.zeroLocus k
      (MvPolynomial.vanishingIdeal k (smoothConormalFibreProjection I))) :
    Projectivization.mk k ξ hξ ∈
      projectiveHomogeneousClosure
        (projectivizedDirectionSet (smoothConormalDirectionSet I)) := by
  intro P d hP hT
  obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by
    simpa [funext_iff] using hξ
  have hXPvan : MvPolynomial.X i * P ∈ MvPolynomial.vanishingIdeal k
      (smoothConormalFibreProjection I) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro v hv
    by_cases hv0 : v = 0
    · subst v
      simp
    · have hproj : Projectivization.mk k v hv0 ∈
          projectivizedDirectionSet (smoothConormalDirectionSet I) := by
        rcases hv with ⟨y, hy, hc⟩
        exact ⟨v, ⟨y, hy, hv0, hc⟩, hv0, rfl⟩
      change MvPolynomial.eval v (MvPolynomial.X i * P) = 0
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      rw [hT hproj v hv0 rfl, mul_zero]
  intro v hv hz
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff k ξ v hξ hv).mp hz
  have hξXP : MvPolynomial.eval ξ (MvPolynomial.X i * P) = 0 :=
    (MvPolynomial.mem_zeroLocus_iff.mp hvan) _ hXPvan
  have hξP : MvPolynomial.eval ξ P = 0 := by
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X] at hξXP
    exact (mul_eq_zero.mp hξXP).resolve_left hi
  have hscaled := eval_smul_of_isHomogeneous P d hP (a : k) v
  have ha' : (a : k) • v = ξ := by
    rw [← Units.smul_def]
    exact ha
  rw [ha', hξP] at hscaled
  exact (mul_eq_zero.mp hscaled.symm).resolve_left
    (pow_ne_zero d (Units.ne_zero a))

end

end Stafford38.Geometry.ProjectiveConormalDirections
