/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.Nullstellensatz
import LeanPool.Stafford38.Stafford38.Geometry.AffineConormalClosure

/-!
# Density of the equation conormal over a principal open

The first lemma is the algebraic Nullstellensatz/primality core used by the
principal-open density argument.  The conormal-specific graph construction is
kept as a separate theorem below, so its hypotheses and its use of the
equation-defined conormal are visible at the call site.
-/

namespace Stafford38.Geometry.ConormalPrincipalOpenDensity

open Stafford38.Characteristic
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation

noncomputable section

variable {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}

theorem mem_of_vanishes_on_principal_open
    (I : Ideal (MvPolynomial (Fin n) k)) (hI : I.IsPrime)
    {f p : MvPolynomial (Fin n) k} (hf : f ∉ I)
    (hp : ∀ y : Fin n → k, y ∈ MvPolynomial.zeroLocus k I →
      MvPolynomial.eval y f ≠ 0 → MvPolynomial.eval y p = 0) :
    p ∈ I := by
  have hfp : f * p ∈ MvPolynomial.vanishingIdeal k
      (MvPolynomial.zeroLocus k I) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro y hy
    by_cases hfy : MvPolynomial.eval y f = 0
    · simp [hfy]
    · rw [map_mul]
      change MvPolynomial.eval y f * MvPolynomial.eval y p = 0
      rw [hp y hy hfy]
      simp
  let : I.IsPrime := hI
  have hfpI : f * p ∈ I := by
    rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus I] at hfp
    exact hfp
  rcases hI.mem_or_mem hfpI with hfi | hpi
  · exact False.elim (hf hfi)
  · exact hpi

def restrictedEquationConormalLocus
    (I : Ideal (MvPolynomial (Fin n) k)) (S : Set (Fin n → k)) :
    Set (PhaseVar n → k) :=
  {q | q ∈ equationConormalLocus I ∧
    (fun i => q (Sum.inl i)) ∈ S}

theorem restricted_subset_equationConormalLocus
    (I : Ideal (MvPolynomial (Fin n) k)) (S : Set (Fin n → k)) :
    restrictedEquationConormalLocus I S ⊆ equationConormalLocus I := by
  intro q hq
  exact hq.1

/-- A covector in the equation conormal is the gradient of one equation of
the ideal; finite linear combinations can be absorbed into that equation. -/
theorem exists_equation_with_differentialAt_eq
    (I : Ideal (MvPolynomial (Fin n) k)) (y ξ : Fin n → k)
    (hξ : coordinateCovector ξ ∈ affineConormalSpace y I) :
    ∃ h ∈ I, ∀ i, differentialAt y h i = ξ i := by
  classical
  obtain ⟨c, hc⟩ :=
    coordinate_mem_affineConormalSpace_exists_finsupp y ξ I hξ
  let h : MvPolynomial (Fin n) k :=
    ∑ p ∈ c.support, MvPolynomial.C (c p) * p.1
  refine ⟨h, ?_, fun i => ?_⟩
  · apply Ideal.sum_mem
    intro p hp
    exact I.mul_mem_left _ p.2
  · rw [hc i]
    simp only [h, differentialAt, map_sum, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_C, zero_mul, zero_add, MvPolynomial.eval_sum,
      MvPolynomial.eval_mul, MvPolynomial.eval_C]

def gradientGraphSubstitution (h : MvPolynomial (Fin n) k) :
    SymbolRing k n →+* MvPolynomial (Fin n) k :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim MvPolynomial.X (fun i => MvPolynomial.pderiv i h))

theorem eval_gradientGraphSubstitution
    (h : MvPolynomial (Fin n) k) (P : SymbolRing k n) (y : Fin n → k) :
    MvPolynomial.eval y (gradientGraphSubstitution h P) =
      MvPolynomial.eval (Sum.elim y (differentialAt y h)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [gradientGraphSubstitution]
  | add P Q hP hQ =>
      simp only [gradientGraphSubstitution] at hP hQ
      simp only [gradientGraphSubstitution, map_add, MvPolynomial.eval_add]
      rw [hP, hQ]
  | mul_X P i hP =>
      simp only [gradientGraphSubstitution] at hP
      rcases i with i | i
      · simp only [gradientGraphSubstitution, map_mul, MvPolynomial.eval₂Hom_X',
          Sum.elim_inl, MvPolynomial.eval_mul, MvPolynomial.eval_X]
        rw [hP]
      · simp only [gradientGraphSubstitution, map_mul, MvPolynomial.eval₂Hom_X',
          Sum.elim_inr, MvPolynomial.eval_mul]
        rw [hP]
        simp [differentialAt]

/-- Restricting the equation conormal to any subset containing the principal
open part of the prime base variety does not change its algebraic closure. -/
theorem equationConormalClosure_restricted_eq
    (I : Ideal (MvPolynomial (Fin n) k)) (hI : I.IsPrime)
    (f : MvPolynomial (Fin n) k) (hf : f ∉ I)
    (S : Set (Fin n → k))
    (hS : S ⊆ MvPolynomial.zeroLocus k I)
    (hopen : ∀ y : Fin n → k, y ∈ MvPolynomial.zeroLocus k I →
      MvPolynomial.eval y f ≠ 0 → y ∈ S) :
    MvPolynomial.zeroLocus k
        (MvPolynomial.vanishingIdeal k (restrictedEquationConormalLocus I S)) =
      equationConormalClosure I := by
  apply Set.Subset.antisymm
  · exact zeroLocus_vanishingIdeal_mono_of_subset_zeroLocus
      (restrictedEquationConormalLocus I S)
      (MvPolynomial.vanishingIdeal k (equationConormalLocus I))
      (fun q hq P hP => hP q hq.1)
  · apply zeroLocus_vanishingIdeal_mono_of_subset_zeroLocus
    intro q qlocus P hP
    let y : Fin n → k := fun i => q (.inl i)
    let ξ : Fin n → k := fun i => q (.inr i)
    obtain ⟨h, hhI, hgrad⟩ :=
      exists_equation_with_differentialAt_eq I y ξ qlocus.2
    have hrho : gradientGraphSubstitution h P ∈ I := by
      apply mem_of_vanishes_on_principal_open I hI hf
      intro z hzI hzf
      have hzS : z ∈ S := hopen z hzI hzf
      have hgraph : Sum.elim z (differentialAt z h) ∈
          restrictedEquationConormalLocus I S := by
        refine ⟨⟨hzI, ?_⟩, hzS⟩
        rw [affineConormalSpace_eq_equationCovectorSpan]
        apply Submodule.subset_span
        exact ⟨⟨h, hhI⟩, rfl⟩
      rw [eval_gradientGraphSubstitution]
      exact hP _ hgraph
    have hyrho := qlocus.1 _ hrho
    rw [eval_gradientGraphSubstitution] at hyrho
    change MvPolynomial.eval (Sum.elim y (differentialAt y h)) P = 0 at hyrho
    have hgradfun : differentialAt y h = ξ := funext hgrad
    have hsplit : Sum.elim y ξ = q := by
      funext i
      rcases i with i | i <;> rfl
    rw [hgradfun, hsplit] at hyrho
    exact hyrho


end

end Stafford38.Geometry.ConormalPrincipalOpenDensity
