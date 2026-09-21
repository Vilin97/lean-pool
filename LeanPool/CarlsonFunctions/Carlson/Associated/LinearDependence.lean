/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.FiniteType

/-! # Denominator-cleared dependence over an integral domain

These algebraic helpers contain no Carlson functions or analytic assumptions. -/

@[expose] public noncomputable section
namespace DirichletTransform

/-- Clearing a nonzero scalar denominator in a submodule. -/
def denominatorClosure {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] (P : Submodule A M) : Submodule A M where
  carrier := {v | ∃ d : A, d ≠ 0 ∧ d • v ∈ P}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro v w ⟨d, hd, hv⟩ ⟨e, he, hw⟩
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    have h := P.add_mem (P.smul_mem e hv) (P.smul_mem d hw)
    rw [smul_comm e d v] at h
    simpa only [smul_add, mul_smul] using h
  smul_mem' := by
    rintro c v ⟨d, hd, hv⟩
    refine ⟨d, hd, ?_⟩
    rw [smul_comm d c v]
    exact P.smul_mem c hv

theorem mem_denominatorClosure {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] (P : Submodule A M) {v : M} (hv : v ∈ P) :
    v ∈ denominatorClosure P :=
  ⟨1, one_ne_zero, by simpa using hv⟩

theorem denominatorClosure_cancel {A M : Type*} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] (P : Submodule A M) {c : A} {v : M}
    (hc : c ≠ 0) (hv : c • v ∈ denominatorClosure P) :
    v ∈ denominatorClosure P := by
  obtain ⟨d, hd, hv⟩ := hv
  exact ⟨d * c, mul_ne_zero hd hc, by simpa [mul_smul] using hv⟩

/-- Clearing denominators reduces dependence in a saturated finite span to dependence
of coefficient vectors over the original integral domain. -/
theorem exists_relation_of_mem_denominatorClosure
    {A M J K : Type*} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M]
    [Fintype J] [Fintype K] (v : K → M) (w : J → M)
    (hcard : Fintype.card K < Fintype.card J)
    (hw : ∀ j, w j ∈ denominatorClosure (Submodule.span A (Set.range v))) :
    ∃ a : J → A, (∃ j, a j ≠ 0) ∧ ∑ j, a j • w j = 0 := by
  choose d hd hmem using hw
  choose p hp using fun j => (Submodule.mem_span_range_iff_exists_fun A).mp (hmem j)
  have hdep : ¬ LinearIndependent A p := by
    intro h
    have hc := h.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at hc
    omega
  obtain ⟨a, ha, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  refine ⟨fun j => a j * d j, ⟨j, mul_ne_zero hj (hd j)⟩, ?_⟩
  simp_rw [mul_smul, ← hp, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hcoeff (k : K) : ∑ j, a j * p j k = 0 := by
    simpa using congrFun ha k
  simp_rw [← Finset.sum_smul, hcoeff, zero_smul, Finset.sum_const_zero]

end DirichletTransform
