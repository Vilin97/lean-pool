/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.EndomorphismKernelSupport
public import Mathlib.RingTheory.Ideal.Maps


/-!
# Kernel support over a base ring

A finite module over a commutative Noetherian coefficient algebra is Hopfian
over that algebra.  This gives the kernel--cokernel support inclusion after
restriction of scalars, without assuming finite generation over the base.
-/

@[expose] public section

namespace AlgebraicAnalysis

theorem endomorphism_kernel_support_subset_cokernel_support_over_base
    {R C E : Type*} [CommRing R] [CommRing C] [Algebra R C]
    [AddCommGroup E] [Module C E] [Module R E] [IsScalarTower R C E]
    [IsNoetherianRing C] [Module.Finite C E] (f : Module.End C E) :
    Module.support R (LinearMap.ker (f.restrictScalars R)) ⊆
      Module.support R (E ⧸ LinearMap.range (f.restrictScalars R)) := by
  intro p hp
  rw [Module.mem_support_iff_exists_annihilator] at hp ⊢
  obtain ⟨x, hx⟩ := hp
  let xC : LinearMap.ker f := ⟨x.1, by
    exact x.2⟩
  let I : Ideal C := (C ∙ xC).annihilator
  have hdisj : Disjoint (I : Set C) (p.asIdeal.primeCompl.map (algebraMap R C)) := by
    rw [Set.disjoint_left]
    rintro c hc ⟨r, hr, rfl⟩
    have hc' : algebraMap R C r • xC.1 = 0 := by
      have hcx : algebraMap R C r • xC = 0 := by
        exact (Submodule.mem_annihilator_span_singleton _ _).mp hc
      exact congrArg Subtype.val hcx
    have hrx : r • x = 0 := by
      apply Subtype.ext
      change r • x.1 = 0
      simpa [xC, IsScalarTower.algebraMap_smul C r x.1] using hc'
    have hrann : r ∈ (R ∙ x).annihilator := by
      exact (Submodule.mem_annihilator_span_singleton _ _).mpr hrx
    exact hr (hx hrann)
  obtain ⟨q, hqprime, hIq, hqdisj⟩ := I.exists_le_prime_disjoint _ hdisj
  let q' : PrimeSpectrum C := ⟨q, hqprime⟩
  have hxC : q' ∈ Module.support C (LinearMap.ker f) := by
    rw [Module.mem_support_iff_exists_annihilator]
    exact ⟨xC, show (C ∙ xC).annihilator ≤ q from hIq⟩
  have hcokerC : q' ∈ Module.support C (E ⧸ LinearMap.range f) :=
    endomorphism_kernel_support_subset_cokernel_support f hxC
  obtain ⟨y, hy⟩ := Module.mem_support_iff_exists_annihilator.mp hcokerC
  refine ⟨y, ?_⟩
  intro r hr
  have hmap : algebraMap R C r ∈ (C ∙ y).annihilator := by
    rw [Submodule.mem_annihilator_span_singleton]
    have hry : r • y = 0 :=
      (Submodule.mem_annihilator_span_singleton _ _).mp hr
    simpa [IsScalarTower.algebraMap_smul C r y] using hry
  by_contra hrp
  exact Set.disjoint_left.mp hqdisj (hy hmap) ⟨r, hrp, rfl⟩


end AlgebraicAnalysis
