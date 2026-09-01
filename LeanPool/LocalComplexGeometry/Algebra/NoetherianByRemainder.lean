/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Finite generation from a finite remainder module

This is the commutative-algebra skeleton of Rückert's induction.  If an ideal
contains an element `p` and reduction modulo `p` lands in a Noetherian module,
then finitely many lifted remainders together with `p` generate the ideal.
-/

open Set


namespace LocalComplexGeometry

theorem Ideal.fg_of_remainder_kernel
    {R A M : Type*} [CommRing R] [CommRing A] [AddCommGroup M]
    [Algebra R A] [Module R M] [IsNoetherian R M]
    (I : Ideal A) (p : A) (hp : p ∈ I)
    (rem : A →ₗ[R] M)
    (hker : LinearMap.ker rem ≤ (Ideal.span ({p} : Set A)).restrictScalars R) :
    I.FG := by
  let N : Submodule R M := (I.restrictScalars R).map rem
  have hNfg : N.FG := IsNoetherian.noetherian N
  obtain ⟨k, y, hy⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hNfg
  have hy_mem (i : Fin k) : y i ∈ N := by
    rw [← hy]
    exact Submodule.subset_span (Set.mem_range_self i)
  choose x hxI hxrem using fun i ↦ (Submodule.mem_map.mp (hy_mem i))
  let J : Ideal A := Ideal.span (Set.range x ∪ {p})
  have hpJ : p ∈ J := Ideal.subset_span (Set.mem_union_right _ (Set.mem_singleton p))
  have hxJ (i : Fin k) : x i ∈ J :=
    Ideal.subset_span (Set.mem_union_left _ (Set.mem_range_self i))
  have hspan_le_J : Submodule.span R (Set.range x) ≤ J.restrictScalars R := by
    apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    exact hxJ i
  have hrem_span : (Submodule.span R (Set.range x)).map rem = N := by
    rw [Submodule.map_span, ← hy]
    congr 1
    ext z
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hxrem i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, hxrem i⟩
  have hIJ : I ≤ J := by
    intro z hzI
    have hzremN : rem z ∈ N :=
      Submodule.mem_map.mpr ⟨z, hzI, rfl⟩
    rw [← hrem_span] at hzremN
    obtain ⟨t, htspan, htrem⟩ := Submodule.mem_map.mp hzremN
    have htJ : t ∈ J := hspan_le_J htspan
    have hdiffKer : z - t ∈ LinearMap.ker rem := by
      simp only [LinearMap.mem_ker, map_sub, htrem, sub_self]
    have hdiffP : z - t ∈ Ideal.span ({p} : Set A) := hker hdiffKer
    have hPJ : Ideal.span ({p} : Set A) ≤ J := by
      apply Ideal.span_le.mpr
      intro q hq
      simpa only [Set.mem_singleton_iff] using hq ▸ hpJ
    have hdiffJ : z - t ∈ J := hPJ hdiffP
    have := J.add_mem hdiffJ htJ
    simpa using this
  have hJI : J ≤ I := by
    apply Ideal.span_le.mpr
    intro z hz
    rcases hz with hz | hz
    · obtain ⟨i, rfl⟩ := hz
      exact hxI i
    · simpa only [Set.mem_singleton_iff] using hz ▸ hp
  have hJ : J = I := le_antisymm hJI hIJ
  refine Submodule.fg_def.mpr ⟨(Set.range x ∪ {p}), ?_, ?_⟩
  · exact (Set.finite_range x).union (Set.finite_singleton p)
  · exact hJ

end LocalComplexGeometry
