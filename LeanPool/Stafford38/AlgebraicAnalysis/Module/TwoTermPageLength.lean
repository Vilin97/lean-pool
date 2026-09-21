/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

namespace AlgebraicAnalysis.TwoTermPageLength

open scoped ENat

theorem exists_boundary_eq_top_of_iSup_eq_top
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [IsNoetherian R M] (D : ℕ →o Submodule R M) (hD : ⨆ r, D r = ⊤) :
    ∃ N, D N = ⊤ := by
  obtain ⟨N, hN⟩ := (IsNoetherian.noetherian (⊤ : Submodule R M)).stabilizes_of_iSup_eq D hD
  exact ⟨N, hN.symm⟩

theorem twoTermPage_length_target_le_source
    {R : Type*} [Ring R]
    (A C : ℕ → Type*)
    [∀ r, AddCommGroup (A r)] [∀ r, Module R (A r)]
    [∀ r, AddCommGroup (C r)] [∀ r, Module R (C r)]
    (hA0 : IsFiniteLength R (A 0))
    (hC0 : IsFiniteLength R (C 0))
    (d : ∀ r, A r →ₗ[R] C r)
    (sourceSucc : ∀ r, A (r + 1) ≃ₗ[R] LinearMap.ker (d r))
    (targetSucc : ∀ r, C (r + 1) ≃ₗ[R] C r ⧸ LinearMap.range (d r))
    (N : ℕ) [Subsingleton (C N)] :
    Module.length R (C 0) ≤ Module.length R (A 0) := by
  have hA : ∀ r, IsFiniteLength R (A r) := by
    intro r
    induction r with
    | zero => exact hA0
    | succ r ihr =>
        apply (sourceSucc r).symm.isFiniteLength
        exact IsFiniteLength.of_injective ihr (Submodule.subtype_injective _)
  have hC : ∀ r, IsFiniteLength R (C r) := by
    intro r
    induction r with
    | zero => exact hC0
    | succ r ihr =>
        apply (targetSucc r).symm.isFiniteLength
        exact IsFiniteLength.of_surjective ihr (Submodule.mkQ_surjective _)
  let : ∀ r, IsNoetherian R (A r) := fun r =>
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hA r)).1
  let : ∀ r, IsArtinian R (A r) := fun r =>
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hA r)).2
  let : ∀ r, IsNoetherian R (C r) := fun r =>
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hC r)).1
  let : ∀ r, IsArtinian R (C r) := fun r =>
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hC r)).2
  have source_length (r : ℕ) :
      Module.length R (A r) =
        Module.length R (A (r + 1)) + Module.length R (LinearMap.range (d r)) := by
    rw [(sourceSucc r).length_eq]
    exact Module.length_eq_add_of_exact
      (LinearMap.ker (d r)).subtype (d r).rangeRestrict
      (Submodule.subtype_injective _)
      (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict (d r)))
      (by
        rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict])
  have target_length (r : ℕ) :
      Module.length R (C r) =
        Module.length R (LinearMap.range (d r)) + Module.length R (C (r + 1)) := by
    rw [(targetSucc r).length_eq]
    exact Module.length_eq_add_of_exact
      (LinearMap.range (d r)).subtype (LinearMap.range (d r)).mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ _)
  have source_ne_top (r : ℕ) : Module.length R (A r) ≠ ⊤ := Module.length_ne_top
  have target_ne_top (r : ℕ) : Module.length R (C r) ≠ ⊤ := Module.length_ne_top
  have range_ne_top (r : ℕ) : Module.length R (LinearMap.range (d r)) ≠ ⊤ := by
    exact Module.length_ne_top
  have invariant : ∀ n,
      ENat.toNat (Module.length R (C 0)) + ENat.toNat (Module.length R (A n)) =
        ENat.toNat (Module.length R (A 0)) + ENat.toNat (Module.length R (C n)) := by
    intro n
    induction n with
    | zero => simp [add_comm]
    | succ n ih =>
      have hs := congrArg ENat.toNat (source_length n)
      have ht := congrArg ENat.toNat (target_length n)
      rw [ENat.toNat_add (source_ne_top (n + 1)) (range_ne_top n)] at hs
      rw [ENat.toNat_add (range_ne_top n) (target_ne_top (n + 1))] at ht
      omega
  have h := invariant N
  have hCN : ENat.toNat (Module.length R (C N)) = 0 := by simp
  rw [hCN, add_zero] at h
  have hnat : ENat.toNat (Module.length R (C 0)) ≤
      ENat.toNat (Module.length R (A 0)) := by omega
  rw [← ENat.natCast_toNat (target_ne_top 0), ← ENat.natCast_toNat (source_ne_top 0)]
  exact_mod_cast hnat


end AlgebraicAnalysis.TwoTermPageLength
