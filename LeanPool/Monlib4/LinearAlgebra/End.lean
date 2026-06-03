/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
 # Some obvious lemmas on module.End

This file contains some obvious lemmas on `module.End`.
-/


open scoped BigOperators

theorem LinearMap.comp_one {R E F : Type _} [Semiring R] [AddCommMonoid E] [AddCommMonoid F]
    [Module R F] [Module R E] (f : E →ₗ[R] F) : f ∘ₗ (1 : E →ₗ[R] E) = f := rfl

theorem LinearMap.one_comp {R E F : Type _} [Semiring R] [AddCommMonoid E] [AddCommMonoid F]
    [Module R F] [Module R E] (f : E →ₗ[R] F) : (1 : F →ₗ[R] F) ∘ₗ f = f := rfl

theorem LinearMap.comp_sum {R M M₂ M₃ : Type _} [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]
    [AddCommMonoid M₃] [Module R M] [Module R M₂] [Module R M₃] (g : M₃ →ₗ[R] M₂) {α : Type _}
    (s : Finset α) (f : α → M →ₗ[R] M₃) : g ∘ₗ ∑ a ∈ s, f a = ∑ a ∈ s, g ∘ₗ f a := by
  simp_rw [LinearMap.ext_iff, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    map_sum, forall_true_iff]

theorem LinearMap.sum_comp {R M M₂ M₃ : Type _} [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]
    [AddCommMonoid M₃] [Module R M] [Module R M₂] [Module R M₃] (f : M →ₗ[R] M₃) {α : Type _}
    (s : Finset α) (g : α → M₃ →ₗ[R] M₂) : (∑ a ∈ s, g a) ∘ₗ f = ∑ a ∈ s, g a ∘ₗ f := by
  simp_rw [LinearMap.ext_iff, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    forall_true_iff]

theorem Module.End.has_eigenvector_iff_hasEigenvalue {R M : Type _} [CommRing R] [AddCommGroup M]
    [Module R M] {T : Module.End R M} {α : R} :
    (∃ v : M, T v = α • v ∧ v ≠ 0) ↔ Module.End.HasEigenvalue T α :=
  by
  constructor
  · rintro ⟨v, hv⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    exact hv
  · intro h
    simp only [Module.End.HasEigenvalue, Module.End.HasUnifEigenvalue] at h
    simp_rw [Submodule.ne_bot_iff] at h
    rcases h with ⟨x, Hx, hx⟩
    use x
    rw [← Module.End.mem_eigenspace_iff]
    exact ⟨Hx, hx⟩
