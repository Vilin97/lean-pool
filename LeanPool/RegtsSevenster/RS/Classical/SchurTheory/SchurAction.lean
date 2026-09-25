/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.CentralElem

/-!
# Schur scalarity for commuting endomorphisms

Over ℂ, an endomorphism of a finite-dimensional irreducible
representation commuting with the group action is scalar: it has
an eigenvalue, and the eigenspace is an invariant subspace.  The
image of a class-function element under a representation commutes
with the action, so it acts as a scalar on every irreducible.
-/

namespace RS

open Finset LinearMap

variable {G V : Type*}

/-- Irreducibility, spelled invariant-submodule-theoretically. -/
def IsIrredRep [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  Nontrivial V ∧
    ∀ p : Submodule ℂ V,
      (∀ (g : G) (v : V), v ∈ p → ρ g v ∈ p) → p = ⊥ ∨ p = ⊤

/-- **Schur scalarity**: a commuting endomorphism of an
irreducible representation is scalar. -/
theorem commuting_scalar
    [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Representation ℂ G V}
    (hirr : IsIrredRep ρ) (T : Module.End ℂ V)
    (hT : ∀ g : G, T ∘ₗ (ρ g : V →ₗ[ℂ] V) =
      (ρ g : V →ₗ[ℂ] V) ∘ₗ T) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  have : Nontrivial V := hirr.1
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  refine ⟨c, ?_⟩
  have hker : LinearMap.ker (T - c • LinearMap.id) ≠ ⊥ := by
    intro hbot
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    have hmem : v ∈ LinearMap.ker (T - c • LinearMap.id) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply]
      rw [hv.apply_eq_smul]
      exact sub_self _
    rw [hbot, Submodule.mem_bot] at hmem
    exact hv.2 hmem
  have hinv : ∀ (g : G) (v : V),
      v ∈ LinearMap.ker (T - c • LinearMap.id) →
      ρ g v ∈ LinearMap.ker (T - c • LinearMap.id) := by
    intro g v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at hv ⊢
    have hTg := congrFun (congrArg (fun (f : V →ₗ[ℂ] V) =>
      (f : V → V)) (hT g)) v
    simp only [LinearMap.coe_comp, Function.comp_apply] at hTg
    rw [hTg]
    rw [show T v = c • v from by
      have := hv
      linear_combination (norm := module) this]
    rw [map_smul]
    exact sub_self _
  rcases hirr.2 _ hinv with hbot | htop
  · exact absurd hbot hker
  · have : T - c • LinearMap.id = 0 := by
      apply LinearMap.ext
      intro v
      have hv : v ∈ LinearMap.ker (T - c • LinearMap.id) := by
        rw [htop]; exact Submodule.mem_top
      rw [LinearMap.mem_ker] at hv
      rw [hv]; rfl
    have h2 := congrArg (fun (f : Module.End ℂ V) =>
      f + c • LinearMap.id) this
    simpa using h2

/-- The image of a class-function element commutes with the
action. -/
theorem asAlgebraHom_classElem_comm
    [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (c : G → ℂ) (hc : ∀ g h : G, c (h * g * h⁻¹) = c g) (g : G) :
    (ρ.asAlgebraHom (classElem c)) ∘ₗ (ρ g : V →ₗ[ℂ] V) =
      (ρ g : V →ₗ[ℂ] V) ∘ₗ ρ.asAlgebraHom (classElem c) := by
  classical
  have h1 : ρ.asAlgebraHom (classElem c * MonoidAlgebra.single g 1) =
      ρ.asAlgebraHom (MonoidAlgebra.single g 1 * classElem c) := by
    rw [classElem_mul_comm c hc]
  rw [map_mul, map_mul] at h1
  rw [show (ρ.asAlgebraHom (MonoidAlgebra.single g 1) :
      V →ₗ[ℂ] V) = (ρ g : V →ₗ[ℂ] V) from by
    rw [Representation.asAlgebraHom_single, one_smul]] at h1
  exact h1

/-- **Scalar action**: a class-function element acts as a scalar
on every irreducible representation. -/
theorem asAlgebraHom_classElem_scalar
    [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    {ρ : Representation ℂ G V}
    (hirr : IsIrredRep ρ) (c : G → ℂ)
    (hc : ∀ g h : G, c (h * g * h⁻¹) = c g) :
    ∃ z : ℂ, ρ.asAlgebraHom (classElem c) = z • LinearMap.id := by
  classical
  exact
    commuting_scalar hirr _ (asAlgebraHom_classElem_comm ρ c hc)

end RS
