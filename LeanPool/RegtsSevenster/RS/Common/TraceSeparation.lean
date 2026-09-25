/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Linear independence from a trace supported at the identity

A linear functional on an algebra that is nonzero at the identity
of a group representation and zero at every other group element
separates the represented elements. Its translates give dual
functionals, so the group elements are linearly independent.
-/

@[expose] public section

namespace RS

/-- A trace supported at the identity separates every element of
a group representation. -/
theorem linearIndependent_of_group_trace {G A : Type*} [Group G]
    [DecidableEq G]
    [Ring A] [Algebra ℂ A] (ρ : G →* A) (τ : A →ₗ[ℂ] ℂ)
    {c : ℂ} (hc : c ≠ 0)
    (hτ : ∀ σ, τ (ρ σ) = if σ = 1 then c else 0) :
    LinearIndependent ℂ (fun σ => ρ σ) := by
  classical
  let dual : G → Module.Dual ℂ A := fun σ =>
    c⁻¹ • τ.comp (LinearMap.mulLeft ℂ (ρ σ⁻¹))
  apply LinearIndependent.of_pairwise_dual_eq_zero_one _ dual
  · intro σ π hne
    change c⁻¹ * τ (ρ σ⁻¹ * ρ π) = 0
    rw [← map_mul, hτ, ite_eq_right (fun h => hne (inv_mul_eq_one.mp h)),
      mul_zero]
  · intro σ
    change c⁻¹ * τ (ρ σ⁻¹ * ρ σ) = 1
    rw [← map_mul, inv_mul_cancel, hτ, ite_eq_left rfl, inv_mul_cancel₀ hc]

/-- In a finite-dimensional algebra a group representation with
such a trace has at most the dimension many group elements. -/
theorem card_le_finrank_of_group_trace {G A : Type*} [Group G]
    [DecidableEq G]
    [Fintype G] [Ring A] [Algebra ℂ A] [Module.Finite ℂ A]
    (ρ : G →* A) (τ : A →ₗ[ℂ] ℂ) {c : ℂ} (hc : c ≠ 0)
    (hτ : ∀ σ, τ (ρ σ) = if σ = 1 then c else 0) :
    Fintype.card G ≤ Module.finrank ℂ A :=
  (linearIndependent_of_group_trace ρ τ hc hτ).fintype_card_le_finrank

end RS
