/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Generator-level interface for Zhou's spatial factor map.  The analytic
crossed-product construction is reduced to the kernel, quotient, and vacuum
transport equations used by the regular factor.
Paper: §3.
-/
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.SemidirectClosure

/-!
The semidirect generator transport component of the Connes rigidity formalization.
-/

namespace Connes
namespace SemidirectGeneratorTransport

noncomputable section

/- The regular operators from the two semidirect factors form the generator
family used by the closure reduction. Paper: §3.
-/
/--
The `generatorSet` construction used in the Connes rigidity formalization.
-/
def generatorSet
    {A K : Type*} [Group A] [Group K]
    (φ : K →* MulAut A) :
    Set (GroupL2 (A ⋊[φ] K) →L[ℂ] GroupL2 (A ⋊[φ] K)) :=
  (Set.range fun a : A =>
    (leftRegularRepresentation (A ⋊[φ] K) (SemidirectProduct.inl a) :
      GroupL2 (A ⋊[φ] K) →L[ℂ] GroupL2 (A ⋊[φ] K))) ∪
  (Set.range fun k : K =>
    (leftRegularRepresentation (A ⋊[φ] K) (SemidirectProduct.inr k) :
      GroupL2 (A ⋊[φ] K) →L[ℂ] GroupL2 (A ⋊[φ] K)))

/-- The two generator families are the only analytic data needed for factor
transport. Paper: §3. -/
structure Data
    {A K : Type*} [Group A] [Group K]
    {φ₁ φ₂ : K →* MulAut A}
    (U : GroupL2 (A ⋊[φ₁] K) ≃ₗᵢ[ℂ] GroupL2 (A ⋊[φ₂] K)) where
  kernel_generator : ∀ a : A,
    U.conjStarAlgEquiv
        (leftRegularRepresentation (A ⋊[φ₁] K)
          (SemidirectProduct.inl a) :
          GroupL2 (A ⋊[φ₁] K) →L[ℂ] GroupL2 (A ⋊[φ₁] K)) =
      (leftRegularRepresentation (A ⋊[φ₂] K)
        (SemidirectProduct.inl a) :
        GroupL2 (A ⋊[φ₂] K) →L[ℂ] GroupL2 (A ⋊[φ₂] K))
  quotient_generator : ∀ k : K,
    U.conjStarAlgEquiv
        (leftRegularRepresentation (A ⋊[φ₁] K)
          (SemidirectProduct.inr k) :
          GroupL2 (A ⋊[φ₁] K) →L[ℂ] GroupL2 (A ⋊[φ₁] K)) =
      (leftRegularRepresentation (A ⋊[φ₂] K)
        (SemidirectProduct.inr k) :
        GroupL2 (A ⋊[φ₂] K) →L[ℂ] GroupL2 (A ⋊[φ₂] K))

/- The generator transport equations give equality of the two generator
sets. Paper: §3. -/
theorem generatorSet_image_eq
    {A K : Type*} [Group A] [Group K]
    {φ₁ φ₂ : K →* MulAut A}
    {U : GroupL2 (A ⋊[φ₁] K) ≃ₗᵢ[ℂ] GroupL2 (A ⋊[φ₂] K)}
    (data : Data U) :
    U.conjStarAlgEquiv '' generatorSet φ₁ = generatorSet φ₂ := by
  ext T
  constructor
  · rintro ⟨S, (⟨a, rfl⟩ | ⟨k, rfl⟩), rfl⟩
    · exact Or.inl ⟨a, (data.kernel_generator a).symm⟩
    · exact Or.inr ⟨k, (data.quotient_generator k).symm⟩
  · rintro (⟨a, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨_, Or.inl ⟨a, rfl⟩, data.kernel_generator a⟩
    · exact ⟨_, Or.inr ⟨k, rfl⟩, data.quotient_generator k⟩

/- The generator equations imply transport of regular-factor membership.
Paper: §3. -/
theorem mem_regularClosure_iff
    {A K : Type*} [Group A] [Group K]
    {φ₁ φ₂ : K →* MulAut A}
    {U : GroupL2 (A ⋊[φ₁] K) ≃ₗᵢ[ℂ] GroupL2 (A ⋊[φ₂] K)}
    (data : Data U) (T : GroupL2 (A ⋊[φ₁] K) →L[ℂ] GroupL2 (A ⋊[φ₁] K)) :
    T ∈ vonNeumannClosure
        (Set.range fun g : A ⋊[φ₁] K =>
          (leftRegularRepresentation (A ⋊[φ₁] K) g :
            GroupL2 (A ⋊[φ₁] K) →L[ℂ] GroupL2 (A ⋊[φ₁] K))) ↔
      U.conjStarAlgEquiv T ∈ vonNeumannClosure
        (Set.range fun g : A ⋊[φ₂] K =>
          (leftRegularRepresentation (A ⋊[φ₂] K) g :
            GroupL2 (A ⋊[φ₂] K) →L[ℂ] GroupL2 (A ⋊[φ₂] K))) := by
  rw [semidirect_vonNeumannClosure_eq_inl_inr φ₁,
    semidirect_vonNeumannClosure_eq_inl_inr φ₂]
  simpa only [generatorSet] using
    mem_vonNeumannClosure_iff_of_conj_image_eq U
      (generatorSet φ₁) (generatorSet φ₂) (generatorSet_image_eq data) T

end
end SemidirectGeneratorTransport
end Connes
