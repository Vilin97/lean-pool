/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Module.FreeSummandInduction


/-!
# A projective-image terminal module lemma

This file isolates the unconditional linear-algebra step in a torsion
presentation: a surjection from a product which kills its free factor factors
through the first factor.  It does not assert that a torsion module admits
such a presentation.
-/

@[expose] public section

namespace AlgebraicAnalysis.TorsionProjectiveImage

variable {R P F T : Type*} [Ring R]
variable [AddCommGroup P] [Module R P]
variable [AddCommGroup F] [Module R F]
variable [AddCommGroup T] [Module R T]

/-- A linear map out of a product which vanishes on the second factor is
already a map out of the first factor. -/
theorem linearMap_product_factor_first
    (q : P × F →ₗ[R] T)
    (hkill : ∀ z : F, q (0, z) = 0) :
    ∃ q₁ : P →ₗ[R] T,
      q = q₁.comp (LinearMap.fst R P F) := by
  let q₁ : P →ₗ[R] T := q.comp (LinearMap.inl R P F)
  refine ⟨q₁, ?_⟩
  apply LinearMap.ext
  rintro ⟨p, z⟩
  have hdecomp : (p, z) = (p, 0) + (0, z) := by
    ext <;> simp
  calc
    q (p, z) = q ((p, 0) + (0, z)) := congrArg q hdecomp
    _ = q (p, 0) + q (0, z) := q.map_add _ _
    _ = q (p, 0) := by rw [hkill, add_zero]
    _ = q₁ p := rfl
    _ = (q₁.comp (LinearMap.fst R P F)) (p, z) := rfl

/-- Surjectivity also descends through the factorization in
`linearMap_product_factor_first`. -/
theorem surjective_factor_first_of_surjective
    (q : P × F →ₗ[R] T)
    (hkill : ∀ z : F, q (0, z) = 0)
    (hq : Function.Surjective q) :
    ∃ q₁ : P →ₗ[R] T, Function.Surjective q₁ := by
  obtain ⟨q₁, hfactor⟩ := linearMap_product_factor_first q hkill
  refine ⟨q₁, ?_⟩
  intro t
  obtain ⟨z, hz⟩ := hq t
  refine ⟨z.1, ?_⟩
  rw [hfactor] at hz
  simpa using hz

/-- If a module `P` is identified with a projective left ideal times a free
factor, and a quotient map kills that free factor, then the target is a
homomorphic image of the projective left ideal.  Here `I : Submodule R R` is
a left ideal of the ring. -/
theorem projective_leftIdeal_image_of_terminal_split
    (I : Submodule R R) [Module.Projective R I]
    (e : P ≃ₗ[R] I × F)
    (q : P →ₗ[R] T) (hq : Function.Surjective q)
    (hkill : ∀ z : F, q (e.symm (0, z)) = 0) :
    ∃ qI : I →ₗ[R] T,
      Function.Surjective qI ∧ Module.Projective R I := by
  let qprod : I × F →ₗ[R] T := q.comp e.symm.toLinearMap
  have hqprod : Function.Surjective qprod := by
    intro t
    obtain ⟨p, hp⟩ := hq t
    refine ⟨e p, ?_⟩
    simpa [qprod] using hp
  have hkillprod : ∀ z : F, qprod (0, z) = 0 := by
    intro z
    exact hkill z
  obtain ⟨qI, hqI⟩ := surjective_factor_first_of_surjective qprod hkillprod hqprod
  exact ⟨qI, hqI, inferInstance⟩


end AlgebraicAnalysis.TorsionProjectiveImage
