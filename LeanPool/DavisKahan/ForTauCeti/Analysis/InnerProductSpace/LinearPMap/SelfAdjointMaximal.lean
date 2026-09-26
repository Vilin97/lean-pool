/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure

/-!
# A self-adjoint operator has no proper self-adjoint extension

If `A ≤ B` and both are self-adjoint, then `A = B`.

This is the reason one never has to prove *both* inclusions when identifying
two self-adjoint operators — most immediately, when identifying the generator
of the unitary group of `A` with `A` itself, which is the uniqueness half of
Stone's theorem.  Either inclusion suffices, and in that application only one
of the two is within reach.

The proof is order theory once the adjoint is known to be order-reversing.
That in turn is nearly definitional: membership in the adjoint domain is a
continuity statement quantified over the operator's domain, so *shrinking* the
operator makes the condition easier to satisfy.

## Provenance

*New.*  Mathlib 4.32 has `LinearPMap.adjoint` and `LinearPMap.IsSelfAdjoint`
but neither of the two lemmas below.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The adjoint is order-reversing.**  Enlarging an operator shrinks its
adjoint: the identity defining the adjoint is quantified over the operator's
domain, so it is a weaker requirement for the smaller operator. -/
theorem adjoint_le_adjoint {A B : H →ₗ.[ℂ] H} (hA : Dense (A.domain : Set H))
    (h : A ≤ B) : B.adjoint ≤ A.adjoint := by
  have hB : Dense (B.domain : Set H) := hA.mono h.1
  -- the defining identity for `B`, restricted to `A`'s domain
  have key : ∀ (y : B.adjoint.domain) (x : A.domain),
      ⟪B.adjoint y, (x : H)⟫_ℂ = ⟪(y : H), A x⟫_ℂ := by
    intro y x
    have hx : (x : H) ∈ B.domain := h.1 x.2
    have hval : A x = B ⟨(x : H), hx⟩ := h.2 rfl
    rw [hval]
    exact _root_.LinearPMap.adjoint_isFormalAdjoint hB y ⟨(x : H), hx⟩
  refine ⟨fun y hy => ?_, ?_⟩
  · exact _root_.LinearPMap.mem_adjoint_domain_of_exists (T := A) y
      ⟨B.adjoint ⟨y, hy⟩, fun x => key ⟨y, hy⟩ x⟩
  · rintro ⟨y, hyB⟩ ⟨y', hyA⟩ hyy
    simp only at hyy
    subst hyy
    exact (_root_.LinearPMap.adjoint_apply_eq hA ⟨y, hyA⟩ (fun x => key ⟨y, hyB⟩ x)).symm

/-- **Self-adjoint operators are maximal.**  A self-adjoint operator has no
proper self-adjoint extension, so either inclusion identifies the two. -/
theorem eq_of_le_of_isSelfAdjoint {A B : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (h : A ≤ B) : A = B := by
  have h1 : B.adjoint ≤ A.adjoint := adjoint_le_adjoint hA.dense_domain h
  rw [_root_.LinearPMap.isSelfAdjoint_def] at hA hB
  rw [hA, hB] at h1
  exact le_antisymm h h1

end LinearPMap
end TauCeti
