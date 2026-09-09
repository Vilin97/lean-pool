/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.HahnBanach

@[expose] public section

/-!
# Hilbert-space representation of a functional bounded through an embedding

A linear functional on a complex vector space that is bounded in the norm of an
injective linear map into a Hilbert space is represented by an inner product in
that Hilbert space. No topology on the source vector space is needed.
-/

namespace NavierStokesR3.HilbertFunctionalExtension

universe u v

variable {E : Type u} [AddCommGroup E] [Module ℂ E]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Transfer a functional to the range of an injective linear map, extend it by
Hahn–Banach, and represent the extension by the Hilbert-space inner product. -/
theorem exists_inner_representation (B : E →ₗ[ℂ] H)
    (hB : Function.Injective B) (F : E →ₗ[ℂ] ℂ) {C : ℝ}
    (hbound : ∀ x : E, ‖F x‖ ≤ C * ‖B x‖) :
    ∃ q : H, ∀ x : E, F x = @inner ℂ H _ q (B x) := by
  classical
  let e : E ≃ₗ[ℂ] LinearMap.range B := LinearEquiv.ofInjective B hB
  let f : LinearMap.range B →ₗ[ℂ] ℂ := F.comp e.symm.toLinearMap
  have he (z : LinearMap.range B) : B (e.symm z) = (z : H) := by
    change ((e (e.symm z) : LinearMap.range B) : H) = (z : H)
    rw [e.apply_symm_apply]
  have hf : ∀ z : LinearMap.range B, ‖f z‖ ≤ C * ‖z‖ := by
    intro z
    change ‖F (e.symm z)‖ ≤ C * ‖(z : H)‖
    simpa only [he] using hbound (e.symm z)
  let fc : LinearMap.range B →L[ℂ] ℂ := f.mkContinuous C hf
  obtain ⟨G, hG, _⟩ := exists_extension_norm_eq (LinearMap.range B) fc
  refine ⟨(InnerProductSpace.toDual ℂ H).symm G, ?_⟩
  intro x
  rw [InnerProductSpace.toDual_symm_apply]
  calc
    F x = fc (e x) := by simp [fc, f]
    _ = G ((e x : LinearMap.range B) : H) := (hG (e x)).symm
    _ = G (B x) := rfl

end NavierStokesR3.HilbertFunctionalExtension
