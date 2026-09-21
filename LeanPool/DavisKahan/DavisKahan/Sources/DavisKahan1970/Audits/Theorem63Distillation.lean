/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63FiniteSource

/-!
# Audit: the Theorem 6.3 dimension hypothesis does not imply acuteness

A previous repository distillation mistranscribed Davis--Kahan 1970,
Theorem 6.3.  It replaced the paper's directed cross-block definition of
`tan Θ₀` by a symmetric `IsAcute Z V` conclusion and attempted to derive that
conclusion from an isometric embedding of the smaller trial space into the
larger exact space.

That implication is false.  The paper does not use it: it works with the
singular values of `E₀⋆ F₁`, equivalently the directed projection from the trial
space into the orthogonal complement of the exact space.

The theorem below is a permanent regression test for the bad distillation.
Even a strict finite-dimensional inclusion admits an isometric embedding while
failing symmetric acuteness.
-/

open Module (finrank)

namespace TauCeti
namespace DavisKahan1970
namespace Theorem63DistillationAudit


/-- The isometric inclusion from the zero subspace into the full one-dimensional
space.  This deliberately minimal witness keeps the regression theorem
independent of coordinate calculations. -/
noncomputable def botToTopIsometry :
    (⊥ : Submodule ℂ ℂ) →ₗᵢ[ℂ] (⊤ : Submodule ℂ ℂ) where
  toLinearMap := Submodule.inclusion bot_le
  norm_map' _ := rfl

/-- The erroneous geometric implication introduced by the old distillation. -/
def MistranscribedDimensionImpliesAcute : Prop :=
  ∀ (Z V : Submodule ℂ ℂ),
    finrank ℂ Z < finrank ℂ V →
    Nonempty (Z →ₗᵢ[ℂ] V) →
    IsAcute Z V

/-- A strict dimension inequality and an isometric embedding do **not** imply
symmetric Davis--Kahan acuteness.  For `Z = ⊥` and `V = ⊤`, the nonzero vector
`1 ∈ V` projects to zero in `Z`. -/
theorem not_mistranscribedDimensionImpliesAcute :
    ¬ MistranscribedDimensionImpliesAcute := by
  intro h
  have hacute := h (⊥ : Submodule ℂ ℂ) (⊤ : Submodule ℂ ℂ)
    (by simp) ⟨botToTopIsometry⟩
  have hone : (1 : ℂ) = 0 := hacute.2 1 (by simp) (by simp)
  exact one_ne_zero hone

end Theorem63DistillationAudit
end DavisKahan1970
end TauCeti
