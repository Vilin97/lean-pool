/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.GraphSubspace

/-!
# Basic bounded block-operator and Riccati definitions

This module contains the dependency-minimal definitions shared by the bounded
Riccati leaf proofs.  The public facade is
`DavisKahan.InfiniteDimensional.Riccati.Bounded`.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- Self-adjoint `2 × 2` bounded block operator data. -/
structure BlockOperatorData where
  A0 : E0 →L[𝕜] E0
  A1 : E1 →L[𝕜] E1
  B01 : E1 →L[𝕜] E0
  B10 : E0 →L[𝕜] E1
  selfAdjoint0 : A0.IsSymmetric
  selfAdjoint1 : A1.IsSymmetric
  offDiagonalAdjoint : ∀ x y, ⟪B01 y, x⟫_𝕜 = ⟪y, B10 x⟫_𝕜

/-- Bounded block operator on the Hilbert direct sum. -/
noncomputable def blockOperator
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 E0 E1).symm :
      (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1)) ∘L
    ((H.A0 ∘L WithLp.fstL 2 𝕜 E0 E1 + H.B01 ∘L WithLp.sndL 2 𝕜 E0 E1).prod
      (H.B10 ∘L WithLp.fstL 2 𝕜 E0 E1 + H.A1 ∘L WithLp.sndL 2 𝕜 E0 E1))

/-- Graph of a bounded angular operator in the Hilbert direct sum. -/
noncomputable def blockGraph (X : E0 →L[𝕜] E1) :
    Submodule 𝕜 (WithLp 2 (E0 × E1)) :=
  LinearMap.range ((WithLp.linearEquiv 2 𝕜 (E0 × E1)).symm.toLinearMap ∘ₗ
    LinearMap.id.prod X.toLinearMap)

/-- Block-diagonal operator on the Hilbert direct sum. -/
noncomputable def blockDiagonalOperator
    (D0 : E0 →L[𝕜] E0) (D1 : E1 →L[𝕜] E1) :
    WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 E0 E1).symm :
      (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1)) ∘L (D0.prodMap D1) ∘L
    ((WithLp.prodContinuousLinearEquiv 2 𝕜 E0 E1) :
      WithLp 2 (E0 × E1) →L[𝕜] E0 × E1)

/-- Riccati defect `A₁X - XA₀ - XB₀₁X + B₁₀`. -/
def riccatiDefect (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : E0 →L[𝕜] E1 :=
  H.A1 ∘L X - X ∘L H.A0 - X ∘L H.B01 ∘L X + H.B10

/-- A bounded solution of the operator Riccati equation. -/
def SolvesRiccati (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  riccatiDefect H X = 0

end DavisKahanExt
end TauCeti
