/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace

/-!
# Operator blocks relative to an orthogonal decomposition

Pinching, off-diagonal parts, and zero-compression predicates used by the
finite double-angle and tangent theories.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
/-- The diagonal part (pinch) of an operator relative to `U ⊕ Uᗮ`. -/
noncomputable def pinch (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (H : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  projection U ∘ₗ H ∘ₗ projection U +
    complementaryProjection U ∘ₗ H ∘ₗ complementaryProjection U

/-- The off-diagonal part of an operator relative to `U ⊕ Uᗮ`. -/
noncomputable def offDiagonalPart (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (H : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  H - pinch U H

/-- Davis--Kahan's vanishing-pinch hypothesis. -/
def IsOffDiagonal (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (H : E →ₗ[𝕜] E) : Prop :=
  pinch U H = 0

/-- The weaker one-block condition used by the `tan Θ` theorem. -/
def HasZeroCompression (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (H : E →ₗ[𝕜] E) : Prop :=
  projection U ∘ₗ H ∘ₗ projection U = 0

omit [FiniteDimensional 𝕜 E] in
/-- A vanishing pinch has a vanishing selected diagonal block.
-/
theorem hasZeroCompression_of_isOffDiagonal
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (H : E →ₗ[𝕜] E)
    (hoff : IsOffDiagonal U H) : HasZeroCompression U H := by
  unfold IsOffDiagonal at hoff
  unfold HasZeroCompression
  apply LinearMap.ext
  intro x
  have hP_idem (y : E) : projection U (projection U y) = projection U y := by
    change U.starProjection (U.starProjection y) = U.starProjection y
    exact Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem y)
  have hP_comp (y : E) : projection U (complementaryProjection U y) = 0 := by
    change U.starProjection (Uᗮ.starProjection y) = 0
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact Uᗮ.starProjection_apply_mem y
  have h := congrArg (projection U) (LinearMap.congr_fun hoff x)
  simpa [pinch, LinearMap.comp_apply, hP_idem, hP_comp] using h

omit [FiniteDimensional 𝕜 E] in
/-- A vanishing pinch is unchanged when the two summands of the orthogonal
splitting are exchanged.
-/
theorem isOffDiagonal_orthogonal
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (H : E →ₗ[𝕜] E)
    (hoff : IsOffDiagonal U H) : IsOffDiagonal Uᗮ H := by
  unfold IsOffDiagonal at hoff ⊢
  simpa [pinch, projection, complementaryProjection, add_comm] using hoff

omit [FiniteDimensional 𝕜 E] in
/-- Operator-form zero compression implies the corresponding sesquilinear
block vanishes.
-/
theorem inner_map_eq_zero_of_hasZeroCompression
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (H : E →ₗ[𝕜] E)
    (hzero : HasZeroCompression U H)
    {u u' : E} (hu : u ∈ U) (hu' : u' ∈ U) : ⟪u, H u'⟫_𝕜 = 0 := by
  have hblock := LinearMap.congr_fun hzero u'
  have hproj : U.starProjection (H u') = 0 := by
    simpa [HasZeroCompression, projection,
      Submodule.starProjection_eq_self_iff.mpr hu'] using hblock
  calc
    ⟪u, H u'⟫_𝕜 = ⟪U.starProjection u, H u'⟫_𝕜 := by
      rw [Submodule.starProjection_eq_self_iff.mpr hu]
    _ = ⟪u, U.starProjection (H u')⟫_𝕜 :=
      U.inner_starProjection_left_eq_right u (H u')
    _ = 0 := by rw [hproj, inner_zero_right]

omit [FiniteDimensional 𝕜 E] in
/-- Both diagonal sesquilinear blocks vanish for an off-diagonal map.
-/
theorem inner_blocks_eq_zero_of_isOffDiagonal
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (H : E →ₗ[𝕜] E)
    (hoff : IsOffDiagonal U H) :
    (∀ u ∈ U, ∀ u' ∈ U, ⟪u, H u'⟫_𝕜 = 0) ∧
      (∀ w ∈ Uᗮ, ∀ w' ∈ Uᗮ, ⟪w, H w'⟫_𝕜 = 0) := by
  constructor
  · intro u hu u' hu'
    exact inner_map_eq_zero_of_hasZeroCompression U H
      (hasZeroCompression_of_isOffDiagonal U H hoff) hu hu'
  · intro w hw w' hw'
    exact inner_map_eq_zero_of_hasZeroCompression Uᗮ H
      (hasZeroCompression_of_isOffDiagonal Uᗮ H
        (isOffDiagonal_orthogonal U H hoff)) hw hw'

end DavisKahan.FiniteDimensional
end TauCeti
