/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransport

/-!
# Reflections survive a change of scalar field

`Submodule.reflection K x = 2 • K.starProjection x - x`, and the `2 •` is an
`ℕ`-action: a reflection is built from the orthogonal projection and the additive
group alone.  `TauCeti.ScalarTransport` changes neither, so a reflection
transports to the reflection of the transported subspace, and so does the image
of a subspace under one.

This is what carries the Davis--Kahan double-angle objects — the mirror image of
`U` in `V` and the projector differences built from it — across a change of
scalar field.

## Main results

* `TauCeti.ScalarTransport.reflection_of`.
* `TauCeti.ScalarTransport.submodule_map_reflection`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none**.
-/

public section

namespace TauCeti
namespace ScalarTransport

universe u w v

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The reflection of a transported subspace is the transported reflection. -/
theorem reflection_of (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] (x : E) :
    (submodule (e := e) S).reflection (of (e := e) x) =
      of (e := e) (S.reflection x) := by
  rw [Submodule.reflection_apply, Submodule.reflection_apply, starProjection_of]
  rfl

/-- The image of a subspace under a reflection transports.

`@[simp]` because the transported reflection image is the normal form: every
consumer wants the two transports pushed inside, not a reflection of a transport. -/
@[simp] theorem submodule_map_reflection (S T : Submodule 𝕜 E)
    [S.HasOrthogonalProjection] [T.HasOrthogonalProjection] :
    submodule (e := e) (S.map (T.reflection.toLinearEquiv : E →ₗ[𝕜] E)) =
      (submodule (e := e) S).map
        (((submodule (e := e) T).reflection.toLinearEquiv :
          ScalarTransport e E →ₗ[𝕂] ScalarTransport e E)) := by
  ext x
  simp only [mem_submodule, Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, hux⟩
    refine ⟨of (e := e) u, (mem_submodule (e := e)).mpr hu, ?_⟩
    have h : (submodule (e := e) T).reflection (of (e := e) u) =
        of (e := e) (T.reflection u) := reflection_of (e := e) T u
    exact h.trans (congrArg (of (e := e)) hux)
  · rintro ⟨w, hw, hwx⟩
    refine ⟨out (e := e) w, (mem_submodule (e := e)).mp hw, ?_⟩
    have h : (submodule (e := e) T).reflection w =
        of (e := e) (T.reflection (out (e := e) w)) :=
      reflection_of (e := e) T (out (e := e) w)
    exact congrArg (out (e := e)) (h.symm.trans hwx)

/-- The projector onto the mirror image transports. -/
theorem starProjection_map_reflection_of (S T : Submodule 𝕜 E)
    [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]
    [(S.map (T.reflection.toLinearEquiv : E →ₗ[𝕜] E)).HasOrthogonalProjection]
    [((submodule (e := e) S).map
      ((submodule (e := e) T).reflection.toLinearEquiv :
        ScalarTransport e E →ₗ[𝕂] ScalarTransport e E)).HasOrthogonalProjection]
    (x : E) :
    ((submodule (e := e) S).map
        ((submodule (e := e) T).reflection.toLinearEquiv :
          ScalarTransport e E →ₗ[𝕂] ScalarTransport e E)).starProjection
        (of (e := e) x) =
      of (e := e) ((S.map (T.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection x) := by
  rw [Submodule.starProjection_congr_apply
    (submodule_map_reflection (e := e) S T).symm (of (e := e) x)]
  exact starProjection_of (e := e) _ x

end ScalarTransport
end TauCeti
