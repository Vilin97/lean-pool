/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseVariationalOperator

@[expose] public section

/-!
# Recovering the source's transverse coordinates

The moving plane with normal `(F⁻¹)* m₀` is exactly the image under `F` of
the fixed plane `m₀⊥`.  Orthogonal projection gives a bounded coordinate map,
and on the moving plane its reconstruction is the identity.  These are
coefficient identities, not assumptions about a differential inverse.
-/

noncomputable section

namespace EulerTransverseFrameCoordinates

open InnerProductSpace ContinuousLinearMap

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The fixed reference transverse plane. -/
abbrev referencePlane (m₀ : E) : Submodule ℝ E := (ℝ ∙ m₀)ᗮ

/-- The actual pulled-back normal used by the packet construction. -/
def movingNormal (F : E ≃L[ℝ] E) (m₀ : E) : E := F.symm.toContinuousLinearMap.adjoint m₀

/-- Bounded recovery of fixed-plane coordinates from a physical displacement. -/
def coordinates (F : E ≃L[ℝ] E) (m₀ : E) : E →L[ℝ] referencePlane m₀ :=
  (referencePlane m₀).orthogonalProjectionOnto.comp F.symm.toContinuousLinearMap

/-- Moving tangency is exactly fixed-plane membership after applying `F⁻¹`. -/
theorem tangent_iff (F : E ≃L[ℝ] E) (m₀ η : E) :
    ⟪movingNormal F m₀, η⟫_ℝ = 0 ↔ F.symm η ∈ referencePlane m₀ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  unfold movingNormal
  rw [adjoint_inner_left]
  rfl

/-- Reconstructing a tangent displacement from its recovered coordinates is exact. -/
theorem reconstruct (F : E ≃L[ℝ] E) (m₀ η : E)
    (hη : ⟪movingNormal F m₀, η⟫_ℝ = 0) :
    F (coordinates F m₀ η : E) = η := by
  have hm : F.symm η ∈ referencePlane m₀ := (tangent_iff F m₀ η).1 hη
  have hp := (referencePlane m₀).orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨F.symm η, hm⟩ : referencePlane m₀)
  change F ((referencePlane m₀).orthogonalProjectionOnto (F.symm η) : E) = η
  rw [hp]
  exact F.apply_symm_apply η

omit [CompleteSpace E] in
/-- The coordinate map is a left inverse to `F` restricted to the reference plane. -/
theorem coordinates_leftInverse (F : E ≃L[ℝ] E) (m₀ : E) (ξ : referencePlane m₀) :
    coordinates F m₀ (F (ξ : E)) = ξ := by
  change (referencePlane m₀).orthogonalProjectionOnto (F.symm (F (ξ : E))) = ξ
  rw [F.symm_apply_apply]
  exact (referencePlane m₀).orthogonalProjectionOnto_mem_subspace_eq_self ξ

omit [CompleteSpace E] in
/-- The coordinate map has the expected polynomial bound from the inverse frame. -/
theorem coordinates_norm (F : E ≃L[ℝ] E) (m₀ η : E) :
    ‖coordinates F m₀ η‖ ≤ ‖F.symm.toContinuousLinearMap‖ * ‖η‖ := by
  exact ((referencePlane m₀).norm_orthogonalProjectionOnto_apply_le (F.symm η)).trans
    (F.symm.toContinuousLinearMap.le_opNorm η)

/-- Any orthonormal identification with the fixed plane gives the source's `R⊥` coordinates. -/
def frameCoordinates (F : E ≃L[ℝ] E) (m₀ : E)
    (R : U ≃ₗᵢ[ℝ] referencePlane m₀) : E →L[ℝ] U :=
  R.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (coordinates F m₀)

/-- The full source reconstruction `η = F R⊥ ξ` follows from moving tangency. -/
theorem frame_reconstruct (F : E ≃L[ℝ] E) (m₀ η : E)
    (R : U ≃ₗᵢ[ℝ] referencePlane m₀) (hη : ⟪movingNormal F m₀, η⟫_ℝ = 0) :
    F (R (frameCoordinates F m₀ R η) : E) = η := by
  change F (R (R.symm (coordinates F m₀ η)) : E) = η
  rw [R.apply_symm_apply]
  exact reconstruct F m₀ η hη

omit [CompleteSpace E] in
/-- Passing to an orthonormal coordinate basis has no extra norm cost. -/
theorem frameCoordinates_norm (F : E ≃L[ℝ] E) (m₀ η : E)
    (R : U ≃ₗᵢ[ℝ] referencePlane m₀) :
    ‖frameCoordinates F m₀ R η‖ ≤ ‖F.symm.toContinuousLinearMap‖ * ‖η‖ := by
  change ‖R.symm (coordinates F m₀ η)‖ ≤ _
  rw [R.symm.norm_map]
  exact coordinates_norm F m₀ η

section Paths

variable {X : Type*} [TopologicalSpace X]

/-- Applying a continuous inverse-frame path produces actual continuous
transverse coordinates, not separate incompatible pointwise choices. -/
def coordinatePath (m₀ : E) (R : U ≃ₗᵢ[ℝ] referencePlane m₀)
    (A : C(X, E →L[ℝ] E)) (η : C(X, E)) : C(X, U) :=
  ⟨fun t => R.symm ((referencePlane m₀).orthogonalProjectionOnto (A t (η t))),
    R.symm.continuous.comp ((referencePlane m₀).orthogonalProjectionOnto.continuous.comp
      (A.continuous.clm_apply η.continuous))⟩

/-- The recovered continuous coordinates reconstruct every tangent displacement. -/
theorem coordinatePath_reconstruct (m₀ : E) (R : U ≃ₗᵢ[ℝ] referencePlane m₀)
    (F : X → E ≃L[ℝ] E) (A : C(X, E →L[ℝ] E))
    (hA : ∀ t, A t = (F t).symm.toContinuousLinearMap) (η : C(X, E))
    (hη : ∀ t, ⟪movingNormal (F t) m₀, η t⟫_ℝ = 0) (t : X) :
    F t (R (coordinatePath m₀ R A η t) : E) = η t := by
  change F t (R (R.symm ((referencePlane m₀).orthogonalProjectionOnto
    (A t (η t)))) : E) = η t
  rw [hA t]
  exact frame_reconstruct (F t) m₀ (η t) R (hη t)

omit [CompleteSpace E] in
/-- Zero endpoint displacements give zero endpoint coordinates. -/
theorem coordinatePath_zero_at (m₀ : E) (R : U ≃ₗᵢ[ℝ] referencePlane m₀)
    (A : C(X, E →L[ℝ] E)) (η : C(X, E)) (t : X) (hη : η t = 0) :
    coordinatePath m₀ R A η t = 0 := by
  change R.symm ((referencePlane m₀).orthogonalProjectionOnto (A t (η t))) = 0
  simp only [hη, map_zero]

omit [CompleteSpace E] in
/-- Pointwise coordinate control only pays the actual inverse-frame norm. -/
theorem coordinatePath_norm (m₀ : E) (R : U ≃ₗᵢ[ℝ] referencePlane m₀)
    (A : C(X, E →L[ℝ] E)) (η : C(X, E)) (t : X) :
    ‖coordinatePath m₀ R A η t‖ ≤ ‖A t‖ * ‖η t‖ := by
  change ‖R.symm ((referencePlane m₀).orthogonalProjectionOnto (A t (η t)))‖ ≤ _
  rw [R.symm.norm_map]
  exact ((referencePlane m₀).norm_orthogonalProjectionOnto_apply_le (A t (η t))).trans
    ((A t).le_opNorm (η t))

end Paths

end EulerTransverseFrameCoordinates
