/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.TanTheta.UnboundedSpectrum

/-!
# Graph-angle form of the unbounded tangent theorem

The per-vector tangent estimate controls the ratio between the complementary
and exact projection components of every trial vector.  To turn that ratio
into a bounded tangent operator, one must select the transverse branch: the
exact coordinate projection from the trial subspace onto the exact subspace
must be a bounded linear equivalence.

This module packages that transversality datum explicitly.  It constructs the
bounded graph angular map, proves that its graph is exactly the trial
subspace, and transfers the unbounded genuine-spectrum vector estimate to an
operator-norm tangent bound.

No continuation theorem is used here.  A later branch-continuation result can
construct the coordinate equivalence and then apply these theorems directly.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace TanTheta


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Proof-carrying transverse coordinates for a trial subspace `Z` over an
exact subspace `V`.  The coordinate equivalence is the restriction of the
orthogonal projection onto `V`. -/
structure TrialExactCoordinates
    (Z V : Submodule ℂ H) [V.HasOrthogonalProjection] where
  toExact : Z ≃L[ℂ] V
  toExact_apply (z : Z) :
    (toExact z : H) = V.starProjection (z : H)

namespace TrialExactCoordinates

variable {Z V : Submodule ℂ H} [V.HasOrthogonalProjection]

/-- The complementary coordinate of the trial graph. -/
noncomputable def angularMap
    (C : TrialExactCoordinates Z V) : V →L[ℂ] Vᗮ :=
  (Vᗮ.starProjection.codRestrict Vᗮ
      (fun x => Vᗮ.starProjection_apply_mem x)) ∘L
    Z.subtypeL ∘L C.toExact.symm.toContinuousLinearMap

omit [CompleteSpace H] in
/-- The angular coordinate is the complementary projection of the unique
trial vector with the prescribed exact coordinate. -/
theorem angularMap_apply_coe
    (C : TrialExactCoordinates Z V) (v : V) :
    (C.angularMap v : H) =
      (C.toExact.symm v : H) -
        V.starProjection (C.toExact.symm v : H) := by
  change Vᗮ.starProjection (C.toExact.symm v : H) = _
  exact V.starProjection_orthogonal_apply _

omit [CompleteSpace H] in
/-- Reconstruct the unique trial vector from its exact and angular
coordinates. -/
theorem exact_add_angularMap
    (C : TrialExactCoordinates Z V) (v : V) :
    (v : H) + (C.angularMap v : H) =
      (C.toExact.symm v : H) := by
  have hproj :
      V.starProjection (C.toExact.symm v : H) = (v : H) := by
    rw [← C.toExact_apply (C.toExact.symm v)]
    exact congrArg (fun w : V => (w : H)) (C.toExact.apply_symm_apply v)
  rw [C.angularMap_apply_coe, hproj]
  abel

/-- The graph embedding associated with the transverse trial coordinates. -/
noncomputable def graphEmbedding
    (C : TrialExactCoordinates Z V) : V →L[ℂ] H :=
  V.subtypeL + Vᗮ.subtypeL ∘L C.angularMap

omit [CompleteSpace H] in
/-- The graph embedding is the inverse coordinate map viewed in the ambient
Hilbert space. -/
theorem graphEmbedding_apply
    (C : TrialExactCoordinates Z V) (v : V) :
    C.graphEmbedding v = (C.toExact.symm v : H) := by
  change (v : H) + (C.angularMap v : H) = _
  exact C.exact_add_angularMap v

omit [CompleteSpace H] in
/-- The graph of the angular coordinate map is exactly the trial subspace. -/
theorem range_graphEmbedding
    (C : TrialExactCoordinates Z V) :
    LinearMap.range C.graphEmbedding.toLinearMap = Z := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    change C.graphEmbedding v ∈ Z
    rw [C.graphEmbedding_apply]
    exact (C.toExact.symm v).property
  · intro x hx
    let z : Z := ⟨x, hx⟩
    refine ⟨C.toExact z, ?_⟩
    change C.graphEmbedding (C.toExact z) = x
    calc
      C.graphEmbedding (C.toExact z) = (C.toExact.symm (C.toExact z) : H) :=
        C.graphEmbedding_apply _
      _ = x := congrArg (fun w : Z => (w : H))
        (C.toExact.symm_apply_apply z)

omit [CompleteSpace H] in
/-- A per-vector tangent estimate on the trial subspace gives an operator-norm
bound for its graph angular map. -/
theorem norm_angularMap_le_div
    (C : TrialExactCoordinates Z V)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hvec : ∀ x : H, ∀ _hx : x ∈ Z,
      δ * ‖x - V.starProjection x‖ ≤
        ρ * ‖V.starProjection x‖) :
    ‖C.angularMap‖ ≤ ρ / δ := by
  have hdiv0 : 0 ≤ ρ / δ := div_nonneg hρ0 hδ.le
  refine ContinuousLinearMap.opNorm_le_bound _ hdiv0 fun v => ?_
  let z : Z := C.toExact.symm v
  have hz := hvec (z : H) z.property
  have hproj : V.starProjection (z : H) = (v : H) := by
    rw [← C.toExact_apply z]
    exact congrArg (fun w : V => (w : H)) (C.toExact.apply_symm_apply v)
  have hang : (C.angularMap v : H) =
      (z : H) - V.starProjection (z : H) := by
    exact C.angularMap_apply_coe v
  have hraw : δ * ‖C.angularMap v‖ ≤ ρ * ‖v‖ := by
    simpa [hang, hproj] using hz
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hδ).2
  simpa [mul_comm] using hraw

omit [CompleteSpace H] in
/-- Multiplicative form of the graph-angle tangent bound. -/
theorem mul_norm_angularMap_le
    (C : TrialExactCoordinates Z V)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hvec : ∀ x : H, ∀ _hx : x ∈ Z,
      δ * ‖x - V.starProjection x‖ ≤
        ρ * ‖V.starProjection x‖) :
    δ * ‖C.angularMap‖ ≤ ρ := by
  have hnorm := C.norm_angularMap_le_div hδ hρ0 hvec
  calc
    δ * ‖C.angularMap‖ ≤ δ * (ρ / δ) :=
      mul_le_mul_of_nonneg_left hnorm hδ.le
    _ = ρ := by field_simp

end TrialExactCoordinates

/-- Genuine-spectrum unbounded tangent theorem in graph-angle operator form.

The exact target is the orthogonal complement of the interval spectral range.
The trial block supplies the exterior Ritz spectrum and bounded residual.  The
coordinate datum selects the transverse graph branch. -/
theorem tanTheta_unbounded_graphAngle_trialBlock
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : BoundedCompressionTrialBlock A Z)
    {α β δ : ℝ} (hαβ : α ≤ β) (hδ : 0 < δ)
    (hZspec : ∀ x ∈ spectrum ℝ D.operator,
      x ≤ α - δ ∨ β + δ ≤ x)
    (C : TrialExactCoordinates Z
      (selfAdjointSpectralSubspace A hA (Set.Icc α β)
        measurableSet_Icc)ᗮ) :
    δ * ‖C.angularMap‖ ≤ ‖D.residual‖ := by
  let W := selfAdjointSpectralSubspace A hA (Set.Icc α β)
    measurableSet_Icc
  have hvec : ∀ x : H, ∀ hx : x ∈ Z,
      δ * ‖x - Wᗮ.starProjection x‖ ≤
        ‖D.residual‖ * ‖Wᗮ.starProjection x‖ := by
    exact tanTheta_unbounded_exactSpectralIcc_trialBlock
      A hA D hαβ hδ hZspec
  exact C.mul_norm_angularMap_le hδ (norm_nonneg D.residual) hvec

end TanTheta
end DavisKahan
end TauCeti
