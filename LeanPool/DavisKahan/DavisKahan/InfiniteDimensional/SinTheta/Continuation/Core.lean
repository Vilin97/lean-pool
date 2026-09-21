/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.DoubleAngle
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SpectraBridge.DirectRotationAPI
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ResolventOperator
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Core -/

open TauCeti.DavisKahan.Angle


/-!
# Spectral projection continuation and branch selection

Literature writeup: local TeX, Sections 15 and 20--24.  The infinite-
dimensional tangent theorems require selecting the perturbed spectral
component by a norm-continuous path of Riesz projections.
-/


/-! ## Weak-agent execution plan: continuation

Split this module into a local analytic theorem and a global topological
argument.

Local theorem: under a fixed separating contour and a uniform resolvent bound,
prove norm continuity of the Riesz projection from the second resolvent
identity.  State a quantitative Lipschitz estimate; continuity is its
corollary.

Global theorem: for a continuous path of projections `P t`, prove rank or
component constancy.  In finite dimension use `‖P-Q‖ < 1` to construct an
isomorphism between the ranges.  In infinite dimension use the same estimate
to obtain the graph representation.  Cover the parameter interval by local
neighborhoods and use connectedness/clopen reasoning.

Keep the spectral identification separate: show the continued Riesz
projection equals the requested spectral projection only after the path
argument.  This prevents a cycle between continuity and spectral selection.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Linear perturbation path. -/
def operatorPath (A H : E →L[𝕜] E) (t : ℝ) : E →L[𝕜] E :=
  A + (t : 𝕜) • H


omit [CompleteSpace E] in
/-- Difference of two points on the affine perturbation path. -/
theorem operatorPath_sub
    (A H : E →L[𝕜] E) (t u : ℝ) :
    operatorPath A H t - operatorPath A H u =
      ((t - u : ℝ) : 𝕜) • H := by
  calc
    operatorPath A H t - operatorPath A H u =
        (t : 𝕜) • H - (u : 𝕜) • H := by
      simp only [operatorPath]
      abel
    _ = ((t : 𝕜) - (u : 𝕜)) • H := by
      rw [sub_smul]
    _ = ((t - u : ℝ) : 𝕜) • H := by
      rw [RCLike.ofReal_sub]

omit [CompleteSpace E] in
/-- Exact norm of an affine-path increment. -/
theorem norm_operatorPath_sub
    (A H : E →L[𝕜] E) (t u : ℝ) :
    ‖operatorPath A H t - operatorPath A H u‖ = ‖t - u‖ * ‖H‖ := by
  rw [operatorPath_sub, norm_smul, RCLike.norm_ofReal, Real.norm_eq_abs]

omit [CompleteSpace E] in
/-- Quantitative path-parameter estimate for the resolvent at one fixed
spectral parameter.  Under a uniform bound `M` at two path values, the
resolvent varies at most linearly in `|t-u|`.

This is the analytic operator estimate to be integrated along a separating
contour in the proof of `continuous_continuedProjection`. -/
theorem norm_resolventOperator_operatorPath_sub_le
    (A H : E →L[𝕜] E) (z : 𝕜) (M : ℝ) (t u : ℝ)
    (ht : InResolventSet (operatorPath A H t) z)
    (hu : InResolventSet (operatorPath A H u) z)
    (hMt : ‖resolventOperator (operatorPath A H t) z‖ ≤ M)
    (hMu : ‖resolventOperator (operatorPath A H u) z‖ ≤ M) :
    ‖resolventOperator (operatorPath A H t) z -
        resolventOperator (operatorPath A H u) z‖ ≤
      M ^ 2 * ‖H‖ * ‖t - u‖ := by
  calc
    ‖resolventOperator (operatorPath A H t) z -
        resolventOperator (operatorPath A H u) z‖ ≤
      M * ‖operatorPath A H u - operatorPath A H t‖ * M :=
        norm_resolventOperator_sub_le_of_bounds
          (operatorPath A H u) (operatorPath A H t) hu ht hMu hMt
    _ = M * (‖u - t‖ * ‖H‖) * M := by
      rw [norm_operatorPath_sub]
    _ = M ^ 2 * ‖H‖ * ‖t - u‖ := by
      rw [norm_sub_rev]
      ring

omit [CompleteSpace E] in
/-- Set-uniform version of the fixed-parameter resolvent estimate. -/
theorem norm_resolventOperator_operatorPath_sub_le_of_uniform_bound
    (A H : E →L[𝕜] E) (z : 𝕜) (M : ℝ) (I : Set ℝ)
    (hmem : ∀ t ∈ I, InResolventSet (operatorPath A H t) z)
    (hbound : ∀ t ∈ I,
      ‖resolventOperator (operatorPath A H t) z‖ ≤ M)
    {t u : ℝ} (ht : t ∈ I) (hu : u ∈ I) :
    ‖resolventOperator (operatorPath A H t) z -
        resolventOperator (operatorPath A H u) z‖ ≤
      M ^ 2 * ‖H‖ * ‖t - u‖ :=
  norm_resolventOperator_operatorPath_sub_le A H z M t u
    (hmem t ht) (hmem u hu) (hbound t ht) (hbound u hu)


/-! ## Complex spectral-distance specialization -/

section ComplexResolventDistance

variable {Hc : Type*} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
  [CompleteSpace Hc]

/-- Along a complex self-adjoint affine path, a common positive distance from
one spectral parameter to every path spectrum supplies the endpoint
resolvent-set and norm hypotheses automatically. -/
theorem norm_resolventOperator_operatorPath_sub_le_of_spectral_distance
    (A H : Hc →L[ℂ] Hc) (z : ℂ) (delta : ℝ) (hdelta : 0 < delta)
    (I : Set ℝ)
    (hself : ∀ t ∈ I, (operatorPath A H t).IsSymmetric)
    (hsep : ∀ t ∈ I, ∀ lam ∈ realSpectrum (operatorPath A H t),
      delta ≤ ‖z - (lam : ℂ)‖)
    {t u : ℝ} (ht : t ∈ I) (hu : u ∈ I) :
    ‖resolventOperator (operatorPath A H t) z -
        resolventOperator (operatorPath A H u) z‖ ≤
      delta⁻¹ ^ 2 * ‖H‖ * ‖t - u‖ := by
  obtain ⟨htmem, htbound⟩ :=
    complex_inResolventSet_and_norm_resolvent_le_inv_distance
      (operatorPath A H t) (hself t ht) z delta hdelta (hsep t ht)
  obtain ⟨humem, hubound⟩ :=
    complex_inResolventSet_and_norm_resolvent_le_inv_distance
      (operatorPath A H u) (hself u hu) z delta hdelta (hsep u hu)
  exact norm_resolventOperator_operatorPath_sub_le A H z delta⁻¹ t u
    htmem humem htbound hubound

end ComplexResolventDistance

/-- `P` and `Q` are joined by a continuous path of orthogonal projections, so they lie in
the same connected component of the projection set. -/
def SameProjectionComponent (P Q : E →L[𝕜] E) : Prop :=
  ∃ path : ℝ → E →L[𝕜] E,
    ContinuousOn path (Set.Icc (0 : ℝ) 1) ∧ path 0 = P ∧ path 1 = Q ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, IsOrthogonalProjection (path t)


/-! ## Close complex orthogonal projections

The direct-rotation package turns the local geometric step in spectral
continuation into a short theorem.  A projection supplied abstractly as an
idempotent symmetric continuous linear map is first identified with the
orthogonal projection onto its fixed-point subspace.  Norm closeness then says
those two fixed-point subspaces are acute, so their canonical direct rotation
is the required global unitary intertwiner.
-/

section ComplexCloseProjections

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Fixed-point subspace of a bounded operator.  For an orthogonal projection
this is its range, but the kernel presentation gives closedness and the
orthogonal-projection instance without a separate closed-range theorem. -/
private noncomputable def projectionFixedSpace
    (P : H →L[ℂ] H) : Submodule ℂ H :=
  (P - 1).ker

private noncomputable instance projectionFixedSpaceComplete
    (P : H →L[ℂ] H) : CompleteSpace (projectionFixedSpace P) :=
  (P - 1).isClosed_ker.completeSpace_coe

private noncomputable instance projectionFixedSpaceHasOrthogonalProjection
    (P : H →L[ℂ] H) :
    (projectionFixedSpace P).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

omit [CompleteSpace H] in
private theorem mem_projectionFixedSpace_iff
    (P : H →L[ℂ] H) (x : H) :
    x ∈ projectionFixedSpace P ↔ P x = x := by
  change (P - 1) x = 0 ↔ P x = x
  simp only [sub_apply, one_apply_eq_self, sub_eq_zero]

omit [CompleteSpace H] in
private theorem projection_apply_idempotent
    (P : H →L[ℂ] H) (hP : IsOrthogonalProjection P) (x : H) :
    P (P x) = P x := by
  have h := congrArg (fun T : H →L[ℂ] H => T x) hP.1
  simpa only [ContinuousLinearMap.comp_apply] using h

/-- An abstract orthogonal projection is the canonical orthogonal projection
onto its fixed-point/range subspace. -/
private theorem projection_fixedSpace_eq
    (P : H →L[ℂ] H) (hP : IsOrthogonalProjection P) :
    Submodule.starProjection (projectionFixedSpace P) = P := by
  ext x
  apply (projectionFixedSpace P).eq_starProjection_of_mem_of_inner_eq_zero
  · rw [mem_projectionFixedSpace_iff]
    exact projection_apply_idempotent P hP x
  · intro y hy
    have hyfix : P y = y :=
      (mem_projectionFixedSpace_iff P y).mp hy
    have hsym : ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ :=
      hP.2 x y
    rw [inner_sub_left]
    calc
      ⟪x, y⟫_ℂ - ⟪P x, y⟫_ℂ = ⟪x, y⟫_ℂ - ⟪x, P y⟫_ℂ := by rw [hsym]
      _ = 0 := by rw [hyfix, sub_self]

/-- Norm-close complex orthogonal projections have unitarily equivalent ranges
and complements.  The unitary is the canonical acute direct rotation of their
fixed-point subspaces. -/
theorem range_equiv_of_projection_norm_lt_one
    (P Q : H →L[ℂ] H)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hclose : ‖P - Q‖ < 1) :
    ∃ W : H →L[ℂ] H, TauCeti.LinearPMap.IsUnitaryOperator W ∧ W ∘L P = Q ∘L W := by
  let U : Submodule ℂ H := projectionFixedSpace P
  let V : Submodule ℂ H := projectionFixedSpace Q
  have hPU : U.starProjection = P := by
    simpa only [U] using projection_fixedSpace_eq P hP
  have hQV : V.starProjection = Q := by
    simpa only [V] using projection_fixedSpace_eq Q hQ
  have hacute : IsUniformlyAcute U V := by
    change ‖U.starProjection - V.starProjection‖ < 1
    rw [hPU, hQV]
    exact hclose
  let W : H →L[ℂ] H := complexDirectRotation U V hacute
  refine ⟨W, ?_, ?_⟩
  · simpa only [W] using complexDirectRotation_unitary U V hacute
  · have hintertwine := complexDirectRotation_intertwines U V hacute
    rw [hPU, hQV] at hintertwine
    simpa only [W] using hintertwine

end ComplexCloseProjections

end DavisKahanExt
end TauCeti
