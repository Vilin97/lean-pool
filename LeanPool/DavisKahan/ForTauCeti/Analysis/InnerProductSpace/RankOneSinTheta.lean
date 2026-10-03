/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

/-
Staged for Tau Ceti: additions to the principal-angle API.
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.Frobenius

/-! # The single-angle case: sine norms of a line against a subspace

When the source subspace is a line `𝕜 ∙ v`, the sine cross-projection
`sinThetaMap (𝕜 ∙ v) W = P_{Wᗮ} P_{𝕜∙v}` is the rank-one map
`x ↦ ⟪v, x⟫ • P_{Wᗮ} v`.  A rank-one operator has a single nonzero singular
value, so *every* normalized unitarily invariant norm of it is the same number
— here `‖P_{Wᗮ} v‖`, the sine of the one principal angle.

That collapse is what makes the single-vector Davis--Kahan statements
unambiguous: the paper writes `sin Θ(v̂, v)` without saying which norm, and for
`d = 1` it does not matter.  The two lemmas below prove it for the two norms the
statements actually use, directly from the rank-one formula rather than through
singular-value theory.

## Main results

* `TauCeti.sinThetaMap_span_singleton_apply`: the rank-one formula.
* `TauCeti.norm_starProjection_orthogonal_sq`: `‖P_{Wᗮ} v‖² = 1 - ‖P_W v‖²`.
* `TauCeti.opNorm_sinThetaMap_span_singleton` and
  `TauCeti.sinThetaFrobenius_span_singleton`: both norms equal `‖P_{Wᗮ} v‖`.
-/

@[expose] public section

open Module (finrank)
open scoped InnerProductSpace BigOperators

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]

omit [FiniteDimensional 𝕜 E] in
/-- **The single-angle sine map is rank one.**  On the line `𝕜 ∙ v` with `v` a
unit vector, `sinThetaMap` sends `x` to `⟪v, x⟫ • P_{Wᗮ} v`. -/
theorem sinThetaMap_span_singleton_apply {v : E} (hv : ‖v‖ = 1) (x : E) :
    sinThetaMap (𝕜 ∙ v) W x = ⟪v, x⟫_𝕜 • projection Wᗮ v := by
  have hproj : projection (𝕜 ∙ v) x = ⟪v, x⟫_𝕜 • v := by
    change (𝕜 ∙ v).starProjection x = _
    rw [Submodule.starProjection_singleton, hv]
    simp
  change projection Wᗮ (projection (𝕜 ∙ v) x) = _
  rw [hproj, map_smul]

omit [FiniteDimensional 𝕜 E] in
/-- Pythagoras for a projector: the complementary component of a unit vector has
squared norm `1 - ‖P_W v‖²`. -/
theorem norm_starProjection_orthogonal_sq {v : E} (hv : ‖v‖ = 1) :
    ‖projection Wᗮ v‖ ^ 2 = 1 - ‖projection W v‖ ^ 2 := by
  have hsplit : projection W v + projection Wᗮ v = v := by
    change W.starProjection v + Wᗮ.starProjection v = v
    simp
  have hperp : ⟪projection W v, projection Wᗮ v⟫_𝕜 = 0 :=
    Submodule.inner_right_of_mem_orthogonal (W.starProjection_apply_mem v)
      (Wᗮ.starProjection_apply_mem v)
  have hkey := @norm_add_sq 𝕜 _ _ _ _ (projection W v) (projection Wᗮ v)
  rw [hsplit, hv, hperp] at hkey
  simp only [map_zero, mul_zero, add_zero, one_pow] at hkey
  linarith

/-- **The operator norm of the single-angle sine map** is the length of the
complementary component. -/
theorem opNorm_sinThetaMap_span_singleton {v : E} (hv : ‖v‖ = 1) :
    ‖(sinThetaMap (𝕜 ∙ v) W).toContinuousLinearMap‖ = ‖projection Wᗮ v‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_) ?_
  · rw [LinearMap.coe_toContinuousLinearMap', sinThetaMap_span_singleton_apply hv,
      norm_smul, mul_comm]
    have hcs : ‖⟪v, x⟫_𝕜‖ ≤ ‖x‖ := by
      have hle := norm_inner_le_norm (𝕜 := 𝕜) v x
      rwa [hv, one_mul] at hle
    exact mul_le_mul_of_nonneg_left hcs (norm_nonneg _)
  · -- The bound is attained at `v` itself.
    have h := (sinThetaMap (𝕜 ∙ v) W).toContinuousLinearMap.le_opNorm v
    rw [LinearMap.coe_toContinuousLinearMap', sinThetaMap_span_singleton_apply hv,
      norm_smul, hv, mul_one] at h
    have hvv : ‖⟪v, v⟫_𝕜‖ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hv]
      simp
    rwa [hvv, one_mul] at h

/-- **The Frobenius norm of the single-angle sine map** is the same number: a
rank-one operator has one singular value, so the two norms agree. -/
theorem sinThetaFrobenius_span_singleton {v : E} (hv : ‖v‖ = 1) :
    sinThetaFrobenius (𝕜 ∙ v) W = ‖projection Wᗮ v‖ := by
  classical
  rw [sinThetaFrobenius_eq,
    UnitarilyInvariantSeminorm.frobenius_apply_basis (𝕜 := 𝕜) (E := E) _ rfl
      (stdOrthonormalBasis 𝕜 E)]
  have hcol : ∀ i, ‖sinThetaMap (𝕜 ∙ v) W (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 =
      ‖⟪v, stdOrthonormalBasis 𝕜 E i⟫_𝕜‖ ^ 2 * ‖projection Wᗮ v‖ ^ 2 := by
    intro i
    rw [sinThetaMap_span_singleton_apply hv, norm_smul, mul_pow]
  rw [Finset.sum_congr rfl fun i _ => hcol i, ← Finset.sum_mul]
  -- Parseval: the coefficients of the unit vector `v` square-sum to `1`.
  rw [show (∑ i, ‖⟪v, stdOrthonormalBasis 𝕜 E i⟫_𝕜‖ ^ 2) = 1 by
    rw [OrthonormalBasis.sum_sq_norm_inner_left (stdOrthonormalBasis 𝕜 E) v, hv,
      one_pow], one_mul,
    Real.sqrt_sq (norm_nonneg _)]

end TauCeti
