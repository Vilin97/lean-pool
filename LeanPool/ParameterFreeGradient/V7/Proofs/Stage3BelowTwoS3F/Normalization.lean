/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.Ledger

/-!
Convexity, coordinate gradients, and lower bounds survive affine oracle normalization.
-/

namespace V7.Stage3BelowTwoS3F

theorem normalized_coordinateGradient (inst : PositiveInstance p d x0)
    (c : Point d) {M D : ℝ} (hM : 0 < M) (hD : 0 < D) :
    O3.IsCoordinateGradient (normalizedPairOracle c M D inst.oracle).value
      (normalizedPairOracle c M D inst.oracle).gradient := by
  intro y
  have hinner : HasFDerivAt (fun z : Point d => c + D • z)
      (D • ContinuousLinearMap.id ℝ (Point d)) y := by fun_prop
  have hbase := (inst.coordinateGradient (c + D • y)).1.hasFDerivAt
  have hcomp := hbase.comp y hinner
  have hscaled := (hcomp.sub_const (inst.oracle.value c)).const_smul
    (1 / (M * D ^ (2 : ℕ)))
  have hfun : (fun z : Point d =>
      (inst.oracle.value (c + D • z) - inst.oracle.value c) /
        (M * D ^ (2 : ℕ))) =
      (1 / (M * D ^ (2 : ℕ))) •
        (fun z : Point d => inst.oracle.value (c + D • z) - inst.oracle.value c) := by
    funext z
    simp [div_eq_mul_inv, smul_eq_mul, mul_comm]
  constructor
  · dsimp [normalizedPairOracle]
    rw [hfun]
    simpa [Function.comp_apply] using hscaled.differentiableAt
  · intro h
    dsimp [normalizedPairOracle]
    have heq := congrArg (fun T : Point d →L[ℝ] ℝ => T h) hscaled.fderiv
    rw [hfun]
    rw [show fderiv ℝ
      ((1 / (M * D ^ (2 : ℕ))) •
        (fun z : Point d => inst.oracle.value (c + D • z) - inst.oracle.value c)) y h =
      ((1 / (M * D ^ (2 : ℕ))) • fderiv ℝ inst.oracle.value (c + D • y) ∘L
        (D • ContinuousLinearMap.id ℝ (Point d))) h by
          simpa [Function.comp_apply] using heq]
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [(inst.coordinateGradient (c + D • y)).2]
    rw [O3.Stage2RouteD.pairing_smul_right,
      O3.Stage2RouteD.pairing_smul_left]
    field_simp [hM.ne', hD.ne']

theorem normalized_convex (inst : PositiveInstance p d x0)
    (c : Point d) {M D : ℝ} (hM : 0 < M) (hD : 0 < D) :
    O3.IsConvexObjective (normalizedPairOracle c M D inst.oracle).value := by
  unfold O3.IsConvexObjective
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  dsimp [normalizedPairOracle]
  have hconvAll := inst.convex
  unfold O3.IsConvexObjective at hconvAll
  have hconv := hconvAll.2 (Set.mem_univ (c + D • x))
    (Set.mem_univ (c + D • y)) ha hb hab
  have harg : c + D • (a • x + b • y) =
      a • (c + D • x) + b • (c + D • y) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hc := congrArg (fun t : ℝ => t * c i) hab
    nlinarith
  rw [harg]
  have hden : 0 < M * D ^ (2 : ℕ) := mul_pos hM (sq_pos_of_pos hD)
  rw [div_le_iff₀ hden]
  have hcst : a * ((inst.oracle.value (c + D • x) - inst.oracle.value c) /
        (M * D ^ (2 : ℕ))) +
      b * ((inst.oracle.value (c + D • y) - inst.oracle.value c) /
        (M * D ^ (2 : ℕ))) =
      (a * inst.oracle.value (c + D • x) + b * inst.oracle.value (c + D • y) -
        inst.oracle.value c) / (M * D ^ (2 : ℕ)) := by
    field_simp [hden.ne']
    have hc := congrArg (fun t : ℝ => t * inst.oracle.value c) hab
    nlinarith
  rw [hcst]
  rw [div_mul_cancel₀ _ hden.ne']
  exact sub_le_sub_right hconv (inst.oracle.value c)

theorem normalized_bddBelow (inst : PositiveInstance p d x0)
    (c : Point d) {M D : ℝ} (hM : 0 < M) :
    BddBelow (Set.range (normalizedPairOracle c M D inst.oracle).value) := by
  obtain ⟨xstar, hxstar⟩ := inst.minimizerNonempty
  refine ⟨(inst.oracle.value xstar - inst.oracle.value c) /
      (M * D ^ (2 : ℕ)), ?_⟩
  rintro r ⟨y, rfl⟩
  dsimp [normalizedPairOracle]
  exact div_le_div_of_nonneg_right (by linarith [hxstar (c + D • y)])
    (mul_nonneg hM.le (sq_nonneg D))

end V7.Stage3BelowTwoS3F
