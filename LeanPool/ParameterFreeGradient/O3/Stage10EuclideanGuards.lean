/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.O3.Stage8EuclideanGap
public import LeanPool.ParameterFreeGradient.O3.Stage9FiniteDataOGMG

/-!
# Stage 10: Euclidean guard semantics

Every observable source guard is proved to pass when the trial scale dominates
the true smoothness constant.  In particular, the ordered interpolation
inequality is derived from convexity and the exact `L/2` descent lemma; it is
not assumed as a certificate.
-/

@[expose] public section

namespace O3

/-- The exact Euclidean smooth-convex interpolation inequality. -/
theorem euclidean_interpolation_of_smooth_convex
    {d : ℕ} (P : AdmissibleInstance d 2) (x y : Vec d) :
    (lpNorm 2 (P.grad x - P.grad y)) ^ (2 : ℕ) / (2 * P.L) ≤
      P.f x - P.f y - pairing (P.grad y) (x - y) := by
  let gx := P.grad x
  let gy := P.grad y
  let gd := gx - gy
  let z := x - P.L⁻¹ • gd
  let N := (lpNorm 2 gd) ^ (2 : ℕ)
  have hL : 0 < P.L := P.L_pos
  have hLne : P.L ≠ 0 := hL.ne'
  have hdes := Stage3Anchor.smooth_descent_lp P.p_gt_one
    (holderConjugate_conjugateExponent P.p_gt_one)
    P.gradient_spec P.smooth x z
  have hconv := Stage3Anchor.firstOrderConvex_of_coordinateGradient
    P.convex P.gradient_spec y z
  have hzsub : z - x = (-P.L⁻¹) • gd := by
    funext i
    simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hzy : z - y = (x - y) - P.L⁻¹ • gd := by
    funext i
    simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hnorm : (lpNorm 2 (z - x)) ^ (2 : ℕ) = P.L⁻¹ ^ 2 * N := by
    rw [hzsub, Stage2RouteC.lpNorm_smul (by norm_num)]
    rw [abs_neg, abs_of_pos (inv_pos.mpr hL)]
    dsimp only [N]
    ring
  have hpairx : pairing gx (z - x) = -P.L⁻¹ * pairing gx gd := by
    rw [hzsub, Stage2RouteD.pairing_smul_right]
  have hpairy : pairing gy (z - y) =
      pairing gy (x - y) - P.L⁻¹ * pairing gy gd := by
    rw [hzy]
    unfold pairing
    calc
      (∑ i, gy i * ((x - y) - P.L⁻¹ • gd) i) =
          ∑ i, (gy i * (x - y) i - P.L⁻¹ * (gy i * gd i)) := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
            ring
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
  have hcross : pairing gx gd - pairing gy gd = N := by
    have hs : pairing gd gd = N := by
      exact pairing_self_eq_lpNorm_two_sq gd
    rw [show pairing gd gd = pairing gx gd - pairing gy gd by
      exact pairing_sub_left gx gy gd] at hs
    exact hs
  have hdes' : P.f z ≤ P.f x - P.L⁻¹ * pairing gx gd +
      (P.L / 2) * (P.L⁻¹ ^ 2 * N) := by
    change P.f z ≤ P.f x + pairing gx (z - x) +
      (P.L / 2) * (lpNorm 2 (z - x)) ^ (2 : ℕ) at hdes
    rw [hpairx, hnorm] at hdes
    linarith
  have hconv' : P.f y + pairing gy (x - y) -
      P.L⁻¹ * pairing gy gd ≤ P.f z := by
    change P.f y + pairing gy (z - y) ≤ P.f z at hconv
    rw [hpairy] at hconv
    linarith
  have hinvSq : P.L * (P.L⁻¹ ^ 2) = P.L⁻¹ := by
    field_simp [hLne]
  have hinvSqN : P.L * (P.L⁻¹ ^ 2) * N = P.L⁻¹ * N := by
    rw [hinvSq]
  have hquad : (P.L / 2) * (P.L⁻¹ ^ 2 * N) = P.L⁻¹ * N / 2 := by
    nlinarith [hinvSqN]
  rw [hquad] at hdes'
  have hcrossInv : P.L⁻¹ * (pairing gx gd - pairing gy gd) =
      P.L⁻¹ * N := by rw [hcross]
  change N / (2 * P.L) ≤ _
  have hhalf : P.L⁻¹ * N / 2 ≤
      P.f x - P.f y - pairing gy (x - y) := by
    nlinarith [hdes', hconv', hcrossInv]
  have heq : N / (2 * P.L) = P.L⁻¹ * N / 2 := by
    field_simp [hLne]
  rw [heq]
  exact hhalf

/-- If `L ≤ M`, every ordered finite-data interpolation guard passes. -/
theorem euclideanInterpolationGuard_holds_of_le
    {d : ℕ} (P : AdmissibleInstance d 2) {M : ℝ}
    (hM : 0 < M) (hLM : P.L ≤ M) (x y : Vec d) :
    (interpolationGuard (P.f x) (P.f y)
      (pairing (P.grad y) (x - y))
      ((lpNorm 2 (P.grad x - P.grad y)) ^ (2 : ℕ)) M).Holds := by
  have hbase := euclidean_interpolation_of_smooth_convex P x y
  have hN : 0 ≤ (lpNorm 2 (P.grad x - P.grad y)) ^ (2 : ℕ) := sq_nonneg _
  have hcoef :
      (lpNorm 2 (P.grad x - P.grad y)) ^ (2 : ℕ) / (2 * M) ≤
        (lpNorm 2 (P.grad x - P.grad y)) ^ (2 : ℕ) / (2 * P.L) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hM)
      (mul_pos (by norm_num) P.L_pos)).2
    nlinarith
  rw [interpolationGuard_holds_iff]
  linarith

/-- Every actual Phase-A upper-model guard passes under `L ≤ M`. -/
theorem euclideanEstimateGuard_holds_of_le
    {d : ℕ} (P : AdmissibleInstance d 2) {M : ℝ}
    (hLM : P.L ≤ M) (k : ℕ) :
    (euclideanEstimateGuard P M k).Holds := by
  let y := euclideanEstimateQuery P M k
  let z := (euclideanEstimateState P M (k + 1)).accelerated
  have hd := Stage3Anchor.smooth_descent_lp P.p_gt_one
    (holderConjugate_conjugateExponent P.p_gt_one)
    P.gradient_spec P.smooth y z
  have hn : 0 ≤ (lpNorm 2 (z - y)) ^ (2 : ℕ) := sq_nonneg _
  have hc : (P.L / 2) * (lpNorm 2 (z - y)) ^ (2 : ℕ) ≤
      (M / 2) * (lpNorm 2 (z - y)) ^ (2 : ℕ) := by nlinarith
  have hf : P.f z ≤ P.f y + pairing (P.grad y) (z - y) +
      (M / 2) * (lpNorm 2 (z - y)) ^ (2 : ℕ) := by linarith
  simpa only [euclideanEstimateGuard, euclideanEstimateObservation,
    AdmissibleInstance.oracle, PairOracle.observe, GuardCheck.Holds,
    upperModelGuard, sub_nonneg, y, z] using hf

/-- The actual Stage-9 terminal descent guard passes under `L ≤ M`. -/
theorem ogmgTerminalDescentCheck_holds_of_le
    {d : ℕ} (P : AdmissibleInstance d 2) (cfg : OGMGExecutionConfig d)
    (hcfg : cfg.oracle = P.oracle) {M : ℝ} (hcfgM : cfg.M = M)
    (hLM : P.L ≤ M) :
    (ogmgTerminalDescentCheck cfg).Holds := by
  let u := (ogmgState cfg cfg.horizon).current
  let v := ogmgV cfg cfg.horizon
  have hd := Stage3Anchor.smooth_descent_lp P.p_gt_one
    (holderConjugate_conjugateExponent P.p_gt_one)
    P.gradient_spec P.smooth u v
  have hn : 0 ≤ (lpNorm 2 (v - u)) ^ (2 : ℕ) := sq_nonneg _
  have hc : (P.L / 2) * (lpNorm 2 (v - u)) ^ (2 : ℕ) ≤
      (M / 2) * (lpNorm 2 (v - u)) ^ (2 : ℕ) := by nlinarith
  have hf : P.f v ≤ P.f u + pairing (P.grad u) (v - u) +
      (M / 2) * (lpNorm 2 (v - u)) ^ (2 : ℕ) := by linarith
  rw [ogmgTerminalDescentCheck_holds_iff]
  simpa only [ogmgTerminalObservation, ogmgObservation, ogmgGradient,
    hcfg, hcfgM, AdmissibleInstance.oracle, PairOracle.observe, u, v] using hf

end O3
