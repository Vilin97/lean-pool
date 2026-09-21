/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.Projection
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.PositiveBesovCore

/-!
# Finite positive Besov aggregation

This is the scale-cancellation step from a local cube Poincare estimate to a
finite `B¹_{2,∞}` seminorm bound.  It contains no analytic input beyond the
explicit local oscillation and normalized descendant-energy hypotheses.
-/

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

/-- A scale-sharp local oscillation bound and uniform normalized descendant
energy control imply the finite triadic-cube `B¹_{2,∞}` bound. -/
theorem cubeBesovPartialSeminormTop_one_two_le_of_localOscillation
    {d : ℕ} (Q : TriadicCube d) (N : ℕ) (f : Vec d → ℝ)
    (K G : ℝ) (E : TriadicCube d → ℝ)
    (hK : 0 ≤ K) (hG : 0 ≤ G)
    (hE : ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j, 0 ≤ E R)
    (hosc : ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) f ≤ K * cubeScaleFactor R * E R)
    (havg : ∀ j ∈ Finset.range (N + 1),
      descendantsAverage Q j (fun R => E R ^ 2) ≤ G ^ 2) :
    cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N f ≤ K * G := by
  refine cubeBesovPartialSeminormTop_le_of_forall_depthSeminorm_le
    Q 1 (2 : ℝ≥0∞) N f ?_
  intro j hj
  let a : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j
  let A : TriadicCube d → ℝ := fun R => K * cubeScaleFactor R * E R
  have ha_pos : 0 < a := by
    dsimp [a]
    exact div_pos
      (by simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
      (by positivity)
  have hA_nonneg : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ A R := by
    intro R hR
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg hK (le_of_lt <| by
        simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) R.scale)))
      (hE j hj R hR)
  have hlocal : ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) f ≤ A R := by
    intro R hR
    exact hosc j hj R hR
  have hdepth :=
    cubeBesovDepthSeminorm_two_le_depthWeight_mul_descendantsAverage_sq_rpow_half
      Q 1 f j A hA_nonneg hlocal
  have hscaled :
      descendantsAverage Q j (fun R => (A R) ^ 2) =
        (K * a) ^ 2 * descendantsAverage Q j (fun R => E R ^ 2) := by
    let D : Finset (TriadicCube d) := descendantsAtDepth Q j
    have hsum :
        ∑ R ∈ D, (A R) ^ 2 =
          ∑ R ∈ D, (K * a) ^ 2 * E R ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro R hR
      dsimp [A]
      rw [show cubeScaleFactor R = a by
        dsimp [a]
        exact cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth (by simpa [D] using hR)]
      ring
    change (D.card : ℝ)⁻¹ * ∑ R ∈ D, (A R) ^ 2 =
      (K * a) ^ 2 * ((D.card : ℝ)⁻¹ * ∑ R ∈ D, E R ^ 2)
    rw [hsum, ← Finset.mul_sum]
    ring
  have hinside :
      descendantsAverage Q j (fun R => (A R) ^ 2) ≤ (K * a * G) ^ 2 := by
    rw [hscaled]
    calc
      (K * a) ^ 2 * descendantsAverage Q j (fun R => E R ^ 2)
          ≤ (K * a) ^ 2 * G ^ 2 := by
              exact mul_le_mul_of_nonneg_left (havg j hj) (sq_nonneg _)
      _ = (K * a * G) ^ 2 := by ring
  have hroot :
      (descendantsAverage Q j (fun R => (A R) ^ 2)) ^ (1 / 2 : ℝ) ≤ K * a * G := by
    have hleft : 0 ≤ descendantsAverage Q j (fun R => (A R) ^ 2) :=
      descendantsAverage_nonneg Q j _ fun _ _ => sq_nonneg _
    have hright : 0 ≤ K * a * G := by
      exact mul_nonneg (mul_nonneg hK ha_pos.le) hG
    calc
      (descendantsAverage Q j (fun R => (A R) ^ 2)) ^ (1 / 2 : ℝ)
          ≤ ((K * a * G) ^ 2) ^ (1 / 2 : ℝ) := by
              exact Real.rpow_le_rpow hleft hinside (by norm_num)
      _ = K * a * G := sq_rpow_half_eq_of_nonneg hright
  have hweight_a : cubeBesovDepthWeight Q 1 j * a = 1 := by
    dsimp [cubeBesovDepthWeight, a]
    rw [Real.rpow_neg_one]
    exact inv_mul_cancel₀ (ne_of_gt ha_pos)
  calc
    cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞) f j
        ≤ cubeBesovDepthWeight Q 1 j *
          (descendantsAverage Q j (fun R => (A R) ^ 2)) ^ (1 / 2 : ℝ) := hdepth
    _ ≤ cubeBesovDepthWeight Q 1 j * (K * a * G) := by
      exact mul_le_mul_of_nonneg_left hroot (cubeBesovDepthWeight_nonneg Q 1 j)
    _ = K * G := by
      calc
        cubeBesovDepthWeight Q 1 j * (K * a * G)
            = K * (cubeBesovDepthWeight Q 1 j * a) * G := by ring
        _ = K * G := by simp [hweight_a]

end

end Homogenization
