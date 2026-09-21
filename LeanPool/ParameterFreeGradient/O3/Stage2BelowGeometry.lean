/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Stage2RouteA
import LeanPool.ParameterFreeGradient.O3.Stage2RouteB
import Mathlib.Analysis.Convex.Deriv

/-!
# Stage 2 closure: below-two geometry

This file combines the native conjugate-smoothness Hessian bound with the
explicit duality/Fenchel reduction.  The exported theorem is the frozen
`O3.BelowGeometryStatement` without additional hypotheses.
-/

namespace O3
namespace Stage2Closure

open scoped BigOperators
open Stage2RouteA Stage2RouteB

lemma dualityMap_two {d : ℕ} (u : Point d) : dualityMap 2 u = u := by
  by_cases hu : u = 0
  · subst u
    exact Stage2RouteB.dualityMap_zero (by norm_num)
  · have hn : lpNorm 2 u ≠ 0 := (lpNorm_pos_of_ne_zero hu).ne'
    rw [dualityMap, if_neg hn]
    funext i
    norm_num [powerDualityMap]

lemma squaredLpEnergy_two_smooth {d : ℕ} (u v : Point d) :
    squaredLpEnergy 2 v ≤
      squaredLpEnergy 2 u + pairing (dualityMap 2 u) (v - u) +
        ((2 - 1) / 2) * (lpNorm 2 (v - u)) ^ (2 : ℕ) := by
  rw [dualityMap_two]
  rw [squaredLpEnergy_eq_quadraticRegularizer (by norm_num : (0 : ℝ) < 2),
    squaredLpEnergy_eq_quadraticRegularizer (by norm_num : (0 : ℝ) < 2)]
  simp only [quadraticRegularizer, sub_zero]
  simp_rw [Stage2RouteC.lpNorm_two_sq]
  simp only [pairing, Pi.sub_apply]
  rw [show ((2 : ℝ) - 1) / 2 = 1 / 2 by norm_num]
  have hsum : (∑ i : Fin d, v i ^ (2 : ℕ)) =
      (∑ i : Fin d, u i ^ (2 : ℕ)) +
        2 * (∑ i : Fin d, u i * (v i - u i)) +
        (∑ i : Fin d, (v i - u i) ^ (2 : ℕ)) := by
    calc
      (∑ i : Fin d, v i ^ (2 : ℕ)) =
          ∑ i : Fin d, ((u i ^ (2 : ℕ) + 2 * (u i * (v i - u i))) +
            (v i - u i) ^ (2 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  nlinarith

lemma hasDerivAt_squaredLpEnergy_line {q : ℝ} (hq : 1 < q) {d : ℕ}
    (u h : Point d) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ squaredLpEnergy q (u + s • h))
      (pairing (dualityMap q (u + t • h)) h) t := by
  by_cases hz : u + t • h = 0
  · have hcoord : ∀ i, u i = -t * h i := by
      intro i
      have hi := congrFun hz i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      linarith
    have hfun : (fun s : ℝ ↦ squaredLpEnergy q (u + s • h)) =
        fun s : ℝ ↦ (s - t) ^ (2 : ℕ) * squaredLpEnergy q h := by
      funext s
      rw [show u + s • h = (fun i ↦ (s - t) * h i) by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hcoord i]
        ring]
      exact squaredLpEnergy_scalar_mul (by linarith : 0 < q) h
    rw [hfun]
    have hd := (((hasDerivAt_id t).sub_const t).pow 2).mul_const
      (squaredLpEnergy q h)
    rw [hz, Stage2RouteB.dualityMap_zero (by linarith : 0 < q)]
    simpa [pairing] using hd
  · change HasDerivAt (Stage2RouteA.lineEnergy q u h)
      (pairing (dualityMap q (u + t • h)) h) t
    exact Stage2RouteA.hasDerivAt_lineEnergy_of_ne_zero hq u h t hz

noncomputable def smoothRemainder (q : ℝ) {d : ℕ}
    (u h : Point d) (t : ℝ) : ℝ :=
  squaredLpEnergy q (u + t • h) -
    ((q - 1) / 2) * t ^ (2 : ℕ) * (lpNorm q h) ^ (2 : ℕ)

noncomputable def smoothRemainderDeriv (q : ℝ) {d : ℕ}
    (u h : Point d) (t : ℝ) : ℝ :=
  pairing (dualityMap q (u + t • h)) h -
    (q - 1) * t * (lpNorm q h) ^ (2 : ℕ)

lemma hasDerivAt_smoothRemainder {q : ℝ} (hq : 1 < q) {d : ℕ}
    (u h : Point d) (t : ℝ) :
    HasDerivAt (smoothRemainder q u h) (smoothRemainderDeriv q u h t) t := by
  have he := hasDerivAt_squaredLpEnergy_line hq u h t
  have hquad : HasDerivAt
      (fun s : ℝ ↦ ((q - 1) / 2) * s ^ (2 : ℕ) * (lpNorm q h) ^ (2 : ℕ))
      ((q - 1) * t * (lpNorm q h) ^ (2 : ℕ)) t := by
    have hraw := (((hasDerivAt_id t).pow 2).const_mul ((q - 1) / 2)).mul_const
      ((lpNorm q h) ^ (2 : ℕ))
    simp [id_eq] at hraw
    have heq : ((q - 1) / 2) * (2 * t) * (lpNorm q h) ^ (2 : ℕ) =
        (q - 1) * t * (lpNorm q h) ^ (2 : ℕ) := by ring
    rw [← heq]
    exact hraw
  exact he.sub hquad

lemma exists_hasDerivAt_smoothRemainderDeriv_nonpos {q : ℝ} (hq : 2 < q)
    {d : ℕ} (u h : Point d) (t : ℝ) :
    ∃ w : ℝ, HasDerivAt (smoothRemainderDeriv q u h) w t ∧ w ≤ 0 := by
  obtain ⟨a, ha, hale⟩ :=
    Stage2RouteA.exists_hasDerivAt_line_duality_pair_le_above_two hq u h t
  have hlinear : HasDerivAt
      (fun s : ℝ ↦ (q - 1) * s * (lpNorm q h) ^ (2 : ℕ))
      ((q - 1) * (lpNorm q h) ^ (2 : ℕ)) t := by
    simpa [id_eq] using ((hasDerivAt_id t).const_mul (q - 1)).mul_const
      ((lpNorm q h) ^ (2 : ℕ))
  refine ⟨a - (q - 1) * (lpNorm q h) ^ (2 : ℕ), ?_, by linarith⟩
  exact ha.sub hlinear

lemma smoothRemainder_concave_above_two {q : ℝ} (hq : 2 < q) {d : ℕ}
    (u h : Point d) : ConcaveOn ℝ Set.univ (smoothRemainder q u h) := by
  have hGdiff : Differentiable ℝ (smoothRemainderDeriv q u h) := by
    intro t
    obtain ⟨w, hw, _⟩ := exists_hasDerivAt_smoothRemainderDeriv_nonpos hq u h t
    exact hw.differentiableAt
  have hGnonpos : ∀ t, deriv (smoothRemainderDeriv q u h) t ≤ 0 := by
    intro t
    obtain ⟨w, hw, hw0⟩ := exists_hasDerivAt_smoothRemainderDeriv_nonpos hq u h t
    rw [hw.deriv]
    exact hw0
  have hGanti : Antitone (smoothRemainderDeriv q u h) :=
    antitone_of_deriv_nonpos hGdiff hGnonpos
  have hFdiff : Differentiable ℝ (smoothRemainder q u h) :=
    fun t ↦ (hasDerivAt_smoothRemainder (by linarith : 1 < q) u h t).differentiableAt
  have hFderiv : deriv (smoothRemainder q u h) = smoothRemainderDeriv q u h := by
    funext t
    exact (hasDerivAt_smoothRemainder (by linarith : 1 < q) u h t).deriv
  have hanti : Antitone (deriv (smoothRemainder q u h)) := by
    simpa only [hFderiv] using hGanti
  exact hanti.concaveOn_univ_of_deriv hFdiff

lemma squaredLpEnergy_smooth_above_two {q : ℝ} (hq : 2 < q) {d : ℕ}
    (u v : Point d) :
    squaredLpEnergy q v ≤ squaredLpEnergy q u +
      pairing (dualityMap q u) (v - u) +
        ((q - 1) / 2) * (lpNorm q (v - u)) ^ (2 : ℕ) := by
  let h : Point d := v - u
  have huv : u + h = v := by
    funext i
    simp only [h, Pi.add_apply, Pi.sub_apply]
    ring
  have hconc := smoothRemainder_concave_above_two hq u h
  have htangent := hconc.slope_le_of_hasDerivAt
    (x := (0 : ℝ)) (y := (1 : ℝ)) (by simp) (by simp) (by norm_num)
    (hasDerivAt_smoothRemainder (by linarith : 1 < q) u h 0)
  norm_num [slope, smoothRemainder, smoothRemainderDeriv] at htangent
  rw [huv] at htangent
  change squaredLpEnergy q v ≤ squaredLpEnergy q u +
    pairing (dualityMap q u) h +
      ((q - 1) / 2) * (lpNorm q h) ^ (2 : ℕ)
  nlinarith

theorem conjugateSmoothness : ConjugateSmoothnessStatement := by
  intro p hp hp2 d u v
  by_cases hpEq : p = 2
  · subst p
    norm_num [conjugateExponent_eq]
    simpa only [show ((2 : ℝ) - 1) / 2 = 1 / 2 by norm_num] using
      squaredLpEnergy_two_smooth u v
  · have hpLt : p < 2 := lt_of_le_of_ne hp2 hpEq
    have hq : 2 < conjugateExponent p := by
      rw [conjugateExponent_eq, lt_div_iff₀ (by linarith : 0 < p - 1)]
      linarith
    exact squaredLpEnergy_smooth_above_two hq u v

end Stage2Closure

/-- Frozen Stage 2 target: exact strong convexity of the squared finite
`ell_p` norm for every real `1 < p ≤ 2` and every finite dimension. -/
theorem belowGeometry : BelowGeometryStatement :=
  Stage2RouteB.conjugateSmoothness_implies_belowGeometry
    Stage2Closure.conjugateSmoothness

end O3
