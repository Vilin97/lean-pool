/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Statements.LocalBox
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Smooth localization inside a parabolic ball

A ball compactly inside the space-time domain admits a smooth cutoff and
a compactly interior product box containing its support.
-/

public section

open Set Metric
open scoped Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Core.Endgame

private theorem compact_raw_parabolic_closedBall (z₀ : ParabolicPoint) (r : ℝ) :
    IsCompact (parabolicHomeomorph.symm ⁻¹' closedBall z₀ r) := by
  have hspace : IsCompact (vec3Homeomorph ⁻¹'
      closedBall (vec3Homeomorph z₀.1) r) :=
    vec3Homeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  refine (hspace.prod (isCompact_Icc (a := z₀.2 - r ^ 2)
    (b := z₀.2 + r ^ 2))).of_isClosed_subset
      (isClosed_closedBall.preimage parabolicHomeomorph.symm.continuous) ?_
  intro z hz
  change dist (parabolicHomeomorph.symm z) z₀ ≤ r at hz
  rw [dist_eq_parabolicDist] at hz
  have hs := (max_le_iff.mp hz).1
  have ht := (Real.sqrt_le_iff.mp (max_le_iff.mp hz).2).2
  change vec3EuclideanNorm (z.1 - z₀.1) ≤ r at hs
  change |z.2 - z₀.2| ≤ r ^ 2 at ht
  refine ⟨?_, ?_⟩
  · change dist (vec3Homeomorph z.1) (vec3Homeomorph z₀.1) ≤ r
    simpa only [vec3Homeomorph_apply, dist_eq_norm, ← WithLp.toLp_sub,
      ← vec3EuclideanNorm_eq_l2] using hs
  · change z₀.2 - r ^ 2 ≤ z.2 ∧ z.2 ≤ z₀.2 + r ^ 2
    have habs := abs_le.mp ht
    constructor <;> linarith only [habs.1, habs.2]

/-- A positive interior parabolic ball supplies a compactly interior spatial
ball and time interval. -/
theorem localBox_of_parabolic_ball
    {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {r : ℝ}
    (hr : 0 < r) (hball : ball z₀ (2 * r) ⊆ spaceTimeSet Ω I) :
    localBox Ω I (vec3Ball z₀.1 r) (Ioo (z₀.2 - r ^ 2) (z₀.2 + r ^ 2)) := by
  have htime : z₀.2 - r ^ 2 < z₀.2 + r ^ 2 := by
    have hr2 := sq_pos_of_pos hr
    linarith only [hr2]
  refine ⟨isOpen_vec3Ball _ _, ?_, ?_, ordConnected_Ioo, ?_, ?_⟩
  · rw [closure_vec3Ball hr]
    have hcompact := vec3Homeomorph.isCompact_preimage.mpr
      (isCompact_closedBall (vec3Homeomorph z₀.1) r)
    convert hcompact using 1
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_closedBall,
      vec3Homeomorph_apply, dist_eq_norm, ← WithLp.toLp_sub,
      ← vec3EuclideanNorm_eq_l2]
  · rw [closure_vec3Ball hr]
    intro x hx
    have hmem : dist (parabolicHomeomorph.symm (x, z₀.2)) z₀ < 2 * r := by
      rw [dist_eq_parabolicDist]
      change max (vec3EuclideanNorm (x - z₀.1)) (Real.sqrt |z₀.2 - z₀.2|) < 2 * r
      rw [sub_self, abs_zero, Real.sqrt_zero]
      exact max_lt (lt_of_le_of_lt hx (by linarith only [hr])) (by positivity)
    exact (hball hmem).1
  · rw [closure_Ioo htime.ne]
    exact isCompact_Icc
  · rw [closure_Ioo htime.ne]
    intro t ht
    have hmem : dist (parabolicHomeomorph.symm (z₀.1, t)) z₀ < 2 * r := by
      rw [dist_eq_parabolicDist]
      change max (vec3EuclideanNorm (z₀.1 - z₀.1)) (Real.sqrt |t - z₀.2|) < 2 * r
      rw [sub_self, vec3EuclideanNorm_zero]
      apply max_lt (by positivity)
      have habs : |t - z₀.2| ≤ r ^ 2 := abs_le.mpr
        ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
      exact (Real.sqrt_le_iff.mpr ⟨hr.le, habs⟩).trans_lt (by linarith only [hr])
    exact (hball hmem).2

/-- There is a smooth cutoff equal to one on the closed ball of radius `r/8`,
supported inside the ball of radius `r/4`, with a local product box containing
its support. -/
theorem exists_localization_cutoff
    {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {r : ℝ}
    (hr : 0 < r) (hball : ball z₀ (2 * r) ⊆ spaceTimeSet Ω I) :
    ∃ φ : Vec3 × ℝ → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I ∧
      (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) ∧
      (∀ z ∈ closedBall z₀ (r / 8), φ (z.1, z.2) = 1) ∧
      tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹' ball z₀ (r / 4) ∧
      localBox Ω I (vec3Ball z₀.1 r) (Ioo (z₀.2 - r ^ 2) (z₀.2 + r ^ 2)) ∧
      tsupport φ ⊆ vec3Ball z₀.1 r ×ˢ Ioo (z₀.2 - r ^ 2) (z₀.2 + r ^ 2) := by
  let U : Set (Vec3 × ℝ) := parabolicHomeomorph.symm ⁻¹' ball z₀ (r / 6)
  let K : Set (Vec3 × ℝ) := parabolicHomeomorph.symm ⁻¹' closedBall z₀ (r / 8)
  have hU : IsOpen U := isOpen_ball.preimage parabolicHomeomorph.symm.continuous
  have hK : IsClosed K := isClosed_closedBall.preimage parabolicHomeomorph.symm.continuous
  have hKU : K ⊆ U := preimage_mono (closedBall_subset_ball (by linarith only [hr]))
  obtain ⟨φ, hφsmooth, hφrange, hφsupport, hφone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hU hK hKU
  have hts : tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹' closedBall z₀ (r / 6) := by
    rw [tsupport, hφsupport]
    exact closure_minimal (preimage_mono ball_subset_closedBall)
      (isClosed_closedBall.preimage parabolicHomeomorph.symm.continuous)
  have hcompact : HasCompactSupport φ :=
    (compact_raw_parabolic_closedBall z₀ (r / 6)).of_isClosed_subset
      isClosed_closure hts
  have htsball : tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹' ball z₀ (r / 4) :=
    hts.trans (preimage_mono (closedBall_subset_ball (by linarith only [hr])))
  refine ⟨φ, ⟨hφsmooth, hcompact, ?_⟩, ?_, ?_, htsball,
    localBox_of_parabolic_ball hr hball, ?_⟩
  · intro z hz
    exact hball (ball_subset_ball (by linarith only [hr]) (htsball hz))
  · intro z
    exact hφrange (mem_range_self z)
  · intro z hz
    exact (hφone (z.1, z.2)).mp hz
  · intro z hz
    have hb := htsball hz
    change dist (parabolicHomeomorph.symm z) z₀ < r / 4 at hb
    rw [dist_eq_parabolicDist] at hb
    change max (vec3EuclideanNorm (z.1 - z₀.1)) (Real.sqrt |z.2 - z₀.2|) < r / 4 at hb
    have hspace := (max_lt_iff.mp hb).1
    have htime := (Real.sqrt_lt (abs_nonneg _) (by positivity : 0 ≤ r / 4)).mp
      (max_lt_iff.mp hb).2
    refine ⟨hspace.trans (by linarith only [hr]), ?_⟩
    have habs : |z.2 - z₀.2| < r ^ 2 :=
      htime.trans (by nlinarith only [sq_pos_of_pos hr])
    have ht := abs_lt.mp habs
    constructor <;> linarith only [ht.1, ht.2]

end CKN.Core.Endgame
