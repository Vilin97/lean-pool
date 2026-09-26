/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CompactBall
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Localization
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

/-!
# A first-round localization cutoff at arbitrary centre

Paper label `eq:local-equation` localizes the equation to a parabolic ball of
arbitrary centre and radius.  This file supplies the geometry and the smooth
cutoff that the first bootstrap round uses.  The open parabolic box
`B_r(x) × (t - r², t + r²)` is exactly the parabolic metric ball of `eq:parabolic-ball`
read through `spaceTimeSet`, the same set is its own preimage along the product
identification, and a ball sitting compactly inside the space-time domain
admits a smooth cutoff equal to one on the inner quarter-ball, supported inside
the three-eighths-ball, and contained in the product box of half radius.
-/

public section

open Set Metric
open scoped Topology
open CKN.Foundation.Parabolic
open CKN.Core.Endgame


noncomputable section

namespace CKN.Core.Step4

/-- Equation `eq:local-equation`, in box form: `spaceTimeSet` applied to the spatial
ball `vec3Ball z₀.1 r` and the time interval `(z₀.2 - r², z₀.2 + r²)` is the parabolic
metric ball `Metric.ball z₀ r` of `eq:parabolic-ball`. -/
theorem parabolic_box_eq_ball (z₀ : ParabolicPoint) (r : ℝ) :
    spaceTimeSet (vec3Ball z₀.1 r) (Set.Ioo (z₀.2 - r ^ 2) (z₀.2 + r ^ 2)) =
      Metric.ball z₀ r :=
  (metricBall_eq_parabolicBall z₀ r).symm

/-- Equation `eq:local-equation`, preimage form: the product box of spatial ball and
open time interval is contained in the preimage of the parabolic metric ball under the
product identification `parabolicHomeomorph.symm`. -/
theorem parabolic_box_subset_ball_preimage (z₀ : ParabolicPoint) (r : ℝ) :
    vec3Ball z₀.1 r ×ˢ Set.Ioo (z₀.2 - r ^ 2) (z₀.2 + r ^ 2) ⊆
      parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ r := by
  rintro ⟨y, s⟩ hz
  rw [metricBall_eq_parabolicBall]
  exact hz

/-- Equation `eq:local-equation`, first-round cutoff: a parabolic ball of radius `2R`
inside the space-time domain `Ω × I` admits a smooth cutoff `φ` with values in `[0, 1]`,
equal to one on the ball of radius `R/4`, supported in the ball of radius `3R/8`, and
supported in the product box of spatial radius `R/2` and time half-width `(R/2)²`, which
is compactly interior to `Ω × I`. -/
theorem exists_first_round_cutoff
    {Ω : Set Vec3} {I : Set ℝ} {z₀ : ParabolicPoint} {R : ℝ}
    (hR : 0 < R) (hdom : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I) :
    ∃ φ : Vec3 × ℝ → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I ∧
      (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) ∧
      (∀ z ∈ Metric.ball z₀ (R / 4), φ (z.1, z.2) = 1) ∧
      tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ (3 * R / 8) ∧
      localBox Ω I (vec3Ball z₀.1 (R / 2))
        (Set.Ioo (z₀.2 - (R / 2) ^ 2) (z₀.2 + (R / 2) ^ 2)) ∧
      tsupport φ ⊆ vec3Ball z₀.1 (R / 2) ×ˢ
        Set.Ioo (z₀.2 - (R / 2) ^ 2) (z₀.2 + (R / 2) ^ 2) := by
  let U : Set (Vec3 × ℝ) := parabolicHomeomorph.symm ⁻¹' ball z₀ (R / 3)
  let K : Set (Vec3 × ℝ) := parabolicHomeomorph.symm ⁻¹' closedBall z₀ (R / 4)
  have hU : IsOpen U := isOpen_ball.preimage parabolicHomeomorph.symm.continuous
  have hK : IsClosed K := isClosed_closedBall.preimage parabolicHomeomorph.symm.continuous
  have hKU : K ⊆ U := preimage_mono (closedBall_subset_ball (by linarith only [hR]))
  obtain ⟨φ, hφsmooth, hφrange, hφsupport, hφone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hU hK hKU
  have hts : tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹' closedBall z₀ (R / 3) := by
    rw [tsupport, hφsupport]
    exact closure_minimal (preimage_mono ball_subset_closedBall)
      (isClosed_closedBall.preimage parabolicHomeomorph.symm.continuous)
  have hcompact : HasCompactSupport φ :=
    (parabolicHomeomorph.symm.isCompact_preimage.mpr
      (isCompact_parabolic_closedBall z₀ (R / 3))).of_isClosed_subset
      isClosed_closure hts
  have htsball : tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹' ball z₀ (3 * R / 8) :=
    hts.trans (preimage_mono (closedBall_subset_ball (by linarith only [hR])))
  refine ⟨φ, ⟨hφsmooth, hcompact, ?_⟩, ?_, ?_, htsball, ?_, ?_⟩
  · intro z hz
    have hb : parabolicHomeomorph.symm z ∈ ball z₀ (2 * R) :=
      ball_subset_ball (by linarith only [hR]) (htsball hz)
    exact hdom hb
  · intro z
    exact hφrange (mem_range_self z)
  · intro z hz
    exact (hφone (z.1, z.2)).mp (ball_subset_closedBall hz)
  · have h2 : 2 * (R / 2) = R := by ring
    refine localBox_of_parabolic_ball (by linarith only [hR]) ?_
    rw [h2]
    exact (ball_subset_ball (by linarith only [hR])).trans hdom
  · rintro ⟨y, s⟩ hz
    have hb : parabolicHomeomorph.symm (y, s) ∈ ball z₀ (R / 2) :=
      ball_subset_ball (by linarith only [hR]) (htsball hz)
    rw [metricBall_eq_parabolicBall] at hb
    exact hb

end CKN.Core.Step4
