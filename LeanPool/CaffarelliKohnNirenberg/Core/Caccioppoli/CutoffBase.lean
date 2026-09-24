/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Admissibility
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Cutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.SpaceTime
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus

/-! The spatial-temporal cutoff and its support estimates. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

lemma parabolic_norm_eq_cutoff_norm (x : Vec3) :
    vec3EuclideanNorm x = CKN.vecEuclideanNorm x := by
  simp [CKN.vecEuclideanNorm, vec3EuclideanNorm, vecNormSq]
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-! The cutoff used in the local energy estimate.  The spatial factor is the
two-derivative cutoff from the pressure construction; the temporal factor is
given a separate outer radius so that its support can be placed inside the
open time interval. -/

def caccioppoli_cutoff (x₀ : Vec3) (t₀ ρ R : ℝ) (hρ : 0 < ρ) (_hR : ρ / 2 < R)
    (z : Vec3 × ℝ) : ℝ :=
  mollifiedBallCutoff x₀ hρ z.1 * timeCutoff t₀ (ρ / 2) R z.2

lemma caccioppoli_cutoff_time_parameters {ρ R : ℝ}
    (hρ : 0 < ρ) (hR : ρ / 2 < R) : 0 ≤ ρ / 2 ∧ ρ / 2 < R := by
  exact ⟨by linarith only [hρ], hR⟩

theorem caccioppoli_cutoff_smooth (x₀ : Vec3) (t₀ ρ R : ℝ)
    (hρ : 0 < ρ) (hR : ρ / 2 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (caccioppoli_cutoff x₀ t₀ ρ R hρ hR) := by
  unfold caccioppoli_cutoff
  apply (mollifiedBallCutoff_smooth x₀ hρ).comp contDiff_fst |>.mul
  exact (timeCutoff_smooth (caccioppoli_cutoff_time_parameters hρ hR).1 hR).comp
    contDiff_snd

theorem caccioppoli_cutoff_nonneg (x₀ : Vec3) (t₀ ρ R : ℝ)
    (hρ : 0 < ρ) (hR : ρ / 2 < R) (z : Vec3 × ℝ) :
    0 ≤ caccioppoli_cutoff x₀ t₀ ρ R hρ hR z := by
  unfold caccioppoli_cutoff
  exact mul_nonneg (mollifiedBallCutoff_nonneg x₀ hρ _)
    (timeCutoff_nonneg t₀ (ρ / 2) R z.2)

theorem caccioppoli_cutoff_eq_one_on (x₀ : Vec3) (t₀ ρ R : ℝ)
    (hρ : 0 < ρ) (hR : ρ / 2 < R) {z : Vec3 × ℝ}
    (hx : z.1 ∈ vec3Ball x₀ (ρ / 2))
    (ht : z.2 ∈ Icc (t₀ - (ρ / 2) ^ 2) t₀) :
    caccioppoli_cutoff x₀ t₀ ρ R hρ hR z = 1 := by
  unfold caccioppoli_cutoff
  rw [mollifiedBallCutoff_eq_one_on_inner x₀ hρ]
  · rw [timeCutoff_eq_one_on (caccioppoli_cutoff_time_parameters hρ hR).1 hR ht]
    norm_num
  · apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    have hrad : ρ / 2 ≤ 13 * ρ / 20 := by
      linarith only [hρ]
    have hx' : CKN.vecEuclideanNorm (z.1 - x₀) < ρ / 2 := by
      rw [← parabolic_norm_eq_cutoff_norm]
      exact mem_vec3Ball.mp hx
    exact (hx'.trans_le hrad)

theorem caccioppoli_cutoff_support_subset (x₀ : Vec3) (t₀ ρ R : ℝ)
    (hρ : 0 < ρ) (hR : ρ / 2 < R) :
    Function.support (caccioppoli_cutoff x₀ t₀ ρ R hρ hR) ⊆
      euclideanBall x₀ (3 * ρ / 4) ×ˢ
        Ioo (t₀ - R ^ 2) (t₀ + (R ^ 2 - (ρ / 2) ^ 2)) := by
  intro z hz
  constructor
  · apply (mollifiedBallCutoff_tsupport_subset_outer x₀ hρ)
    apply subset_tsupport
    intro hzero
    apply hz
    simp [caccioppoli_cutoff, hzero]
  · apply timeCutoff_support_subset (caccioppoli_cutoff_time_parameters hρ hR).1 hR
    intro hzero
    apply hz
    simp [caccioppoli_cutoff, hzero]

theorem caccioppoli_cutoff_hasCompactSupport (x₀ : Vec3) (t₀ ρ R : ℝ)
    (hρ : 0 < ρ) (hR : ρ / 2 < R) :
    HasCompactSupport (caccioppoli_cutoff x₀ t₀ ρ R hρ hR) := by
  refine HasCompactSupport.intro
    ((isCompact_euclideanClosedBall x₀ (R := 3 * ρ / 4) (by positivity)).prod
      (isCompact_Icc : IsCompact (Icc (t₀ - R ^ 2)
        (t₀ + (R ^ 2 - (ρ / 2) ^ 2))))) ?_
  intro z hz
  by_contra hne
  have hmem := caccioppoli_cutoff_support_subset x₀ t₀ ρ R hρ hR
    (show z ∈ Function.support (caccioppoli_cutoff x₀ t₀ ρ R hρ hR) from
      Function.mem_support.mpr hne)
  by_cases hx : z.1 ∈ euclideanClosedBall x₀ (3 * ρ / 4)
  · have ht : z.2 ∉ Icc (t₀ - R ^ 2)
        (t₀ + (R ^ 2 - (ρ / 2) ^ 2)) := by
      intro ht
      exact hz ⟨hx, ht⟩
    exact ht (⟨hmem.2.1.le, hmem.2.2.le⟩)
  · apply hx
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hmem.1).le

theorem caccioppoli_cutoff_time_support_bound (x₀ : Vec3) (t₀ ρ R r : ℝ)
    (hρ : 0 < ρ) (hR : ρ / 2 < R) (_ : 0 < r)
    (hgapr : R ^ 2 - (ρ / 2) ^ 2 < r ^ 2) :
    tsupport (caccioppoli_cutoff x₀ t₀ ρ R hρ hR) ⊆
      {z : Vec3 × ℝ | z.2 < t₀ + r ^ 2} := by
  intro z hz
  have hupper_mem : z ∈ {y : Vec3 × ℝ |
      y.2 ≤ t₀ + (R ^ 2 - (ρ / 2) ^ 2)} := by
    apply closure_minimal
    · intro y hy
      exact (caccioppoli_cutoff_support_subset x₀ t₀ ρ R hρ hR hy).2.2.le
    · exact isClosed_Iic.preimage continuous_snd
    · exact hz
  have hupper : z.2 ≤ t₀ + (R ^ 2 - (ρ / 2) ^ 2) := hupper_mem
  have hstrict : t₀ + (R ^ 2 - (ρ / 2) ^ 2) < t₀ + r ^ 2 := by
    linarith only [hgapr]
  exact lt_of_le_of_lt hupper hstrict

end CKN
