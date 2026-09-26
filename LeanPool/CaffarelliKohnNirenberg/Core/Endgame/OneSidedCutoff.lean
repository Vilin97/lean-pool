/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedGeometry
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Statements.LocalBox
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Domain localization preserving a fixed negative-time cutoff

The fixed smooth cutoff is chosen independently of the domain. Multiplying
it by a cutoff equal to one near the closed unit cylinder makes it admissible
on any open domain containing that cylinder. At every point of time at most
zero, the resulting function agrees locally with the fixed cutoff. Thus its
negative-time derivatives do not acquire domain-dependent constants.
-/

public section

open Set Metric Filter
open scoped Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Core.Endgame

private theorem compact_spatial_closedBall (r : ℝ) :
    IsCompact {x : Vec3 | vec3EuclideanNorm (x - 0) ≤ r} := by
  have hcompact := vec3Homeomorph.isCompact_preimage.mpr
    (isCompact_closedBall (vec3Homeomorph (0 : Vec3)) r)
  convert hcompact using 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage, mem_closedBall,
    vec3Homeomorph_apply, dist_eq_norm, ← WithLp.toLp_sub,
    ← vec3EuclideanNorm_eq_l2]

/-- The closed unit cylinder admits a compactly interior product box with
an open time interval, without any connectedness assumption on the ambient
time set. -/
theorem exists_localBox_around_closed_unit
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hunit : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I) :
    ∃ Ω' J, localBox Ω I Ω' J ∧ IsOpen J ∧
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω' J := by
  have hcl : closure (parabolicCylinder (0 : Vec3) 0 1) =
      {x : Vec3 | vec3EuclideanNorm (x - 0) ≤ 1} ×ˢ Icc (-1 : ℝ) 0 := by
    rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1)]
    norm_num
    rfl
  have hXΩ : {x : Vec3 | vec3EuclideanNorm (x - 0) ≤ 1} ⊆ Ω := by
    intro x hx
    have hmem : parabolicHomeomorph.symm (x, 0) ∈
        closure (parabolicCylinder (0 : Vec3) 0 1) := by
      rw [hcl]
      exact ⟨hx, by norm_num⟩
    exact (hunit hmem).1
  have hTI : Icc (-1 : ℝ) 0 ⊆ I := by
    intro t ht
    have hmem : parabolicHomeomorph.symm ((0 : Vec3), t) ∈
        closure (parabolicCylinder (0 : Vec3) 0 1) := by
      rw [hcl]
      change vec3EuclideanNorm ((0 : Vec3) - 0) ≤ 1 ∧ t ∈ Icc (-1 : ℝ) 0
      exact ⟨by simp only [sub_self, vec3EuclideanNorm_zero]; norm_num, ht⟩
    exact (hunit hmem).2
  obtain ⟨Ω', hΩ'open, hXΩ', hΩ'Ω, hΩ'compact⟩ :=
    exists_open_between_and_isCompact_closure (compact_spatial_closedBall 1) hΩ hXΩ
  obtain ⟨δ, hδ, hδI⟩ := isCompact_Icc.exists_thickening_subset_open hI hTI
  have hlt : -1 - δ / 2 < δ / 2 := by linarith only [hδ]
  have hJsub : Icc (-1 - δ / 2) (δ / 2) ⊆ I := by
    intro t ht
    apply hδI
    rw [mem_thickening_iff]
    by_cases hlow : t ≤ -1
    · refine ⟨-1, by norm_num, ?_⟩
      rw [Real.dist_eq, abs_of_nonpos (by linarith only [hlow])]
      linarith only [ht.1, hδ]
    · by_cases hhigh : t ≤ 0
      · exact ⟨t, ⟨(lt_of_not_ge hlow).le, hhigh⟩, by simpa only [dist_self] using hδ⟩
      · refine ⟨0, by norm_num, ?_⟩
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_of_not_ge hhigh)]
        linarith only [ht.2, hδ]
  refine ⟨Ω', Ioo (-1 - δ / 2) (δ / 2),
    ⟨hΩ'open, hΩ'compact, hΩ'Ω, ordConnected_Ioo, ?_, ?_⟩, isOpen_Ioo, ?_⟩
  · rw [closure_Ioo hlt.ne]
    exact isCompact_Icc
  · rw [closure_Ioo hlt.ne]
    exact hJsub
  · intro z hz
    rw [hcl] at hz
    exact ⟨hXΩ' hz.1, ⟨by linarith only [hz.2.1, hδ],
      by linarith only [hz.2.2, hδ]⟩⟩

end CKN.Core.Endgame
