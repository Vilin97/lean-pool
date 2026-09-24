/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseGrowth

/-! # Backward patches up to the final time of an origin carrier

Relative neighborhoods of the closed inner carrier are covered by spatial
half-balls and backward windows contained in the larger Morrey carrier.
At final time zero the neighborhood extends past zero, while its intersection
with the carrier is still controlled by a backward window ending at zero.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic
noncomputable section
namespace CKN.Core.Step4

/-- A closed-carrier point has a relatively open neighborhood controlled by
one fixed backward localization entirely inside the larger carrier. -/
theorem originClause_backward_derivative_patch
    {R₀ R₁ : ℝ} (hR₁ : 0 < R₁) (hgap : R₁ < R₀)
    {w : ParabolicPoint} (hw : w ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁)) :
    ∃ (z : ParabolicPoint) (ρ : ℝ) (U : Set ParabolicPoint),
      0 < ρ ∧ IsOpen U ∧ w ∈ U ∧
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ closure (parabolicCylinder (0 : Vec3) 0 R₀) ∧
      parabolicCylinder z.1 z.2 ρ ⊆ parabolicCylinder (0 : Vec3) 0 R₀ ∧
      vec3Ball z.1 (ρ/2) ⊆ vec3Ball (0 : Vec3) R₀ ∧
      U ∩ parabolicCylinder (0 : Vec3) 0 R₁ ⊆
        vec3Ball z.1 (ρ/2) ×ˢ Ioc (z.2-ρ^2) z.2 := by
  classical
  let ρ := (R₀-R₁)/4
  let t := min (w.2+ρ^2/2) 0
  let b := if t = 0 then 1 else t
  let U : Set ParabolicPoint := vec3Ball w.1 (ρ/2) ×ˢ Ioo (t-ρ^2) b
  have hρ : 0 < ρ := by dsimp [ρ]; linarith only [hgap]
  have hρgap : ρ < R₀-R₁ := by dsimp [ρ]; linarith only [hgap]
  have hR₀ : 0 < R₀ := hR₁.trans hgap
  have hws := hw
  rw [closure_parabolicCylinder hR₁] at hws
  have hwx : vec3EuclideanNorm (w.1-0) ≤ R₁ := hws.1
  have hwlo : -R₁^2 ≤ w.2 := by simpa only [zero_sub] using hws.2.1
  have hwhi : w.2 ≤ 0 := hws.2.2
  have htlo : w.2 ≤ t := le_min (by linarith only [sq_nonneg ρ]) hwhi
  have hthi : t ≤ 0 := min_le_right _ _
  have htl : t-ρ^2 < w.2 := by
    have hh : t ≤ w.2+ρ^2/2 := min_le_left _ _
    nlinarith only [hh, sq_pos_of_pos hρ]
  have htu : w.2 < b := by
    dsimp only [b]
    split_ifs with he
    · linarith only [hwhi]
    · have heq : t = w.2+ρ^2/2 := min_eq_left (le_of_not_ge (fun h => he (min_eq_right h)))
      rw [heq]
      linarith only [sq_pos_of_pos hρ]
  have hsquare : R₁^2+ρ^2 < R₀^2 := by
    have hprod := mul_pos (sub_pos.mpr hgap) hR₁
    have hsq := (sq_lt_sq₀ hρ.le (sub_pos.mpr hgap).le).mpr hρgap
    nlinarith only [hprod, hsq]
  have htri (y : Vec3) : vec3EuclideanNorm (y-0) ≤
      vec3EuclideanNorm (y-w.1) + vec3EuclideanNorm (w.1-0) := by
    simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub]
    simpa only [dist_eq_norm] using
      dist_triangle (WithLp.toLp 2 y) (WithLp.toLp 2 w.1) (WithLp.toLp 2 (0 : Vec3))
  have hsp (y : Vec3) (hy : vec3EuclideanNorm (y-w.1) ≤ ρ) :
      vec3EuclideanNorm (y-0) < R₀ := by
    linarith only [htri y, hy, hwx, hρgap]
  refine ⟨(w.1,t), ρ, U, hρ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_spaceTimeSet _ _ (isOpen_vec3Ball _ _) isOpen_Ioo
  · exact ⟨by simpa only [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero] using half_pos hρ,
      htl, htu⟩
  · rw [closure_parabolicCylinder hρ, closure_parabolicCylinder hR₀]
    intro v hv
    exact ⟨(hsp v.1 hv.1).le,
      by dsimp only [Prod.fst, Prod.snd] at hv; nlinarith only [hv.2.1, htlo, hwlo, hsquare],
      hv.2.2.trans hthi⟩
  · intro v hv
    exact ⟨hsp v.1 hv.1.le,
      by change 0-R₀^2 < v.2; nlinarith only [hv.2.1, htlo, hwlo, hsquare],
      hv.2.2.trans hthi⟩
  · intro y hy
    apply hsp y
    change vec3EuclideanNorm (y-w.1) < ρ/2 at hy
    linarith only [hy, hρ]
  · intro v hv
    refine ⟨hv.1.1, hv.1.2.1, ?_⟩
    by_cases he : t = 0
    · simpa only [he] using hv.2.2.2
    · have hb : b = t := ite_eq_right he
      exact (hb ▸ hv.1.2.2).le

/-- Closed cylinder containment gives the exact spatial ball and backward
window as a local suitable-solution box. -/
theorem originClause_localBox_of_closed_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    localBox Ω I (vec3Ball z.1 ρ) (Ioc (z.2-ρ^2) z.2) := by
  have hcl : closure (Ioc (z.2-ρ^2) z.2) ⊆ Icc (z.2-ρ^2) z.2 :=
    closure_minimal Ioc_subset_Icc_self isClosed_Icc
  rw [closure_parabolicCylinder hρ] at hsub
  refine ⟨isOpen_vec3Ball _ _, originClauseIsCompact_closure_vec3Ball hρ, ?_,
    ordConnected_Ioc, isCompact_Icc.of_isClosed_subset isClosed_closure hcl, ?_⟩
  · intro y hy
    rw [closure_vec3Ball hρ] at hy
    exact (hsub (a := (y,z.2)) ⟨hy, by linarith only [sq_nonneg ρ], le_rfl⟩).1
  · intro s hs
    exact (hsub (a := (z.1,s)) ⟨by simpa only [Set.mem_ofPred_eq, sub_self, vec3EuclideanNorm_zero] using hρ.le, hcl hs⟩).2

/-- The closure of a backward origin carrier is compact. -/
theorem originClause_closed_carrier_compact {R : ℝ} (hR : 0 < R) :
    IsCompact (closure (parabolicCylinder (0 : Vec3) 0 R)) := by
  rw [closure_parabolicCylinder hR]
  have hx := originClauseIsCompact_closure_vec3Ball (x := (0 : Vec3)) hR
  rw [closure_vec3Ball hR] at hx
  have hp := hx.prod (isCompact_Icc : IsCompact (Icc (0-R^2) (0 : ℝ)))
  exact parabolicHomeomorph.isCompact_preimage.mpr hp

end CKN.Core.Step4
