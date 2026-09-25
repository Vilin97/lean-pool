/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedGeometry
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Finite one-sided coverings and total integral estimates

A finite metric-ball cover of the closed intermediate cylinder gives a
finite backward-cylinder cover after truncating the forward time shifts.
All centers and the number of cylinders are chosen before the integrand.
-/

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Core.Endgame

private theorem compact_closed_intermediate_cylinder {a : ℝ} (ha : 0 < a) :
    IsCompact (closure (parabolicCylinder (0 : Vec3) 0 a)) := by
  have hspace : IsCompact {x : Vec3 | vec3EuclideanNorm (x - 0) ≤ a} := by
    have hcompact := vec3Homeomorph.isCompact_preimage.mpr
      (isCompact_closedBall (vec3Homeomorph (0 : Vec3)) a)
    convert hcompact using 1
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_closedBall,
      vec3Homeomorph_apply, dist_eq_norm, ← WithLp.toLp_sub,
      ← vec3EuclideanNorm_eq_l2]
  apply parabolicHomeomorph.symm.isCompact_preimage.mp
  rw [closure_parabolicCylinder ha]
  exact hspace.prod isCompact_Icc

private theorem ball_inter_le_subset_truncated_self
    {z : ParabolicPoint} {δ T : ℝ} (hδ : 0 < δ) :
    ball z δ ∩ {w : ParabolicPoint | w.2 ≤ T} ⊆
      parabolicCylinder (truncatedCylinderCenter z z δ T).1
        (truncatedCylinderCenter z z δ T).2 (2 * δ) := by
  intro w hw
  obtain ⟨hball, ht⟩ := hw
  rw [mem_ball, dist_eq_parabolicDist] at hball
  have hx := (max_lt_iff.mp hball).1
  have htime := (Real.sqrt_lt (abs_nonneg _) hδ.le).mp (max_lt_iff.mp hball).2
  have habs := abs_lt.mp htime
  change vec3EuclideanNorm (w.1 - z.1) < 2 * δ ∧
    min (z.2 + δ ^ 2) T - (2 * δ) ^ 2 < w.2 ∧
    w.2 ≤ min (z.2 + δ ^ 2) T
  refine ⟨hx.trans (by linarith only [hδ]), ?_, le_min ?_ ht⟩
  · have hmin := min_le_left (z.2 + δ ^ 2) T
    nlinarith only [habs.1, hmin, sq_nonneg δ]
  · linarith only [habs.2]

private theorem truncated_self_center_mem_three_quarters
    {z : ParabolicPoint} {δ a : ℝ} (ha : 0 < a) (ha34 : a < 3 / 4)
    (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 a)) :
    truncatedCylinderCenter z z δ 0 ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4) := by
  rw [closure_parabolicCylinder ha] at hz
  change vec3EuclideanNorm (z.1 - 0) ≤ a ∧
    0 - a ^ 2 ≤ z.2 ∧ z.2 ≤ 0 at hz
  change vec3EuclideanNorm (z.1 - 0) < 3 / 4 ∧
    0 - (3 / 4 : ℝ) ^ 2 < min (z.2 + δ ^ 2) 0 ∧ min (z.2 + δ ^ 2) 0 ≤ 0
  refine ⟨lt_of_le_of_lt hz.1 ha34, ?_, min_le_right _ _⟩
  have hzmin : z.2 ≤ min (z.2 + δ ^ 2) 0 :=
    le_min (le_add_of_nonneg_right (sq_nonneg δ)) hz.2.2
  have hbottom : 0 - (3 / 4 : ℝ) ^ 2 < z.2 := by
    have hsq : a ^ 2 < (3 / 4 : ℝ) ^ 2 := by nlinarith only [ha, ha34]
    linarith only [hz.2.1, hsq]
  exact hbottom.trans_le hzmin

/-- At every prescribed positive scale, finitely many cylinders of half
that radius, with admissible centers, cover the intermediate cylinder.
The selected centers depend only on the scale and the fixed geometry. -/
theorem exists_finite_one_sided_cylinder_cover_on_cylinder
    (a ρ₀ : ℝ) (ha : 0 < a) (ha34 : a < 3 / 4) (hρ₀ : 0 < ρ₀) :
    ∃ s : Finset ParabolicPoint,
      (∀ z ∈ s, z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4)) ∧
      parabolicCylinder (0 : Vec3) 0 a ⊆
        ⋃ z ∈ s, parabolicCylinder z.1 z.2 (ρ₀ / 2) := by
  classical
  let K : Set ParabolicPoint := closure (parabolicCylinder (0 : Vec3) 0 a)
  have hδ : 0 < ρ₀ / 4 := by positivity
  have hcover : K ⊆ ⋃ z ∈ K, ball z (ρ₀ / 4) := by
    intro z hz
    exact mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, mem_ball_self hδ⟩⟩
  obtain ⟨b, hbK, hbfinite, hbcover⟩ :=
    (compact_closed_intermediate_cylinder ha).elim_finite_subcover_image
      (fun _ _ => isOpen_ball) hcover
  let c : ParabolicPoint → ParabolicPoint := fun z => truncatedCylinderCenter z z (ρ₀ / 4) 0
  refine ⟨hbfinite.toFinset.image c, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact truncated_self_center_mem_three_quarters ha ha34 (hbK (hbfinite.mem_toFinset.mp hw))
  · intro w hw
    obtain ⟨z, hz⟩ := mem_iUnion.mp (hbcover (subset_closure hw))
    obtain ⟨hzb, hwball⟩ := mem_iUnion.mp hz
    have hzimage : c z ∈ hbfinite.toFinset.image c :=
      Finset.mem_image.mpr ⟨z, hbfinite.mem_toFinset.mpr hzb, rfl⟩
    refine mem_iUnion.mpr ⟨c z, mem_iUnion.mpr ⟨hzimage, ?_⟩⟩
    have htime : w.2 ≤ 0 := hw.2.2
    have hmem := ball_inter_le_subset_truncated_self hδ ⟨hwball, htime⟩
    convert hmem using 1
    dsimp [c]
    congr 1
    ring

/-- A finite geometric multiplicity turns uniform small-cylinder integral
bounds into a total bound on the intermediate cylinder. The integer is
chosen before the integrand or its bound, so its dependence is only on the
fixed geometry and `ρ₀`. -/
theorem exists_one_sided_integral_constant_on_cylinder
    (a ρ₀ : ℝ) (ha : 0 < a) (ha34 : a < 3 / 4) (hρ₀ : 0 < ρ₀) :
    ∃ N : ℕ, ∀ F : ParabolicPoint → ℝ≥0∞, ∀ B : ℝ≥0∞,
      (∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
        (∫⁻ w in parabolicCylinder z.1 z.2 (ρ₀ / 2), F w) ≤ B) →
      (∫⁻ w in parabolicCylinder (0 : Vec3) 0 a, F w) ≤ (N : ℝ≥0∞) * B := by
  classical
  obtain ⟨s, hscenters, hscover⟩ :=
    exists_finite_one_sided_cylinder_cover_on_cylinder a ρ₀ ha ha34 hρ₀
  refine ⟨s.card, fun F B hB => ?_⟩
  have hcover : parabolicCylinder (0 : Vec3) 0 a ⊆
      ⋃ z : s, parabolicCylinder z.1.1 z.1.2 (ρ₀ / 2) := by
    intro w hw
    obtain ⟨z, hz⟩ := mem_iUnion.mp (hscover hw)
    obtain ⟨hzs, hwz⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨⟨z, hzs⟩, hwz⟩
  calc
    _ ≤ ∫⁻ w in ⋃ z : s, parabolicCylinder z.1.1 z.1.2 (ρ₀ / 2), F w :=
      lintegral_mono_set hcover
    _ ≤ ∑' z : s, ∫⁻ w in parabolicCylinder z.1.1 z.1.2 (ρ₀ / 2), F w :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' _z : s, B := ENNReal.tsum_le_tsum fun z => hB z.1 (hscenters z.1 z.2)
    _ = (s.card : ℝ≥0∞) * B := by simp only [tsum_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]


/-- A geometric multiplicity bounds the total integral on the fixed cylinder. -/
theorem exists_one_sided_integral_constant (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) :
    ∃ N : ℕ, ∀ F : ParabolicPoint → ℝ≥0∞, ∀ B : ℝ≥0∞,
      (∀ z ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4),
        (∫⁻ w in parabolicCylinder z.1 z.2 (ρ₀ / 2), F w) ≤ B) →
      (∫⁻ w in parabolicCylinder (0 : Vec3) 0 (5 / 8), F w) ≤ (N : ℝ≥0∞) * B :=
  exists_one_sided_integral_constant_on_cylinder (5 / 8) ρ₀
    (by norm_num) (by norm_num) hρ₀

end CKN.Core.Endgame
