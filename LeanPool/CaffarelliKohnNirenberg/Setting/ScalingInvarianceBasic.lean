/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingQuantities
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Scaling Invariance Basic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology Pointwise
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- Spatial part of the parabolic change of variables. -/
def scalingSpace (μ : ℝ) (x₀ : Vec3) : Vec3 → Vec3 :=
  fun y => x₀ + μ • y

/-- Temporal part of the parabolic change of variables. -/
def scalingTime (μ : ℝ) (t₀ : ℝ) : ℝ → ℝ :=
  fun s => t₀ + μ ^ 2 * s

/-- Parabolic dilation followed by space-time translation. -/
def scalingParabolic (μ : ℝ) (z₀ : ParabolicPoint) :
    ParabolicPoint → ParabolicPoint :=
  fun z => parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)

/-- Spatial domain pulled back under the parabolic change of variables. -/
def rescaledSpace (μ : ℝ) (x₀ : Vec3) (Ω : Set Vec3) : Set Vec3 :=
  scalingSpace μ x₀ ⁻¹' Ω

/-- Time domain pulled back under the parabolic change of variables. -/
def rescaledTime (μ : ℝ) (t₀ : ℝ) (I : Set ℝ) : Set ℝ :=
  scalingTime μ t₀ ⁻¹' I

theorem scalingParabolic_eq (μ : ℝ) (z₀ : ParabolicPoint) :
    scalingParabolic μ z₀ =
      fun z => (scalingSpace μ z₀.1 z.1, scalingTime μ z₀.2 z.2) := by
  funext z
  rfl

theorem rescaledSpaceTimeSet_eq_preimage (μ : ℝ) (z₀ : ParabolicPoint)
    (Ω : Set Vec3) (I : Set ℝ) :
    spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) =
      scalingParabolic μ z₀ ⁻¹' spaceTimeSet Ω I := by
  ext z
  rcases z with ⟨y, s⟩
  rfl

private theorem scalingSpace_continuous (μ : ℝ) (x₀ : Vec3) :
    Continuous (scalingSpace μ x₀) := by
  change Continuous (fun y : Vec3 => x₀ + μ • y)
  fun_prop

private theorem scalingTime_continuous (μ : ℝ) (t₀ : ℝ) :
    Continuous (scalingTime μ t₀) := by
  change Continuous (fun s : ℝ => t₀ + μ ^ 2 * s)
  fun_prop

private theorem scalingParabolic_continuous (μ : ℝ) (z₀ : ParabolicPoint) :
    Continuous (scalingParabolic μ z₀) := by
  rw [scalingParabolic_eq]
  exact continuous_prod_to_parabolicPoint.comp
    (((scalingSpace_continuous μ z₀.1).comp continuous_fst |>.prodMk
      ((scalingTime_continuous μ z₀.2).comp continuous_snd)).comp
        continuous_parabolicPoint_to_prod)

theorem rescaledSpace_isOpen {μ : ℝ} (x₀ : Vec3) {Ω : Set Vec3}
    (hΩ : IsOpen Ω) : IsOpen (rescaledSpace μ x₀ Ω) :=
  hΩ.preimage (scalingSpace_continuous μ x₀)

theorem rescaledTime_isOpen {μ : ℝ} (t₀ : ℝ) {I : Set ℝ}
    (hI : IsOpen I) : IsOpen (rescaledTime μ t₀ I) :=
  hI.preimage (scalingTime_continuous μ t₀)

theorem rescaledTime_ordConnected {μ : ℝ} (_ : 0 < μ) (t₀ : ℝ)
    {I : Set ℝ} (hI : I.OrdConnected) :
    (rescaledTime μ t₀ I).OrdConnected := by
  apply hI.preimage_mono
  intro a b hab
  dsimp [scalingTime]
  simpa [add_comm] using
    (add_le_add_left (mul_le_mul_of_nonneg_left hab (sq_nonneg μ)) t₀)

/-- Homeomorphism underlying the spatial scaling map. -/
def scalingSpaceHomeomorph (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) :
    Vec3 ≃ₜ Vec3 :=
  (Homeomorph.smulOfNeZero μ hμ.ne').trans (Homeomorph.addLeft x₀)

private theorem scalingSpace_eq_homeomorph (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) :
    scalingSpace μ x₀ = scalingSpaceHomeomorph μ hμ x₀ := by
  funext y
  simp [scalingSpace, scalingSpaceHomeomorph]

/-- Homeomorphism underlying the temporal scaling map. -/
def scalingTimeHomeomorph (μ : ℝ) (hμ : 0 < μ) (t₀ : ℝ) :
    ℝ ≃ₜ ℝ :=
  (Homeomorph.smulOfNeZero (μ ^ 2) (sq_pos_of_pos hμ).ne').trans
    (Homeomorph.addLeft t₀)

private theorem scalingTime_eq_homeomorph (μ : ℝ) (hμ : 0 < μ) (t₀ : ℝ) :
    scalingTime μ t₀ = scalingTimeHomeomorph μ hμ t₀ := by
  funext s
  simp [scalingTime, scalingTimeHomeomorph, smul_eq_mul]

/-- Inverse temporal affine map used in scaling the weak equations. -/
def scalingTimeInv (μ : ℝ) (t₀ : ℝ) : ℝ → ℝ :=
  fun s => (μ ^ 2)⁻¹ * (s - t₀)

private theorem scalingTime_left_inverse (μ : ℝ) (hμ : 0 < μ) (t₀ s : ℝ) :
    scalingTimeInv μ t₀ (scalingTime μ t₀ s) = s := by
  dsimp [scalingTimeInv, scalingTime]
  field_simp [hμ.ne']
  ring

private theorem scalingTime_right_inverse (μ : ℝ) (hμ : 0 < μ) (t₀ s : ℝ) :
    scalingTime μ t₀ (scalingTimeInv μ t₀ s) = s := by
  dsimp [scalingTimeInv, scalingTime]
  field_simp [hμ.ne']
  ring

private theorem scalingTime_image_eq_preimage {μ : ℝ} (hμ : 0 < μ) (t₀ : ℝ)
    (J : Set ℝ) :
    scalingTime μ t₀ '' J = scalingTimeInv μ t₀ ⁻¹' J := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    change scalingTimeInv μ t₀ (scalingTime μ t₀ t) ∈ J
    simpa only [scalingTime_left_inverse μ hμ t₀ t] using ht
  · intro hs
    change scalingTimeInv μ t₀ s ∈ J at hs
    exact ⟨scalingTimeInv μ t₀ s, hs,
      scalingTime_right_inverse μ hμ t₀ s⟩

private theorem scalingTimeInv_monotone {μ : ℝ} (_ : 0 < μ) (t₀ : ℝ) :
    Monotone (scalingTimeInv μ t₀) := by
  intro a b hab
  dsimp [scalingTimeInv]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hab t₀)
    (inv_nonneg.mpr (sq_nonneg μ))

theorem map_scalingSpace (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) :
    Measure.map (scalingSpace μ x₀) (volume : Measure Vec3) =
      ENNReal.ofReal (μ⁻¹ ^ 3) • (volume : Measure Vec3) := by
  have h : scalingSpace μ x₀ =
      (fun y : Vec3 => x₀ + y) ∘ (fun y : Vec3 => μ • y) := by
    funext y
    simp [scalingSpace]
  rw [h, ← Measure.map_map (measurable_const_add x₀) (measurable_const_smul μ)]
  rw [Measure.map_addHaar_smul (μ := (volume : Measure Vec3)) hμ.ne',
    Measure.map_smul]
  on_goal 1 => rw [MeasureTheory.map_add_left_eq_self]
  · congr 1
    rw [Module.finrank_fin_fun, abs_of_pos (inv_pos.mpr (pow_pos hμ 3)), ← inv_pow]
  · exact (measurable_const_add x₀).aemeasurable

theorem map_scalingTime (μ : ℝ) (hμ : 0 < μ) (t₀ : ℝ) :
    Measure.map (scalingTime μ t₀) (volume : Measure ℝ) =
      ENNReal.ofReal ((μ ^ 2)⁻¹) • (volume : Measure ℝ) := by
  have h : scalingTime μ t₀ =
      (fun s : ℝ => t₀ + s) ∘ (fun s : ℝ => μ ^ 2 • s) := by
    funext s
    simp [scalingTime, smul_eq_mul]
  rw [h, ← Measure.map_map (measurable_const_add t₀)
    (measurable_const_smul (μ ^ 2))]
  rw [Measure.map_addHaar_smul (μ := (volume : Measure ℝ))
    (sq_pos_of_pos hμ).ne', Measure.map_smul]
  on_goal 1 => rw [MeasureTheory.map_add_left_eq_self]
  · congr 1
    rw [Module.finrank_self]
    norm_num
  · exact (measurable_const_add t₀).aemeasurable

theorem map_scalingParabolic (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    Measure.map (scalingParabolic μ z₀) (volume : Measure ParabolicPoint) =
      ENNReal.ofReal (μ⁻¹ ^ 5) • (volume : Measure ParabolicPoint) := by
  have hcoef : ENNReal.ofReal (μ⁻¹ ^ 3) * ENNReal.ofReal ((μ ^ 2)⁻¹) =
      ENNReal.ofReal (μ⁻¹ ^ 5) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [inv_pow, inv_pow]
    rw [mul_comm (μ ^ 3)⁻¹, ← mul_inv_rev, ← pow_add]
  have hmap := Measure.map_prod_map (volume : Measure Vec3) (volume : Measure ℝ)
    (scalingSpaceHomeomorph μ hμ z₀.1).measurable
    (scalingTimeHomeomorph μ hμ z₀.2).measurable
  rw [← scalingSpace_eq_homeomorph μ hμ z₀.1,
    ← scalingTime_eq_homeomorph μ hμ z₀.2] at hmap
  rw [map_scalingSpace μ hμ z₀.1, map_scalingTime μ hμ z₀.2,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul] at hmap
  have hvol : (volume : Measure (Vec3 × ℝ)) =
      (volume : Measure Vec3).prod (volume : Measure ℝ) := rfl
  have hmap' : ENNReal.ofReal (μ⁻¹ ^ 5) •
      (volume : Measure (Vec3 × ℝ)) =
      Measure.map (fun z : Vec3 × ℝ =>
        (z₀.1 + μ • z.1, z₀.2 + μ ^ 2 * z.2))
        (volume : Measure (Vec3 × ℝ)) := by
    rw [← hcoef, hvol]
    change (ENNReal.ofReal (μ⁻¹ ^ 3) * ENNReal.ofReal ((μ ^ 2)⁻¹)) •
        (volume : Measure Vec3).prod (volume : Measure ℝ) =
      Measure.map (Prod.map (scalingSpace μ z₀.1) (scalingTime μ z₀.2))
        ((volume : Measure Vec3).prod (volume : Measure ℝ))
    exact hmap
  exact hmap'.symm

theorem map_scalingSpace_restrict {μ : ℝ} (hμ : 0 < μ) (x₀ : Vec3)
    {Ω : Set Vec3} (hΩ : MeasurableSet Ω) :
    Measure.map (scalingSpace μ x₀)
        (volume.restrict (rescaledSpace μ x₀ Ω)) =
      ENNReal.ofReal (μ⁻¹ ^ 3) • volume.restrict Ω := by
  have h := Measure.restrict_map (μ := (volume : Measure Vec3))
    ((scalingSpaceHomeomorph μ hμ x₀).measurable) hΩ
  calc
    Measure.map (scalingSpace μ x₀)
        (volume.restrict (rescaledSpace μ x₀ Ω)) =
        Measure.map (scalingSpaceHomeomorph μ hμ x₀)
          (volume.restrict ((scalingSpaceHomeomorph μ hμ x₀) ⁻¹' Ω)) := by
            rw [rescaledSpace, scalingSpace_eq_homeomorph μ hμ x₀]
    _ = (Measure.map (scalingSpaceHomeomorph μ hμ x₀) volume).restrict Ω := h.symm
    _ = ENNReal.ofReal (μ⁻¹ ^ 3) • volume.restrict Ω := by
      have hs := map_scalingSpace μ hμ x₀
      rw [scalingSpace_eq_homeomorph μ hμ x₀] at hs
      have hs' := congrArg (fun m => m.restrict Ω) hs
      rw [Measure.restrict_smul] at hs'
      exact hs'

theorem map_scalingTime_restrict {μ : ℝ} (hμ : 0 < μ) (t₀ : ℝ)
    {I : Set ℝ} (hI : MeasurableSet I) :
    Measure.map (scalingTime μ t₀)
        (volume.restrict (rescaledTime μ t₀ I)) =
      ENNReal.ofReal ((μ ^ 2)⁻¹) • volume.restrict I := by
  have h := Measure.restrict_map (μ := (volume : Measure ℝ))
    ((scalingTimeHomeomorph μ hμ t₀).measurable) hI
  calc
    Measure.map (scalingTime μ t₀)
        (volume.restrict (rescaledTime μ t₀ I)) =
        Measure.map (scalingTimeHomeomorph μ hμ t₀)
          (volume.restrict ((scalingTimeHomeomorph μ hμ t₀) ⁻¹' I)) := by
            rw [rescaledTime, scalingTime_eq_homeomorph μ hμ t₀]
    _ = (Measure.map (scalingTimeHomeomorph μ hμ t₀) volume).restrict I := h.symm
    _ = ENNReal.ofReal ((μ ^ 2)⁻¹) • volume.restrict I := by
      have hs := map_scalingTime μ hμ t₀
      rw [scalingTime_eq_homeomorph μ hμ t₀] at hs
      have hs' := congrArg (fun m => m.restrict I) hs
      rw [Measure.restrict_smul] at hs'
      exact hs'

theorem map_scalingParabolic_restrict {μ : ℝ} (hμ : 0 < μ)
    (z₀ : ParabolicPoint) {Ω : Set Vec3} {I : Set ℝ}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I) :
    Measure.map (scalingParabolic μ z₀)
        (volume.restrict (spaceTimeSet (rescaledSpace μ z₀.1 Ω)
          (rescaledTime μ z₀.2 I))) =
      ENNReal.ofReal (μ⁻¹ ^ 5) • volume.restrict (spaceTimeSet Ω I) := by
  have hset : spaceTimeSet (rescaledSpace μ z₀.1 Ω)
      (rescaledTime μ z₀.2 I) = scalingParabolic μ z₀ ⁻¹'
        spaceTimeSet Ω I := rescaledSpaceTimeSet_eq_preimage μ z₀ Ω I
  have h :
      (Measure.map (scalingParabolic μ z₀) (volume : Measure ParabolicPoint)).restrict
          (spaceTimeSet Ω I) =
        Measure.map (scalingParabolic μ z₀)
          ((volume : Measure ParabolicPoint).restrict
            (scalingParabolic μ z₀ ⁻¹' spaceTimeSet Ω I)) :=
    Measure.restrict_map (μ := (volume : Measure ParabolicPoint))
      (scalingParabolic_continuous μ z₀).measurable (hΩ.prod hI)
  rw [map_scalingParabolic μ hμ z₀, Measure.restrict_smul] at h
  rw [hset]
  exact h.symm

theorem localBox_forward {μ : ℝ} (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (rescaledSpace μ z₀.1 Ω)
      (rescaledTime μ z₀.2 I) Ω' J) :
    localBox Ω I (scalingSpace μ z₀.1 '' Ω')
      (scalingTime μ z₀.2 '' J) := by
  rcases hbox with ⟨hΩ'op, hΩ'c, hΩ'Ω, hJord, hJc, hJI⟩
  let eΩ := scalingSpaceHomeomorph μ hμ z₀.1
  let eI := scalingTimeHomeomorph μ hμ z₀.2
  have heΩ : scalingSpace μ z₀.1 = eΩ := scalingSpace_eq_homeomorph μ hμ z₀.1
  have heI : scalingTime μ z₀.2 = eI := scalingTime_eq_homeomorph μ hμ z₀.2
  have hΩclosure :
      closure (scalingSpace μ z₀.1 '' Ω') = eΩ '' closure Ω' := by
    rw [heΩ, ← eΩ.image_closure]
  have hJclosure :
      closure (scalingTime μ z₀.2 '' J) = eI '' closure J := by
    rw [heI, ← eI.image_closure]
  refine ⟨eΩ.isOpenMap Ω' hΩ'op, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hΩclosure]
    exact hΩ'c.image eΩ.continuous
  · rw [hΩclosure]
    rintro y ⟨x, hx, rfl⟩
    rw [← heΩ]
    exact hΩ'Ω hx
  · rw [scalingTime_image_eq_preimage hμ z₀.2 J]
    exact hJord.preimage_mono (scalingTimeInv_monotone hμ z₀.2)
  · rw [hJclosure]
    exact hJc.image eI.continuous
  · rw [hJclosure]
    rintro s ⟨t, ht, rfl⟩
    rw [← heI]
    exact hJI ht

end CKN
