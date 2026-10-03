/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyPoincare

/-!
# Seeley Scaling

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace CKN

noncomputable section

/-- Affine map transporting the unit ball to a ball centered at `x₀` with scale `r`. -/
@[expose] def seeleyAffineMap (x₀ : Vec 3) (r : ℝ) (x : Vec 3) : Vec 3 :=
  x₀ + r • x

private theorem seeleyAffineMap_preimage (x₀ : Vec 3) {r : ℝ} (hr : 0 < r) :
    seeleyAffineMap x₀ r ⁻¹' euclideanBall x₀ r = euclideanBall (0 : Vec 3) 1 := by
  ext x
  constructor
  · intro hx
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx
    dsimp [seeleyAffineMap] at hx'
    rw [add_sub_cancel_left, vecEuclideanNorm_smul, abs_of_pos hr] at hx'
    exact lt_of_mul_lt_mul_left (by simpa using hx') hr.le
  · intro hx
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
    dsimp [seeleyAffineMap]
    rw [add_sub_cancel_left, vecEuclideanNorm_smul, abs_of_pos hr]
    simpa [sub_zero] using mul_lt_mul_of_pos_left hx' hr

private theorem seeleyAffineMap_measurableEmbedding {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding (seeleyAffineMap x₀ r) := by
  have hs := measurableEmbedding_const_smul₀ (α := Vec 3) hr.ne'
  have ha := (MeasurableEquiv.addLeft x₀).measurableEmbedding
  have hc := ha.comp hs
  change MeasurableEmbedding (fun x : Vec 3 => x₀ + r • x)
  exact hc

private theorem seeleyAffineMap_volume {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) :
    Measure.map (seeleyAffineMap x₀ r) (volume : Measure (Vec 3)) =
      ENNReal.ofReal (r⁻¹ ^ 3) • volume := by
  have hsmul := Measure.map_addHaar_smul (volume : Measure (Vec 3)) hr.ne'
  have htrans := MeasureTheory.map_add_left_eq_self (volume : Measure (Vec 3)) x₀
  have hcomp : seeleyAffineMap x₀ r =
      (fun y : Vec 3 => x₀ + y) ∘ (fun y : Vec 3 => r • y) := by
    funext y
    rfl
  rw [hcomp, ← Measure.map_map (measurable_const_add x₀)
    (measurable_const_smul r), hsmul,
    Measure.map_smul _ (measurable_const_add x₀).aemeasurable]
  rw [htrans]
  congr 1
  rw [Module.finrank_pi, Fintype.card_fin]
  simp [abs_of_pos (pow_pos hr 3), inv_pow]

private theorem seeleyAffineMap_restrict {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) :
    Measure.map (seeleyAffineMap x₀ r)
        (volume.restrict (euclideanBall (0 : Vec 3) 1)) =
      ENNReal.ofReal (r⁻¹ ^ 3) • volume.restrict (euclideanBall x₀ r) := by
  have he := seeleyAffineMap_measurableEmbedding (x₀ := x₀) hr
  have hres := he.restrict_map (volume : Measure (Vec 3))
    (euclideanBall x₀ r)
  rw [seeleyAffineMap_volume (x₀ := x₀) hr] at hres
  rw [Measure.restrict_smul] at hres
  rw [seeleyAffineMap_preimage x₀ hr] at hres
  exact hres.symm

theorem seeleyAffine_eLpNorm_comp {x₀ : Vec 3} {r : ℝ} (hr : 0 < r)
    {β : Type*} [NormedAddCommGroup β]
    {f : Vec 3 → β} (hf : Continuous f) (p : ℝ≥0∞) :
    eLpNorm (f ∘ seeleyAffineMap x₀ r) p
        (volume.restrict (euclideanBall (0 : Vec 3) 1)) =
      ENNReal.ofReal (r⁻¹ ^ 3) ^ (1 / p).toReal *
        eLpNorm f p (volume.restrict (euclideanBall x₀ r)) := by
  have he := seeleyAffineMap_measurableEmbedding (x₀ := x₀) hr
  have hmap := seeleyAffineMap_restrict (x₀ := x₀) hr
  calc
    eLpNorm (f ∘ seeleyAffineMap x₀ r) p
        (volume.restrict (euclideanBall (0 : Vec 3) 1)) =
        eLpNorm f p (Measure.map (seeleyAffineMap x₀ r)
          (volume.restrict (euclideanBall (0 : Vec 3) 1))) := by
      symm
      exact eLpNorm_map_measure hf.aestronglyMeasurable
        he.measurable.aemeasurable
    _ = eLpNorm f p
        (ENNReal.ofReal (r⁻¹ ^ 3) •
          volume.restrict (euclideanBall x₀ r)) := by rw [hmap]
    _ = _ := by
      rw [eLpNorm_smul_measure_of_ne_zero (by positivity)]
      simp [smul_eq_mul]

private theorem seeleyBall_volume_pos (x₀ : Vec 3) {r : ℝ} (hr : 0 < r) :
    0 < (volume (euclideanBall x₀ r)).toReal := by
  have hopen : IsOpen (euclideanBall x₀ r) := by
    change IsOpen ((fun x : Vec 3 => euclideanSqDist x x₀) ⁻¹' Iio (r ^ 2))
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hpos : 0 < volume (euclideanBall x₀ r) := by
    apply hopen.measure_pos volume
    refine ⟨x₀, ?_⟩
    change euclideanSqDist x₀ x₀ < r ^ 2
    rw [euclideanSqDist_self]
    positivity
  have htop : volume (euclideanBall x₀ r) ≠ ∞ := by
    apply ne_of_lt
    exact (measure_mono (by
      intro x hx
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).2
        ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx).le)).trans_lt
      (isCompact_euclideanClosedBall x₀ hr.le).measure_lt_top
  exact ENNReal.toReal_pos hpos.ne' htop

private theorem seeleyAffine_integral_comp {x₀ : Vec 3} {r : ℝ} (hr : 0 < r)
    {f : Vec 3 → ℝ} (hf : Continuous f) :
    ∫ x in euclideanBall (0 : Vec 3) 1, f (seeleyAffineMap x₀ r x) ∂volume =
      (ENNReal.ofReal (r⁻¹ ^ 3)).toReal *
        ∫ y in euclideanBall x₀ r, f y ∂volume := by
  have he := seeleyAffineMap_measurableEmbedding (x₀ := x₀) hr
  have hmap := seeleyAffineMap_restrict (x₀ := x₀) hr
  calc
    ∫ x in euclideanBall (0 : Vec 3) 1, f (seeleyAffineMap x₀ r x) ∂volume =
        ∫ y, f y ∂Measure.map (seeleyAffineMap x₀ r)
          (volume.restrict (euclideanBall (0 : Vec 3) 1)) := by
      symm
      exact integral_map he.measurable.aemeasurable hf.aestronglyMeasurable
    _ = ∫ y, f y ∂(ENNReal.ofReal (r⁻¹ ^ 3) •
          volume.restrict (euclideanBall x₀ r)) := by rw [hmap]
    _ = (ENNReal.ofReal (r⁻¹ ^ 3)).toReal *
          ∫ y in euclideanBall x₀ r, f y ∂volume := by
      rw [integral_smul_measure]
      simp [smul_eq_mul]

theorem seeleyAffine_average {x₀ : Vec 3} {r : ℝ} (hr : 0 < r)
    {f : Vec 3 → ℝ} (hf : Continuous f) :
    average (volume.restrict (euclideanBall (0 : Vec 3) 1))
        (f ∘ seeleyAffineMap x₀ r) =
      average (volume.restrict (euclideanBall x₀ r)) f := by
  let U : Set (Vec 3) := euclideanBall (0 : Vec 3) 1
  have hI := seeleyAffine_integral_comp (x₀ := x₀) hr hf
  have hIone := seeleyAffine_integral_comp (x₀ := x₀) hr
    (f := fun _ : Vec 3 => (1 : ℝ)) continuous_const
  change (⨍ x in U, f (seeleyAffineMap x₀ r x) ∂volume) =
    ⨍ x in euclideanBall x₀ r, f x ∂volume
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
  simp only [smul_eq_mul]
  rw [hI]
  have hIone' :
      ∫ x in U, (1 : ℝ) ∂volume =
        (ENNReal.ofReal (r⁻¹ ^ 3)).toReal *
          ∫ y in euclideanBall x₀ r, (1 : ℝ) ∂volume := by
    simpa [U] using hIone
  have hvolU : ∫ x in U, (1 : ℝ) ∂volume = volume.real U := by
    rw [integral_const]
    simp [Measure.real]
  have hvolBall :
      ∫ x in euclideanBall x₀ r, (1 : ℝ) ∂volume =
        volume.real (euclideanBall x₀ r) := by
    rw [integral_const]
    simp [Measure.real]
  have hposU : 0 < (volume U).toReal := by
    dsimp [U]
    exact seeleyBall_volume_pos (0 : Vec 3) (by norm_num)
  have hposBall : 0 < (volume (euclideanBall x₀ r)).toReal :=
    seeleyBall_volume_pos x₀ hr
  have hcoef : 0 < (ENNReal.ofReal (r⁻¹ ^ 3)).toReal := by
    exact ENNReal.toReal_pos (by positivity) ENNReal.ofReal_ne_top
  rw [← hvolU, ← hvolBall, hIone']
  field_simp [hposU.ne', hposBall.ne', hcoef.ne']

private theorem seeleyAffine_fderiv {x₀ : Vec 3} (r : ℝ)
    {f : Vec 3 → ℝ} (x : Vec 3) :
    fderiv ℝ (f ∘ seeleyAffineMap x₀ r) x =
      r • fderiv ℝ f (seeleyAffineMap x₀ r x) := by
  have hcomp :
      (fun x : Vec 3 => f (seeleyAffineMap x₀ r x)) =
        (fun x : Vec 3 => (fun y : Vec 3 => f (x₀ + y)) (r • x)) := by
    funext y
    rfl
  change fderiv ℝ (fun x : Vec 3 => f (seeleyAffineMap x₀ r x)) x = _
  rw [hcomp]
  have hfd :
      fderiv ℝ (fun x : Vec 3 => (fun y : Vec 3 => f (x₀ + y)) (r • x)) x =
        r • fderiv ℝ (fun y : Vec 3 => f (x₀ + y)) (r • x) := by
    simpa using
      (fderiv_comp_smul (𝕜 := ℝ) (f := fun y : Vec 3 => f (x₀ + y))
        (x := x) r)
  rw [hfd, fderiv_comp_add_left]
  simp [seeleyAffineMap]

theorem seeleyAffine_classicalGradient {x₀ : Vec 3} {r : ℝ}
    {f : Vec 3 → ℝ} (_ : ContDiff ℝ 1 f) (x : Vec 3) :
    classicalGradient (f ∘ seeleyAffineMap x₀ r) x =
      r • classicalGradient f (seeleyAffineMap x₀ r x) := by
  apply funext
  intro i
  rw [classicalGradient_apply, seeleyAffine_fderiv]
  rfl

end
end CKN
