/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Slice
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Function.EssSup

/-!
# Scaling, translation, and radius monotonicity

The declarations here keep the geometric maps from `Basic.lean` and expose the
change-of-variables statements needed for scale-invariant quantities.  In
particular, no source-facing quantity is introduced in this module.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

noncomputable section

namespace CKN.Foundation.Parabolic.Integration

/-- A parabolic rescaling with a scalar power weight. -/
def parabolicRescale (a : ℝ) (κ : ℝ) (x : Vec3) (t : ℝ)
    (u : ParabolicPoint → ℝ) (p : ParabolicPoint) : ℝ :=
  a ^ κ * u (parabolicTranslate x t (parabolicScale a p))

/-- The image of a centred cylinder under a positive rescaling and translation. -/
theorem parabolicCylinder_rescale_image {a : ℝ} (ha : 0 < a) (x : Vec3) (t r : ℝ) :
    parabolicTranslate x t '' (parabolicScale a '' parabolicCylinder 0 0 r) =
    parabolicCylinder x t (a * r) := by
  rw [parabolicCylinder_scale ha]
  simpa [parabolicTranslate, zero_add, zero_smul] using
    (parabolicCylinder_translate x (0 : Vec3) t 0 (a * r))

private theorem add_setIntegral (s : Set Vec3) (x : Vec3) (F : Vec3 → ℝ) :
    ∫ y in s, F (x + y) = ∫ y in x +ᵥ s, F y := by
  symm
  exact (measurePreserving_add_left (volume : Measure Vec3) x).setIntegral_image_emb
    (Homeomorph.addLeft x).measurableEmbedding F s

private theorem add_time_setIntegral (s : Set ℝ) (t : ℝ) (F : ℝ → ℝ) :
    ∫ s in s, F (t + s) = ∫ s in t +ᵥ s, F s := by
  symm
  exact (measurePreserving_add_left (volume : Measure ℝ) t).setIntegral_image_emb
    (Homeomorph.addLeft t).measurableEmbedding F s

private theorem ball_scale_image {a r : ℝ} (ha : 0 < a) :
    a • vec3Ball 0 r = vec3Ball 0 (a * r) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change vec3EuclideanNorm (z - 0) < r at hz
    have hz' : vec3EuclideanNorm z < r := by simpa using hz
    change vec3EuclideanNorm (a • z - 0) < a * r
    rw [sub_zero, vec3EuclideanNorm_smul, abs_of_pos ha]
    exact mul_lt_mul_of_pos_left hz' ha
  · intro hy
    change vec3EuclideanNorm (y - 0) < a * r at hy
    refine ⟨a⁻¹ • y, ?_, ?_⟩
    · change vec3EuclideanNorm (a⁻¹ • y - 0) < r
      rw [sub_zero, vec3EuclideanNorm_smul, abs_inv, abs_of_pos ha]
      have h := mul_lt_mul_of_pos_left hy (inv_pos.mpr ha)
      simpa [ha.ne'] using h
    · change a • (a⁻¹ • y) = y
      simp [smul_smul, ha.ne']

private theorem ball_translate_image (x : Vec3) {r : ℝ} :
    (fun y : Vec3 => x + y) '' vec3Ball 0 r = vec3Ball x r := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change vec3EuclideanNorm ((x + z) - x) < r
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz
  · intro hy
    refine ⟨y - x, ?_, ?_⟩
    · change vec3EuclideanNorm (y - x - 0) < r
      simpa [sub_zero] using hy
    · simp [sub_eq_add_neg]

private theorem interval_scale_image {a : ℝ} (ha : 0 < a) (s₁ s₂ : ℝ) :
    a • Ioc s₁ s₂ = Ioc (a * s₁) (a * s₂) := by
  ext s
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨mul_lt_mul_of_pos_left hu.1 ha, mul_le_mul_of_nonneg_left hu.2 ha.le⟩
  · intro hs
    refine ⟨a⁻¹ * s, ?_, ?_⟩
    · constructor
      · have h := mul_lt_mul_of_pos_left hs.1 (inv_pos.mpr ha)
        simpa [ha.ne'] using h
      · have h := mul_le_mul_of_nonneg_left hs.2 (inv_pos.mpr ha).le
        simpa [ha.ne'] using h
    · change a * (a⁻¹ * s) = s
      field_simp [ha.ne']

private theorem interval_translate_image (t : ℝ) (s₁ s₂ : ℝ) :
    (fun s : ℝ => t + s) '' Ioc s₁ s₂ = Ioc (t + s₁) (t + s₂) := by
  ext s
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨by simpa [add_comm] using add_lt_add_left hu.1 t,
      by simpa [add_comm] using add_le_add_left hu.2 t⟩
  · intro hs
    refine ⟨s - t, ?_, ?_⟩
    · constructor
      · exact lt_sub_iff_add_lt.mpr (by simpa [add_comm] using hs.1)
      · show s - t ≤ s₂
        exact sub_le_iff_le_add.mpr (by simpa [add_comm] using hs.2)
    · simp

private theorem spatial_comp_translate_scale {a : ℝ} (ha : 0 < a)
    (x : Vec3) (r : ℝ) (F : Vec3 → ℝ) :
    ∫ y in vec3Ball 0 r, F (x + a • y) =
      a⁻¹ ^ Module.finrank ℝ Vec3 * ∫ y in vec3Ball x (a * r), F y := by
  have h := Measure.setIntegral_comp_smul_of_pos volume
    (fun y => F (x + y)) (vec3Ball 0 r) ha
  have ht := add_setIntegral (a • vec3Ball 0 r) x F
  rw [ht] at h
  have hset : x +ᵥ (a • vec3Ball 0 r) = vec3Ball x (a * r) := by
    change (fun y : Vec3 => x + y) '' (a • vec3Ball 0 r) = _
    rw [ball_scale_image ha, ball_translate_image]
  rw [hset] at h
  simpa [smul_eq_mul, mul_comm] using h

private theorem time_comp_translate_scale {a : ℝ} (ha : 0 < a)
    (t r : ℝ) (F : ℝ → ℝ) :
    ∫ s in Ioc (-r ^ 2) 0, F (t + a ^ 2 * s) =
      (a ^ 2)⁻¹ * ∫ s in Ioc (t - (a * r) ^ 2) t, F s := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have h := Measure.setIntegral_comp_smul_of_pos volume
    (fun s => F (t + s)) (Ioc (-r ^ 2) 0) ha2
  have ht := add_time_setIntegral ((a ^ 2) • Ioc (-r ^ 2) 0) t F
  rw [ht] at h
  have hset : t +ᵥ ((a ^ 2) • Ioc (-r ^ 2) 0) =
      Ioc (t - (a * r) ^ 2) t := by
    change (fun s : ℝ => t + s) '' ((a ^ 2) • Ioc (-r ^ 2) 0) = _
    rw [interval_scale_image ha2, interval_translate_image]
    congr 1 <;> ring
  rw [hset] at h
  simpa [smul_eq_mul, sub_eq_add_neg, mul_pow, mul_comm, add_comm, add_left_comm,
    add_assoc] using h

private theorem map_spatial_affine {a : ℝ} (ha : 0 < a) (x : Vec3) :
    Measure.map (fun y : Vec3 => x + a • y) volume =
      ENNReal.ofReal (a⁻¹ ^ 3) • (volume : Measure Vec3) := by
  change Measure.map ((fun y : Vec3 => x + y) ∘ (fun y => a • y)) volume = _
  rw [← Measure.map_map (measurable_const_add x) (measurable_const_smul a)]
  rw [Measure.map_addHaar_smul volume ha.ne', Measure.map_smul]
  rw [MeasureTheory.map_add_left_eq_self]
  · congr 1
    norm_num [Module.finrank_fin_fun, abs_of_pos ha, inv_pow]
  · exact (measurable_const_add x).aemeasurable

private theorem spatial_affine_preimage {a : ℝ} (ha : 0 < a) (x : Vec3) (r : ℝ) :
    (fun y : Vec3 => x + a • y) ⁻¹' vec3Ball x (a * r) = vec3Ball 0 r := by
  ext y
  constructor
  · intro hy
    change vec3EuclideanNorm ((x + a • y) - x) < a * r at hy
    rw [add_sub_cancel_left, vec3EuclideanNorm_smul, abs_of_pos ha] at hy
    change vec3EuclideanNorm (y - 0) < r
    simpa [sub_zero] using lt_of_mul_lt_mul_left hy ha.le
  · intro hy
    change vec3EuclideanNorm (y - 0) < r at hy
    change vec3EuclideanNorm ((x + a • y) - x) < a * r
    rw [add_sub_cancel_left, vec3EuclideanNorm_smul, abs_of_pos ha]
    exact mul_lt_mul_of_pos_left (by simpa [sub_zero] using hy) ha

private theorem spatial_affine_map_restrict {a : ℝ} (ha : 0 < a) (x : Vec3) (r : ℝ) :
    Measure.map (fun y : Vec3 => x + a • y) (volume.restrict (vec3Ball 0 r)) =
      ENNReal.ofReal (a⁻¹ ^ 3) • volume.restrict (vec3Ball x (a * r)) := by
  have hpre := spatial_affine_preimage ha x r
  calc
    Measure.map (fun y : Vec3 => x + a • y)
        (volume.restrict (vec3Ball 0 r)) =
        Measure.map (fun y : Vec3 => x + a • y)
          (volume.restrict ((fun y : Vec3 => x + a • y) ⁻¹' vec3Ball x (a * r))) := by
            rw [hpre]
    _ = (Measure.map (fun y : Vec3 => x + a • y) volume).restrict
          (vec3Ball x (a * r)) := by
      exact (Measure.restrict_map ((measurable_const_add x).comp
        (measurable_const_smul a)) (vec3Ball_measurable x (a * r))).symm
    _ = ENNReal.ofReal (a⁻¹ ^ 3) • volume.restrict (vec3Ball x (a * r)) := by
      rw [map_spatial_affine ha x, Measure.restrict_smul]

private theorem spatial_setLIntegral_comp_translate_scale {a : ℝ} (ha : 0 < a)
    (x : Vec3) (r : ℝ) (F : Vec3 → ℝ≥0∞) :
    ∫⁻ y in vec3Ball 0 r, F (x + a • y) =
      ENNReal.ofReal (a⁻¹ ^ 3) * ∫⁻ y in vec3Ball x (a * r), F y := by
  have hmap := spatial_affine_map_restrict ha x r
  change ∫⁻ y : Vec3, F (x + a • y) ∂volume.restrict (vec3Ball 0 r) = _
  let e : Vec3 → Vec3 :=
    (Homeomorph.addLeft x) ∘ (Homeomorph.smul (isUnit_iff_ne_zero.2 ha.ne').unit)
  have hemb : MeasurableEmbedding e :=
    (Homeomorph.addLeft x).measurableEmbedding.comp
      (Homeomorph.smul (isUnit_iff_ne_zero.2 ha.ne').unit).measurableEmbedding
  have he : (fun y : Vec3 => x + a • y) = e := by
    funext y
    simp [e, Function.comp_def]
  calc
    ∫⁻ y in vec3Ball 0 r, F (x + a • y) =
        ∫⁻ y in vec3Ball 0 r, F (e y) := by congr 1
    _ = ∫⁻ y, F y ∂Measure.map e (volume.restrict (vec3Ball 0 r)) :=
      (hemb.lintegral_map F).symm
    _ = ENNReal.ofReal (a⁻¹ ^ 3) *
        ∫⁻ y in vec3Ball x (a * r), F y := by
      have hmap' : Measure.map e (volume.restrict (vec3Ball 0 r)) =
          ENNReal.ofReal (a⁻¹ ^ 3) • volume.restrict (vec3Ball x (a * r)) := by
        simpa [e, he] using hmap
      rw [hmap', lintegral_smul_measure]
      rfl

/-- Bochner integration on a parabolic cylinder changes by the homogeneous factor `a⁻⁵`. -/
theorem cylinder_setIntegral_comp_parabolicRescale {a : ℝ} (ha : 0 < a)
    (x : Vec3) (t r : ℝ) (F : ParabolicPoint → ℝ)
    (hsource : IntegrableOn
      (fun z => F (parabolicTranslate x t (parabolicScale a z)))
      (parabolicCylinder 0 0 r) volume)
    (htarget : IntegrableOn F (parabolicCylinder x t (a * r)) volume) :
    ∫ z in parabolicCylinder 0 0 r,
        F (parabolicTranslate x t (parabolicScale a z)) =
      a⁻¹ ^ 5 * ∫ z in parabolicCylinder x t (a * r), F z := by
  have hsource' := integral_parabolicCylinder (x := (0 : Vec3)) (t := 0) hsource
  have htarget' := integral_parabolicCylinder htarget
  rw [hsource', htarget']
  have hspace : ∀ s : ℝ,
      ∫ y in vec3Ball 0 r,
          F (parabolicTranslate x t (parabolicScale a (y, s))) =
        a⁻¹ ^ Module.finrank ℝ Vec3 *
          ∫ y in vec3Ball x (a * r), F (y, t + a ^ 2 * s) := by
    intro s
    simpa [parabolicTranslate, parabolicScale, zero_add, zero_smul] using
      (spatial_comp_translate_scale ha x r
        (fun y => F (y, t + a ^ 2 * s)))
  simp_rw [hspace]
  rw [integral_const_mul]
  have htime :
      ∫ s in Ioc (0 - r ^ 2) 0,
          ∫ y in vec3Ball x (a * r), F ((y, t + a ^ 2 * s) : ParabolicPoint) =
        (a ^ 2)⁻¹ * ∫ s in Ioc (t - (a * r) ^ 2) t,
          ∫ y in vec3Ball x (a * r), F ((y, s) : ParabolicPoint) := by
    simpa [sub_zero, smul_eq_mul] using
      (time_comp_translate_scale ha t r
        (fun s => ∫ y in vec3Ball x (a * r), F ((y, s) : ParabolicPoint)))
  rw [htime]
  simp only [Module.finrank_fin_fun]
  field_simp [ha.ne']

/-- The corresponding nonnegative cylinder lintegral has homogeneous factor `a⁻⁵`. -/
theorem cylinder_setLIntegral_comp_parabolicRescale {a : ℝ} (ha : 0 < a)
    (x : Vec3) (t r p : ℝ) (u : ParabolicPoint → ℝ) (hp : 0 ≤ p)
    (hsource : IntegrableOn
      (fun z => |u (parabolicTranslate x t (parabolicScale a z))| ^ p)
      (parabolicCylinder 0 0 r) volume)
    (htarget : IntegrableOn (fun z => |u z| ^ p)
      (parabolicCylinder x t (a * r)) volume) :
    ∫⁻ z in parabolicCylinder 0 0 r,
        ‖u (parabolicTranslate x t (parabolicScale a z))‖ₑ ^ p =
      ENNReal.ofReal (a⁻¹ ^ 5) *
        ∫⁻ z in parabolicCylinder x t (a * r), ‖u z‖ₑ ^ p := by
  have hs :
      ∫⁻ z in parabolicCylinder 0 0 r,
          ‖u (parabolicTranslate x t (parabolicScale a z))‖ₑ ^ p =
        ENNReal.ofReal
          (∫ z in parabolicCylinder 0 0 r,
            |u (parabolicTranslate x t (parabolicScale a z))| ^ p) := by
    symm
    have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := (volume : Measure ParabolicPoint).restrict (parabolicCylinder 0 0 r))
      hsource (Filter.Eventually.of_forall fun z =>
        Real.rpow_nonneg (abs_nonneg _) _)
    have he : ∀ z : ParabolicPoint,
        ENNReal.ofReal (|u (parabolicTranslate x t (parabolicScale a z))| ^ p) =
          ‖u (parabolicTranslate x t (parabolicScale a z))‖ₑ ^ p := by
      intro z
      change ENNReal.ofReal
          (‖u (parabolicTranslate x t (parabolicScale a z))‖ ^ p) = _
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp, ofReal_norm]
    rw [h]
    exact MeasureTheory.lintegral_congr_ae
      (Filter.Eventually.of_forall he)
  have ht :
      ENNReal.ofReal
          (∫ z in parabolicCylinder x t (a * r), |u z| ^ p) =
        ∫⁻ z in parabolicCylinder x t (a * r), ‖u z‖ₑ ^ p := by
    have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := (volume : Measure ParabolicPoint).restrict
        (parabolicCylinder x t (a * r))) htarget
      (Filter.Eventually.of_forall fun z => Real.rpow_nonneg (abs_nonneg _) _)
    have he : ∀ z : ParabolicPoint,
        ENNReal.ofReal (|u z| ^ p) = ‖u z‖ₑ ^ p := by
      intro z
      change ENNReal.ofReal (‖u z‖ ^ p) = _
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp, ofReal_norm]
    rw [h]
    exact MeasureTheory.lintegral_congr_ae
      (Filter.Eventually.of_forall he)
  calc
    _ = ENNReal.ofReal
        (∫ z in parabolicCylinder 0 0 r,
          |u (parabolicTranslate x t (parabolicScale a z))| ^ p) := hs
    _ = ENNReal.ofReal (a⁻¹ ^ 5 *
        ∫ z in parabolicCylinder x t (a * r), |u z| ^ p) := by
      rw [cylinder_setIntegral_comp_parabolicRescale ha x t r
        (fun z => |u z| ^ p) hsource htarget]
    _ = ENNReal.ofReal (a⁻¹ ^ 5) * ENNReal.ofReal
        (∫ z in parabolicCylinder x t (a * r), |u z| ^ p) := by
      rw [ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (a⁻¹ ^ 5) *
        ∫⁻ z in parabolicCylinder x t (a * r), ‖u z‖ₑ ^ p := by
      rw [ht]

/-- The velocity-weighted cylinder power integral changes by `a^(p-5)`. -/
theorem cylinder_setIntegral_rescaled_power {a : ℝ} (ha : 0 < a)
    (x : Vec3) (t r p : ℝ) (u : ParabolicPoint → ℝ)
    (hsource : IntegrableOn
      (fun z => |u (parabolicTranslate x t (parabolicScale a z))| ^ p)
      (parabolicCylinder 0 0 r) volume)
    (htarget : IntegrableOn (fun z => |u z| ^ p)
      (parabolicCylinder x t (a * r)) volume) :
    ∫ z in parabolicCylinder 0 0 r,
        |a * u (parabolicTranslate x t (parabolicScale a z))| ^ p =
      a ^ (p - 5) * ∫ z in parabolicCylinder x t (a * r), |u z| ^ p := by
  have hbase := cylinder_setIntegral_comp_parabolicRescale ha x t r
    (fun z => |u z| ^ p) hsource htarget
  calc
    ∫ z in parabolicCylinder 0 0 r,
        |a * u (parabolicTranslate x t (parabolicScale a z))| ^ p =
        ∫ z in parabolicCylinder 0 0 r,
          a ^ p * |u (parabolicTranslate x t (parabolicScale a z))| ^ p := by
            apply MeasureTheory.integral_congr_ae
            exact Filter.Eventually.of_forall fun z => by
              change |a * u (parabolicTranslate x t (parabolicScale a z))| ^ p =
                a ^ p * |u (parabolicTranslate x t (parabolicScale a z))| ^ p
              rw [abs_mul, abs_of_pos ha, Real.mul_rpow ha.le (abs_nonneg _)]
    _ = a ^ p * ∫ z in parabolicCylinder 0 0 r,
          |u (parabolicTranslate x t (parabolicScale a z))| ^ p :=
      MeasureTheory.integral_const_mul _ _
    _ = a ^ p * (a⁻¹ ^ 5 * ∫ z in parabolicCylinder x t (a * r), |u z| ^ p) := by
      rw [hbase]
    _ = a ^ (p - 5) * ∫ z in parabolicCylinder x t (a * r), |u z| ^ p := by
      rw [inv_pow, ← Real.rpow_natCast a 5]
      have hneg : a ^ (-5 : ℝ) = (a ^ (5 : ℝ))⁻¹ := Real.rpow_neg ha.le 5
      change a ^ p * ((a ^ (5 : ℝ))⁻¹ *
        ∫ z in parabolicCylinder x t (a * r), |u z| ^ p) = _
      rw [← hneg]
      rw [← mul_assoc]
      rw [← Real.rpow_add ha p (-5)]
      congr 2

/-- A single spatial time slice changes by the spatial factor `a⁻³`. -/
theorem timeSlice_setIntegral_comp_parabolicRescale {a : ℝ} (ha : 0 < a)
    (x : Vec3) (t r s : ℝ) (F : Vec3 → ℝ) :
    ∫ y in vec3Ball 0 r,
        F (parabolicTranslate x t (parabolicScale a (y, s))).1 =
      a⁻¹ ^ Module.finrank ℝ Vec3 *
        ∫ y in vec3Ball x (a * r), F y := by
  simpa [parabolicTranslate, parabolicScale, zero_add, zero_smul] using
    (spatial_comp_translate_scale ha x r (fun y => F y))

/-- A velocity-weighted time-slice power integral changes by `a^(p-3)`. -/
theorem timeSlice_setIntegral_rescaled_power {a : ℝ} (ha : 0 < a)
    (x : Vec3) (t r s p : ℝ) (u : ParabolicPoint → ℝ)
    (_ : IntegrableOn
      (fun y => |u (parabolicTranslate x t (parabolicScale a (y, s)))| ^ p)
      (vec3Ball 0 r) volume)
    (_ : IntegrableOn (fun y => |u (y, t + a ^ 2 * s)| ^ p)
      (vec3Ball x (a * r)) volume) :
    ∫ y in vec3Ball 0 r,
        |a * u (parabolicTranslate x t (parabolicScale a (y, s)))| ^ p =
      a ^ (p - 3) * ∫ y in vec3Ball x (a * r), |u (y, t + a ^ 2 * s)| ^ p := by
  have hbase := timeSlice_setIntegral_comp_parabolicRescale ha x t r s
    (fun y => |u (y, t + a ^ 2 * s)| ^ p)
  have hbase' :
      ∫ y in vec3Ball 0 r,
          |u (parabolicTranslate x t (parabolicScale a (y, s)))| ^ p =
        a⁻¹ ^ 3 * ∫ y in vec3Ball x (a * r), |u (y, t + a ^ 2 * s)| ^ p := by
    simpa [parabolicTranslate, parabolicScale, zero_add, zero_smul,
      Module.finrank_fin_fun] using hbase
  calc
    ∫ y in vec3Ball 0 r,
        |a * u (parabolicTranslate x t (parabolicScale a (y, s)))| ^ p =
        ∫ y in vec3Ball 0 r,
          a ^ p * |u (parabolicTranslate x t (parabolicScale a (y, s)))| ^ p := by
            apply MeasureTheory.integral_congr_ae
            exact Filter.Eventually.of_forall fun y => by
              change |a * u (parabolicTranslate x t (parabolicScale a (y, s)))| ^ p =
                a ^ p * |u (parabolicTranslate x t (parabolicScale a (y, s)))| ^ p
              rw [abs_mul, abs_of_pos ha, Real.mul_rpow ha.le (abs_nonneg _)]
    _ = a ^ p * ∫ y in vec3Ball 0 r,
          |u (parabolicTranslate x t (parabolicScale a (y, s)))| ^ p :=
      MeasureTheory.integral_const_mul _ _
    _ = a ^ p * (a⁻¹ ^ 3 * ∫ y in vec3Ball x (a * r),
          |u (y, t + a ^ 2 * s)| ^ p) := by
      rw [hbase']
    _ = a ^ (p - 3) * ∫ y in vec3Ball x (a * r), |u (y, t + a ^ 2 * s)| ^ p := by
      rw [inv_pow, ← Real.rpow_natCast a 3]
      have hneg : a ^ (-3 : ℝ) = (a ^ (3 : ℝ))⁻¹ := Real.rpow_neg ha.le 3
      change a ^ p * ((a ^ (3 : ℝ))⁻¹ *
        ∫ y in vec3Ball x (a * r), |u (y, t + a ^ 2 * s)| ^ p) = _
      rw [← hneg, ← mul_assoc, ← Real.rpow_add ha p (-3)]
      congr 2

private theorem map_time_affine {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Measure.map (fun s : ℝ => t + a ^ 2 * s) volume =
      ENNReal.ofReal ((a ^ 2)⁻¹) • (volume : Measure ℝ) := by
  change Measure.map ((fun s : ℝ => t + s) ∘ (fun s => a ^ 2 • s)) volume = _
  rw [← Measure.map_map (measurable_const_add t) (measurable_const_smul (a ^ 2))]
  rw [Measure.map_addHaar_smul volume (sq_pos_of_pos ha).ne', Measure.map_smul]
  rw [MeasureTheory.map_add_left_eq_self]
  · congr 1
    norm_num [Module.finrank_fin_fun, abs_of_pos ha, inv_pow]
  · exact (measurable_const_add t).aemeasurable

private theorem time_affine_preimage {a : ℝ} (ha : 0 < a) (t r : ℝ) :
    (fun s : ℝ => t + a ^ 2 * s) ⁻¹' Ioc (t - (a * r) ^ 2) t =
      Ioc (-r ^ 2) 0 := by
  ext s
  constructor
  · intro hs
    change t - (a * r) ^ 2 < t + a ^ 2 * s ∧ t + a ^ 2 * s ≤ t at hs
    constructor
    · have h : -(a ^ 2 * s) < (a * r) ^ 2 := by
        apply (sub_lt_sub_iff_left t).mp
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hs.1
      have h' : -(a * r) ^ 2 < a ^ 2 * s := by
        simpa using neg_lt_neg h
      have h'' : a ^ 2 * (-(r ^ 2)) < a ^ 2 * s := by
        simpa [mul_pow] using h'
      exact lt_of_mul_lt_mul_left h'' (sq_pos_of_pos ha).le
    · have h : 0 ≤ -(a ^ 2 * s) := by
        apply (sub_le_sub_iff_left t).mp
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hs.2
      have h' : a ^ 2 * s ≤ 0 := neg_nonneg.mp h
      exact le_of_mul_le_mul_left (by simpa using h') (sq_pos_of_pos ha)
  · intro hs
    change -r ^ 2 < s ∧ s ≤ 0 at hs
    constructor
    · have h : a ^ 2 * (-(r ^ 2)) < a ^ 2 * s :=
        mul_lt_mul_of_pos_left hs.1 (sq_pos_of_pos ha)
      have h' : -(a * r) ^ 2 < a ^ 2 * s := by simpa [mul_pow] using h
      have h'' : t - (a * r) ^ 2 < t + a ^ 2 * s := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (add_lt_add_left h' t)
      exact h''
    · have h : a ^ 2 * s ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_pos_of_pos ha).le hs.2
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (add_le_add_left h t)

private theorem time_affine_map_restrict {a : ℝ} (ha : 0 < a) (t r : ℝ) :
    Measure.map (fun s : ℝ => t + a ^ 2 * s)
        (volume.restrict (Ioc (-r ^ 2) 0)) =
      ENNReal.ofReal ((a ^ 2)⁻¹) •
        volume.restrict (Ioc (t - (a * r) ^ 2) t) := by
  have hpre := time_affine_preimage ha t r
  calc
    Measure.map (fun s : ℝ => t + a ^ 2 * s)
        (volume.restrict (Ioc (-r ^ 2) 0)) =
        Measure.map (fun s : ℝ => t + a ^ 2 * s)
          (volume.restrict ((fun s : ℝ => t + a ^ 2 * s) ⁻¹'
            Ioc (t - (a * r) ^ 2) t)) := by rw [hpre]
    _ = (Measure.map (fun s : ℝ => t + a ^ 2 * s) volume).restrict
          (Ioc (t - (a * r) ^ 2) t) := by
      exact (Measure.restrict_map ((measurable_const_add t).comp
        (measurable_const_mul (a ^ 2))) measurableSet_Ioc).symm
    _ = ENNReal.ofReal ((a ^ 2)⁻¹) • volume.restrict
          (Ioc (t - (a * r) ^ 2) t) := by
      rw [map_time_affine ha t, Measure.restrict_smul]

private theorem time_setLIntegral_comp_translate_scale {a : ℝ} (ha : 0 < a)
    (t r : ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioc (-r ^ 2) 0, F (t + a ^ 2 * s) =
      ENNReal.ofReal ((a ^ 2)⁻¹) *
        ∫⁻ s in Ioc (t - (a * r) ^ 2) t, F s := by
  have hmap := time_affine_map_restrict ha t r
  let e : ℝ → ℝ := (Homeomorph.addLeft t) ∘
    (Homeomorph.smul (isUnit_iff_ne_zero.2 (sq_pos_of_pos ha).ne').unit)
  have hemb : MeasurableEmbedding e :=
    (Homeomorph.addLeft t).measurableEmbedding.comp
      (Homeomorph.smul (isUnit_iff_ne_zero.2 (sq_pos_of_pos ha).ne').unit).measurableEmbedding
  have he : (fun s : ℝ => t + a ^ 2 * s) = e := by
    funext s
    simp [e, Function.comp_def]
  calc
    ∫⁻ s in Ioc (-r ^ 2) 0, F (t + a ^ 2 * s) =
        ∫⁻ s in Ioc (-r ^ 2) 0, F (e s) := by congr 1
    _ = ∫⁻ s, F s ∂Measure.map e (volume.restrict (Ioc (-r ^ 2) 0)) :=
      (hemb.lintegral_map F).symm
    _ = ENNReal.ofReal ((a ^ 2)⁻¹) *
        ∫⁻ s in Ioc (t - (a * r) ^ 2) t, F s := by
      have hmap' : Measure.map e (volume.restrict (Ioc (-r ^ 2) 0)) =
          ENNReal.ofReal ((a ^ 2)⁻¹) •
            volume.restrict (Ioc (t - (a * r) ^ 2) t) := by
        simpa [e, he] using hmap
      rw [hmap', lintegral_smul_measure]
      rfl

theorem timeSlice_setLIntegral_comp_parabolicRescale {a : ℝ} (ha : 0 < a)
    (x : Vec3) (t r s : ℝ) (g : ParabolicPoint → ℝ) :
    ∫⁻ y in vec3Ball 0 r,
        ‖g (parabolicTranslate x t (parabolicScale a (y, s)))‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (a⁻¹ ^ 3) *
        ∫⁻ y in vec3Ball x (a * r), ‖g (y, t + a ^ 2 * s)‖ₑ ^ (2 : ℝ) := by
  simpa [parabolicTranslate, parabolicScale, zero_add, zero_smul] using
    (spatial_setLIntegral_comp_translate_scale ha x r
      (fun y => ‖g (y, t + a ^ 2 * s)‖ₑ ^ (2 : ℝ)))

/-- Spatial change of variables under a positive dilation. -/
theorem spatial_setIntegral_comp_smul {a : ℝ} (ha : 0 < a) (x : Vec3) (r : ℝ)
    (f : Vec3 → ℝ) :
    ∫ y in vec3Ball x r, f (a • y) =
      (a ^ Module.finrank ℝ Vec3)⁻¹ • ∫ y in a • vec3Ball x r, f y := by
  exact Measure.setIntegral_comp_smul_of_pos volume f (vec3Ball x r) ha

/-- One-dimensional time change of variables under a positive dilation. -/
theorem time_setIntegral_comp_smul {a : ℝ} (ha : 0 < a) (s₁ s₂ : ℝ)
    (f : ℝ → ℝ) :
    ∫ s in Set.Ioc s₁ s₂, f (a • s) =
      (a ^ Module.finrank ℝ ℝ)⁻¹ • ∫ s in a • Set.Ioc s₁ s₂, f s := by
  exact Measure.setIntegral_comp_smul_of_pos volume f (Set.Ioc s₁ s₂) ha

/-- Spatial power integrals transform with an arbitrary constant weight. -/
theorem spatial_setIntegral_rescaled_power {a : ℝ} (ha : 0 < a) (x : Vec3) (r p c : ℝ)
    (u : Vec3 → ℝ) :
    ∫ y in vec3Ball x r, |c * u (a • y)| ^ p =
      (a ^ Module.finrank ℝ Vec3)⁻¹ *
        ∫ y in a • vec3Ball x r, |c * u y| ^ p := by
  simpa only [smul_eq_mul] using
    (spatial_setIntegral_comp_smul ha x r (fun y => |c * u y| ^ p))

/-- Time-slice power integrals transform with an arbitrary constant weight. -/
theorem time_setIntegral_rescaled_power {a : ℝ} (ha : 0 < a) (s₁ s₂ p c : ℝ)
    (u : ℝ → ℝ) :
    ∫ s in Set.Ioc s₁ s₂, |c * u (a • s)| ^ p =
      (a ^ Module.finrank ℝ ℝ)⁻¹ *
        ∫ s in a • Set.Ioc s₁ s₂, |c * u s| ^ p := by
  simpa only [smul_eq_mul] using
    (time_setIntegral_comp_smul ha s₁ s₂ (fun s => |c * u s| ^ p))

/-- Translation preserves the volume of a parabolic cylinder. -/
theorem volume_parabolicCylinder_translate (a x : Vec3) (τ t r : ℝ) :
    volume (parabolicCylinder (a + x) (τ + t) r) =
      volume (parabolicCylinder x t r) := by
  rw [volume_parabolicCylinder, volume_parabolicCylinder, volume_vec3Ball]
  simp_rw [volume_vec3Ball]

/-- The nonnegative energy of a spatial time slice. -/
def timeSliceBallEnergy (x : Vec3) (r s : ℝ) (g : ParabolicPoint → ℝ) : ℝ≥0∞ :=
  ∫⁻ y in vec3Ball x r, ‖g (y, s)‖ₑ ^ (2 : ℝ)

/-- Essential supremum of a time-slice energy over the cylinder time interval. -/
def timeSliceEnergyEssSup (x : Vec3) (t r : ℝ) (g : ParabolicPoint → ℝ) : ℝ≥0∞ :=
  essSup (timeSliceBallEnergy x r · g) (volume.restrict (Ioc (t - r ^ 2) t))

/-- The time-slice energy essential supremum changes by the spatial factor `a⁻³`. -/
theorem timeSliceEnergyEssSup_comp_parabolicRescale {a : ℝ} (ha : 0 < a)
    (x : Vec3) (t r : ℝ) (g : ParabolicPoint → ℝ)
    (hsource : Filter.IsBoundedUnder (· ≤ ·)
      (ae (volume.restrict (Ioc (-r ^ 2) 0)))
      (fun s => ∫⁻ y in vec3Ball x (a * r),
        ‖g (y, t + a ^ 2 * s)‖ₑ ^ (2 : ℝ)))
    (htarget : Filter.IsBoundedUnder (· ≤ ·)
      (ae (volume.restrict (Ioc (t - (a * r) ^ 2) t)))
      (fun s => ∫⁻ y in vec3Ball x (a * r), ‖g (y, s)‖ₑ ^ (2 : ℝ))) :
    timeSliceEnergyEssSup 0 0 r
        (fun z => g (parabolicTranslate x t (parabolicScale a z))) =
      ENNReal.ofReal (a⁻¹ ^ 3) * timeSliceEnergyEssSup x t (a * r) g := by
  let E : ℝ → ℝ≥0∞ := fun s =>
    ∫⁻ y in vec3Ball x (a * r), ‖g (y, s)‖ₑ ^ (2 : ℝ)
  let Ec : ℝ → ℝ≥0∞ := fun s =>
    ∫⁻ y in vec3Ball 0 r,
      ‖g (parabolicTranslate x t (parabolicScale a (y, s)))‖ₑ ^ (2 : ℝ)
  let f : ℝ → ℝ := fun s => t + a ^ 2 * s
  let μs : Measure ℝ := volume.restrict (Ioc (-r ^ 2) 0)
  let μt : Measure ℝ := volume.restrict (Ioc (t - (a * r) ^ 2) t)
  let e : ℝ → ℝ := (Homeomorph.addLeft t) ∘
    (Homeomorph.smul (isUnit_iff_ne_zero.2 (sq_pos_of_pos ha).ne').unit)
  have hemb : MeasurableEmbedding e :=
    (Homeomorph.addLeft t).measurableEmbedding.comp
      (Homeomorph.smul (isUnit_iff_ne_zero.2 (sq_pos_of_pos ha).ne').unit).measurableEmbedding
  have hef : e = f := by
    funext s
    simp [e, f, Function.comp_def]
  have hmap : Measure.map e μs =
      ENNReal.ofReal ((a ^ 2)⁻¹) • μt := by
    simpa [e, f, μs, μt, hef] using time_affine_map_restrict ha t r
  have hchange := hemb.essSup_map_measure (μ := μs) (g := E)
    (hgf := by simpa [μs, Function.comp_def, E, f, hef] using hsource)
    (hg := by
      have hc : ENNReal.ofReal ((a ^ 2)⁻¹) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
      rw [hmap, Measure.ae_ennreal_smul_measure_eq hc]
      exact htarget)
  have hpoint : Ec = fun s => ENNReal.ofReal (a⁻¹ ^ 3) * E (e s) := by
    funext s
    simpa [Ec, E, e, f, Function.comp_def, hef] using
      timeSlice_setLIntegral_comp_parabolicRescale ha x t r s g
  have hcalc : essSup Ec μs = ENNReal.ofReal (a⁻¹ ^ 3) * essSup E μt := by
    calc
      essSup Ec μs =
          essSup (fun s => ENNReal.ofReal (a⁻¹ ^ 3) * E (e s)) μs := by
        rw [hpoint]
      _ = ENNReal.ofReal (a⁻¹ ^ 3) * essSup (E ∘ e) μs := by
        simpa only [Function.comp_apply] using
          (ENNReal.essSup_const_mul (μ := μs) (f := E ∘ e)
            (a := ENNReal.ofReal (a⁻¹ ^ 3)))
      _ = ENNReal.ofReal (a⁻¹ ^ 3) * essSup E (Measure.map e μs) := by
        exact congrArg (fun z => ENNReal.ofReal (a⁻¹ ^ 3) * z) hchange.symm
      _ = ENNReal.ofReal (a⁻¹ ^ 3) *
          essSup E (ENNReal.ofReal ((a ^ 2)⁻¹) • μt) := by
        rw [hmap]
      _ = ENNReal.ofReal (a⁻¹ ^ 3) * essSup E μt := by
        rw [essSup_ennreal_smul_measure]
        exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  simpa [timeSliceEnergyEssSup, timeSliceBallEnergy, Ec, E, μs, μt,
    sub_zero, Function.comp_def] using hcalc

/-- Essential suprema increase when the measure and the integrand both increase. -/
theorem essSup_mono_measure_and_ae {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {f g : α → ℝ≥0∞}
    (hμν : μ ≤ ν) (hfg : f ≤ᵐ[μ] g) :
    essSup f μ ≤ essSup g ν := by
  exact (essSup_mono_ae hfg).trans (essSup_mono_measure' hμν)

/-- The time interval for a smaller nonnegative radius is contained in the larger one. -/
theorem time_interval_mono_radius {t r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hrr : r₁ ≤ r₂) :
    Ioc (t - r₁ ^ 2) t ⊆ Ioc (t - r₂ ^ 2) t := by
  intro s hs
  refine ⟨?_, hs.2⟩
  have hr₂ : 0 ≤ r₂ := hr₁.trans hrr
  have hrsq : r₁ ^ 2 ≤ r₂ ^ 2 := (sq_le_sq₀ hr₁ hr₂).2 hrr
  exact (sub_le_sub_left hrsq t).trans_lt hs.1

/-- The time-slice `L²` energy essential supremum is monotone in the radius. -/
theorem timeSliceEnergyEssSup_mono_radius {x : Vec3} {t r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hrr : r₁ ≤ r₂) (g : ParabolicPoint → ℝ) :
    timeSliceEnergyEssSup x t r₁ g ≤ timeSliceEnergyEssSup x t r₂ g := by
  apply essSup_mono_measure_and_ae
  · exact Measure.restrict_mono (time_interval_mono_radius hr₁ hrr) le_rfl
  · exact Filter.Eventually.of_forall fun s =>
      ball_lintegral_norm_sq_mono_radius hrr g

/-- The radius-normalized time-slice essential supremum has the standard comparison. -/
theorem timeSliceEnergyEssSup_div_radius_le {x : Vec3} {t r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hrr : r₁ ≤ r₂) (g : ParabolicPoint → ℝ) :
    timeSliceEnergyEssSup x t r₁ g / ENNReal.ofReal r₁ ≤
      ENNReal.ofReal (r₂ / r₁) *
        (timeSliceEnergyEssSup x t r₂ g / ENNReal.ofReal r₂) := by
  have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ hrr
  have hbase := timeSliceEnergyEssSup_mono_radius (x := x) (t := t)
    hr₁.le hrr g
  have hdiv :
      timeSliceEnergyEssSup x t r₁ g / ENNReal.ofReal r₁ ≤
        timeSliceEnergyEssSup x t r₂ g / ENNReal.ofReal r₁ := by
    exact ENNReal.div_le_div_right hbase _
  calc
    _ ≤ timeSliceEnergyEssSup x t r₂ g / ENNReal.ofReal r₁ := hdiv
    _ = ENNReal.ofReal (r₂ / r₁) *
        (timeSliceEnergyEssSup x t r₂ g / ENNReal.ofReal r₂) := by
      rw [ENNReal.ofReal_div_of_pos hr₁]
      simp only [ENNReal.div_eq_inv_mul]
      have hc := ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hr₂).ne'
        (ENNReal.ofReal_ne_top)
      calc
        _ = (ENNReal.ofReal r₁)⁻¹ * timeSliceEnergyEssSup x t r₂ g * 1 := by simp
        _ = (ENNReal.ofReal r₁)⁻¹ * timeSliceEnergyEssSup x t r₂ g *
            (ENNReal.ofReal r₂ * (ENNReal.ofReal r₂)⁻¹) := by rw [hc]
        _ = _ := by ring

end CKN.Foundation.Parabolic.Integration
