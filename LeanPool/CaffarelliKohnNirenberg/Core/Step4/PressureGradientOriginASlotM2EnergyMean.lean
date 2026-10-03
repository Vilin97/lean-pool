/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientInputsCentred
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceProductMeasurability

/-! # The parabolic seminorm of a spatial mean

A spatial mean over a fixed ball is, on any set of centres inside a slightly
smaller ball, dominated by a spatial convolution of the averaged field with
the indicator of one larger ball. Minkowski's inequality for the parabolic
seminorm then bounds the mean's seminorm by that of the field itself, with
the ratio of the two ball volumes as the only coefficient. No covering of
the averaging ball by cells of the running radius is needed.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
noncomputable section
namespace CKN.Core.Step4

/-- The averaging kernel: the normalized indicator of the enlarged ball. -/
def gapMeanKernel (ρ : ℝ) : Vec3 → ℝ≥0∞ := fun y =>
  (volume (vec3Ball (0 : Vec3) ρ))⁻¹ *
    (vec3Ball (0 : Vec3) (7 * ρ / 4)).indicator (fun _ => (1 : ℝ≥0∞)) y

theorem gapMeanKernel_measurable (ρ : ℝ) : Measurable (gapMeanKernel ρ) := by
  unfold gapMeanKernel
  exact measurable_const.mul
    ((measurable_indicator_const_iff (1 : ℝ≥0∞)).mpr (vec3Ball_measurable _ _))

theorem gapMeanKernel_ne_top {ρ : ℝ} (hρ : 0 < ρ) (y : Vec3) :
    gapMeanKernel ρ y ≠ ∞ := by
  have hpos : volume (vec3Ball (0 : Vec3) ρ) ≠ 0 := by
    rw [volume_vec3Ball_eq]
    have h1 : ENNReal.ofReal ρ ≠ 0 := by
      simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hρ
    exact mul_ne_zero (pow_ne_zero 3 h1)
      (by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using
        (by positivity : (0 : ℝ) < Real.pi * 4 / 3))
  unfold gapMeanKernel
  refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hpos) ?_
  by_cases hy : y ∈ vec3Ball (0 : Vec3) (7 * ρ / 4)
  · simp only [Set.indicator_of_mem hy]
    exact ENNReal.one_ne_top
  · simp only [Set.indicator_of_notMem hy]
    exact ENNReal.zero_ne_top

/-- The kernel has total mass the ratio of the two ball volumes. -/
theorem gapMeanKernel_lintegral {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ y, gapMeanKernel ρ y) = ENNReal.ofReal ((7 / 4 : ℝ) ^ 3) := by
  have hV : volume (vec3Ball (0 : Vec3) ρ) =
      ENNReal.ofReal ρ ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := volume_vec3Ball_eq _ _
  have hW : volume (vec3Ball (0 : Vec3) (7 * ρ / 4)) =
      ENNReal.ofReal ((7 / 4 : ℝ) ^ 3) * volume (vec3Ball (0 : Vec3) ρ) := by
    rw [volume_vec3Ball_eq, hV, ← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 7 * ρ / 4),
      ← ENNReal.ofReal_pow hρ.le,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (7 / 4 : ℝ) ^ 3)]
    congr 1
    ring
  have hVpos : volume (vec3Ball (0 : Vec3) ρ) ≠ 0 := by
    rw [hV]
    refine mul_ne_zero (pow_ne_zero 3 ?_) ?_
    · simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hρ
    · simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using
        (by positivity : (0 : ℝ) < Real.pi * 4 / 3)
  have hVtop : volume (vec3Ball (0 : Vec3) ρ) ≠ ∞ := Integration.volume_vec3Ball_lt_top.ne
  unfold gapMeanKernel
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hVpos),
    lintegral_indicator (vec3Ball_measurable _ _), setLIntegral_const, one_mul, hW, ← mul_assoc,
    mul_comm (volume (vec3Ball (0 : Vec3) ρ))⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel hVpos hVtop, mul_one]

/-- A slice-constant field carried by a ball of radius `3ρ/4` is dominated by
the spatial convolution of the averaged field with the averaging kernel. -/
theorem gap_constant_slice_le_convolution
    (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    {g : ParabolicPoint → ℝ} (hg : Measurable g)
    {m : ℝ → ℝ} {S : Set ParabolicPoint}
    (hScar : ∀ w ∈ S, w.1 ∈ vec3Ball x₀ (3 * ρ / 4))
    (w : ParabolicPoint)
    (hdom : w ∈ S → ENNReal.ofReal |m w.2| * volume (vec3Ball (0 : Vec3) ρ) ≤
      ∫⁻ z in vec3Ball x₀ ρ, ENNReal.ofReal |g (z, w.2)|) :
    ENNReal.ofReal |S.indicator (fun v : ParabolicPoint => m v.2) w| ≤
      spatialConvolution (gapMeanKernel ρ) (fun v => ENNReal.ofReal |g v|) w := by
  by_cases hw : w ∈ S
  · rw [Set.indicator_of_mem hw]
    have hx : w.1 ∈ vec3Ball x₀ (3 * ρ / 4) := hScar w hw
    set V := volume (vec3Ball (0 : Vec3) ρ) with hVdef
    have hVpos : V ≠ 0 := by
      rw [hVdef, volume_vec3Ball_eq]
      refine mul_ne_zero (pow_ne_zero 3 ?_) ?_
      · simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hρ
      · simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using
          (by positivity : (0 : ℝ) < Real.pi * 4 / 3)
    have hVtop : V ≠ ∞ := Integration.volume_vec3Ball_lt_top.ne
    set H : Vec3 → ℝ≥0∞ :=
      (vec3Ball x₀ ρ).indicator (fun z => ENNReal.ofReal |g (z, w.2)|) with hH
    have hHmeas : Measurable H := by
      rw [hH]
      refine Measurable.indicator ?_ (vec3Ball_measurable _ _)
      have hz : Measurable (fun z : Vec3 => g (z, w.2)) :=
        hg.comp (measurable_id.prodMk measurable_const)
      simpa only [Real.enorm_eq_ofReal_abs] using hz.enorm
    have hshift : (∫⁻ y, H (w.1 - y)) = ∫⁻ z, H z :=
      (Measure.measurePreserving_sub_left (volume : Measure Vec3) w.1).lintegral_comp hHmeas
    have hlow : ∀ y : Vec3, V⁻¹ * H (w.1 - y) ≤
        gapMeanKernel ρ y * ENNReal.ofReal |g (parabolicTranslate (-y) 0 w)| := by
      intro y
      by_cases hy : w.1 - y ∈ vec3Ball x₀ ρ
      · have hball : y ∈ vec3Ball (0 : Vec3) (7 * ρ / 4) := by
          have h1 : vec3EuclideanNorm (w.1 - y - x₀) < ρ := hy
          have h2 : vec3EuclideanNorm (w.1 - x₀) < 3 * ρ / 4 := hx
          have htri : vec3EuclideanNorm (y - 0) ≤
              vec3EuclideanNorm (w.1 - x₀) + vec3EuclideanNorm (w.1 - y - x₀) := by
            have hrw : y - 0 = (w.1 - x₀) - (w.1 - y - x₀) := by abel
            rw [hrw]
            exact vec3EuclideanNorm_sub_le _ _
          change vec3EuclideanNorm (y - 0) < 7 * ρ / 4
          linarith only [htri, h1, h2]
        have hK : gapMeanKernel ρ y = V⁻¹ := by
          unfold gapMeanKernel
          rw [Set.indicator_of_mem hball, mul_one]
        have heq : parabolicTranslate (-y) 0 w = (w.1 - y, w.2) := by
          unfold parabolicTranslate
          refine Prod.ext ?_ ?_ <;> simp only [neg_add_eq_sub, zero_add]
        rw [hK, heq, hH, Set.indicator_of_mem hy]
      · rw [hH, Set.indicator_of_notMem hy, mul_zero]
        simp
    have hconv : V⁻¹ * (∫⁻ z in vec3Ball x₀ ρ, ENNReal.ofReal |g (z, w.2)|) ≤
        spatialConvolution (gapMeanKernel ρ) (fun v => ENNReal.ofReal |g v|) w := by
      have hrestrict : (∫⁻ z in vec3Ball x₀ ρ, ENNReal.ofReal |g (z, w.2)|) = ∫⁻ z, H z := by
        rw [hH, lintegral_indicator (vec3Ball_measurable _ _)]
      rw [hrestrict, ← hshift, ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hVpos)]
      exact lintegral_mono hlow
    refine le_trans ?_ hconv
    have h := hdom hw
    calc
      ENNReal.ofReal |m w.2| = V⁻¹ * (ENNReal.ofReal |m w.2| * V) := by
        rw [mul_comm (ENNReal.ofReal |m w.2|) V, ← mul_assoc,
          ENNReal.inv_mul_cancel hVpos hVtop, one_mul]
      _ ≤ _ := mul_le_mul' le_rfl h
  · rw [Set.indicator_of_notMem hw, abs_zero, ENNReal.ofReal_zero]
    simp

/-- The a.e. form of the extended-valued seminorm comparison. -/
theorem gap_morreyENorm_mono_ae {p q : ℝ} (hp : 0 ≤ p)
    {f g : ParabolicPoint → ℝ≥0∞}
    (hfg : ∀ᵐ z ∂(volume : Measure ParabolicPoint), f z ≤ g z) :
    morreyENorm p q f ≤ morreyENorm p q g := by
  unfold morreyENorm
  refine iSup_le fun z => iSup_le fun r => ?_
  refine le_trans ?_ (le_iSup_of_le z (le_iSup_of_le r le_rfl))
  unfold morreyENormCell
  refine mul_le_mul_right ?_ _
  refine ENNReal.rpow_le_rpow (lintegral_mono_ae ?_) (one_div_nonneg.mpr hp)
  filter_upwards [ae_restrict_of_ae hfg] with w hw
  exact ENNReal.rpow_le_rpow hw hp

/-- A time-indexed almost-everywhere statement holds almost everywhere in
space-time. -/
theorem gap_ae_of_ae_time {P : ParabolicPoint → Prop}
    (h : ∀ᵐ s ∂(volume : Measure ℝ), ∀ x : Vec3, P (x, s)) :
    ∀ᵐ w ∂(volume : Measure ParabolicPoint), P w := by
  rw [MeasureTheory.ae_iff] at h ⊢
  have hsub : {w : ParabolicPoint | ¬ P w} ⊆
      (Set.univ : Set Vec3) ×ˢ {s : ℝ | ¬ ∀ x : Vec3, P (x, s)} := by
    intro w hw
    exact ⟨Set.mem_univ _, fun hall => hw (hall w.1)⟩
  refine measure_mono_null hsub ?_
  have hz : ((volume : Measure Vec3).prod (volume : Measure ℝ))
      ((Set.univ : Set Vec3) ×ˢ {s : ℝ | ¬ ∀ x : Vec3, P (x, s)}) = 0 := by
    rw [Measure.prod_prod, h, mul_zero]
  exact hz

/-- The a.e. form of the mean seminorm bound. -/
theorem gap_constant_slice_morreyNorm_le_ae
    (x₀ : Vec3) {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : (3 : ℝ) ≤ τ)
    {g : ParabolicPoint → ℝ} (hg : Measurable g) (hfin : morreyNorm 3 τ g ≠ ∞)
    {m : ℝ → ℝ} {S : Set ParabolicPoint}
    (hScar : ∀ w ∈ S, w.1 ∈ vec3Ball x₀ (3 * ρ / 4))
    (hdom : ∀ᵐ w ∂(volume : Measure ParabolicPoint), w ∈ S →
      ENNReal.ofReal |m w.2| * volume (vec3Ball (0 : Vec3) ρ) ≤
        ∫⁻ z in vec3Ball x₀ ρ, ENNReal.ofReal |g (z, w.2)|) :
    morreyNorm 3 τ (S.indicator (fun v : ParabolicPoint => m v.2)) ≤
      ENNReal.ofReal ((7 / 4 : ℝ) ^ 3) * morreyNorm 3 τ g := by
  have hmeasF : AEMeasurable (fun yz : Vec3 × ParabolicPoint =>
      gapMeanKernel ρ yz.1 *
        (fun v => ENNReal.ofReal |g v|) (parabolicTranslate (-yz.1) 0 yz.2))
      (volume.prod volume) := by
    refine Measurable.aemeasurable ?_
    have hmap : Measurable
        (fun yz : Vec3 × ParabolicPoint => parabolicTranslate (-yz.1) 0 yz.2) := by
      unfold parabolicTranslate
      exact (measurable_fst.neg.add (measurable_fst.comp measurable_snd)).prodMk
        (measurable_const.add (measurable_snd.comp measurable_snd))
    have hcomp : Measurable (fun yz : Vec3 × ParabolicPoint =>
        ENNReal.ofReal |g (parabolicTranslate (-yz.1) 0 yz.2)|) := by
      simpa only [Real.enorm_eq_ofReal_abs, Function.comp_def] using (hg.comp hmap).enorm
    exact ((gapMeanKernel_measurable ρ).comp measurable_fst).mul hcomp
  have hfinit : morreyENorm 3 τ (fun v => ENNReal.ofReal |g v|) ≠ ∞ := by
    rw [morreyENorm_ofReal_abs]
    exact hfin
  calc
    morreyNorm 3 τ (S.indicator (fun v : ParabolicPoint => m v.2))
        = morreyENorm 3 τ (fun w =>
            ENNReal.ofReal |S.indicator (fun v : ParabolicPoint => m v.2) w|) :=
      (morreyENorm_ofReal_abs 3 τ _).symm
    _ ≤ morreyENorm 3 τ
          (spatialConvolution (gapMeanKernel ρ) (fun v => ENNReal.ofReal |g v|)) := by
      refine gap_morreyENorm_mono_ae (by norm_num) ?_
      filter_upwards [hdom] with w hw
      exact gap_constant_slice_le_convolution x₀ hρ hg hScar w hw
    _ ≤ (∫⁻ y, gapMeanKernel ρ y) *
          morreyENorm 3 τ (fun v => ENNReal.ofReal |g v|) :=
      morreyENorm_spatialConvolution_le (by norm_num) hτ hmeasF
        (gapMeanKernel_ne_top hρ) hfinit
    _ = ENNReal.ofReal ((7 / 4 : ℝ) ^ 3) * morreyNorm 3 τ g := by
      rw [gapMeanKernel_lintegral hρ, morreyENorm_ofReal_abs]

/-- The spatial mean's mass on its own averaging ball. -/
theorem gap_centred_mean_mass_le (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (u : ParabolicPoint → Vec3) (s : ℝ) (k : Fin 3) :
    ENNReal.ofReal |sourceSliceCentredMean x₀ ρ u s k| * volume (vec3Ball (0 : Vec3) ρ) ≤
      ∫⁻ z in vec3Ball x₀ ρ, ENNReal.ofReal |u (z, s) k| := by
  have hvol : volume (vec3Ball (0 : Vec3) ρ) = volume (vec3Ball x₀ ρ) :=
    (volume_vec3Ball x₀ ρ).symm
  have hVtop : volume (vec3Ball x₀ ρ) ≠ ∞ := Integration.volume_vec3Ball_lt_top.ne
  have hVpos : (0 : ℝ) < (volume (vec3Ball x₀ ρ)).toReal := by
    rw [volume_vec3Ball_eq, ENNReal.toReal_mul, ← ENNReal.ofReal_pow hρ.le,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ ρ ^ 3),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi * 4 / 3)]
    positivity
  have habs := centred_source_average_component_bound (x := x₀) (ρ := ρ) (u := u) (s := s) k
  rw [Real.norm_eq_abs] at habs
  have havg : (⨍ y in vec3Ball x₀ ρ, |u (y, s) k|) =
      ((volume (vec3Ball x₀ ρ)).toReal)⁻¹ * ∫ y in vec3Ball x₀ ρ, |u (y, s) k| := by
    rw [average_eq, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
  rw [havg] at habs
  by_cases hint : IntegrableOn (fun z => |u (z, s) k|) (vec3Ball x₀ ρ) volume
  · have hmul : |sourceSliceCentredMean x₀ ρ u s k| * (volume (vec3Ball x₀ ρ)).toReal ≤
        ∫ y in vec3Ball x₀ ρ, |u (y, s) k| := by
      have h1 := mul_le_mul_of_nonneg_right habs hVpos.le
      rw [mul_comm ((volume (vec3Ball x₀ ρ)).toReal)⁻¹
          (∫ y in vec3Ball x₀ ρ, |u (y, s) k|),
        mul_assoc, inv_mul_cancel₀ hVpos.ne', mul_one] at h1
      exact h1
    have hEq : ENNReal.ofReal (∫ z in vec3Ball x₀ ρ, |u (z, s) k|) =
        ∫⁻ z in vec3Ball x₀ ρ, ENNReal.ofReal |u (z, s) k| :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (fun z => abs_nonneg _))
    calc
      ENNReal.ofReal |sourceSliceCentredMean x₀ ρ u s k| * volume (vec3Ball (0 : Vec3) ρ)
          = ENNReal.ofReal (|sourceSliceCentredMean x₀ ρ u s k| *
              (volume (vec3Ball x₀ ρ)).toReal) := by
            rw [hvol, ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_toReal hVtop]
      _ ≤ ENNReal.ofReal (∫ z in vec3Ball x₀ ρ, |u (z, s) k|) :=
            ENNReal.ofReal_le_ofReal hmul
      _ = _ := hEq
  · have hzero : (∫ y in vec3Ball x₀ ρ, |u (y, s) k|) = 0 := integral_undef hint
    rw [hzero, mul_zero] at habs
    have : |sourceSliceCentredMean x₀ ρ u s k| = 0 :=
      le_antisymm habs (abs_nonneg _)
    rw [this, ENNReal.ofReal_zero, zero_mul]
    simp

/-- The parabolic seminorm of the centred spatial mean on a carrier inside the
inner ball and the source time window is the velocity seminorm times `(7/4)³`. -/
theorem gap_centred_mean_carrier_morreyNorm_le
    (x₀ : Vec3) {ρ R₀ τ : ℝ} (hρ : 0 < ρ) (hτ : (3 : ℝ) ≤ τ)
    (hball : vec3Ball x₀ ρ ⊆ vec3Ball (0 : Vec3) R₀)
    {u : ParabolicPoint → Vec3} (k : Fin 3) {KU : ℝ≥0∞} (hKU : KU ≠ ∞)
    (hmeas : AEMeasurable ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
      (fun w => u w k)) volume)
    (hU : morreyNorm 3 τ ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
      (fun w => u w k)) ≤ KU)
    {S : Set ParabolicPoint} (hScar : ∀ w ∈ S, w.1 ∈ vec3Ball x₀ (3 * ρ / 4))
    (hStime : ∀ w ∈ S, w.2 ∈ Ioc (-(R₀ ^ 2)) 0) :
    morreyNorm 3 τ (S.indicator (fun w => sourceSliceCentredMean x₀ ρ u w.2 k)) ≤
      ENNReal.ofReal ((7 / 4 : ℝ) ^ 3) * KU := by
  obtain ⟨g, hgmeas, hgae⟩ := hmeas
  have hgnorm : morreyNorm 3 τ g ≤ KU := by
    refine le_trans (routeA_morreyNorm_mono_ae (by norm_num) ?_) hU
    filter_upwards [hgae] with w hw
    rw [hw]
  have hfin : morreyNorm 3 τ g ≠ ∞ := ne_top_of_le_ne_top hKU hgnorm
  have hslice : ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure Vec3),
      (parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => u w k) (z, s) = g (z, s) := by
    refine ae_ae_of_ae_prod_snd (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ))
      (p := fun w : Vec3 × ℝ =>
        (parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun v => u v k) w = g w) ?_
    exact hgae
  have hint : ∀ᵐ s ∂(volume : Measure ℝ), ∀ _x : Vec3,
      (∫⁻ z in vec3Ball x₀ ρ, ENNReal.ofReal
        |(parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun w => u w k) (z, s)|) =
        ∫⁻ z in vec3Ball x₀ ρ, ENNReal.ofReal |g (z, s)| := by
    filter_upwards [hslice] with s hs
    intro _x
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hs] with z hz
    rw [hz]
  have hpush : ∀ᵐ w ∂(volume : Measure ParabolicPoint),
      (∫⁻ z in vec3Ball x₀ ρ, ENNReal.ofReal
        |(parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun v => u v k) (z, w.2)|) =
        ∫⁻ z in vec3Ball x₀ ρ, ENNReal.ofReal |g (z, w.2)| :=
    gap_ae_of_ae_time hint
  have hdom : ∀ᵐ w ∂(volume : Measure ParabolicPoint), w ∈ S →
      ENNReal.ofReal |sourceSliceCentredMean x₀ ρ u w.2 k| *
        volume (vec3Ball (0 : Vec3) ρ) ≤
        ∫⁻ z in vec3Ball x₀ ρ, ENNReal.ofReal |g (z, w.2)| := by
    filter_upwards [hpush] with w hw hwS
    refine le_trans (gap_centred_mean_mass_le x₀ hρ u w.2 k) (le_of_eq ?_)
    rw [← hw]
    refine lintegral_congr_ae ((ae_restrict_iff' (vec3Ball_measurable x₀ ρ)).mpr
      (Filter.Eventually.of_forall (fun z hz => ?_)))
    have htime : w.2 ∈ Ioc (0 - R₀ ^ 2) 0 := by simpa using hStime w hwS
    have hmem : (z, w.2) ∈ parabolicCylinder (0 : Vec3) 0 R₀ := ⟨hball hz, htime⟩
    have hval : (parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun v => u v k) (z, w.2) =
        u (z, w.2) k := Set.indicator_of_mem hmem _
    dsimp only
    rw [hval]
  exact le_trans (gap_constant_slice_morreyNorm_le_ae x₀ hρ hτ hgmeas hfin
    (m := fun s => sourceSliceCentredMean x₀ ρ u s k) (S := S) hScar hdom)
    (mul_le_mul' le_rfl hgnorm)

end CKN.Core.Step4
