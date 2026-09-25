/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.Basic
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Convolution Lp -/

@[expose] public section

namespace Homogenization

open scoped ENNReal Convolution
open MeasureTheory

noncomputable section

/-- The function `x ↦ |x|^p` is convex on `ℝ` for `p ≥ 1`. -/
lemma convexOn_abs_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : ℝ => |x| ^ p) := by
  have h1 : ConvexOn ℝ Set.univ (fun x : ℝ => |x|) := convexOn_univ_norm
  have h2 : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => t ^ p) := convexOn_rpow hp
  have h3 : MonotoneOn (fun t : ℝ => t ^ p) (Set.Ici 0) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow ha hab (le_trans zero_le_one hp)
  have himg : (fun x : ℝ => |x|) '' Set.univ ⊆ Set.Ici 0 := by
    intro y hy
    rcases hy with ⟨x, -, rfl⟩
    exact abs_nonneg x
  have himg_convex : Convex ℝ ((fun x : ℝ => |x|) '' Set.univ) := by
    have heq : (fun x : ℝ => |x|) '' Set.univ = Set.Ici 0 := by
      ext y
      simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Ici]
      constructor
      · rintro ⟨x, rfl⟩
        exact abs_nonneg x
      · intro hy
        exact ⟨y, abs_of_nonneg hy⟩
    rw [heq]
    exact convex_Ici 0
  exact (h2.subset himg himg_convex).comp h1 (h3.mono himg)

/-- A real-valued density of integral `1` yields a probability measure via
`withDensity`. -/
lemma isProbabilityMeasure_withDensity_ofReal
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {ρ : α → ℝ}
    (hρ_nonneg : ∀ x, 0 ≤ ρ x) (hρ_int : Integrable ρ μ) (hρ_one : ∫ x, ρ x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (ρ x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hρ_int (ae_of_all _ hρ_nonneg), hρ_one]
  simp

/-- Jensen's inequality for `x ↦ |x|^p` against a probability measure. -/
lemma jensen_abs_rpow_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hf : Integrable f μ) (hfpow : Integrable (fun x => |f x| ^ p) μ) :
    |∫ x, f x ∂μ| ^ p ≤ ∫ x, |f x| ^ p ∂μ := by
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => |x| ^ p) := convexOn_abs_rpow hp
  have hcont : ContinuousOn (fun x : ℝ => |x| ^ p) Set.univ := by
    exact (continuous_abs.rpow_const fun _ => Or.inr (le_trans zero_le_one hp)).continuousOn
  have hclosed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
  have hfs : ∀ᵐ x ∂μ, f x ∈ Set.univ := Filter.Eventually.of_forall (fun _ => Set.mem_univ _)
  exact hconv.map_integral_le hcont hclosed hfs hf hfpow

/-- Translation invariance of `eLpNorm` for Lebesgue measure on `Vec d`. -/
lemma eLpNorm_comp_sub_right {d : ℕ} (f : Vec d → ℝ) (t : Vec d) (p : ENNReal) :
    eLpNorm (fun x => f (x - t)) p volume = eLpNorm f p volume := by
  have heq : (fun x => f (x - t)) = f ∘ ((· + (-t)) : Vec d → Vec d) := by
    funext x
    simp [sub_eq_add_neg]
  rw [heq]
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight (-t)
  have hcomp : f ∘ (fun x : Vec d => x + (-t)) = f ∘ e := rfl
  rw [hcomp, ← e.measurableEmbedding.eLpNorm_map_measure]
  have hmap : Measure.map e volume = volume := by
    change Measure.map (fun x : Vec d => x + (-t)) volume = volume
    simpa using (MeasureTheory.map_add_right_eq_self (μ := (volume : Measure (Vec d))) (-t))
  rw [hmap]

/-- Translation invariance of `lintegral` for Lebesgue measure on `Vec d`. -/
lemma lintegral_comp_sub_right {d : ℕ} (f : Vec d → ℝ≥0∞) (hf : Measurable f) (t : Vec d) :
    ∫⁻ x, f (x - t) ∂(volume : Measure (Vec d)) = ∫⁻ x, f x ∂(volume : Measure (Vec d)) := by
  have heq : (fun x => f (x - t)) = f ∘ ((· + (-t)) : Vec d → Vec d) := by
    funext x
    simp [sub_eq_add_neg]
  rw [heq, lintegral_comp hf (measurable_add_const (-t))]
  have hmap : Measure.map (fun x : Vec d => x + (-t)) (volume : Measure (Vec d)) = volume := by
    simpa using (MeasureTheory.map_add_right_eq_self (μ := (volume : Measure (Vec d))) (-t))
  rw [hmap]

/-- Fubini plus translation invariance for the kernel used in the Jensen proof of
convolution contraction. -/
lemma fubini_translation_key {d : ℕ} (ρ : Vec d → ℝ≥0∞) (g : Vec d → ℝ) (p : ℝ)
    (hρ : Measurable ρ) (hg : Measurable g) :
    ∫⁻ x, ∫⁻ t, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume =
      (∫⁻ t, ρ t ∂volume) * (∫⁻ x, (ENNReal.ofReal |g x|) ^ p ∂volume) := by
  have hswap :
      ∫⁻ x, ∫⁻ t, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume =
        ∫⁻ t, ∫⁻ x, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume := by
    apply lintegral_lintegral_swap
    apply AEMeasurable.mul
    · exact (hρ.comp measurable_snd).aemeasurable
    · apply Measurable.aemeasurable
      apply Measurable.pow_const
      exact ENNReal.measurable_ofReal.comp
        (continuous_abs.measurable.comp (hg.comp (measurable_fst.sub measurable_snd)))
  rw [hswap]
  have hfactor :
      ∫⁻ t, ∫⁻ x, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume =
        ∫⁻ t, ρ t * ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume := by
    congr 1
    ext t
    exact lintegral_const_mul _ <|
      Measurable.pow_const
        (ENNReal.measurable_ofReal.comp
          (continuous_abs.measurable.comp (hg.comp (measurable_id.sub measurable_const)))) p
  rw [hfactor]
  have htrans :
      ∀ t, ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p ∂(volume : Measure (Vec d)) =
        ∫⁻ x, (ENNReal.ofReal |g x|) ^ p ∂volume := by
    intro t
    exact lintegral_comp_sub_right _
      (Measurable.pow_const
        (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hg)) p) t
  simp_rw [htrans]
  rw [lintegral_mul_const _ hρ, mul_comm]

private lemma integral_withDensity_ofReal_eq_integral_mul
    {d : ℕ} {f g : Vec d → ℝ}
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_meas : AEMeasurable f volume) :
    ∫ x, g x ∂(volume.withDensity fun x => ENNReal.ofReal (f x)) = ∫ x, f x * g x := by
  have heq :
      (fun x => ENNReal.ofReal (f x)) = fun x => (Real.toNNReal (f x) : ℝ≥0∞) := by
    funext x
    rw [ENNReal.ofReal_eq_coe_nnreal (hf_nonneg x), Real.toNNReal_of_nonneg (hf_nonneg x)]
  rw [heq]
  rw [integral_withDensity_eq_integral_smul₀ (hf_meas.real_toNNReal)]
  congr 1
  funext x
  simp [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hf_nonneg x)]

/-- Convolution with a nonnegative unit-mass kernel is an `L^p` contraction on
`Vec d` for `1 ≤ p < ∞`. -/
theorem young_convolution_nonneg_integral_one
    {d : ℕ} {ρ g : Vec d → ℝ} {p : ENNReal}
    (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hρ_nonneg : ∀ x, 0 ≤ ρ x)
    (hρ_int : Integrable ρ volume)
    (hρ_one : ∫ x, ρ x = 1)
    (hρ_meas : Measurable ρ)
    (hg_meas : Measurable g) :
    eLpNorm (convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) p volume ≤
      eLpNorm g p volume := by
  have hp_ne_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp'
  have hp_ge_one : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp').mpr hp
  let μ : Measure (Vec d) := volume.withDensity fun t => ENNReal.ofReal (ρ t)
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_withDensity_ofReal hρ_nonneg hρ_int hρ_one
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp'
    (MeasureTheory.AEStronglyMeasurable.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
      hρ_meas.aestronglyMeasurable hg_meas.aestronglyMeasurable)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp' hg_meas.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow _ (by positivity : 0 ≤ 1 / p.toReal)
  have hfubini :=
    fubini_translation_key (d := d) (fun t => ENNReal.ofReal (ρ t)) g p.toReal
      (hρ_meas.ennreal_ofReal) hg_meas
  have hρ_lint_one : ∫⁻ t, ENNReal.ofReal (ρ t) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρ_int (ae_of_all _ hρ_nonneg), hρ_one]
    simp
  have hpointwise :
      ∀ x, ‖convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ p.toReal ≤
        ∫⁻ t, ENNReal.ofReal (ρ t) * (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume := by
    intro x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [Real.enorm_eq_ofReal_abs]
    have heq_int : ∫ t, ρ t * g (x - t) = ∫ t, g (x - t) ∂μ := by
      symm
      exact integral_withDensity_ofReal_eq_integral_mul hρ_nonneg hρ_meas.aemeasurable
    rw [heq_int]
    by_cases hg_int_μ : Integrable (fun t => g (x - t)) μ
    · by_cases hgpow_int_μ : Integrable (fun t => |g (x - t)| ^ p.toReal) μ
      · have hJensen := jensen_abs_rpow_integral μ hp_ge_one hg_int_μ hgpow_int_μ
        have heq_pow :
            ∫ t, |g (x - t)| ^ p.toReal ∂μ =
              (∫⁻ t, ENNReal.ofReal (ρ t) * (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume).toReal := by
          rw [integral_withDensity_ofReal_eq_integral_mul hρ_nonneg hρ_meas.aemeasurable]
          rw [integral_eq_lintegral_of_nonneg_ae]
          · congr 1
            apply lintegral_congr
            intro t
            rw [ENNReal.ofReal_mul (hρ_nonneg t)]
            congr 1
            rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_pos.le]
          · exact ae_of_all _ (fun t => mul_nonneg (hρ_nonneg t) (Real.rpow_nonneg (abs_nonneg _) _))
          · have habs_rpow_meas : Measurable (fun t => |g (x - t)| ^ p.toReal) := by
              have hcont : Continuous (fun y : ℝ => |y| ^ p.toReal) :=
                continuous_abs.rpow_const (fun _ => Or.inr hp_pos.le)
              exact hcont.measurable.comp (hg_meas.comp (measurable_const.sub measurable_id))
            exact (hρ_meas.mul habs_rpow_meas).aestronglyMeasurable
        calc
          ENNReal.ofReal |∫ t, g (x - t) ∂μ| ^ p.toReal
              = ENNReal.ofReal (|∫ t, g (x - t) ∂μ| ^ p.toReal) := by
                  rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_pos.le]
          _ ≤ ENNReal.ofReal (∫ t, |g (x - t)| ^ p.toReal ∂μ) := by
                exact ENNReal.ofReal_le_ofReal hJensen
          _ =
              ENNReal.ofReal
                ((∫⁻ t, ENNReal.ofReal (ρ t) * (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                  ∂volume).toReal) := by
                rw [heq_pow]
          _ ≤ ∫⁻ t, ENNReal.ofReal (ρ t) * (ENNReal.ofReal |g (x - t)|) ^ p.toReal
                ∂volume := by
                exact ENNReal.ofReal_toReal_le
      · have hnot_finite :
            ∫⁻ t, ENNReal.ofReal (ρ t) * (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume = ⊤ := by
          have h_eq :
              ∫⁻ t, ENNReal.ofReal (ρ t) * (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume =
                ∫⁻ t, (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂μ := by
            have hsub : Measurable (fun t : Vec d => x - t) := measurable_const.sub measurable_id
            have h_abs_meas : Measurable (fun t => |g (x - t)|) :=
              continuous_abs.measurable.comp (hg_meas.comp hsub)
            have h_meas_pow : Measurable (fun t => (ENNReal.ofReal |g (x - t)|) ^ p.toReal) :=
              Measurable.pow_const h_abs_meas.ennreal_ofReal p.toReal
            symm
            convert
              lintegral_withDensity_eq_lintegral_mul volume hρ_meas.ennreal_ofReal h_meas_pow
              using 2
          rw [h_eq]
          have habs_rpow_nonneg : ∀ t, 0 ≤ |g (x - t)| ^ p.toReal :=
            fun t => Real.rpow_nonneg (abs_nonneg _) _
          have habs_rpow_meas : Measurable (fun t => |g (x - t)| ^ p.toReal) := by
            have hcont : Continuous (fun y : ℝ => |y| ^ p.toReal) :=
              continuous_abs.rpow_const (fun _ => Or.inr hp_pos.le)
            have hsub : Measurable (fun t : Vec d => x - t) := measurable_const.sub measurable_id
            exact hcont.measurable.comp (hg_meas.comp hsub)
          have h_top : ∫⁻ t, (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂μ = ⊤ := by
            rw [← lintegral_ofReal_ne_top_iff_integrable habs_rpow_meas.aestronglyMeasurable
                (ae_of_all _ habs_rpow_nonneg)] at hgpow_int_μ
            push Not at hgpow_int_μ
            convert hgpow_int_μ using 1
            congr 1
            ext t
            rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_pos.le]
          rw [h_top]
        simp [hnot_finite]
    ·
      rw [integral_undef hg_int_μ]
      simp only [abs_zero, ENNReal.ofReal_zero]
      rw [ENNReal.zero_rpow_of_pos hp_pos]
      exact zero_le
  calc
    ∫⁻ x, ‖convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ p.toReal ∂volume
        ≤ ∫⁻ x, ∫⁻ t,
            ENNReal.ofReal (ρ t) * (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume ∂volume := by
            exact lintegral_mono hpointwise
    _ = (∫⁻ t, ENNReal.ofReal (ρ t) ∂volume) *
          (∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume) := hfubini
    _ = 1 * (∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume) := by rw [hρ_lint_one]
    _ = ∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume := one_mul _
    _ = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂volume := by
          congr 1
          ext x
          rw [Real.enorm_eq_ofReal_abs]

/-- `AEMeasurable` version of `young_convolution_nonneg_integral_one`, obtained by
passing to a measurable representative of the input function. -/
theorem young_convolution_nonneg_integral_one_of_aemeasurable
    {d : ℕ} {ρ g : Vec d → ℝ} {p : ENNReal}
    (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hρ_nonneg : ∀ x, 0 ≤ ρ x)
    (hρ_int : Integrable ρ volume)
    (hρ_one : ∫ x, ρ x = 1)
    (hρ_meas : Measurable ρ)
    (hg_meas : AEMeasurable g volume) :
    eLpNorm (convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) p volume ≤
      eLpNorm g p volume := by
  let g' : Vec d → ℝ := hg_meas.mk g
  have hconv :
      convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume =
        convolution ρ g' (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    simpa [g'] using
      (MeasureTheory.convolution_congr (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (μ := (volume : Measure (Vec d)))
        (h1 := Filter.EventuallyEq.rfl) (h2 := hg_meas.ae_eq_mk))
  rw [hconv]
  calc
    eLpNorm (convolution ρ g' (ContinuousLinearMap.lsmul ℝ ℝ) volume) p volume
        ≤ eLpNorm g' p volume :=
      young_convolution_nonneg_integral_one hp hp' hρ_nonneg hρ_int hρ_one hρ_meas
        hg_meas.measurable_mk
    _ = eLpNorm g p volume := by
          exact eLpNorm_congr_ae hg_meas.ae_eq_mk.symm

end

end Homogenization
