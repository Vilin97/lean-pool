/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Spatial and space-time averages

This file gives named wrappers for the two averages used on parabolic cylinders.
The definitions remain the ordinary Mathlib set averages, so existing `average`,
`eLpNorm`, and restriction lemmas apply without a second normalization convention.
-/

public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

noncomputable section

namespace CKN.Foundation.Parabolic.Integration

/-- The spatial average of a scalar function at a fixed time. -/
@[expose]
def spatialAverage (x : Vec3) (r s : ℝ) (g : ParabolicPoint → ℝ) : ℝ :=
  ⨍ y in vec3Ball x r, g (y, s)

/-- The space-time average of a scalar function on a parabolic cylinder. -/
def cylinderAverage (x : Vec3) (t r : ℝ) (g : ParabolicPoint → ℝ) : ℝ :=
  ⨍ z in parabolicCylinder x t r, g z

/-- The spatial average is the normalized spatial integral. -/
theorem spatialAverage_eq_toReal_inv_smul (x : Vec3) (r s : ℝ)
    (g : ParabolicPoint → ℝ) :
    spatialAverage x r s g =
      (volume (vec3Ball x r)).toReal⁻¹ • ∫ y in vec3Ball x r, g (y, s) := by
  exact setAverage_eq_toReal_inv_smul volume (vec3Ball x r) (fun y => g (y, s))

/-- The spatial average is bounded by the average of the absolute value. -/
theorem spatialAverage_abs_le {x : Vec3} {r s : ℝ} {g : ParabolicPoint → ℝ} :
    |spatialAverage x r s g| ≤
      ⨍ y in vec3Ball x r, |g (y, s)| := by
  unfold spatialAverage
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, smul_eq_mul, smul_eq_mul,
    abs_mul, abs_of_nonneg (inv_nonneg.mpr MeasureTheory.measureReal_nonneg)]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := (volume : Measure Vec3).restrict (vec3Ball x r))
        (fun y : Vec3 => g (y, s))))
    (inv_nonneg.mpr MeasureTheory.measureReal_nonneg)

/-- Jensen's inequality for a nonnegative real power of a set average. -/
theorem setAverage_abs_rpow_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {f : α → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hsPos : 0 < μ s) (hsTop : μ s < ∞)
    (hf : IntegrableOn (fun x => |f x|) s μ)
    (hfp : IntegrableOn (fun x => |f x| ^ p) s μ) :
    (⨍ x in s, |f x| ∂μ) ^ p ≤ ⨍ x in s, |f x| ^ p ∂μ := by
  have h := (convexOn_rpow hp).map_set_average_le
    (Real.continuous_rpow_const (zero_le_one.trans hp)).continuousOn isClosed_Ici
    hsPos.ne' hsTop.ne (ae_of_all _ fun x => abs_nonneg (f x))
    hf hfp
  simpa only [Function.comp_apply] using h

/-- Jensen's inequality for the norm of a vector-valued set average. -/
theorem setAverage_norm_rpow_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {s : Set α} {f : α → E} {p : ℝ}
    (hp : 1 ≤ p) (hsPos : 0 < μ s) (hsTop : μ s < ∞)
    (hf : IntegrableOn f s μ)
    (hfp : IntegrableOn (fun x => ‖f x‖ ^ p) s μ) :
    ‖⨍ x in s, f x ∂μ‖ ^ p ≤ ⨍ x in s, ‖f x‖ ^ p ∂μ := by
  calc
    ‖⨍ x in s, f x ∂μ‖ ^ p ≤ (⨍ x in s, ‖f x‖ ∂μ) ^ p := by
      exact Real.rpow_le_rpow (norm_nonneg _) (setAverage_norm_le μ s f)
        (zero_le_one.trans hp)
    _ ≤ ⨍ x in s, ‖f x‖ ^ p ∂μ := by
      have hfnorm : IntegrableOn (fun x => ‖f x‖) s μ := by
        change Integrable (fun x => ‖f x‖) (μ.restrict s)
        exact hf.norm
      exact (convexOn_rpow hp).map_set_average_le
        (Real.continuous_rpow_const (zero_le_one.trans hp)).continuousOn isClosed_Ici
        hsPos.ne' hsTop.ne (ae_of_all _ fun x => norm_nonneg (f x)) hfnorm hfp

private theorem setLAverage_const_mul_add {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {f : α → ℝ≥0∞} (hsPos : 0 < μ s) (hsTop : μ s < ∞)
    (hf : AEMeasurable f (μ.restrict s)) (c d : ℝ≥0∞) :
    ⨍⁻ x in s, c * (f x + d) ∂μ = c * ((⨍⁻ x in s, f x ∂μ) + d) := by
  rw [MeasureTheory.setLAverage_eq, MeasureTheory.setLAverage_eq]
  have hfd : AEMeasurable (fun x => f x + d) (μ.restrict s) :=
    hf.add measurable_const.aemeasurable
  rw [MeasureTheory.lintegral_const_mul'' c hfd]
  rw [MeasureTheory.lintegral_add_left' hf]
  rw [MeasureTheory.setLIntegral_const]
  rw [mul_div_assoc, ENNReal.add_div, mul_add]
  rw [mul_comm d (μ s), mul_div_assoc, ENNReal.mul_div_cancel hsPos.ne' hsTop.ne]
  rw [mul_add]

/-- Mean oscillation is bounded by `2^p` times the oscillation around any constant. -/
theorem setLaverage_norm_sub_setAverage_rpow_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {s : Set α} {f : α → E} {p : ℝ} {c : E}
    (hp : 1 ≤ p) (hsPos : 0 < μ s) (hsTop : μ s < ∞)
    (hf : IntegrableOn f s μ)
    (hfp : IntegrableOn (fun x => ‖f x - c‖ ^ p) s μ) :
    ⨍⁻ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ₑ ^ p ∂μ ≤
      (2 : ℝ≥0∞) ^ p * ⨍⁻ x in s, ‖f x - c‖ₑ ^ p ∂μ := by
  let m : E := ⨍ y in s, f y ∂μ
  let A : α → ℝ≥0∞ := fun x => ‖f x - c‖ₑ ^ p
  let B : ℝ≥0∞ := ‖c - m‖ₑ
  have hc : IntegrableOn (fun _ : α => c) s μ :=
    integrableOn_const hsTop.ne ENNReal.coe_ne_top
  have hsub : IntegrableOn (fun x => f x - c) s μ := by
    change Integrable (fun x => f x - c) (μ.restrict s)
    exact hf.sub hc
  have hA : AEMeasurable A (μ.restrict s) := by
    unfold A
    apply (ENNReal.continuous_rpow_const (y := p)).measurable.comp_aemeasurable
    exact hsub.aestronglyMeasurable.enorm
  have hJ : ‖m - c‖ ^ p ≤ ⨍ x in s, ‖f x - c‖ ^ p ∂μ := by
    have h := setAverage_norm_rpow_le hp hsPos hsTop hsub hfp
    have hsubavg : ⨍ x in s, f x - c ∂μ =
        (⨍ x in s, f x ∂μ) - c := by
      calc
        ⨍ x in s, f x - c ∂μ =
            (⨍ x in s, f x ∂μ) - ⨍ x in s, (fun _ : α => c) x ∂μ := by
          simpa only [Pi.sub_apply] using MeasureTheory.setAverage_sub hf hc
        _ = (⨍ x in s, f x ∂μ) - c := by
          rw [MeasureTheory.setAverage_const hsPos.ne' hsTop.ne c]
    rw [hsubavg] at h
    simpa [m] using h
  have hB : B ^ p ≤ ⨍⁻ x in s, A x ∂μ := by
    have hJ' : (‖c - m‖ : ℝ) ^ p ≤ ⨍ x in s, ‖f x - c‖ ^ p ∂μ := by
      simpa [norm_sub_rev] using hJ
    calc
      B ^ p = ENNReal.ofReal (‖c - m‖ ^ p) := by
        change ‖c - m‖ₑ ^ p = _
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
          (zero_le_one.trans hp)]
      _ ≤ ENNReal.ofReal (⨍ x in s, ‖f x - c‖ ^ p ∂μ) :=
        ENNReal.ofReal_le_ofReal hJ'
      _ = ⨍⁻ x in s, A x ∂μ := by
        rw [MeasureTheory.ofReal_setAverage hfp]
        · rw [MeasureTheory.laverage_eq]
          simp only [Measure.restrict_apply_univ]
          congr 1
          exact MeasureTheory.lintegral_congr_ae
            (Filter.Eventually.of_forall fun x => by
              simp only [A, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
                (zero_le_one.trans hp)])
        · exact Filter.Eventually.of_forall fun _ =>
            Real.rpow_nonneg (norm_nonneg _) _
  have hpoint : ∀ᵐ x ∂μ.restrict s,
      ‖f x - m‖ₑ ^ p ≤ (2 : ℝ≥0∞) ^ (p - 1) * (A x + B ^ p) := by
    filter_upwards [] with x
    calc
      ‖f x - m‖ₑ ^ p ≤ (‖f x - c‖ₑ + ‖c - m‖ₑ) ^ p := by
        rw [show f x - m = (f x - c) + (c - m) by abel]
        exact ENNReal.rpow_le_rpow (enorm_add_le _ _)
          (zero_le_one.trans hp)
      _ ≤ (2 : ℝ≥0∞) ^ (p - 1) * (A x + B ^ p) := by
        simpa [A, B] using
          (ENNReal.rpow_add_le_mul_rpow_add_rpow
            ‖f x - c‖ₑ ‖c - m‖ₑ hp)
  calc
    ⨍⁻ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ₑ ^ p ∂μ =
        ⨍⁻ x in s, ‖f x - m‖ₑ ^ p ∂μ := by rfl
    _ ≤ ⨍⁻ x in s, (2 : ℝ≥0∞) ^ (p - 1) * (A x + B ^ p) ∂μ :=
      MeasureTheory.laverage_mono_ae hpoint
    _ = (2 : ℝ≥0∞) ^ (p - 1) * ((⨍⁻ x in s, A x ∂μ) + B ^ p) := by
      exact setLAverage_const_mul_add hsPos hsTop hA
        ((2 : ℝ≥0∞) ^ (p - 1)) (B ^ p)
    _ ≤ (2 : ℝ≥0∞) ^ (p - 1) * (2 * ⨍⁻ x in s, A x ∂μ) := by
      gcongr
      calc
        (⨍⁻ x in s, A x ∂μ) + B ^ p ≤
            (⨍⁻ x in s, A x ∂μ) + ⨍⁻ x in s, A x ∂μ :=
          by simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hB (⨍⁻ x in s, A x ∂μ)
        _ = 2 * ⨍⁻ x in s, A x ∂μ := (two_mul _).symm
    _ = (2 : ℝ≥0∞) ^ p * ⨍⁻ x in s, ‖f x - c‖ₑ ^ p ∂μ := by
      calc
        (2 : ℝ≥0∞) ^ (p - 1) * (2 * ⨍⁻ x in s, A x ∂μ) =
            ((2 : ℝ≥0∞) ^ (p - 1) * (2 : ℝ≥0∞) ^ (1 : ℝ)) *
              ⨍⁻ x in s, A x ∂μ := by
                rw [ENNReal.rpow_one]
                ring
        _ = (2 : ℝ≥0∞) ^ ((p - 1) + 1) *
              ⨍⁻ x in s, A x ∂μ := by
          rw [ENNReal.rpow_add _ _ (by norm_num) ENNReal.ofNat_ne_top]
        _ = (2 : ℝ≥0∞) ^ p * ⨍⁻ x in s, ‖f x - c‖ₑ ^ p ∂μ := by
          congr 2
          ring

/-- Scalar mean oscillation is bounded by `2^p` times oscillation around a constant. -/
theorem setLaverage_abs_sub_setAverage_rpow_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {f : α → ℝ} {p c : ℝ}
    (hp : 1 ≤ p) (hsPos : 0 < μ s) (hsTop : μ s < ∞)
    (hf : IntegrableOn f s μ)
    (hfp : IntegrableOn (fun x => |f x - c| ^ p) s μ) :
    ⨍⁻ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ₑ ^ p ∂μ ≤
      (2 : ℝ≥0∞) ^ p * ⨍⁻ x in s, ‖f x - c‖ₑ ^ p ∂μ := by
  simpa only [Real.norm_eq_abs] using
    (setLaverage_norm_sub_setAverage_rpow_le hp hsPos hsTop hf hfp)

/-- Scalar mean oscillation on a positive-radius spatial ball. -/
theorem ball_setLaverage_abs_sub_spatialAverage_rpow_le {x : Vec3} {r s : ℝ} {g : ParabolicPoint →
  ℝ}
    {p c : ℝ} (hp : 1 ≤ p) (hr : 0 < r)
    (hg : IntegrableOn (fun y => g (y, s)) (vec3Ball x r) volume)
    (hgp : IntegrableOn (fun y => |g (y, s) - c| ^ p) (vec3Ball x r) volume) :
    ⨍⁻ y in vec3Ball x r,
        ‖g (y, s) - spatialAverage x r s g‖ₑ ^ p ∂volume ≤
      (2 : ℝ≥0∞) ^ p * ⨍⁻ y in vec3Ball x r, ‖g (y, s) - c‖ₑ ^ p ∂volume := by
  exact setLaverage_abs_sub_setAverage_rpow_le hp (volume_vec3Ball_pos hr)
    (volume_vec3Ball_lt_top (x := x) (r := r)) hg hgp

/-- Normalized scalar Hölder monotonicity on a finite positive-measure set. -/
theorem setAverage_abs_rpow_norm_mono {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {f : α → ℝ} {p q : ℝ}
    (hq1 : 1 ≤ q) (hqp : q ≤ p) (hsPos : 0 < μ s) (hsTop : μ s < ∞)
    (hf : IntegrableOn f s μ)
    (hp : IntegrableOn (fun x => |f x| ^ p) s μ) :
    (⨍ x in s, |f x| ^ q ∂μ) ^ q⁻¹ ≤
      (⨍ x in s, |f x| ^ p ∂μ) ^ p⁻¹ := by
  let _ : IsFiniteMeasure (μ.restrict s) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hsTop⟩
  have hf' : AEStronglyMeasurable f (μ.restrict s) :=
    hf.aestronglyMeasurable
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hp0 : 0 < p := lt_of_lt_of_le hq0 hqp
  have hpr : 1 ≤ p / q := by
    rw [le_div_iff₀ hq0]
    simpa using hqp
  have heq : ∀ x, (|f x| ^ q) ^ (p / q) = |f x| ^ p := by
    intro x
    rw [← Real.rpow_mul (abs_nonneg (f x))]
    congr 1
    field_simp [hq0.ne']
  have hpow : IntegrableOn (fun x => (|f x| ^ q) ^ (p / q)) s μ := by
    apply hp.congr
    filter_upwards [] with x
    exact (heq x).symm
  have hJ : (⨍ x in s, |f x| ^ q ∂μ) ^ (p / q) ≤
      ⨍ x in s, |f x| ^ p ∂μ := by
    have hq' : IntegrableOn (fun x => |(|f x| ^ q)|) s μ := by
      change Integrable (fun x => |(|f x| ^ q)|) (μ.restrict s)
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using
        (integrable_norm_rpow_of_le hf' hq0.le hp0.le hqp hp)
    have hpow' : IntegrableOn (fun x => |(|f x| ^ q)| ^ (p / q)) s μ := by
      simpa only [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hpow
    have h := setAverage_abs_rpow_le hpr hsPos hsTop hq' hpow'
    calc
      (⨍ x in s, |f x| ^ q ∂μ) ^ (p / q) ≤
          ⨍ x in s, (|f x| ^ q) ^ (p / q) ∂μ := by
        simpa only [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using h
      _ = ⨍ x in s, |f x| ^ p ∂μ := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall heq
  have hqavg : 0 ≤ ⨍ x in s, |f x| ^ q ∂μ :=
    setAverage_nonneg_of_ae (Filter.Eventually.of_forall fun _ =>
      Real.rpow_nonneg (abs_nonneg (f _)) _)
  have hpavg : 0 ≤ ⨍ x in s, |f x| ^ p ∂μ :=
    setAverage_nonneg_of_ae (Filter.Eventually.of_forall fun _ =>
      Real.rpow_nonneg (abs_nonneg (f _)) _)
  apply (Real.le_rpow_inv_iff_of_pos (Real.rpow_nonneg hqavg _)
    hpavg hp0).2
  rw [← Real.rpow_mul hqavg]
  convert hJ using 1
  field_simp [hq0.ne']

/-- The absolute value of a set average is bounded by the normalized `Lᵖ` mean. -/
theorem setAverage_abs_le_rpow_mean {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {f : α → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hsPos : 0 < μ s) (hsTop : μ s < ∞)
    (hf : IntegrableOn f s μ)
    (hfp : IntegrableOn (fun x => |f x| ^ p) s μ) :
    |⨍ x in s, f x ∂μ| ≤ (⨍ x in s, |f x| ^ p ∂μ) ^ p⁻¹ := by
  calc
    |⨍ x in s, f x ∂μ| ≤ ⨍ x in s, |f x| ∂μ := by
      simpa only [Real.norm_eq_abs] using setAverage_norm_le μ s f
    _ ≤ (⨍ x in s, |f x| ^ p ∂μ) ^ p⁻¹ := by
      simpa using
        (setAverage_abs_rpow_norm_mono (q := 1) (p := p) (by norm_num)
          hp hsPos hsTop hf hfp)

/-- The spatial `L²` lintegral is monotone with the ball radius. -/
theorem ball_lintegral_norm_sq_mono_radius {x : Vec3} {r₁ r₂ s : ℝ}
    (hrr : r₁ ≤ r₂) (g : ParabolicPoint → ℝ) :
    ∫⁻ y in vec3Ball x r₁, ‖g (y, s)‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ y in vec3Ball x r₂, ‖g (y, s)‖ₑ ^ (2 : ℝ) := by
  exact lintegral_mono_set (vec3Ball_mono hrr)

end CKN.Foundation.Parabolic.Integration
