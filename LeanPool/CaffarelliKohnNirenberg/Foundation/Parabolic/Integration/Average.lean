/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

/-!
# Integration and averages on parabolic cylinders

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This independent module records generic average identities and
the product-measure formulas used on balls and parabolic cylinders.

The source-facing scale-invariant quantities are intentionally not defined
here.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

noncomputable section

namespace CKN.Foundation.Parabolic.Integration

private theorem continuous_vec3EuclideanNorm_sub (x : Vec3) :
    Continuous (fun y : Vec3 => vec3EuclideanNorm (y - x)) := by
  unfold vec3EuclideanNorm
  fun_prop

private theorem norm_vec3_sub_le_euclideanNorm (x y : Vec3) :
    ‖y - x‖ ≤ vec3EuclideanNorm (y - x) := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg _)]
  intro i
  change |(y - x) i| ≤ vec3EuclideanNorm (y - x)
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg ((y - x) j)) (Finset.mem_univ i)

/-! ### Measures and cylinder Fubini -/

/-- The volume measure on `ParabolicPoint` is the product of spatial and time volume. -/
theorem volume_parabolicPoint_eq_prod :
    (volume : Measure ParabolicPoint) =
      (volume : Measure Vec3).prod (volume : Measure ℝ) :=
  rfl

/-- A positive-radius Euclidean spatial ball has positive volume. -/
theorem volume_vec3Ball_pos {x : Vec3} {r : ℝ} (hr : 0 < r) :
    0 < volume (vec3Ball x r) := by
  have hopen : IsOpen (vec3Ball x r) := by
    unfold vec3Ball
    exact isOpen_lt (continuous_vec3EuclideanNorm_sub x) continuous_const
  exact hopen.measure_pos volume ⟨x, by simp [vec3EuclideanNorm_zero, hr]⟩

/-- A Euclidean spatial ball has finite volume. -/
theorem volume_vec3Ball_lt_top {x : Vec3} {r : ℝ} :
    volume (vec3Ball x r) < ∞ := by
  have hsub : vec3Ball x r ⊆ Metric.ball x r := by
    intro y hy
    change ‖y - x‖ < r
    exact lt_of_le_of_lt (norm_vec3_sub_le_euclideanNorm x y)
      (by
        change vec3EuclideanNorm (y - x) < r at hy
        exact hy)
  exact (measure_mono hsub).trans_lt
    (measure_ball_lt_top (μ := volume) (x := x) (r := r))

/-- A positive-radius parabolic cylinder has positive volume. -/
theorem volume_parabolicCylinder_pos {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    0 < volume (parabolicCylinder x t r) := by
  rw [volume_parabolicCylinder]
  exact ENNReal.mul_pos (ne_of_gt (volume_vec3Ball_pos hr))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr)))

/-- A parabolic cylinder has finite volume. -/
theorem volume_parabolicCylinder_lt_top {x : Vec3} {t r : ℝ} :
    volume (parabolicCylinder x t r) < ∞ := by
  rw [volume_parabolicCylinder]
  exact ENNReal.mul_lt_top
    (volume_vec3Ball_lt_top (x := x) (r := r))
    ENNReal.ofReal_lt_top

/-- Fubini's theorem on a parabolic cylinder for Bochner-integrable functions. -/
theorem integral_parabolicCylinder {x : Vec3} {t r : ℝ}
    {g : ParabolicPoint → ℝ}
    (hg : IntegrableOn g (parabolicCylinder x t r) volume) :
    ∫ z in parabolicCylinder x t r, g z ∂volume =
      ∫ s in Ioc (t - r ^ 2) t, ∫ y in vec3Ball x r, g (y, s) := by
  rw [parabolicCylinder, volume_parabolicPoint_eq_prod]
  change
    ∫ z in vec3Ball x r ×ˢ Ioc (t - r ^ 2) t, g z ∂
        (volume : Measure Vec3).prod (volume : Measure ℝ) = _
  change IntegrableOn g (vec3Ball x r ×ˢ Ioc (t - r ^ 2) t)
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) at hg
  have hgs :
      IntegrableOn (fun z : ℝ × Vec3 => g z.swap)
        (Ioc (t - r ^ 2) t ×ˢ vec3Ball x r)
        ((volume : Measure ℝ).prod (volume : Measure Vec3)) := by
    exact hg.swap
  calc
    ∫ z in vec3Ball x r ×ˢ Ioc (t - r ^ 2) t, g z ∂
        (volume : Measure Vec3).prod (volume : Measure ℝ) =
        ∫ z in Ioc (t - r ^ 2) t ×ˢ vec3Ball x r, g z.swap ∂
          (volume : Measure ℝ).prod (volume : Measure Vec3) :=
      (setIntegral_prod_swap (μ := (volume : Measure Vec3))
        (ν := (volume : Measure ℝ)) (vec3Ball x r) (Ioc (t - r ^ 2) t) g).symm
    _ = ∫ s in Ioc (t - r ^ 2) t, ∫ y in vec3Ball x r, g (y, s) := by
      rw [setIntegral_prod _ hgs]
      rfl

/-- Tonelli's theorem on a parabolic cylinder for nonnegative extended-real functions. -/
theorem lintegral_parabolicCylinder {x : Vec3} {t r : ℝ}
    {g : ParabolicPoint → ℝ≥0∞}
    (hg : AEMeasurable g (volume.restrict (parabolicCylinder x t r))) :
    ∫⁻ z in parabolicCylinder x t r, g z ∂volume =
      ∫⁻ s in Ioc (t - r ^ 2) t, ∫⁻ y in vec3Ball x r, g (y, s) := by
  rw [parabolicCylinder, volume_parabolicPoint_eq_prod]
  change
    ∫⁻ z in vec3Ball x r ×ˢ Ioc (t - r ^ 2) t, g z ∂
        (volume : Measure Vec3).prod (volume : Measure ℝ) = _
  exact setLIntegral_prod_symm g hg

/-! ### Generic averages -/

/-- The set average is the integral against the reciprocal real measure. -/
theorem setAverage_eq_toReal_inv_smul {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure α) (s : Set α) (f : α → E) :
    ⨍ x in s, f x ∂μ = (μ s).toReal⁻¹ • ∫ x in s, f x ∂μ := by
  simpa [MeasureTheory.measureReal_def] using
    (MeasureTheory.setAverage_eq μ f s)

/-- Set averages are additive when both summands are integrable. -/
theorem setAverage_add_of_integrableOn {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} {f g : α → ℝ}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) :
    ⨍ x in s, (f + g) x ∂μ =
      ⨍ x in s, f x ∂μ + ⨍ x in s, g x ∂μ :=
  MeasureTheory.setAverage_add hf hg

/-- Set averages commute with subtraction under integrability. -/
theorem setAverage_sub_of_integrableOn {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} {f g : α → ℝ}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) :
    ⨍ x in s, (f - g) x ∂μ =
      ⨍ x in s, f x ∂μ - ⨍ x in s, g x ∂μ :=
  MeasureTheory.setAverage_sub hf hg

/-- The average of a constant on a positive finite-measure set is that constant. -/
theorem setAverage_const_of_pos_of_lt_top {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} (hsPos : 0 < μ s) (hsTop : μ s < ∞) (c : ℝ) :
    ⨍ _x in s, c ∂μ = c := by
  exact MeasureTheory.setAverage_const hsPos.ne' hsTop.ne c

/-- Set averages preserve nonnegativity almost everywhere. -/
theorem setAverage_nonneg_of_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} {f : α → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f) :
    0 ≤ ⨍ x in s, f x ∂μ :=
  MeasureTheory.average_nonneg_of_ae hf

/-- The norm of an average is bounded by the average of the norm. -/
theorem setAverage_norm_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (s : Set α) (f : α → E) :
    ‖⨍ x in s, f x ∂μ‖ ≤ ⨍ x in s, ‖f x‖ ∂μ := by
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr MeasureTheory.measureReal_nonneg)]
  exact mul_le_mul_of_nonneg_left
    (MeasureTheory.norm_integral_le_integral_norm
      (μ := μ.restrict s) f)
    (inv_nonneg.mpr MeasureTheory.measureReal_nonneg)

/-- Set averages are monotone almost everywhere. -/
theorem setAverage_mono_of_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : Set α} {f g : α → ℝ}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hfg : f ≤ᵐ[μ.restrict s] g) :
    ⨍ x in s, f x ∂μ ≤ ⨍ x in s, g x ∂μ := by
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
  exact smul_le_smul_of_nonneg_left
    (MeasureTheory.setIntegral_mono_ae_restrict hf hg hfg)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

end CKN.Foundation.Parabolic.Integration
