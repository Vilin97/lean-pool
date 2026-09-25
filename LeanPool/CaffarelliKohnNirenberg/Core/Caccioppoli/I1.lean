/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Terms
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.I1ProductRules

/-!
# I1

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat


noncomputable section

namespace CKN

theorem caccioppoli_I1_heat_operator
    {η : Vec3 × ℝ → ℝ} {x₀ : Vec3} {t₀ r : ℝ}
    {z : ParabolicPoint} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (ht : z.2 - t₀ < r ^ 2) :
    timePartial (fun w : ParabolicPoint =>
        backwardHeatCutoff η x₀ t₀ r w) z +
        ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
          backwardHeatCutoff η x₀ t₀ r w) i i z =
      (timePartial (fun w : ParabolicPoint => η w) z +
          ∑ i, spatialSecondPartial (fun w : ParabolicPoint => η w) i i z) *
          backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
        2 * ∑ i, spatialPartial (fun w : ParabolicPoint => η w) i z *
          (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i) := by
  have hηslice : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun x : Vec3 => η (x, z.2)) := by
    simpa only [Function.comp_def, id_eq] using
      hη.comp (contDiff_id.prodMk (contDiff_const (c := z.2)))
  have hΓslice : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : Vec3 =>
      backwardHeatTestFunction r (x - x₀) (z.2 - t₀)) := by
    have hτ : 0 < r ^ 2 - (z.2 - t₀) := sub_pos.mpr ht
    rw [show (fun x : Vec3 => backwardHeatTestFunction r
        (x - x₀) (z.2 - t₀)) = fun x : Vec3 => r ^ 2 *
          ((4 * Real.pi * (r ^ 2 - (z.2 - t₀))) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ j, (x - x₀) j ^ 2) /
              (4 * (r ^ 2 - (z.2 - t₀))))) by
      funext x
      rw [backwardHeatTestFunction, heatKernel_eq_formula_sum hτ]]
    fun_prop (disch := positivity)
  have htime := caccioppoli_cutoff_heat_timePartial
    (η := η) (x₀ := x₀) (t₀ := t₀) (r := r) (z := z) hη ht
  have htime' : timePartial (fun w : ParabolicPoint =>
      backwardHeatCutoff η x₀ t₀ r w) z =
      timePartial (fun w : ParabolicPoint => η w) z *
          backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
        η z * (-r ^ 2 * heatKernelTimeDerivative (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀))) := by
    simpa only [ParabolicPoint] using htime
  have hfun : (fun x : Vec3 =>
      backwardHeatCutoff η x₀ t₀ r (x, z.2)) =
      (fun x : Vec3 => η (x, z.2) *
        backwardHeatTestFunction r (x - x₀) (z.2 - t₀)) := by
    funext x
    simp only [backwardHeatCutoff, ht, ↓reduceIte]
  have hsum :
      ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
          backwardHeatCutoff η x₀ t₀ r w) i i z =
        spatialLaplacian (fun x : Vec3 => η (x, z.2) *
          backwardHeatTestFunction r (x - x₀) (z.2 - t₀)) z.1 := by
    change ∑ i, mixedSecond (fun x : Vec3 =>
        backwardHeatCutoff η x₀ t₀ r (x, z.2)) i i z.1 = _
    rw [hfun]
    rfl
  rw [htime', hsum]
  have hprod := congrFun (caccioppoli_spatialLaplacian_mul hηslice hΓslice) z.1
  rw [hprod]
  have hΓtime : timePartial (fun w : ParabolicPoint =>
      backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀)) z +
      ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
        backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀)) i i z = 0 := by
    rw [caccioppoli_heat_timePartial (x₀ := x₀) (t₀ := t₀)
      (r := r) (z := z) (by simpa using ht)]
    simp_rw [caccioppoli_heat_secondSpatialPartial (x₀ := x₀) (t₀ := t₀)
      (r := r) (z := z) (by simpa using ht)]
    rw [← Finset.mul_sum]
    have heq := heatKernel_heat_equation
      (x := z.1 - x₀) (t := r ^ 2 - (z.2 - t₀)) (sub_pos.mpr ht)
    unfold heatKernelLaplacian at heq
    rw [heq]
    ring
  have hΓspace : spatialLaplacian (fun x : Vec3 =>
      backwardHeatTestFunction r (x - x₀) (z.2 - t₀)) z.1 =
      -timePartial (fun w : ParabolicPoint =>
        backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀)) z := by
    have hΓtime' := hΓtime
    change timePartial (fun w : ParabolicPoint =>
      backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀)) z +
        spatialLaplacian (fun x : Vec3 =>
          backwardHeatTestFunction r (x - x₀) (z.2 - t₀)) z.1 = 0 at hΓtime'
    linarith only [hΓtime']
  rw [hΓspace]
  rw [show spatialLaplacian (fun x : Vec3 => η (x, z.2)) z.1 =
      ∑ i, spatialSecondPartial (fun w : ParabolicPoint => η w) i i z by rfl]
  rw [caccioppoli_heat_timePartial (x₀ := x₀) (t₀ := t₀)
    (r := r) (z := z) (by simpa using ht)]
  have hΓpartial : ∀ i : Fin 3,
      spatialDeriv (fun x : Vec3 =>
        backwardHeatTestFunction r (x - x₀) (z.2 - t₀)) i z.1 =
        r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) i := by
    intro i
    simpa only [spatialPartial, spatialDeriv] using
      caccioppoli_heat_spatialPartial (x₀ := x₀) (t₀ := t₀)
        (r := r) (z := z) ht i
  simp only [spatialGradDot]
  simp_rw [hΓpartial]
  have hηpartial : ∀ i : Fin 3,
      spatialDeriv (fun x : Vec3 => η (x, z.2)) i z.1 =
        spatialPartial (fun w : ParabolicPoint => η w) i z := by
    intro i
    rfl
  simp_rw [hηpartial]
  have heta : η z = η (z.1, z.2) := rfl
  rw [heta]
  ring

theorem caccioppoli_I1_lintegral_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {U H : α → ℝ≥0∞} {C E : ℝ≥0∞}
    (hC : C ≠ ∞) (hHC : H ≤ᵐ[μ] fun _ => C)
    (hE : (∫⁻ x, U x ∂μ) ≤ E) :
    (∫⁻ x, U x * H x ∂μ) ≤ C * E := by
  calc
    (∫⁻ x, U x * H x ∂μ) ≤ ∫⁻ x, U x * C ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hHC] with x hx
      simpa only [mul_comm (U x)] using mul_le_mul_left hx (U x)
    _ = C * ∫⁻ x, U x ∂μ := by
      calc
        (∫⁻ x, U x * C ∂μ) = ∫⁻ x, C * U x ∂μ := by
          apply lintegral_congr
          intro x
          rw [mul_comm]
        _ = C * ∫⁻ x, U x ∂μ :=
          lintegral_const_mul' C U hC
    _ ≤ C * E := by
      simpa only [mul_comm C] using mul_le_mul_left hE C

theorem caccioppoli_I1_toReal_lintegral_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {U H : α → ℝ≥0∞} {C E : ℝ≥0∞}
    (_ : AEMeasurable U μ) (_ : AEMeasurable H μ)
    (hC : C ≠ ∞) (hHC : H ≤ᵐ[μ] fun _ => C)
    (hE : (∫⁻ x, U x ∂μ) ≤ E)
    (hCE : C * E ≠ ∞) :
    (∫⁻ x, U x * H x ∂μ).toReal ≤ (C * E).toReal := by
  exact ENNReal.toReal_mono hCE
    (caccioppoli_I1_lintegral_bound hC hHC hE)

private theorem caccioppoli_energy_lintegral_bound
    {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ A : ℝ}
    (_ : 0 < ρ)
    (hU : AEMeasurable (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)))
    (hess : essSup (fun s =>
      ∫⁻ y in vec3Ball z.1 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) = ENNReal.ofReal A) :
    (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal A := by
  have hpow : AEMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) :=
    hU.pow_const (2 : ℝ)
  have hinner : ∀ᵐ s ∂(volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)),
      (∫⁻ y in vec3Ball z.1 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ)) ≤
        ENNReal.ofReal A := by
    rw [← hess]
    exact ENNReal.ae_le_essSup (fun s =>
      ∫⁻ y in vec3Ball z.1 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
  calc
    (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ)) =
        ∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, ∫⁻ y in vec3Ball z.1 ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ) :=
      lintegral_parabolicCylinder hpow
    _ ≤ ∫⁻ _s in Ioc (z.2 - ρ ^ 2) z.2, ENNReal.ofReal A := by
      apply lintegral_mono_ae
      exact hinner
    _ = ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal A := by
      have hμ :
          (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) Set.univ =
            ENNReal.ofReal (ρ ^ 2) := by
        simp [Real.volume_Ioc]
      rw [lintegral_const, hμ]
      ring

theorem caccioppoli_I1_normalization
    {ρ r α K C₂₅ I₁ : ℝ} (hρ : 0 < ρ) (_ : 0 < r)
    (hKbound : K ≤ C₂₅ ^ 2)
    (hraw : I₁ ≤ K * (r ^ 2 / ρ ^ 5) * (ρ ^ 3 * α ^ 2)) :
    I₁ ≤ (C₂₅ * (r / ρ) * α) ^ 2 := by
  have hscale : r ^ 2 / ρ ^ 5 * (ρ ^ 3 * α ^ 2) =
      (r / ρ) ^ 2 * α ^ 2 := by
    field_simp [hρ.ne']
  calc
    I₁ ≤ K * (r ^ 2 / ρ ^ 5) * (ρ ^ 3 * α ^ 2) := hraw
    _ = K * (r ^ 2 / ρ ^ 5 * (ρ ^ 3 * α ^ 2)) := by ring
    _ = K * ((r / ρ) ^ 2 * α ^ 2) := by rw [hscale]
    _ ≤ C₂₅ ^ 2 * ((r / ρ) ^ 2 * α ^ 2) := by
      gcongr
    _ = (C₂₅ * (r / ρ) * α) ^ 2 := by ring

theorem caccioppoli_I1_velocity_energy_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (z : ParabolicPoint)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (ρ ^ 3 * alpha u z ρ ^ 2) := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  have hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet Ω' J)) :=
    (hsol.2.2.2.2.2.1 Ω' J hbox).1
  have hnorm : AEStronglyMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)))
      (volume.restrict (spaceTimeSet Ω' J)) := by
    have hc : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact (ENNReal.continuous_ofReal.comp hc).comp_aestronglyMeasurable hu
  have hnorm' : AEStronglyMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)))
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) :=
    hnorm.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have hess : essSup (fun s =>
      ∫⁻ y in vec3Ball z.1 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u (y, s))) ^ (2 : ℝ))
      (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) =
      ENNReal.ofReal (ρ * alpha u z ρ ^ 2) := by
    simpa only [timeSliceEnergyEssSup, timeSliceBallEnergy,
      Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)] using
      sws_timeSliceEnergyEssSup_eq_ofReal_alpha_sq hsol z hρ hsub
  have henergy := caccioppoli_energy_lintegral_bound hρ hnorm'.aemeasurable hess
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ρ ^ 2)] at henergy
  convert henergy using 1
  congr 1
  ring

theorem caccioppoli_I1_cutoff_annulus_pointwise
    {x₀ : Vec3} {t₀ ρ R r : ℝ} (hρ : 0 < ρ) (hR : ρ / 2 < R)
    (hr : 0 < r) (hscale : r ≤ ρ / 2) {z : ParabolicPoint}
    (hp : (z.1 - x₀, z.2 - t₀) ∈
      parabolicCylinder 0 0 ρ \ parabolicCylinder 0 0 (ρ / 2)) :
    |timePartial (fun w : ParabolicPoint =>
        backwardHeatCutoff (caccioppoliCutoff x₀ t₀ ρ R hρ hR)
          x₀ t₀ r w) z +
        ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
          backwardHeatCutoff (caccioppoliCutoff x₀ t₀ ρ R hρ hR)
            x₀ t₀ r w) i i z| ≤
      (32 / (R ^ 2 - (ρ / 2) ^ 2) +
        3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
          (8000000 * r ^ 2 / ρ ^ 3) +
        6 * (cutoffGradientConstant / ρ) *
          (5000000 * r ^ 2 / ρ ^ 4) := by
  have hhtime : z.2 - t₀ < r ^ 2 := by
    have hp' := (mem_parabolicCylinder.mp hp.1).2.2
    exact lt_of_le_of_lt (by simpa only [sub_zero] using hp') (sq_pos_of_pos hr)
  have hht := caccioppoli_I1_heat_operator
    (η := caccioppoliCutoff x₀ t₀ ρ R hρ hR) (x₀ := x₀)
    (t₀ := t₀) (r := r) (z := z)
    (caccioppoli_cutoff_smooth x₀ t₀ ρ R hρ hR) hhtime
  have hηop := caccioppoli_cutoff_time_plus_laplacian_bound
    x₀ t₀ ρ R hρ hR z
  have hΓ := caccioppoli_heat_function_upper_on_annulus hr hρ hscale hp
  have hΓ0 := backwardHeatTestFunction_nonneg
    (x := z.1 - x₀) (t := z.2 - t₀) hr hhtime
  have hC : 0 ≤ cutoffGradientConstant := by
    by_contra hC'
    have hneg : cutoffGradientConstant / ρ < 0 :=
      div_neg_of_neg_of_pos (lt_of_not_ge hC') hρ
    have hbound := caccioppoli_spatial_cutoff_gradient_bound x₀ ρ hρ 0
    have hnorm : 0 ≤ vecEuclideanNorm (classicalGradient
        (mollifiedBallCutoff x₀ hρ) 0) := by
      unfold vecEuclideanNorm
      positivity
    exact (not_lt_of_ge hnorm) (hbound.trans_lt hneg)
  have hCρ : 0 ≤ cutoffGradientConstant / ρ := div_nonneg hC hρ.le
  have hcross : ∀ i : Fin 3,
      |spatialPartial (fun w : ParabolicPoint =>
          caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i z| *
        |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) i| ≤
      (cutoffGradientConstant / ρ) *
        (5000000 * r ^ 2 / ρ ^ 4) := by
    intro i
    exact mul_le_mul
      (caccioppoli_cutoff_spatial_partial_bound x₀ t₀ ρ R hρ hR z i)
      (caccioppoli_heat_spatial_derivative_abs_on_annulus hr hρ hscale i hp)
      (abs_nonneg _) hCρ
  have hsumabs :
      |∑ i, spatialPartial (fun w : ParabolicPoint =>
          caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i z *
          (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i)| ≤
        ∑ i, |spatialPartial (fun w : ParabolicPoint =>
          caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i z| *
        |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i| := by
    calc
      |∑ i, spatialPartial (fun w : ParabolicPoint =>
          caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i z *
          (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i)| ≤
          ∑ i, |spatialPartial (fun w : ParabolicPoint =>
            caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i z *
            (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
              (r ^ 2 - (z.2 - t₀)) i)| := by
        exact (Finset.abs_sum_le_sum_abs
          (fun i : Fin 3 => spatialPartial (fun w : ParabolicPoint =>
            caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i z *
            (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
              (r ^ 2 - (z.2 - t₀)) i)) Finset.univ)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg r)]
  have hht' : timePartial (fun w : ParabolicPoint =>
      backwardHeatCutoff (caccioppoliCutoff x₀ t₀ ρ R hρ hR)
        x₀ t₀ r w) z +
      ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
        backwardHeatCutoff (caccioppoliCutoff x₀ t₀ ρ R hρ hR)
          x₀ t₀ r w) i i z =
    (timePartial (fun w : ParabolicPoint =>
        caccioppoliCutoff x₀ t₀ ρ R hρ hR w) z +
        ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
          caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i i z) *
      backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
      2 * ∑ i, spatialPartial (fun w : ParabolicPoint =>
        caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i z *
        (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) i) := by
    simpa only [ParabolicPoint] using hht
  have hS : 0 ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := by
    exact (abs_nonneg (spatialSecondPartial
      (caccioppoliCutoff x₀ t₀ ρ R hρ hR) 0 0 z)).trans
      (caccioppoli_cutoff_second_spatial_partial_bound x₀ t₀ ρ R hρ hR z 0 0)
  have hA0 : 0 ≤ 32 / (R ^ 2 - (ρ / 2) ^ 2) +
      3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
    have hden : 0 < R ^ 2 - (ρ / 2) ^ 2 := by
      nlinarith only [hR, hρ]
    positivity
  calc
    |timePartial (fun w : ParabolicPoint =>
        backwardHeatCutoff (caccioppoliCutoff x₀ t₀ ρ R hρ hR)
          x₀ t₀ r w) z +
        ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
          backwardHeatCutoff (caccioppoliCutoff x₀ t₀ ρ R hρ hR)
            x₀ t₀ r w) i i z| =
      |(timePartial (fun w : ParabolicPoint =>
          caccioppoliCutoff x₀ t₀ ρ R hρ hR w) z +
          ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
            caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i i z) *
        backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
        2 * ∑ i, spatialPartial (fun w : ParabolicPoint =>
          caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i z *
          (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i)| := by rw [hht']
    _ ≤ |timePartial (fun w : ParabolicPoint =>
          caccioppoliCutoff x₀ t₀ ρ R hρ hR w) z +
          ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
            caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i i z| *
        backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
        2 * |∑ i, spatialPartial (fun w : ParabolicPoint =>
          caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i z *
          (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i)| := by
      calc
        |(timePartial (fun w : ParabolicPoint =>
            caccioppoliCutoff x₀ t₀ ρ R hρ hR w) z +
            ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
              caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i i z) *
          backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
          2 * ∑ i, spatialPartial (fun w : ParabolicPoint =>
            caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i z *
            (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
              (r ^ 2 - (z.2 - t₀)) i)| ≤
          |(timePartial (fun w : ParabolicPoint =>
              caccioppoliCutoff x₀ t₀ ρ R hρ hR w) z +
              ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
                caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i i z) *
            backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀)| +
          |2 * ∑ i, spatialPartial (fun w : ParabolicPoint =>
            caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i z *
            (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
              (r ^ 2 - (z.2 - t₀)) i)| := abs_add_le _ _
        _ = _ := by
          rw [abs_mul, abs_of_nonneg hΓ0, abs_mul,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ (32 / (R ^ 2 - (ρ / 2) ^ 2) +
        3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
          (8000000 * r ^ 2 / ρ ^ 3) +
        2 * ∑ i, |spatialPartial (fun w : ParabolicPoint =>
          caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i z| *
          |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i| := by
      exact add_le_add
        (mul_le_mul hηop hΓ hΓ0 hA0)
        (mul_le_mul_of_nonneg_left hsumabs (by norm_num))
    _ ≤ (32 / (R ^ 2 - (ρ / 2) ^ 2) +
        3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
          (8000000 * r ^ 2 / ρ ^ 3) +
        2 * ∑ _i : Fin 3,
          (cutoffGradientConstant / ρ) *
            (5000000 * r ^ 2 / ρ ^ 4) := by
      have hsumcross :
          (∑ i, |spatialPartial (fun w : ParabolicPoint =>
            caccioppoliCutoff x₀ t₀ ρ R hρ hR w) i z| *
            |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
              (r ^ 2 - (z.2 - t₀)) i|) ≤
          ∑ _i : Fin 3, (cutoffGradientConstant / ρ) *
            (5000000 * r ^ 2 / ρ ^ 4) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hcross i
      have htwo : (0 : ℝ) ≤ 2 := by norm_num
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsumcross htwo)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

theorem caccioppoli_I1_heat_cutoff_annulus_pointwise
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2) (_ : ε < r ^ 2)
    {z : ParabolicPoint} (ht : z.2 ≤ t₀)
    (hp : (z.1 - x₀, z.2 - t₀) ∈
      parabolicCylinder 0 0 ρ \ parabolicCylinder 0 0 (ρ / 2)) :
    |timePartial (fun w : ParabolicPoint =>
        backwardHeatCutoff
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) z +
        ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i i z| ≤
      (32 / ρ ^ 2 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
          (8000000 * r ^ 2 / ρ ^ 3) +
        6 * (cutoffGradientConstant / ρ) *
          (5000000 * r ^ 2 / ρ ^ 4) := by
  have hhtime : z.2 - t₀ < r ^ 2 := by
    have hsq : 0 < r ^ 2 := sq_pos_of_pos hr
    linarith only [ht, hsq]
  have hht := caccioppoli_I1_heat_operator
    (η := caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) (x₀ := x₀)
    (t₀ := t₀) (r := r) (z := z)
    (caccioppoli_heat_cutoff_smooth x₀ t₀ ρ ε hρ hε) hhtime
  have hηop := caccioppoli_heat_cutoff_time_plus_laplacian_bound_on_left
    x₀ t₀ ρ ε hρ hε ht
  have hΓ := caccioppoli_heat_function_upper_on_annulus hr hρ hscale hp
  have hΓ0 := backwardHeatTestFunction_nonneg
    (x := z.1 - x₀) (t := z.2 - t₀) hr hhtime
  have hC : 0 ≤ cutoffGradientConstant := by
    by_contra hC'
    have hneg : cutoffGradientConstant / ρ < 0 :=
      div_neg_of_neg_of_pos (lt_of_not_ge hC') hρ
    have hbound := caccioppoli_spatial_cutoff_gradient_bound x₀ ρ hρ 0
    have hnorm : 0 ≤ vecEuclideanNorm (classicalGradient
        (mollifiedBallCutoff x₀ hρ) 0) := by
      unfold vecEuclideanNorm
      positivity
    exact (not_lt_of_ge hnorm) (hbound.trans_lt hneg)
  have hCρ : 0 ≤ cutoffGradientConstant / ρ := div_nonneg hC hρ.le
  have hcross : ∀ i : Fin 3,
      |spatialPartial (fun w : ParabolicPoint =>
          caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i z| *
        |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) i| ≤
      (cutoffGradientConstant / ρ) *
        (5000000 * r ^ 2 / ρ ^ 4) := by
    intro i
    exact mul_le_mul
      (caccioppoli_heat_cutoff_spatial_partial_bound
        x₀ t₀ ρ ε hρ hε z i)
      (caccioppoli_heat_spatial_derivative_abs_on_annulus hr hρ hscale i hp)
      (abs_nonneg _) hCρ
  have hsumabs :
      |∑ i, spatialPartial (fun w : ParabolicPoint =>
          caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i z *
          (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i)| ≤
        ∑ i, |spatialPartial (fun w : ParabolicPoint =>
          caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i z| *
        |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i| := by
    calc
      _ ≤ ∑ i, |spatialPartial (fun w : ParabolicPoint =>
            caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i z *
            (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
              (r ^ 2 - (z.2 - t₀)) i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg r)]
  have hht' : timePartial (fun w : ParabolicPoint =>
      backwardHeatCutoff
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) z +
      ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
        backwardHeatCutoff
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i i z =
    (timePartial (fun w : ParabolicPoint =>
        caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) z +
        ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
          caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i i z) *
      backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
      2 * ∑ i, spatialPartial (fun w : ParabolicPoint =>
        caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i z *
        (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) i) := by
    simpa only [ParabolicPoint] using hht
  have hS : 0 ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := by
    exact (abs_nonneg (spatialSecondPartial
      (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) 0 0 z)).trans
      (caccioppoli_heat_cutoff_second_spatial_partial_bound
        x₀ t₀ ρ ε hρ hε z 0 0)
  have hA0 : 0 ≤ 32 / ρ ^ 2 +
      3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
    positivity
  calc
    _ = |(timePartial (fun w : ParabolicPoint =>
          caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) z +
          ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
            caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i i z) *
        backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
        2 * ∑ i, spatialPartial (fun w : ParabolicPoint =>
          caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i z *
          (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i)| := by rw [hht']
    _ ≤ |timePartial (fun w : ParabolicPoint =>
          caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) z +
          ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
            caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i i z| *
        backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
        2 * |∑ i, spatialPartial (fun w : ParabolicPoint =>
          caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i z *
          (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i)| := by
      calc
        _ ≤ |(timePartial (fun w : ParabolicPoint =>
              caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) z +
              ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
                caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i i z) *
            backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀)| +
          |2 * ∑ i, spatialPartial (fun w : ParabolicPoint =>
            caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i z *
            (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
              (r ^ 2 - (z.2 - t₀)) i)| := abs_add_le _ _
        _ = _ := by
          rw [abs_mul, abs_of_nonneg hΓ0, abs_mul,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ (32 / ρ ^ 2 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
          (8000000 * r ^ 2 / ρ ^ 3) +
        2 * ∑ i, |spatialPartial (fun w : ParabolicPoint =>
          caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i z| *
          |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i| := by
      exact add_le_add
        (mul_le_mul hηop hΓ hΓ0 hA0)
        (mul_le_mul_of_nonneg_left hsumabs (by norm_num))
    _ ≤ (32 / ρ ^ 2 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
          (8000000 * r ^ 2 / ρ ^ 3) +
        2 * ∑ _i : Fin 3,
          (cutoffGradientConstant / ρ) *
            (5000000 * r ^ 2 / ρ ^ 4) := by
      have hsumcross :
          (∑ i, |spatialPartial (fun w : ParabolicPoint =>
            caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε w) i z| *
            |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
              (r ^ 2 - (z.2 - t₀)) i|) ≤
          ∑ _i : Fin 3, (cutoffGradientConstant / ρ) *
            (5000000 * r ^ 2 / ρ ^ 4) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hcross i
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsumcross
        (by norm_num))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

theorem caccioppoli_I1_heat_cutoff_inner_zero
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2)
    {z : ParabolicPoint} (hx : z.1 ∈ vec3Ball x₀ (ρ / 2))
    (ht : z.2 ∈ Ioc (t₀ - r ^ 2) t₀) :
    timePartial (fun w : ParabolicPoint =>
        backwardHeatCutoff
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) z +
        ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i i z = 0 := by
  have hhtime : z.2 - t₀ < r ^ 2 := by
    linarith only [ht.2, sq_pos_of_pos hr]
  have hht := caccioppoli_I1_heat_operator
    (η := caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) (x₀ := x₀)
    (t₀ := t₀) (r := r) (z := z)
    (caccioppoli_heat_cutoff_smooth x₀ t₀ ρ ε hρ hε) hhtime
  obtain ⟨hT, hS, hSS⟩ := caccioppoli_heat_cutoff_derivatives_zero_on_inner
    x₀ t₀ ρ ε r hρ hε hr hscale hx ht
  rw [hht, hT]
  simp_rw [hS]
  simp_rw [hSS]
  simp only [zero_add, zero_mul, Finset.sum_const_zero, mul_zero]

theorem caccioppoli_I1_heat_cutoff_pointwise_on_cylinder
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2) (hεr : ε < r ^ 2)
    {z : ParabolicPoint} (ht : z.2 ≤ t₀)
    (hz : (z.1 - x₀, z.2 - t₀) ∈ parabolicCylinder 0 0 ρ) :
    |timePartial (fun w : ParabolicPoint =>
        backwardHeatCutoff
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) z +
        ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i i z| ≤
      (32 / ρ ^ 2 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
          (8000000 * r ^ 2 / ρ ^ 3) +
        6 * (cutoffGradientConstant / ρ) *
          (5000000 * r ^ 2 / ρ ^ 4) := by
  by_cases hhalf : (z.1 - x₀, z.2 - t₀) ∈
      parabolicCylinder 0 0 (ρ / 2)
  · have hx : z.1 ∈ vec3Ball x₀ (ρ / 2) := by
      have hspace := (mem_parabolicCylinder.mp hhalf).1
      rw [mem_vec3Ball]
      simpa [sub_sub, vec3EuclideanNorm] using hspace
    have ht' : z.2 ∈ Ioc (t₀ - (ρ / 2) ^ 2) t₀ := by
      have htime := (mem_parabolicCylinder.mp hhalf).2
      constructor
      · linarith only [htime.1]
      · exact ht
    have hhtime : z.2 - t₀ < r ^ 2 := by
      linarith only [ht, sq_pos_of_pos hr]
    have hht := caccioppoli_I1_heat_operator
      (η := caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) (x₀ := x₀)
      (t₀ := t₀) (r := r) (z := z)
      (caccioppoli_heat_cutoff_smooth x₀ t₀ ρ ε hρ hε) hhtime
    obtain ⟨hT, hS, hSS⟩ :=
      caccioppoli_heat_cutoff_derivatives_zero_on_inner
        x₀ t₀ ρ ε (ρ / 2) hρ hε (by linarith only [hρ])
          (le_refl _) hx ht'
    have hC : 0 ≤ cutoffGradientConstant := by
      by_contra hC'
      have hneg : cutoffGradientConstant / ρ < 0 :=
        div_neg_of_neg_of_pos (lt_of_not_ge hC') hρ
      have hbound := caccioppoli_spatial_cutoff_gradient_bound x₀ ρ hρ 0
      have hnorm : 0 ≤ vecEuclideanNorm (classicalGradient
          (mollifiedBallCutoff x₀ hρ) 0) := by
        unfold vecEuclideanNorm
        positivity
      exact (not_lt_of_ge hnorm) (hbound.trans_lt hneg)
    have hSbound : 0 ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := by
      exact (abs_nonneg (spatialSecondPartial
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) 0 0 z)).trans
        (caccioppoli_heat_cutoff_second_spatial_partial_bound
          x₀ t₀ ρ ε hρ hε z 0 0)
    have hCρ : 0 ≤ cutoffGradientConstant / ρ := div_nonneg hC hρ.le
    have hA : 0 ≤ 32 / ρ ^ 2 +
        3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
      positivity
    have hB : 0 ≤ 5000000 * r ^ 2 / ρ ^ 4 := by
      positivity
    rw [hht, hT]
    simp_rw [hS]
    simp_rw [hSS]
    simp only [zero_add, zero_mul, Finset.sum_const_zero, mul_zero, abs_zero]
    have hsix : 0 ≤ (6 : ℝ) * (cutoffGradientConstant / ρ) :=
      mul_nonneg (by norm_num) hCρ
    exact add_nonneg (mul_nonneg hA (by positivity)) (mul_nonneg hsix hB)
  · have hzann : (z.1 - x₀, z.2 - t₀) ∈
        parabolicCylinder 0 0 ρ \ parabolicCylinder 0 0 (ρ / 2) := by
      exact ⟨hz, hhalf⟩
    exact caccioppoli_I1_heat_cutoff_annulus_pointwise hρ hε hr hscale hεr
      ht hzann

end CKN
