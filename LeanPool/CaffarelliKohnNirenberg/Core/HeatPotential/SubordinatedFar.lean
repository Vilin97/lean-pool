/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.SubordinatedNear

/-!
# Subordinated Far

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Core.HeatPotential
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
lemma heatPotential_kernel_integrable_on_split
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    {z p : ParabolicPoint} {r P θ₀ θ₁ : ℝ}
    (hr : 0 < r) (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : AEMeasurable F volume) (hG : ∀ i : Fin 3, AEMeasurable (G i) volume)
    (hNF : morreyNorm P θ₀ F < ∞)
    (hNG : ∀ i : Fin 3, morreyNorm P θ₁ (G i) < ∞)
    (hSupportF : HasCompactSupport F)
    (hSupportG : ∀ i : Fin 3, HasCompactSupport (G i))
    (hδ₀ : 0 < 2 - 5 / θ₀) (hδ₁ : 0 < 1 - 5 / θ₁)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    IntegrableOn (fun v => heatPotentialKernel p v * F v)
        (heatPotentialNearSet z r ∪ ⋃ j : ℕ, heatPotentialFarShellSet z r j) volume ∧
    (∀ i : Fin 3, IntegrableOn
      (fun v => heatPotentialSpatialKernel i p v * G i v)
        (heatPotentialNearSet z r ∪ ⋃ j : ℕ, heatPotentialFarShellSet z r j) volume) := by
  let U : Set ParabolicPoint := ⋃ j : ℕ, heatPotentialFarShellSet z r j
  have hU : MeasurableSet U := MeasurableSet.iUnion
    (fun j => measurableSet_heatPotentialFarShellSet z r j)
  have hnearF := heatPotential_near_kernel_integrable hr hP hPθ₀ hF hNF hδ₀ hp
  have hglobalF := heatPotential_source_integrable_of_compact_support
    hP hPθ₀ hF hNF hSupportF
  have hglobalF' : IntegrableOn F U volume := by
    exact hglobalF.mono_measure Measure.restrict_le_self
  have hfiniteF : (∫⁻ v in U, ENNReal.ofReal |F v|) < ∞ := by
    simpa [IntegrableOn, Real.norm_eq_abs] using
      (hglobalF'.integrable.norm.lintegral_lt_top)
  have hfarF : IntegrableOn (fun v => heatPotentialKernel p v * F v) U volume := by
    exact integrableOn_mul_of_abs_integrable_of_bound hU hF
      (measurable_heatPotentialKernel_translate p).aemeasurable hfiniteF
      (by positivity) (heatPotential_far_uniform_kernel_bound hr hp)
  have hfullF : IntegrableOn (fun v => heatPotentialKernel p v * F v)
      (heatPotentialNearSet z r ∪ U) volume := hnearF.union hfarF
  refine ⟨?_, ?_⟩
  · simpa [U] using hfullF
  · intro i
    have hnearG := heatPotential_near_spatial_kernel_integrable hr hP hPθ₁
      (hG i) (hNG i) hδ₁ hp i
    have hglobalG := heatPotential_source_integrable_of_compact_support
      hP hPθ₁ (hG i) (hNG i) (hSupportG i)
    have hglobalG' : IntegrableOn (G i) U volume := by
      exact hglobalG.mono_measure Measure.restrict_le_self
    have hfiniteG : (∫⁻ v in U, ENNReal.ofReal |G i v|) < ∞ := by
      simpa [IntegrableOn, Real.norm_eq_abs] using
        (hglobalG'.integrable.norm.lintegral_lt_top)
    have hfarG : IntegrableOn
        (fun v => heatPotentialSpatialKernel i p v * G i v) U volume := by
      exact integrableOn_mul_of_abs_integrable_of_bound hU (hG i)
        (measurable_heatPotentialSpatialKernel_translate i p).aemeasurable hfiniteG
        (by positivity) (heatPotential_far_uniform_spatial_kernel_bound hr hp i)
    have hfullG : IntegrableOn
        (fun v => heatPotentialSpatialKernel i p v * G i v)
        (heatPotentialNearSet z r ∪ U) volume := hnearG.union hfarG
    simpa [U] using hfullG

lemma heatPotential_near_oscillation_bound_of_morrey
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    {z p p' : ParabolicPoint} {r γ θ₀ θ₁ P : ℝ}
    (hr : 0 < r) (hγ : 0 < γ)
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5)
    (hθ₁ : 1 / θ₁ = (1 - γ) / 5)
    (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : AEMeasurable F volume) (hG : ∀ i : Fin 3, AEMeasurable (G i) volume)
    (hNF : morreyNorm P θ₀ F < ∞)
    (hNG : ∀ i : Fin 3, morreyNorm P θ₁ (G i) < ∞)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    |((∫ v in heatPotentialNearSet z r,
        heatPotentialKernel p v * F v) +
        ∑ i, ∫ v in heatPotentialNearSet z r,
          heatPotentialSpatialKernel i p v * G i v) -
      ((∫ v in heatPotentialNearSet z r,
        heatPotentialKernel p' v * F v) +
        ∑ i, ∫ v in heatPotentialNearSet z r,
          heatPotentialSpatialKernel i p' v * G i v)| ≤
      (2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
          (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ *
          (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
          (morreyNorm P θ₀ F).toReal +
        ∑ i, 2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
          (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ *
          (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
          (morreyNorm P θ₁ (G i)).toReal) * r ^ γ := by
  have hδ₀ : 0 < 2 - 5 / θ₀ := by
    rw [heat_morrey_theta_zero_identity hθ₀]
    exact hγ
  have hδ₁ : 0 < 1 - 5 / θ₁ := by
    rw [heat_morrey_theta_one_identity hθ₁]
    exact hγ
  have hden : 0 < 1 - (2 : ℝ) ^ (-γ) := by
    have hq : (2 : ℝ) ^ (-γ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hγ])
    linarith only [hq]
  have hFnear : ∀ q ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r,
      (∫ v in heatPotentialNearSet z r,
        |heatPotentialKernel q v * F v|) ≤
      1000 * ((2 : ℝ) ^ (8 - 5 / θ₀) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ *
        (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
        (morreyNorm P θ₀ F).toReal) * r ^ γ := by
    intro q hq
    have h := heatPotential_near_kernel_abs_integral_bound hr hP hPθ₀ hF hNF hδ₀ hq
    simpa [heat_morrey_theta_zero_identity hθ₀] using h
  have hGnear : ∀ (i : Fin 3) (q : ParabolicPoint),
      q ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r →
      (∫ v in heatPotentialNearSet z r,
        |heatPotentialSpatialKernel i q v * G i v|) ≤
      300000 * ((2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
        (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ *
        (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
        (morreyNorm P θ₁ (G i)).toReal) * r ^ γ := by
    intro i q hq
    have h := heatPotential_near_spatial_kernel_abs_integral_bound
      (i := i) hr hP hPθ₁ (hG i) (hNG i) hδ₁ hq
    simpa [heat_morrey_theta_one_identity hθ₁] using h
  let CF : ℝ := 2 * 1000 * ((2 : ℝ) ^ (8 - 5 / θ₀) *
    (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ *
    (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
    (morreyNorm P θ₀ F).toReal)
  let CG : Fin 3 → ℝ := fun i => 2 * 300000 * ((2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
    (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ *
    (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
    (morreyNorm P θ₁ (G i)).toReal)
  have hFdiff : |(∫ v in heatPotentialNearSet z r,
        heatPotentialKernel p v * F v) -
      ∫ v in heatPotentialNearSet z r,
        heatPotentialKernel p' v * F v| ≤ CF * r ^ γ := by
    calc
      _ ≤ (∫ v in heatPotentialNearSet z r,
          |heatPotentialKernel p v * F v|) +
          ∫ v in heatPotentialNearSet z r,
            |heatPotentialKernel p' v * F v| := by
        have hInt := heatPotential_near_kernel_integrable hr hP hPθ₀
          hF hNF hδ₀ hp
        have hInt' := heatPotential_near_kernel_integrable hr hP hPθ₀
          hF hNF hδ₀ hp'
        have hdiff : IntegrableOn (fun v => heatPotentialKernel p v * F v -
            heatPotentialKernel p' v * F v) (heatPotentialNearSet z r) volume :=
          hInt.sub hInt'
        have hmajor : IntegrableOn (fun v =>
            |heatPotentialKernel p v * F v| +
              |heatPotentialKernel p' v * F v|)
            (heatPotentialNearSet z r) volume := hInt.norm.add hInt'.norm
        have hpoint : ∀ᵐ v ∂(volume.restrict (heatPotentialNearSet z r)),
            |heatPotentialKernel p v * F v - heatPotentialKernel p' v * F v| ≤
              |heatPotentialKernel p v * F v| +
                |heatPotentialKernel p' v * F v| := by
          filter_upwards [] with v
          simpa using (abs_sub_le (heatPotentialKernel p v * F v)
            0 (heatPotentialKernel p' v * F v))
        rw [← integral_sub hInt hInt']
        calc
          |∫ v in heatPotentialNearSet z r,
              (heatPotentialKernel p v * F v - heatPotentialKernel p' v * F v)| ≤
              ∫ v in heatPotentialNearSet z r,
                |heatPotentialKernel p v * F v - heatPotentialKernel p' v * F v| := by
            simpa only [Real.norm_eq_abs] using
              (MeasureTheory.norm_integral_le_integral_norm
                (μ := volume.restrict (heatPotentialNearSet z r))
                (fun v => heatPotentialKernel p v * F v -
                  heatPotentialKernel p' v * F v)).trans_eq rfl
          _ ≤ ∫ v in heatPotentialNearSet z r,
              (|heatPotentialKernel p v * F v| +
                |heatPotentialKernel p' v * F v|) :=
            MeasureTheory.integral_mono_ae hdiff.norm hmajor hpoint
          _ = (∫ v in heatPotentialNearSet z r,
              |heatPotentialKernel p v * F v|) +
              ∫ v in heatPotentialNearSet z r,
                |heatPotentialKernel p' v * F v| :=
            MeasureTheory.integral_add hInt.norm hInt'.norm
      _ ≤ CF * r ^ γ := by
        dsimp [CF]
        calc
          _ ≤ (1000 * ((2 : ℝ) ^ (8 - 5 / θ₀) *
              (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ *
              (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
              (morreyNorm P θ₀ F).toReal) * r ^ γ) +
              (1000 * ((2 : ℝ) ^ (8 - 5 / θ₀) *
              (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ *
              (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
              (morreyNorm P θ₀ F).toReal) * r ^ γ) :=
            add_le_add (hFnear p hp) (hFnear p' hp')
          _ = CF * r ^ γ := by ring
  have hGdiff : ∀ i : Fin 3,
      |(∫ v in heatPotentialNearSet z r,
          heatPotentialSpatialKernel i p v * G i v) -
        ∫ v in heatPotentialNearSet z r,
          heatPotentialSpatialKernel i p' v * G i v| ≤ CG i * r ^ γ := by
    intro i
    calc
      _ ≤ (∫ v in heatPotentialNearSet z r,
          |heatPotentialSpatialKernel i p v * G i v|) +
          ∫ v in heatPotentialNearSet z r,
            |heatPotentialSpatialKernel i p' v * G i v| := by
        have hInt := heatPotential_near_spatial_kernel_integrable hr hP hPθ₁
          (hG i) (hNG i) hδ₁ hp i
        have hInt' := heatPotential_near_spatial_kernel_integrable hr hP hPθ₁
          (hG i) (hNG i) hδ₁ hp' i
        have hdiff : IntegrableOn (fun v => heatPotentialSpatialKernel i p v * G i v -
            heatPotentialSpatialKernel i p' v * G i v)
            (heatPotentialNearSet z r) volume := hInt.sub hInt'
        have hmajor : IntegrableOn (fun v =>
            |heatPotentialSpatialKernel i p v * G i v| +
              |heatPotentialSpatialKernel i p' v * G i v|)
            (heatPotentialNearSet z r) volume := hInt.norm.add hInt'.norm
        have hpoint : ∀ᵐ v ∂(volume.restrict (heatPotentialNearSet z r)),
            |heatPotentialSpatialKernel i p v * G i v -
                heatPotentialSpatialKernel i p' v * G i v| ≤
              |heatPotentialSpatialKernel i p v * G i v| +
                |heatPotentialSpatialKernel i p' v * G i v| := by
          filter_upwards [] with v
          simpa using (abs_sub_le (heatPotentialSpatialKernel i p v * G i v)
            0 (heatPotentialSpatialKernel i p' v * G i v))
        rw [← integral_sub hInt hInt']
        calc
          |∫ v in heatPotentialNearSet z r,
              (heatPotentialSpatialKernel i p v * G i v -
                heatPotentialSpatialKernel i p' v * G i v)| ≤
              ∫ v in heatPotentialNearSet z r,
                |heatPotentialSpatialKernel i p v * G i v -
                  heatPotentialSpatialKernel i p' v * G i v| := by
            simpa only [Real.norm_eq_abs] using
              (MeasureTheory.norm_integral_le_integral_norm
                (μ := volume.restrict (heatPotentialNearSet z r))
                (fun v => heatPotentialSpatialKernel i p v * G i v -
                  heatPotentialSpatialKernel i p' v * G i v)).trans_eq rfl
          _ ≤ ∫ v in heatPotentialNearSet z r,
              (|heatPotentialSpatialKernel i p v * G i v| +
                |heatPotentialSpatialKernel i p' v * G i v|) :=
            MeasureTheory.integral_mono_ae hdiff.norm hmajor hpoint
          _ = (∫ v in heatPotentialNearSet z r,
              |heatPotentialSpatialKernel i p v * G i v|) +
              ∫ v in heatPotentialNearSet z r,
                |heatPotentialSpatialKernel i p' v * G i v| :=
            MeasureTheory.integral_add hInt.norm hInt'.norm
      _ ≤ CG i * r ^ γ := by
        dsimp [CG]
        calc
          _ ≤ (300000 * ((2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
              (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ *
              (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
              (morreyNorm P θ₁ (G i)).toReal) * r ^ γ) +
              (300000 * ((2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
              (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ *
              (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
              (morreyNorm P θ₁ (G i)).toReal) * r ^ γ) :=
            add_le_add (hGnear i p hp) (hGnear i p' hp')
          _ = CG i * r ^ γ := by ring
  calc
    _ ≤ |(∫ v in heatPotentialNearSet z r,
          heatPotentialKernel p v * F v) -
        ∫ v in heatPotentialNearSet z r,
          heatPotentialKernel p' v * F v| +
        |(∑ i, ∫ v in heatPotentialNearSet z r,
            heatPotentialSpatialKernel i p v * G i v) -
          ∑ i, ∫ v in heatPotentialNearSet z r,
            heatPotentialSpatialKernel i p' v * G i v| := by
      rw [show ((∫ v in heatPotentialNearSet z r,
          heatPotentialKernel p v * F v) +
          ∑ i, ∫ v in heatPotentialNearSet z r,
            heatPotentialSpatialKernel i p v * G i v) -
        ((∫ v in heatPotentialNearSet z r,
          heatPotentialKernel p' v * F v) +
          ∑ i, ∫ v in heatPotentialNearSet z r,
            heatPotentialSpatialKernel i p' v * G i v) =
        ((∫ v in heatPotentialNearSet z r,
          heatPotentialKernel p v * F v) -
          ∫ v in heatPotentialNearSet z r,
            heatPotentialKernel p' v * F v) +
          ((∑ i, ∫ v in heatPotentialNearSet z r,
            heatPotentialSpatialKernel i p v * G i v) -
          ∑ i, ∫ v in heatPotentialNearSet z r,
            heatPotentialSpatialKernel i p' v * G i v) by ring]
      exact abs_add_le _ _
    _ ≤ CF * r ^ γ + ∑ i, CG i * r ^ γ := by
      exact add_le_add hFdiff (by
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ i, ((∫ v in heatPotentialNearSet z r,
              heatPotentialSpatialKernel i p v * G i v) -
            ∫ v in heatPotentialNearSet z r,
              heatPotentialSpatialKernel i p' v * G i v)| ≤
              ∑ i, |(∫ v in heatPotentialNearSet z r,
                heatPotentialSpatialKernel i p v * G i v) -
              ∫ v in heatPotentialNearSet z r,
                heatPotentialSpatialKernel i p' v * G i v| := by
            simpa using (Finset.abs_sum_le_sum_abs
              (fun i => (∫ v in heatPotentialNearSet z r,
                heatPotentialSpatialKernel i p v * G i v) -
              ∫ v in heatPotentialNearSet z r,
                heatPotentialSpatialKernel i p' v * G i v) Finset.univ)
          _ ≤ ∑ i, CG i * r ^ γ := Finset.sum_le_sum (fun i _ => hGdiff i))
    _ = (CF + ∑ i, CG i) * r ^ γ := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ (2 * 1000 * (2 : ℝ) ^ (8 - 5 / θ₀) *
          (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ *
          (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
          (morreyNorm P θ₀ F).toReal +
        ∑ i, 2 * 300000 * (2 : ℝ) ^ (10 - 1 - 5 / θ₁) *
          (1 - (2 : ℝ) ^ (-γ))⁻¹ * (256 : ℝ) ^ γ *
          (volume (parabolicCylinder 0 0 1)).toReal ^ (1 - 1 / P) *
          (morreyNorm P θ₁ (G i)).toReal) * r ^ γ := by
      dsimp [CF, CG]
      apply le_of_eq
      congr 1
      ring_nf

lemma heatPotential_far_shell_oscillation_bound_of_morrey
    {F : ParabolicPoint → ℝ} {G : Fin 3 → ParabolicPoint → ℝ}
    {z p p' : ParabolicPoint} {r P θ₀ θ₁ : ℝ} {j : ℕ}
    (hr : 0 < r) (hP : 1 ≤ P) (hPθ₀ : P ≤ θ₀) (hPθ₁ : P ≤ θ₁)
    (hF : AEMeasurable F volume) (hG : ∀ i : Fin 3, AEMeasurable (G i) volume)
    (hNF : morreyNorm P θ₀ F < ∞)
    (hNG : ∀ i : Fin 3, morreyNorm P θ₁ (G i) < ∞)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :
    |heatPotentialShellValue F G (heatPotentialFarShellSet z r j) p -
        heatPotentialShellValue F G (heatPotentialFarShellSet z r j) p'| ≤
      (2 * r * ((900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) +
        2 * r * (10000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5))) *
        ((ENNReal.ofReal
          (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r))) ^
          (5 * (1 - 1 / θ₀)) *
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
          morreyNorm P θ₀ F).toReal +
      ∑ i, (2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
        2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6))) *
        ((ENNReal.ofReal
          (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r))) ^
          (5 * (1 - 1 / θ₁)) *
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
          morreyNorm P θ₁ (G i)).toReal := by
  have hFbound := heatPotential_far_shell_integral_oscillation_bound_of_morrey
    (z := z) (p := p) (p' := p') (r := r) (P := P) (θ := θ₀) (j := j)
    hr hP hPθ₀ hF hNF hp hp'
  have hGbound : ∀ i : Fin 3,
      |(∫ v in heatPotentialFarShellSet z r j,
          heatPotentialSpatialKernel i p v * G i v) -
        ∫ v in heatPotentialFarShellSet z r j,
          heatPotentialSpatialKernel i p' v * G i v| ≤
      (2 * r * ((60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) +
        2 * r * (30000000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 6))) *
        ((ENNReal.ofReal
          (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r))) ^
          (5 * (1 - 1 / θ₁)) *
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
          morreyNorm P θ₁ (G i)).toReal := by
    intro i
    exact heatPotential_far_shell_spatial_integral_oscillation_bound_of_morrey
      (z := z) (p := p) (p' := p') (r := r) (P := P) (θ := θ₁) (j := j)
      hr hP hPθ₁ (hG i) (hNG i) hp hp'
  unfold heatPotentialShellValue
  calc
    _ ≤ |(∫ v in heatPotentialFarShellSet z r j,
          heatPotentialKernel p v * F v) -
        ∫ v in heatPotentialFarShellSet z r j,
          heatPotentialKernel p' v * F v| +
        |(∑ i, ∫ v in heatPotentialFarShellSet z r j,
            heatPotentialSpatialKernel i p v * G i v) -
          ∑ i, ∫ v in heatPotentialFarShellSet z r j,
            heatPotentialSpatialKernel i p' v * G i v| := by
      rw [show ((∫ v in heatPotentialFarShellSet z r j,
          heatPotentialKernel p v * F v) +
          ∑ i, ∫ v in heatPotentialFarShellSet z r j,
            heatPotentialSpatialKernel i p v * G i v) -
        ((∫ v in heatPotentialFarShellSet z r j,
          heatPotentialKernel p' v * F v) +
          ∑ i, ∫ v in heatPotentialFarShellSet z r j,
            heatPotentialSpatialKernel i p' v * G i v) =
        ((∫ v in heatPotentialFarShellSet z r j,
          heatPotentialKernel p v * F v) -
          ∫ v in heatPotentialFarShellSet z r j,
            heatPotentialKernel p' v * F v) +
          ((∑ i, ∫ v in heatPotentialFarShellSet z r j,
            heatPotentialSpatialKernel i p v * G i v) -
          ∑ i, ∫ v in heatPotentialFarShellSet z r j,
            heatPotentialSpatialKernel i p' v * G i v) by ring]
      exact abs_add_le _ _
    _ ≤ _ := by
      apply add_le_add hFbound
      rw [← Finset.sum_sub_distrib]
      calc
        |∑ i, ((∫ v in heatPotentialFarShellSet z r j,
            heatPotentialSpatialKernel i p v * G i v) -
          ∫ v in heatPotentialFarShellSet z r j,
            heatPotentialSpatialKernel i p' v * G i v)| ≤
            ∑ i, |(∫ v in heatPotentialFarShellSet z r j,
              heatPotentialSpatialKernel i p v * G i v) -
            ∫ v in heatPotentialFarShellSet z r j,
              heatPotentialSpatialKernel i p' v * G i v| := by
          simpa using (Finset.abs_sum_le_sum_abs
            (fun i => (∫ v in heatPotentialFarShellSet z r j,
              heatPotentialSpatialKernel i p v * G i v) -
            ∫ v in heatPotentialFarShellSet z r j,
              heatPotentialSpatialKernel i p' v * G i v) Finset.univ)
        _ ≤ ∑ i, _ := Finset.sum_le_sum (fun i _ => hGbound i)


end CKN.Core.HeatPotential
