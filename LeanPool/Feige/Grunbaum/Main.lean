/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import LeanPool.Feige.Grunbaum.ProbabilityCore
import LeanPool.Feige.Grunbaum.TruncationConcavity
import LeanPool.Feige.Grunbaum.FinalBridge
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Grünbaum's centroid halfspace theorem

This file closes the geometric, measure-theoretic, and Jensen layers of the
proof.  The public theorem `grunbaum_centroid_halfspace` has only the
assumptions in the mathematical statement.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace Grunbaum

lemma truncDomain_eq_Ici_of_isMinOn {d : ℕ} {C : Set (Euc d)}
    {ℓ : Euc d →L[ℝ] ℝ} {x₀ : Euc d}
    (hx₀ : x₀ ∈ C) (hmin : IsMinOn ℓ C x₀) :
    truncDomain C ℓ = Ici (ℓ x₀) := by
  ext t
  constructor
  · intro ht
    change (trunc C ℓ t).Nonempty at ht
    obtain ⟨x, hxC, hxℓ⟩ := ht
    change ℓ x ≤ t at hxℓ
    exact (hmin hxC).trans hxℓ
  · intro ht
    change (trunc C ℓ t).Nonempty
    exact ⟨x₀, hx₀, ht⟩

lemma cdf_map_uniformVolume_eq_truncVolumeRatio {d : ℕ}
    (C : Set (Euc d)) (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ)
    [IsProbabilityMeasure ((uniformVolume C).map ℓ)] :
    cdf ((uniformVolume C).map ℓ) t =
      (volume (trunc C ℓ t) / volume C).toReal := by
  rw [cdf_eq_real, measureReal_def,
    Measure.map_apply ℓ.measurable measurableSet_Iic]
  have hm : MeasurableSet (ℓ ⁻¹' Iic t) :=
    measurableSet_Iic.preimage ℓ.measurable
  simp only [uniformVolume, Measure.smul_apply,
    Measure.restrict_apply hm, smul_eq_mul, trunc, div_eq_mul_inv]
  rw [inter_comm, mul_comm]

lemma cdfRoot_eq_cdf_rpow_map_uniformVolume {d : ℕ}
    (C : Set (Euc d)) (ℓ : Euc d →L[ℝ] ℝ) (t : ℝ)
    [IsProbabilityMeasure ((uniformVolume C).map ℓ)] :
    cdfRoot C ℓ t =
      cdf ((uniformVolume C).map ℓ) t ^
        ((((d + 1 : ℕ) : ℝ))⁻¹) := by
  rw [cdf_map_uniformVolume_eq_truncVolumeRatio]
  unfold cdfRoot
  rw [ENNReal.toReal_rpow]
  simp only [Nat.cast_add, Nat.cast_one]

lemma ae_map_uniformVolume_mem_Ici_of_isMinOn {d : ℕ}
    (C : FullDimensionalConvexBody d) (ℓ : Euc d →L[ℝ] ℝ)
    {x₀ : Euc d} (hmin : IsMinOn ℓ (C : Set (Euc d)) x₀) :
    ∀ᵐ t ∂(uniformVolume (C : Set (Euc d))).map ℓ, t ∈ Ici (ℓ x₀) := by
  change ∀ᵐ t ∂(uniformVolume (C : Set (Euc d))).map ℓ, ℓ x₀ ≤ t
  rw [ae_map_iff ℓ.measurable.aemeasurable measurableSet_Ici]
  unfold uniformVolume
  apply Measure.ae_smul_measure
  rw [ae_iff]
  have hm : MeasurableSet {x : Euc d | ¬ℓ x₀ ≤ ℓ x} := by
    simpa only [not_le] using
      (measurableSet_lt ℓ.measurable measurable_const)
  rw [Measure.restrict_apply hm]
  have hempty :
      {x : Euc d | ¬ℓ x₀ ≤ ℓ x} ∩ (C : Set (Euc d)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (hmin hx.2)
  rw [hempty, measure_empty]

lemma integrable_id_map_uniformVolume {d : ℕ}
    (C : FullDimensionalConvexBody d) (ℓ : Euc d →L[ℝ] ℝ) :
    Integrable (fun t : ℝ ↦ t)
      ((uniformVolume (C : Set (Euc d))).map ℓ) := by
  have hid_restrict :
      Integrable (fun x : Euc d ↦ x)
        (volume.restrict (C : Set (Euc d))) :=
    continuous_id.continuousOn.integrableOn_compact C.isCompact
  have hid_uniform :
      Integrable (fun x : Euc d ↦ x)
        (uniformVolume (C : Set (Euc d))) := by
    simpa [uniformVolume, Measure.restrict_apply_univ] using
      hid_restrict.to_average
  apply (integrable_map_measure continuous_id.aestronglyMeasurable
    ℓ.measurable.aemeasurable).2
  simpa [Function.comp_def] using ℓ.integrable_comp hid_uniform

theorem cdfRoot_centroid_lower_bound {d : ℕ}
    (C : FullDimensionalConvexBody d)
    (ℓ : Euc d →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    (((d + 1 : ℕ) : ℝ) / (d + 2 : ℕ)) ≤
      cdfRoot (C : Set (Euc d)) ℓ (ℓ C.centroid) := by
  let μ : Measure (Euc d) := uniformVolume (C : Set (Euc d))
  let ν : Measure ℝ := μ.map ℓ
  let : IsProbabilityMeasure μ := by
    simpa [μ] using
      isProbabilityMeasure_uniformVolume (C : Set (Euc d))
        C.volume_ne_zero C.volume_ne_top
  let : IsProbabilityMeasure ν := by
    exact Measure.isProbabilityMeasure_map ℓ.measurable.aemeasurable
  let : NullSingletonClass ν := by
    change NullSingletonClass ((uniformVolume (C : Set (Euc d))).map ℓ)
    exact nullSingletonClass_map_uniform (C : Set (Euc d)) ℓ hℓ
  obtain ⟨x₀, hx₀, hmin⟩ :=
    C.isCompact.exists_isMinOn C.nonempty ℓ.continuous.continuousOn
  have hdomain :
      truncDomain (C : Set (Euc d)) ℓ = Ici (ℓ x₀) :=
    truncDomain_eq_Ici_of_isMinOn hx₀ hmin
  have hconcBody :
      ConcaveOn ℝ (Ici (ℓ x₀))
        (cdfRoot (C : Set (Euc d)) ℓ) := by
    rw [← hdomain]
    exact concaveOn_cdfRoot C.convex C.isCompact ℓ
  have hroot (t : ℝ) :
      cdf ν t ^ ((((d + 1 : ℕ) : ℝ))⁻¹) =
        cdfRoot (C : Set (Euc d)) ℓ t := by
    simpa [ν, μ] using
      (cdfRoot_eq_cdf_rpow_map_uniformVolume
        (C : Set (Euc d)) ℓ t).symm
  have hconc :
      ConcaveOn ℝ (Ici (ℓ x₀))
        (fun t ↦ cdf ν t ^ ((((d + 1 : ℕ) : ℝ))⁻¹)) := by
    convert hconcBody using 1
    funext t
    exact hroot t
  have hsupport :
      ∀ᵐ t ∂ν, t ∈ Ici (ℓ x₀) := by
    simpa [ν, μ] using
      ae_map_uniformVolume_mem_Ici_of_isMinOn C ℓ hmin
  have hid : Integrable (fun t : ℝ ↦ t) ν := by
    simpa [ν, μ] using integrable_id_map_uniformVolume C ℓ
  have hjensen :=
    cdf_rpow_inv_natCast_le_at_mean ν (Nat.succ_ne_zero d)
      (ℓ x₀) hconc hsupport hid
  have hmean :
      (∫ t : ℝ, t ∂ν) = ℓ C.centroid := by
    simpa [ν, μ, FullDimensionalConvexBody.centroid, volumeCentroid] using
      integral_id_map_uniformVolume_eq_centroid_projection
        (C : Set (Euc d)) C.isCompact ℓ
  calc
    (((d + 1 : ℕ) : ℝ) / (d + 2 : ℕ)) =
        (((d + 1 : ℕ) : ℝ) /
          (((d + 1 : ℕ) : ℝ) + 1)) := by
      norm_num [Nat.cast_add]
      ring
    _ ≤ cdf ν (∫ t : ℝ, t ∂ν) ^
          ((((d + 1 : ℕ) : ℝ))⁻¹) := hjensen
    _ = cdfRoot (C : Set (Euc d)) ℓ (ℓ C.centroid) := by
      rw [hmean]
      exact hroot _

/-- The functional form of Grünbaum's centroid halfspace theorem in positive
dimension `n = d + 1`. -/
theorem grunbaum_centroid_halfspace_functional {d : ℕ}
    (C : FullDimensionalConvexBody d)
    (ℓ : Euc d →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (a : ℝ) (ha : ℓ C.centroid ≤ a) :
    grunbaumConstant d ≤ halfspaceVolumeRatio C ℓ a :=
  grunbaum_bound_of_cdfRoot C ℓ a ha
    (cdfRoot_centroid_lower_bound C ℓ hℓ)

/-- **Grünbaum's centroid halfspace theorem.**  Every proper closed
halfspace containing the centroid of a full-dimensional convex body in
dimension `d + 1` contains at least `((d + 1) / (d + 2)) ^ (d + 1)` of its
volume. -/
theorem grunbaum_centroid_halfspace {d : ℕ}
    (C : FullDimensionalConvexBody d) (H : ClosedHalfspace d)
    (hcentroid : C.centroid ∈ H) :
    grunbaumConstant d ≤
      halfspaceVolumeRatio C H.normal H.threshold :=
  grunbaum_centroid_halfspace_functional C H.normal H.normal_ne_zero
    H.threshold (ClosedHalfspace.mem_iff.mp hcentroid)

end Grunbaum
