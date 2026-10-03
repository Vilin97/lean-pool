/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CurveSmoothness

/-! The actual Volterra integral as a bounded operator on compact-time curves. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Extend a compact-interval curve by clamping its time argument. -/
def amnrClampPoint (a b : ℝ) (hab : a ≤ b) (t : ℝ) : Icc a b :=
  ⟨max a (min b t), ⟨le_max_left _ _, (max_le_iff).mpr ⟨hab, min_le_left _ _⟩⟩⟩

/-- The actual continuous clamped extension of a trajectory. -/
def amnrExtendCurve {a b : ℝ} (hab : a ≤ b) (u : C(Icc a b, E)) : ℝ → E :=
  fun t => u (amnrClampPoint a b hab t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Clamping preserves continuity, also at both endpoints. -/
theorem amnrExtendCurve_continuous {a b : ℝ} (hab : a ≤ b) (u : C(Icc a b, E)) :
    Continuous (amnrExtendCurve hab u) := by
  apply u.continuous.comp
  have hh : Continuous (fun t : ℝ => max a (min b t)) := by fun_prop
  exact hh.subtype_mk (fun t => (amnrClampPoint a b hab t).property)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The extension agrees with the actual trajectory inside its interval. -/
theorem amnrExtendCurve_eq_of_mem {a b : ℝ} (hab : a ≤ b) (u : C(Icc a b, E))
    {t : ℝ} (ht : t ∈ Icc a b) : amnrExtendCurve hab u t = u ⟨t, ht⟩ := by
  simp [amnrExtendCurve, amnrClampPoint, max_eq_right ht.1, min_eq_right ht.2]

/-- Integrate the actual trajectory from a prescribed start time. -/
def amnrCurvePrimitive {a b : ℝ} (hab : a ≤ b) (s : ℝ) (u : C(Icc a b, E)) : C(Icc a b, E) :=
  ⟨fun t => ∫ r in s..(t : ℝ), amnrExtendCurve hab u r,
    (intervalIntegral.differentiable_integral_of_continuous
      (amnrExtendCurve_continuous hab u)).continuous.comp continuous_subtype_val⟩

/-- The true compact-time integral has the interval-length operator cost. -/
theorem amnrCurvePrimitive_norm_le {a b s : ℝ} (hab : a ≤ b) (hs : s ∈ Icc a b)
    (u : C(Icc a b, E)) : ‖amnrCurvePrimitive hab s u‖ ≤ (b - a) * ‖u‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (sub_nonneg.mpr hab) (norm_nonneg u))).mpr
  intro t
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := (t : ℝ)) (fun r _ => u.norm_coe_le_norm (amnrClampPoint a b hab r))
  have ht : |(t : ℝ) - s| ≤ b - a := abs_le.mpr ⟨by linarith [hs.2, t.property.1], by linarith
      [hs.1, t.property.2]⟩
  exact hh.trans ((mul_le_mul_of_nonneg_left ht (norm_nonneg u)).trans_eq (mul_comm _ _))

/-- The Volterra integral is an actual bounded linear operator on curves. -/
def amnrCurveIntegral {a b : ℝ} (hab : a ≤ b) (s : ℝ) (hs : s ∈ Icc a b) :
    C(Icc a b, E) →L[ℝ] C(Icc a b, E) :=
  LinearMap.mkContinuous
    { toFun := amnrCurvePrimitive hab s
      map_add' := by
        intro u v
        ext t
        exact intervalIntegral.integral_add
          ((amnrExtendCurve_continuous hab u).intervalIntegrable s t)
          ((amnrExtendCurve_continuous hab v).intervalIntegrable s t)
      map_smul' := by
        intro c u
        ext t
        exact intervalIntegral.integral_smul c (amnrExtendCurve hab u) }
    (b - a) (amnrCurvePrimitive_norm_le hab hs)

/-- The actual integral operator has the exact interval-length upper bound. -/
theorem amnrCurveIntegral_norm_le {a b : ℝ} (hab : a ≤ b) (s : ℝ) (hs : s ∈ Icc a b) :
    ‖amnrCurveIntegral (E := E) hab s hs‖ ≤ b - a := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sub_nonneg.mpr hab)
  exact amnrCurvePrimitive_norm_le hab hs

end AVenhance.Infra.Section4
