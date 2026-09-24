/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Holder
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Doubling
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Slice
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Campanato oscillations on parabolic cylinders

The `L^p` oscillation of a function on a parabolic cylinder, the Campanato
bound it satisfies on a region, the tail constant of the dyadic geometric
series, and the comparison of the average of `|f|` on a subset with the
average on the ambient set.  The oscillations use genuine space-time averages.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter


noncomputable section

namespace CKN.Foundation.Parabolic

instance campanatoParabolicVolumeIsLocallyFinite :
    IsLocallyFiniteMeasure (volume : Measure ParabolicPoint) :=
  { finiteAtNhds := fun p =>
      ⟨@Metric.ball ParabolicPoint parabolicPseudoMetricSpace p 1,
        @Metric.ball_mem_nhds ParabolicPoint parabolicPseudoMetricSpace p 1 one_pos,
        volume_parabolicBall_lt_top one_pos⟩ }

def ParabolicCylinderLpOscillation
    (f : ParabolicPoint → ℝ) (x : Vec3) (t r p : ℝ) : ℝ :=
  (⨍ z in parabolicCylinder x t r,
    |f z - Integration.cylinderAverage x t r f| ^ p) ^ (1 / p)

def ParabolicCylinderCampanatoBoundOn
    (f : ParabolicPoint → ℝ) (U : Set ParabolicPoint)
    (R α K p : ℝ) : Prop :=
  ∀ z ∈ U, ∀ {r : ℝ}, 0 < r → r ≤ R →
    ParabolicCylinderLpOscillation f z.1 z.2 r p ≤ K * r ^ α

def parabolicCampanatoTailConstant (α : ℝ) : ℝ :=
  1 / (1 - (2 : ℝ) ^ (-α))

theorem average_abs_le_outer_average_abs
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {A B : Set α} (hBA : B ⊆ A)
    (hApos : 0 < μ A) (hAtop : μ A < ∞)
    (hBpos : 0 < μ B) (hBtop : μ B < ∞)
    (hfA : IntegrableOn f A μ) :
    (⨍ x in B, |f x| ∂μ) ≤
      (μ A).toReal / (μ B).toReal * (⨍ x in A, |f x| ∂μ) := by
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
  have hmono :
      ∫ x in B, |f x| ∂μ ≤ ∫ x in A, |f x| ∂μ := by
    apply MeasureTheory.integral_mono_measure
    · exact Measure.restrict_mono hBA le_rfl
    · exact Filter.Eventually.of_forall fun x => abs_nonneg (f x)
    · exact hfA.norm
  have hAreal : 0 < (μ A).toReal := ENNReal.toReal_pos hApos.ne' hAtop.ne
  have hBreal : 0 < (μ B).toReal := ENNReal.toReal_pos hBpos.ne' hBtop.ne
  have hBinv : 0 ≤ (μ B).toReal⁻¹ := le_of_lt (inv_pos.mpr hBreal)
  change (μ B).toReal⁻¹ * ∫ x in B, |f x| ∂μ ≤
    (μ A).toReal / (μ B).toReal *
      ((μ A).toReal⁻¹ * ∫ x in A, |f x| ∂μ)
  calc
    (μ B).toReal⁻¹ * ∫ x in B, |f x| ∂μ ≤
        (μ B).toReal⁻¹ * ∫ x in A, |f x| ∂μ :=
      mul_le_mul_of_nonneg_left hmono hBinv
    _ = (μ A).toReal / (μ B).toReal *
        ((μ A).toReal⁻¹ * ∫ x in A, |f x| ∂μ) := by
      field_simp

end CKN.Foundation.Parabolic
