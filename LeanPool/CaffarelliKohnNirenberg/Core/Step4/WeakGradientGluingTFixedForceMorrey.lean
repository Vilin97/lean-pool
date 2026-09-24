/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTFixedSourceMorrey

/-! # Morrey membership of the fixed near-force source

Local force integrability on a finite fixed carrier gives the target source
Morrey class. The cutoff is bounded by one, and no spatial supremum bound
on the force is used.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-- The fixed near-force source has finite target Morrey seminorm directly
from the suitable solution's local force integrability. -/
theorem fixed_near_force_source_morrey_lt_top_of_sws
    {κ q : ℝ} (hκ : 6 / 5 ≤ κ) (hκq : κ ≤ q)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R)
    (hdom : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I) (j : Fin 3) :
    morreyNorm (6 / 5 : ℝ) κ
      ((parabolicCylinder z₀.1 (z₀.2 + R ^ 2 / 4) R).indicator
        (fun w => mollifiedBallCutoff z₀.1 hR w.1 * f w j)) < ⊤ := by
  let Q := parabolicCylinder z₀.1 (z₀.2 + R ^ 2 / 4) R
  let B := vec3Ball z₀.1 R
  let J := Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2)
  let η := mollifiedBallCutoff z₀.1 hR
  have hbox : localBox Ω I B J := localBox_of_parabolic_ball hR hdom
  have hQ : MeasurableSet Q := measurableSet_parabolicCylinder _ _ _
  have hQbox : Q ⊆ B ×ˢ J := by
    intro z hz
    have ht := fixed_pressure_cylinder_subset_ball z₀ hR hz
    rw [metricBall_eq_parabolicBall] at ht
    exact ht
  have hdata := hsol.2.2.2.2.2.1 B J hbox
  have hfq : MemLp (fun w => f w j) (ENNReal.ofReal q) (volume.restrict Q) :=
    (hdata.2.2.2.2.2.2.2.1.eval j).mono_measure (Measure.restrict_mono_set volume hQbox)
  have hQfinite : volume Q < ⊤ := by
    rw [volume_parabolicCylinder]
    exact ENNReal.mul_lt_top (Integration.volume_vec3Ball_lt_top) ENNReal.ofReal_lt_top
  let : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.mpr hQfinite.ne
  have hfk : MemLp (fun w => f w j) (ENNReal.ofReal κ) (volume.restrict Q) :=
    hfq.mono_exponent (ENNReal.ofReal_le_ofReal hκq)
  have hη : Measurable (fun w : ParabolicPoint => η w.1) :=
    (mollifiedBallCutoff_smooth z₀.1 hR).continuous.measurable.comp measurable_fst
  have hprod : MemLp (fun w => η w.1 * f w j) (ENNReal.ofReal κ) (volume.restrict Q) := by
    apply hfk.of_le (hη.aestronglyMeasurable.mul hfk.aestronglyMeasurable)
    exact Eventually.of_forall fun w => by
      have he : ‖η w.1‖ ≤ 1 :=
        (abs_of_nonneg (mollifiedBallCutoff_nonneg z₀.1 hR w.1)).le.trans
          (mollifiedBallCutoff_le_one z₀.1 hR w.1)
      exact (norm_mul (η w.1) (f w j)).le.trans
        (mul_le_of_le_one_left (norm_nonneg _) he)

  exact pressure_source_morrey_lt_top_of_memLp (by norm_num) hκ
    ((memLp_indicator_iff_restrict hQ).mpr hprod)

end CKN.Core.Step4
