/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceQuantitative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceExhaustion

/-!
# Finiteness of the centered majorant on a local box

The source membership required in `eq:pressure-gradient-morrey` follows on
any local box from the spatial Sobolev data of `def:sws`, at almost every
time of that box.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- The centered tensor source belongs to the global spatial `L^{6/5}`
space for almost every time in any local box containing its cutoff. -/
theorem origin_centered_source_memLp_ae_on_local_box
    {Ω U : Set Vec3} {I J : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hbox : localBox Ω I U J)
    {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) (hball : vec3Ball x ρ ⊆ U) (c : ℝ → Vec3) :
    ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      MemLp (fun y => pressureDivergenceCutoffSourceCentredTensor
        (mollifiedBallCutoff x hρ) (spatialDeriv (mollifiedBallCutoff x hρ))
        (fun y => u (y, s)) (fun y => Du (y, s)) (c s) y i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  have hgrad := (hsol.2.2.2.2.2.1 U J hbox).2.2.2.2.2.2.2.2
  have hgradAll : ∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
      HasWeakGradientOn U (fun y => u (y, s) i) (fun y => Du (y, s) i) := ae_all_iff.mpr hgrad
  filter_upwards [slice_memLp_ae_of_sws hsol hbox, hgradAll] with s hs hw
  have hηB := pressure_cutoff_support_subset_ball x hρ
  have hu3 := velocity_norm_memLp_three_on_ball_of_slices hρ hball hs.1 hs.2 hw
  have huComp (i : Fin 3) : MemLp (fun y => u (y, s) i) 3
      (volume.restrict (tsupport (mollifiedBallCutoff x hρ))) := by
    have hui : MemLp (fun y => u (y, s) i) (ENNReal.ofReal (3 : ℝ))
        (volume.restrict (vec3Ball x ρ)) := by
      apply hu3.of_le ((hs.1.eval i).mono_measure (Measure.restrict_mono hball le_rfl)).aestronglyMeasurable
      exact Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _)]
        exact abs_apply_le_vec3EuclideanNorm _ i
    simpa only [ENNReal.ofReal_ofNat] using hui.mono_measure (Measure.restrict_mono hηB le_rfl)
  have hDuComp (i j : Fin 3) : MemLp (fun y => Du (y, s) i j) 2
      (volume.restrict (tsupport (mollifiedBallCutoff x hρ))) :=
    ((hs.2.eval i).eval j).mono_measure (Measure.restrict_mono (hηB.trans hball) le_rfl)
  exact (pressureDivergenceCutoffSourceCentredTensor_memLp_hasCompactSupport
    (c := c s) (mollifiedBallCutoff_hasCompactSupport x hρ).isCompact
    (mollifiedBallCutoff_smooth x hρ) subset_rfl huComp hDuComp).1

end CKN.Core.Step4
