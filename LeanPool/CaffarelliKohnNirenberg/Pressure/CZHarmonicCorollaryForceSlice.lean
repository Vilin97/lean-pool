/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34Slices

/-!
# CZHarmonic Corollary Force Slice

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-! Almost-everywhere integrability of the force density `f` in the `def:sws` class,
restricted to spatial slices of an admissible parabolic cylinder. This is the
vector-valued analogue of `sws_pressure_memLp_slice_ae`. -/

theorem sws_force_memLp_slice_ae
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (fun x : Vec3 => f (x, s)) (ENNReal.ofReal q)
        (volume.restrict (vec3Ball z.1 ρ)) := by
  have hq : 5 / 2 < q := hsol.2.2.2.1
  have hq0 : 0 < q := by linarith only [hq]
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  let B : Set Vec3 := vec3Ball z.1 ρ
  let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet Ω' J)) := hdata.2.2.2.1
  have hfprod : AEStronglyMeasurable f
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hfmeas
  have hfBT : AEStronglyMeasurable f
      ((volume.restrict B).prod (volume.restrict T)) := by
    apply hfprod.mono_measure
    apply Measure.prod_mono
    · exact Measure.restrict_mono_set volume hball
    · exact Measure.restrict_mono_set volume htime
  have hfglobal : MemLp f (ENNReal.ofReal q)
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hdata.2.2.2.2.2.2.2.1
  have hfBT' : MemLp f (ENNReal.ofReal q)
      ((volume.restrict B).prod (volume.restrict T)) := by
    apply hfglobal.mono_measure
    apply Measure.prod_mono
    · exact Measure.restrict_mono_set volume hball
    · exact Measure.restrict_mono_set volume htime
  have hfPow : Integrable (fun w : Vec3 × ℝ =>
      ‖f w‖ ^ q)
      ((volume.restrict B).prod (volume.restrict T)) := by
    have h := hfBT'.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hq0).ne'
      ENNReal.ofReal_ne_top
    change Integrable (fun w : Vec3 × ℝ =>
      ‖f w‖ ^ (ENNReal.ofReal q).toReal)
      ((volume.restrict B).prod (volume.restrict T)) at h
    simpa only [ENNReal.toReal_ofReal hq0.le] using h
  have hfPowSlice := hfPow.prod_left_ae
  have hfMeasSlice := hfBT.prodMk_right
  filter_upwards [hfPowSlice, hfMeasSlice] with s hs hms
  have hs' : Integrable (fun x : Vec3 =>
      ‖f (x, s)‖ ^ (ENNReal.ofReal q).toReal)
      (volume.restrict B) := by
    simpa only [ENNReal.toReal_ofReal hq0.le] using hs
  exact (integrable_norm_rpow_iff hms (ENNReal.ofReal_pos.mpr hq0).ne'
    ENNReal.ofReal_ne_top).mp hs'

end CKN
