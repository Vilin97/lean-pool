/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP7Solution
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalCore

/-!
# Pk Bounds P7 Solution Meas

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

/-! The HLS slice estimate is used on a product cylinder.  This adapter keeps
the representative used to witness the solution's a.e. measurability inside
the proof; the public estimate therefore has no measurable-slice premise. -/

theorem pressureP7_aestronglyMeasurable_on_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    AEStronglyMeasurable
      (fun w : ParabolicPoint =>
        pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
  let B : Set Vec3 := vec3Ball z.1 ρ
  let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hfglobal : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet Ω' J)) := hdata.2.2.2.1
  let fm : ParabolicPoint → Vec3 := hfglobal.mk f
  have hfm : Measurable fm := hfglobal.measurable_mk
  have hηm : Measurable (mollifiedBallCutoff z.1 hρ) :=
    (mollifiedBallCutoff_smooth z.1 hρ).continuous.measurable
  have hfmj (j : Fin 3) : Measurable (fun w : ParabolicPoint => fm w j) := by
    exact (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).measurable.comp hfm
  have hsource (j : Fin 3) : Measurable (fun w : ParabolicPoint =>
      mollifiedBallCutoff z.1 hρ w.1 * fm w j) := by
    exact (hηm.comp measurable_fst).mul (hfmj j)
  have hkernel (j : Fin 3) : Measurable
      (fun w : ParabolicPoint × Vec3 =>
        spatialDeriv newtonianKernel j (w.1.1 - w.2)) := by
    unfold spatialDeriv
    exact (measurable_fderiv_apply_const ℝ newtonianKernel (basisVec j)).comp
      ((measurable_fst.comp measurable_fst).sub measurable_snd)
  let P : Fin 3 → ParabolicPoint → ℝ := fun j w =>
    ∫ y : Vec3, spatialDeriv newtonianKernel j (w.1 - y) *
      (mollifiedBallCutoff z.1 hρ y * fm (y, w.2) j)
  have hPmeas (j : Fin 3) : AEMeasurable (P j) volume := by
    have hmap : Measurable (fun w : ParabolicPoint × Vec3 =>
        (w.2, w.1.2)) :=
      measurable_snd.prodMk (measurable_snd.comp measurable_fst)
    have hsource' : Measurable (fun w : ParabolicPoint × Vec3 =>
        mollifiedBallCutoff z.1 hρ w.2 * fm (w.2, w.1.2) j) := by
      have hcut' : Measurable (fun w : ParabolicPoint × Vec3 =>
          mollifiedBallCutoff z.1 hρ w.2) := hηm.comp measurable_snd
      have hfm' : Measurable (fun w : ParabolicPoint × Vec3 =>
          fm (w.2, w.1.2) j) := (hfmj j).comp hmap
      exact hcut'.mul hfm'
    have hF : Measurable (fun w : ParabolicPoint × Vec3 =>
        spatialDeriv newtonianKernel j (w.1.1 - w.2) *
          (mollifiedBallCutoff z.1 hρ w.2 * fm (w.2, w.1.2) j)) :=
      (hkernel j).mul hsource'
    have hF' : AEStronglyMeasurable (fun w : ParabolicPoint × Vec3 =>
        spatialDeriv newtonianKernel j (w.1.1 - w.2) *
          (mollifiedBallCutoff z.1 hρ w.2 * fm (w.2, w.1.2) j))
        (volume.prod volume) := by
      simpa only [Function.comp_apply] using hF.aestronglyMeasurable
    have hI := hF'.integral_prod_right'
    simpa only [P] using hI.aemeasurable
  let Psum : ParabolicPoint → ℝ := fun w => -∑ j, P j w
  have hPsum : AEMeasurable Psum volume := by
    exact (Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
      (fun j _ => hPmeas j)).neg
  have hfg : f =ᵐ[volume.restrict (spaceTimeSet Ω' J)] fm :=
    hfglobal.ae_eq_mk
  have hBT : B ×ˢ T ⊆ spaceTimeSet Ω' J := by
    intro w hw
    exact ⟨hball hw.1, htime hw.2⟩
  have hfgBT : f =ᵐ[volume.restrict (B ×ˢ T)] fm :=
    ae_restrict_of_ae_restrict_of_subset hBT hfg
  have hfgBT' : f =ᵐ[(volume.restrict B).prod (volume.restrict T)] fm := by
    rw [show volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]] at hfgBT
    exact hfgBT
  have hfgSwap : (fun w : ℝ × Vec3 => f (w.2, w.1)) =ᵐ[
      (volume.restrict T).prod (volume.restrict B)]
      (fun w => fm (w.2, w.1)) := by
    exact MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
      hfgBT'
  have hfgSlices : ∀ᵐ s ∂volume.restrict T, ∀ᵐ y ∂volume.restrict B,
      f (y, s) = fm (y, s) :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hfgSwap
  have hpot : ∀ᵐ s ∂volume.restrict T, ∀ x : Vec3, ∀ j : Fin 3,
      pressureNewtonianDerivativePotential j
          (fun y => mollifiedBallCutoff z.1 hρ y * f (y, s) j) x =
        P j (x, s) := by
    filter_upwards [hfgSlices] with s hs
    have hsourceEq (j : Fin 3) :
        (fun y : Vec3 => mollifiedBallCutoff z.1 hρ y * f (y, s) j) =ᵐ[volume]
          (fun y => mollifiedBallCutoff z.1 hρ y * fm (y, s) j) := by
      apply ae_of_ae_restrict_of_ae_restrict_compl B
      · filter_upwards [hs] with y hy
        have hyj : f (y, s) j = fm (y, s) j :=
          congrArg (fun v : Vec3 => v j) hy
        exact congrArg (fun a : ℝ =>
          mollifiedBallCutoff z.1 hρ y * a) hyj
      · filter_upwards [ae_restrict_mem (show MeasurableSet Bᶜ from
          (vec3Ball_measurable z.1 ρ).compl)] with y hy
        have hy' : y ∉ tsupport (mollifiedBallCutoff z.1 hρ) := by
          intro hyt
          exact hy (pressure_cutoff_support_subset_ball z.1 hρ hyt)
        rw [image_eq_zero_of_notMem_tsupport hy']
        simp
    intro x j
    unfold pressureNewtonianDerivativePotential P
    apply integral_congr_ae
    filter_upwards [hsourceEq j] with y hy
    simp only [hy]
  have hPae : (fun w : Vec3 × ℝ =>
      pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) =ᵐ[
        volume.restrict (B ×ˢ T)] Psum := by
    have hpot' : ∀ᵐ s ∂volume.restrict T, ∀ x : Vec3,
        pressureP7 (mollifiedBallCutoff z.1 hρ) f s x = Psum (x, s) := by
      filter_upwards [hpot] with s hs
      intro x
      change -∑ j, pressureNewtonianDerivativePotential j
          (fun y => mollifiedBallCutoff z.1 hρ y * f (y, s) j) x =
        -∑ j, P j (x, s)
      apply congrArg Neg.neg
      exact Finset.sum_congr rfl (fun j _ => hs x j)
    have hprod : ∀ᵐ w ∂(volume.restrict B).prod (volume.restrict T),
        pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1 = Psum (w.1, w.2) := by
      have hsnd := (Measure.quasiMeasurePreserving_snd
        (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot'
      filter_upwards [hsnd] with w hw
      exact hw w.1
    rw [show volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]]
    exact hprod
  have hPsumR : AEMeasurable Psum
      (volume.restrict (B ×ˢ T)) := hPsum.mono_measure
        (Measure.restrict_le_self)
  have hPae' : (fun w : ParabolicPoint =>
      pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) =ᵐ[
        volume.restrict (parabolicCylinder z.1 z.2 ρ)] Psum := by
    change (fun w : Vec3 × ℝ =>
      pressureP7 (mollifiedBallCutoff z.1 hρ) f w.2 w.1) =ᵐ[
        volume.restrict (parabolicCylinder z.1 z.2 ρ)] Psum
    have hset : parabolicCylinder z.1 z.2 ρ = B ×ˢ T := by
      ext w
      rfl
    rw [hset]
    exact hPae
  have hPsumC : AEMeasurable Psum
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    simpa [ParabolicPoint, parabolicCylinder, B, T] using hPsumR
  exact hPsumC.aestronglyMeasurable.congr hPae'.symm

end CKN
