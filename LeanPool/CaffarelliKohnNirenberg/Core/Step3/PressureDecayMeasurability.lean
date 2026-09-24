/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP7SolutionMeas
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalCore

/-!
# Pressure Decay Measurability

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step3

open CKN

/-! The pressure decomposition is evaluated on a bounded product cylinder.
The solution fields have measurable representatives there; the representatives
are used only to discharge the certificates needed by the `eLpNorm'` triangle
inequality. -/

private lemma pressure_kernel_measurable :
    Measurable (newtonianKernel : Vec3 → ℝ) := by
  have hnorm : Measurable (fun z : Vec3 => vec3EuclideanNorm z) := by
    unfold vec3EuclideanNorm
    fun_prop
  unfold newtonianKernel
  exact measurable_const.div (measurable_const.mul hnorm)

private lemma pressure_kernel_derivative_measurable (j : Fin 3) :
    Measurable (fun z : Vec3 => spatialDeriv newtonianKernel j z) := by
  unfold spatialDeriv
  exact measurable_fderiv_apply_const ℝ newtonianKernel (basisVec j)

theorem pressure_source_measurable_on_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∃ (B : Set Vec3) (T : Set ℝ) (η : Vec3 → ℝ)
      (c : ℝ → Vec3),
      B = vec3Ball z.1 ρ ∧ T = Ioc (z.2 - ρ ^ 2) z.2 ∧
      η = mollifiedBallCutoff z.1 hρ ∧
      (∀ s, c s = fun j =>
        MeasureTheory.average (volume.restrict B) (fun y => u (y, s) j)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP1 η u c p f w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP2 η u c w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP3 η u c w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP4 η u c w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP5 η p w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP6 η p w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP7 η f w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) ∧
      AEStronglyMeasurable
        (fun w : ParabolicPoint => pressureP8 η f w.2 w.1)
        (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
  let B : Set Vec3 := vec3Ball z.1 ρ
  let T : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  let η : Vec3 → ℝ := mollifiedBallCutoff z.1 hρ
  let c : ℝ → Vec3 := fun s => fun j =>
    MeasureTheory.average (volume.restrict B) (fun y => u (y, s) j)
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  have hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet Ω' J)) := hdata.1
  have hp : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet Ω' J)) := hdata.2.2.1
  have hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet Ω' J)) := hdata.2.2.2.1
  have hST : spaceTimeSet Ω' T ⊆ spaceTimeSet Ω' J := by
    intro w hw
    exact ⟨hw.1, htime hw.2⟩
  have hu' : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet Ω' T)) :=
    hu.mono_measure (Measure.restrict_mono_set volume hST)
  have hp' : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet Ω' T)) :=
    hp.mono_measure (Measure.restrict_mono_set volume hST)
  have hf' : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet Ω' T)) :=
    hf.mono_measure (Measure.restrict_mono_set volume hST)
  have hcmeas (j : Fin 3) : AEMeasurable (fun s : ℝ => c s j)
      (volume.restrict T) := by
    dsimp [c, B, T]
    have hI : AEMeasurable (fun s : ℝ =>
        ∫ y in vec3Ball z.1 ρ, u (y, s) j)
        (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) := by
      apply pressure_slice_integral_aemeasurable (g := fun w => u w j)
        (vec3Ball_measurable z.1 ρ) measurableSet_Ioc hball
      have hST' : spaceTimeSet Ω' (Ioc (z.2 - ρ ^ 2) z.2) ⊆
          spaceTimeSet Ω' J := by
        intro w hw
        exact ⟨hw.1, htime hw.2⟩
      exact (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).continuous
        |>.comp_aestronglyMeasurable hu
        |>.mono_measure (Measure.restrict_mono_set volume hST')
    simpa only [MeasureTheory.average_eq, smul_eq_mul] using
      hI.const_mul ((volume.restrict (vec3Ball z.1 ρ)).real Set.univ)⁻¹
  let cm : ℝ → Vec3 := fun s => fun j =>
    AEMeasurable.mk (fun t : ℝ => c t j) (hcmeas j) s
  have hcm : Measurable cm := by
    apply Measurable.of_eval
    intro j
    exact (hcmeas j).measurable_mk
  have hcmEq : c =ᵐ[volume.restrict T] cm := by
    filter_upwards [(hcmeas 0).ae_eq_mk, (hcmeas 1).ae_eq_mk,
      (hcmeas 2).ae_eq_mk] with s h0 h1 h2
    funext j
    fin_cases j <;> assumption
  let um : ParabolicPoint → Vec3 := hu.mk u
  let pm : ParabolicPoint → ℝ := hp.mk p
  let fm : ParabolicPoint → Vec3 := hf.mk f
  have hum : Measurable um := hu.measurable_mk
  have hpm : Measurable pm := hp.measurable_mk
  have hfm : Measurable fm := hf.measurable_mk
  have huEq : u =ᵐ[volume.restrict (spaceTimeSet Ω' T)] um := by
    exact ae_restrict_of_ae_restrict_of_subset hST hu.ae_eq_mk
  have hpEq : p =ᵐ[volume.restrict (spaceTimeSet Ω' T)] pm := by
    exact ae_restrict_of_ae_restrict_of_subset hST hp.ae_eq_mk
  have hfEq : f =ᵐ[volume.restrict (spaceTimeSet Ω' T)] fm := by
    exact ae_restrict_of_ae_restrict_of_subset hST hf.ae_eq_mk
  have hBT : B ×ˢ T ⊆ spaceTimeSet Ω' J := by
    intro w hw
    exact ⟨hball hw.1, htime hw.2⟩
  have huBT : u =ᵐ[(volume.restrict B).prod (volume.restrict T)]
      (fun w => um (w.1, w.2)) := by
    have h := ae_restrict_of_ae_restrict_of_subset hBT
      (hu.ae_eq_mk : u =ᵐ[volume.restrict (spaceTimeSet Ω' J)] um)
    have hmeasure : volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) := by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    change u =ᵐ[volume.restrict (B ×ˢ T)] um at h
    exact hmeasure ▸ h
  have hpBT : p =ᵐ[(volume.restrict B).prod (volume.restrict T)]
      (fun w => pm (w.1, w.2)) := by
    have h := ae_restrict_of_ae_restrict_of_subset hBT
      (hp.ae_eq_mk : p =ᵐ[volume.restrict (spaceTimeSet Ω' J)] pm)
    have hmeasure : volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) := by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    change p =ᵐ[volume.restrict (B ×ˢ T)] pm at h
    exact hmeasure ▸ h
  have hfBT : f =ᵐ[(volume.restrict B).prod (volume.restrict T)]
      (fun w => fm (w.1, w.2)) := by
    have h := ae_restrict_of_ae_restrict_of_subset hBT
      (hf.ae_eq_mk : f =ᵐ[volume.restrict (spaceTimeSet Ω' J)] fm)
    have hmeasure : volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) := by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    change f =ᵐ[volume.restrict (B ×ˢ T)] fm at h
    exact hmeasure ▸ h
  have huSlices : ∀ᵐ s ∂volume.restrict T, ∀ᵐ y ∂volume.restrict B,
      u (y, s) = um (y, s) := by
    have hswap := MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
      huBT
    exact MeasureTheory.Measure.ae_ae_of_ae_prod hswap
  have hpSlices : ∀ᵐ s ∂volume.restrict T, ∀ᵐ y ∂volume.restrict B,
      p (y, s) = pm (y, s) := by
    have hswap := MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
      hpBT
    exact MeasureTheory.Measure.ae_ae_of_ae_prod hswap
  have hfSlices : ∀ᵐ s ∂volume.restrict T, ∀ᵐ y ∂volume.restrict B,
      f (y, s) = fm (y, s) := by
    have hswap := MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
      hfBT
    exact MeasureTheory.Measure.ae_ae_of_ae_prod hswap
  have hηc : HasCompactSupport η := by
    dsimp [η]
    exact mollifiedBallCutoff_hasCompactSupport z.1 hρ
  have hηsupp : tsupport η ⊆ B := by
    dsimp [η, B]
    exact pressure_cutoff_support_subset_ball z.1 hρ
  have hηm : Measurable η := by
    dsimp [η]
    exact (mollifiedBallCutoff_smooth z.1 hρ).continuous.measurable
  have hηd (j : Fin 3) : Measurable (spatialDeriv η j) := by
    exact (contDiff_spatialDeriv_smooth
      (mollifiedBallCutoff_smooth z.1 hρ) j).continuous.measurable
  have hηdd (i j : Fin 3) : Measurable (mixedSecond η i j) := by
    exact (contDiff_mixedSecond_smooth
      (mollifiedBallCutoff_smooth z.1 hρ) i j).continuous.measurable
  have hηlap : Measurable (spatialLaplacian η) := by
    exact (contDiff_spatialLaplacian_smooth
      (mollifiedBallCutoff_smooth z.1 hρ)).continuous.measurable
  have hηddsupp (i j : Fin 3) : tsupport (mixedSecond η i j) ⊆ B := by
    exact (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupp)
  have hηdsupp (j : Fin 3) : tsupport (spatialDeriv η j) ⊆ B := by
    exact (tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηsupp
  have hηlapsupp : tsupport (spatialLaplacian η) ⊆ B := by
    change tsupport (fun x => ∑ j : Fin 3,
      spatialDeriv (spatialDeriv η j) j x) ⊆ B
    apply decomposition_ts_support_sum₃_sws
    intro j
    exact (tsupport_fderiv_apply_subset ℝ (basisVec j)).trans (hηdsupp j)
  have hsrc2 (i j : Fin 3) : ∀ᵐ s ∂volume.restrict T,
      (fun y => mixedSecond η i j y * pressureUTensor u c
        (⟨y, s⟩ : ParabolicPoint) i j) =ᵐ[volume]
        (fun y => mixedSecond η i j y * pressureUTensor um cm
          (⟨y, s⟩ : ParabolicPoint) i j) := by
    filter_upwards [huSlices, hcmEq] with s hus hcs
    apply ae_of_ae_restrict_of_ae_restrict_compl B
    · filter_upwards [hus] with y hy
      have hy' : u (⟨y, s⟩ : ParabolicPoint) = um (⟨y, s⟩ : ParabolicPoint) := by
        simpa using hy
      have hcs' : c s = cm s := hcs
      change mixedSecond η i j y * pressureUTensor u c
          (⟨y, s⟩ : ParabolicPoint) i j =
        mixedSecond η i j y * pressureUTensor um cm
          (⟨y, s⟩ : ParabolicPoint) i j
      simp only [pressureUTensor, hy', hcs']
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Bᶜ from (vec3Ball_measurable z.1 ρ).compl)] with y hy
      have hy' : y ∉ tsupport (mixedSecond η i j) := by
        intro hyt
        exact hy (hηddsupp i j hyt)
      rw [image_eq_zero_of_notMem_tsupport hy']
      simp
  have hsrc3 (i j : Fin 3) : ∀ᵐ s ∂volume.restrict T,
      (fun y => pressureUTensor u c (⟨y, s⟩ : ParabolicPoint) i j *
        spatialDeriv η i y) =ᵐ[volume]
        (fun y => pressureUTensor um cm (⟨y, s⟩ : ParabolicPoint) i j *
          spatialDeriv η i y) := by
    filter_upwards [huSlices, hcmEq] with s hus hcs
    apply ae_of_ae_restrict_of_ae_restrict_compl B
    · filter_upwards [hus] with y hy
      have hy' : u (⟨y, s⟩ : ParabolicPoint) = um (⟨y, s⟩ : ParabolicPoint) := by
        simpa using hy
      have hcs' : c s = cm s := hcs
      change pressureUTensor u c (⟨y, s⟩ : ParabolicPoint) i j * spatialDeriv η i y =
        pressureUTensor um cm (⟨y, s⟩ : ParabolicPoint) i j * spatialDeriv η i y
      simp only [pressureUTensor, hy', hcs']
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Bᶜ from (vec3Ball_measurable z.1 ρ).compl)] with y hy
      have hy' : y ∉ tsupport (spatialDeriv η i) := by
        intro hyt
        exact hy (hηdsupp i hyt)
      rw [image_eq_zero_of_notMem_tsupport hy']
      simp
  have hsrc4 (i j : Fin 3) : ∀ᵐ s ∂volume.restrict T,
      (fun y => pressureUTensor u c (⟨y, s⟩ : ParabolicPoint) i j *
        spatialDeriv η j y) =ᵐ[volume]
        (fun y => pressureUTensor um cm (⟨y, s⟩ : ParabolicPoint) i j *
          spatialDeriv η j y) := by
    filter_upwards [huSlices, hcmEq] with s hus hcs
    apply ae_of_ae_restrict_of_ae_restrict_compl B
    · filter_upwards [hus] with y hy
      have hy' : u (⟨y, s⟩ : ParabolicPoint) = um (⟨y, s⟩ : ParabolicPoint) := by
        simpa using hy
      have hcs' : c s = cm s := hcs
      change pressureUTensor u c (⟨y, s⟩ : ParabolicPoint) i j * spatialDeriv η j y =
        pressureUTensor um cm (⟨y, s⟩ : ParabolicPoint) i j * spatialDeriv η j y
      simp only [pressureUTensor, hy', hcs']
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Bᶜ from (vec3Ball_measurable z.1 ρ).compl)] with y hy
      have hy' : y ∉ tsupport (spatialDeriv η j) := by
        intro hyt
        exact hy (hηdsupp j hyt)
      rw [image_eq_zero_of_notMem_tsupport hy']
      simp
  have hsrc5 : ∀ᵐ s ∂volume.restrict T,
      (fun y => p (y, s) * spatialLaplacian η y) =ᵐ[volume]
        (fun y => pm (y, s) * spatialLaplacian η y) := by
    filter_upwards [hpSlices] with s hps
    apply ae_of_ae_restrict_of_ae_restrict_compl B
    · filter_upwards [hps] with y hy
      rw [hy]
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Bᶜ from (vec3Ball_measurable z.1 ρ).compl)] with y hy
      have hy' : y ∉ tsupport (spatialLaplacian η) := by
        intro hyt
        exact hy (hηlapsupp hyt)
      rw [image_eq_zero_of_notMem_tsupport hy']
      simp
  have hsrc6 (j : Fin 3) : ∀ᵐ s ∂volume.restrict T,
      (fun y => spatialDeriv η j y * p (y, s)) =ᵐ[volume]
        (fun y => spatialDeriv η j y * pm (y, s)) := by
    filter_upwards [hpSlices] with s hps
    apply ae_of_ae_restrict_of_ae_restrict_compl B
    · filter_upwards [hps] with y hy
      rw [hy]
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Bᶜ from (vec3Ball_measurable z.1 ρ).compl)] with y hy
      have hy' : y ∉ tsupport (spatialDeriv η j) := by
        intro hyt
        exact hy (hηdsupp j hyt)
      rw [image_eq_zero_of_notMem_tsupport hy']
      simp
  have hsrc7 (j : Fin 3) : ∀ᵐ s ∂volume.restrict T,
      (fun y => η y * f (y, s) j) =ᵐ[volume]
        (fun y => η y * fm (y, s) j) := by
    filter_upwards [hfSlices] with s hfs
    apply ae_of_ae_restrict_of_ae_restrict_compl B
    · filter_upwards [hfs] with y hy
      rw [hy]
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Bᶜ from (vec3Ball_measurable z.1 ρ).compl)] with y hy
      have hy' : y ∉ tsupport η := by
        intro hyt
        exact hy (hηsupp hyt)
      rw [image_eq_zero_of_notMem_tsupport hy']
      simp
  have hsrc8 (j : Fin 3) : ∀ᵐ s ∂volume.restrict T,
      (fun y => spatialDeriv η j y * f (y, s) j) =ᵐ[volume]
        (fun y => spatialDeriv η j y * fm (y, s) j) := by
    filter_upwards [hfSlices] with s hfs
    apply ae_of_ae_restrict_of_ae_restrict_compl B
    · filter_upwards [hfs] with y hy
      rw [hy]
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Bᶜ from (vec3Ball_measurable z.1 ρ).compl)] with y hy
      have hy' : y ∉ tsupport (spatialDeriv η j) := by
        intro hyt
        exact hy (hηdsupp j hyt)
      rw [image_eq_zero_of_notMem_tsupport hy']
      simp
  have hkernel0 : Measurable (fun w : ParabolicPoint × Vec3 =>
      -newtonianKernel (w.1.1 - w.2)) := by
    exact pressure_kernel_measurable.neg.comp
      ((measurable_fst.comp measurable_fst).sub measurable_snd)
  have hkernel1 (j : Fin 3) : Measurable (fun w : ParabolicPoint × Vec3 =>
      spatialDeriv newtonianKernel j (w.1.1 - w.2)) := by
    exact (pressure_kernel_derivative_measurable j).comp
      ((measurable_fst.comp measurable_fst).sub measurable_snd)
  have hIntegral {g : ParabolicPoint × Vec3 → ℝ} (hg : Measurable g) :
      AEMeasurable (fun w : ParabolicPoint => ∫ y : Vec3, g (w, y)) volume := by
    have h := hg.aestronglyMeasurable.integral_prod_right'
      (μ := (volume : Measure ParabolicPoint))
      (ν := (volume : Measure Vec3))
    simpa only [Function.comp_apply] using h.aemeasurable
  let R2 : ParabolicPoint → ℝ := fun w =>
    ∑ i, ∑ j, ∫ y : Vec3,
      (-newtonianKernel (w.1 - y)) *
        (mixedSecond η i j y * pressureUTensor um cm (y, w.2) i j)
  let R3 : ParabolicPoint → ℝ := fun w =>
    ∑ i, ∑ j, ∫ y : Vec3,
      spatialDeriv newtonianKernel j (w.1 - y) *
        (pressureUTensor um cm (y, w.2) i j * spatialDeriv η i y)
  let R4 : ParabolicPoint → ℝ := fun w =>
    ∑ i, ∑ j, ∫ y : Vec3,
      spatialDeriv newtonianKernel i (w.1 - y) *
        (pressureUTensor um cm (y, w.2) i j * spatialDeriv η j y)
  let R5 : ParabolicPoint → ℝ := fun w =>
    -∫ y : Vec3, (-newtonianKernel (w.1 - y)) *
      (pm (y, w.2) * spatialLaplacian η y)
  let R6 : ParabolicPoint → ℝ := fun w =>
    -2 * ∑ j, ∫ y : Vec3,
      spatialDeriv newtonianKernel j (w.1 - y) *
        (spatialDeriv η j y * pm (y, w.2))
  let R7 : ParabolicPoint → ℝ := fun w =>
    -∑ j, ∫ y : Vec3, spatialDeriv newtonianKernel j (w.1 - y) *
      (η y * fm (y, w.2) j)
  let R8 : ParabolicPoint → ℝ := fun w =>
    -∑ j, ∫ y : Vec3, (-newtonianKernel (w.1 - y)) *
      (spatialDeriv η j y * fm (y, w.2) j)
  have hR2ij (i j : Fin 3) : AEMeasurable (fun w : ParabolicPoint =>
      ∫ y : Vec3, (-newtonianKernel (w.1 - y)) *
        (mixedSecond η i j y * pressureUTensor um cm (y, w.2) i j)) volume := by
    convert hIntegral (g := fun w : ParabolicPoint × Vec3 =>
      -newtonianKernel (w.1.1 - w.2) *
        (mixedSecond η i j w.2 *
          pressureUTensor um cm (w.2, w.1.2) i j)) (by
      apply hkernel0.mul
      unfold pressureUTensor
      fun_prop) using 1
  have hR2 : AEMeasurable R2 volume := by
    dsimp [R2]
    change AEMeasurable (∑ i : Fin 3, ∑ j : Fin 3, fun w : ParabolicPoint =>
      ∫ y : Vec3, (-newtonianKernel (w.1 - y)) *
        (mixedSecond η i j y * pressureUTensor um cm (y, w.2) i j)) volume
    exact Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun j _ => hR2ij i j))
  have hR3ij (i j : Fin 3) : AEMeasurable (fun w : ParabolicPoint =>
      ∫ y : Vec3, spatialDeriv newtonianKernel j (w.1 - y) *
        (pressureUTensor um cm (y, w.2) i j * spatialDeriv η i y)) volume := by
    convert hIntegral (g := fun w : ParabolicPoint × Vec3 =>
      spatialDeriv newtonianKernel j (w.1.1 - w.2) *
        (pressureUTensor um cm (w.2, w.1.2) i j * spatialDeriv η i w.2)) (by
      apply hkernel1 j |>.mul
      unfold pressureUTensor
      fun_prop) using 1
  have hR3 : AEMeasurable R3 volume := by
    dsimp [R3]
    change AEMeasurable (∑ i : Fin 3, ∑ j : Fin 3, fun w : ParabolicPoint =>
      ∫ y : Vec3, spatialDeriv newtonianKernel j (w.1 - y) *
        (pressureUTensor um cm (y, w.2) i j * spatialDeriv η i y)) volume
    exact Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun j _ => hR3ij i j))
  have hR4ij (i j : Fin 3) : AEMeasurable (fun w : ParabolicPoint =>
      ∫ y : Vec3, spatialDeriv newtonianKernel i (w.1 - y) *
        (pressureUTensor um cm (y, w.2) i j * spatialDeriv η j y)) volume := by
    convert hIntegral (g := fun w : ParabolicPoint × Vec3 =>
      spatialDeriv newtonianKernel i (w.1.1 - w.2) *
        (pressureUTensor um cm (w.2, w.1.2) i j * spatialDeriv η j w.2)) (by
      apply hkernel1 i |>.mul
      unfold pressureUTensor
      fun_prop) using 1
  have hR4 : AEMeasurable R4 volume := by
    dsimp [R4]
    change AEMeasurable (∑ i : Fin 3, ∑ j : Fin 3, fun w : ParabolicPoint =>
      ∫ y : Vec3, spatialDeriv newtonianKernel i (w.1 - y) *
        (pressureUTensor um cm (y, w.2) i j * spatialDeriv η j y)) volume
    exact Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun i _ =>
      Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun j _ => hR4ij i j))
  have hR5 : AEMeasurable R5 volume := by
    dsimp [R5]
    convert (hIntegral (g := fun w : ParabolicPoint × Vec3 =>
      -newtonianKernel (w.1.1 - w.2) *
        (pm (w.2, w.1.2) * spatialLaplacian η w.2)) (by
      apply hkernel0.mul
      exact (hpm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).mul
        (hηlap.comp measurable_snd))).neg using 1
  have hR6j (j : Fin 3) : AEMeasurable (fun w : ParabolicPoint =>
      ∫ y : Vec3, spatialDeriv newtonianKernel j (w.1 - y) *
        (spatialDeriv η j y * pm (y, w.2))) volume := by
    convert hIntegral (g := fun w : ParabolicPoint × Vec3 =>
      spatialDeriv newtonianKernel j (w.1.1 - w.2) *
        (spatialDeriv η j w.2 * pm (w.2, w.1.2))) (by
      apply hkernel1 j |>.mul
      exact (hηd j).comp measurable_snd |>.mul
        (hpm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))) using 1
  have hR6 : AEMeasurable R6 volume := by
    dsimp [R6]
    change AEMeasurable ((-2 : ℝ) •
      (∑ j : Fin 3, fun w : ParabolicPoint => ∫ y : Vec3,
        spatialDeriv newtonianKernel j (w.1 - y) *
          (spatialDeriv η j y * pm (y, w.2)))) volume
    exact (Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
      (fun j _ => hR6j j)).const_mul (-2)
  have hR7j (j : Fin 3) : AEMeasurable (fun w : ParabolicPoint =>
      ∫ y : Vec3, spatialDeriv newtonianKernel j (w.1 - y) *
        (η y * fm (y, w.2) j)) volume := by
    convert hIntegral (g := fun w : ParabolicPoint × Vec3 =>
      spatialDeriv newtonianKernel j (w.1.1 - w.2) *
        (η w.2 * fm (w.2, w.1.2) j)) (by
      apply hkernel1 j |>.mul
      exact (hηm.comp measurable_snd).mul
        ((ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).measurable.comp
          (hfm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
    ) using 1
  have hR7 : AEMeasurable R7 volume := by
    dsimp [R7]
    change AEMeasurable (-∑ j : Fin 3, fun w : ParabolicPoint =>
      ∫ y : Vec3, spatialDeriv newtonianKernel j (w.1 - y) *
        (η y * fm (y, w.2) j)) volume
    exact (Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
      (fun j _ => hR7j j)).neg
  have hR8j (j : Fin 3) : AEMeasurable (fun w : ParabolicPoint =>
      ∫ y : Vec3, (-newtonianKernel (w.1 - y)) *
        (spatialDeriv η j y * fm (y, w.2) j)) volume := by
    convert hIntegral (g := fun w : ParabolicPoint × Vec3 =>
      -newtonianKernel (w.1.1 - w.2) *
        (spatialDeriv η j w.2 * fm (w.2, w.1.2) j)) (by
      apply hkernel0.mul
      exact (hηd j).comp measurable_snd |>.mul
        ((ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).measurable.comp
          (hfm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
    ) using 1
  have hR8 : AEMeasurable R8 volume := by
    dsimp [R8]
    change AEMeasurable (-∑ j : Fin 3, fun w : ParabolicPoint =>
      ∫ y : Vec3, (-newtonianKernel (w.1 - y)) *
        (spatialDeriv η j y * fm (y, w.2) j)) volume
    exact (Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
      (fun j _ => hR8j j)).neg
  have hpot2 : ∀ᵐ s ∂volume.restrict T, ∀ x : Vec3,
      pressureP2 η u c s x = R2 (x, s) := by
    have hall : ∀ᵐ s ∂volume.restrict T, ∀ i j : Fin 3, ∀ᵐ y ∂volume,
        mixedSecond η i j y * pressureUTensor u c (y, s) i j =
          mixedSecond η i j y * pressureUTensor um cm (y, s) i j := by
      rw [ae_all_iff]
      intro i
      rw [ae_all_iff]
      intro j
      exact hsrc2 i j
    filter_upwards [hall] with s hs x
    unfold pressureP2 R2
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [hs i j] with y hy
    rw [hy]
  have hpot3 : ∀ᵐ s ∂volume.restrict T, ∀ x : Vec3,
      pressureP3 η u c s x = R3 (x, s) := by
    have hall : ∀ᵐ s ∂volume.restrict T, ∀ i j : Fin 3, ∀ᵐ y ∂volume,
        pressureUTensor u c (y, s) i j * spatialDeriv η i y =
          pressureUTensor um cm (y, s) i j * spatialDeriv η i y := by
      rw [ae_all_iff]
      intro i
      rw [ae_all_iff]
      intro j
      exact hsrc3 i j
    filter_upwards [hall] with s hs x
    unfold pressureP3 R3
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [hs i j] with y hy
    rw [hy]
  have hpot4 : ∀ᵐ s ∂volume.restrict T, ∀ x : Vec3,
      pressureP4 η u c s x = R4 (x, s) := by
    have hall : ∀ᵐ s ∂volume.restrict T, ∀ i j : Fin 3, ∀ᵐ y ∂volume,
        pressureUTensor u c (y, s) i j * spatialDeriv η j y =
          pressureUTensor um cm (y, s) i j * spatialDeriv η j y := by
      rw [ae_all_iff]
      intro i
      rw [ae_all_iff]
      intro j
      exact hsrc4 i j
    filter_upwards [hall] with s hs x
    unfold pressureP4 R4
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [hs i j] with y hy
    rw [hy]
  have hpot5 : ∀ᵐ s ∂volume.restrict T, ∀ x : Vec3,
      pressureP5 η p s x = R5 (x, s) := by
    filter_upwards [hsrc5] with s hs x
    unfold pressureP5 R5
    congr 1
    apply integral_congr_ae
    filter_upwards [hs] with y hy
    rw [hy]
  have hpot6 : ∀ᵐ s ∂volume.restrict T, ∀ x : Vec3,
      pressureP6 η p s x = R6 (x, s) := by
    have hall : ∀ᵐ s ∂volume.restrict T, ∀ j : Fin 3, ∀ᵐ y ∂volume,
        spatialDeriv η j y * p (y, s) =
          spatialDeriv η j y * pm (y, s) := by
      rw [ae_all_iff]
      intro j
      exact hsrc6 j
    filter_upwards [hall] with s hs x
    unfold pressureP6 R6
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [hs j] with y hy
    rw [hy]
  have hpot7 : ∀ᵐ s ∂volume.restrict T, ∀ x : Vec3,
      pressureP7 η f s x = R7 (x, s) := by
    have hall : ∀ᵐ s ∂volume.restrict T, ∀ j : Fin 3, ∀ᵐ y ∂volume,
        η y * f (y, s) j = η y * fm (y, s) j := by
      rw [ae_all_iff]
      intro j
      exact hsrc7 j
    filter_upwards [hall] with s hs x
    unfold pressureP7 R7
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [hs j] with y hy
    rw [hy]
  have hpot8 : ∀ᵐ s ∂volume.restrict T, ∀ x : Vec3,
      pressureP8 η f s x = R8 (x, s) := by
    have hall : ∀ᵐ s ∂volume.restrict T, ∀ j : Fin 3, ∀ᵐ y ∂volume,
        spatialDeriv η j y * f (y, s) j =
          spatialDeriv η j y * fm (y, s) j := by
      rw [ae_all_iff]
      intro j
      exact hsrc8 j
    filter_upwards [hall] with s hs x
    unfold pressureP8 R8
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply integral_congr_ae
    filter_upwards [hs j] with y hy
    rw [hy]
  have hQ2 : (fun w : ParabolicPoint => pressureP2 η u c w.2 w.1) =ᵐ[
      volume.restrict (parabolicCylinder z.1 z.2 ρ)] R2 := by
    change (fun w : ParabolicPoint => pressureP2 η u c w.2 w.1) =ᵐ[
      volume.restrict (B ×ˢ T)] R2
    have hmeasureBT : volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) := by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    rw [hmeasureBT]
    have hprod := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot2
    filter_upwards [hprod] with w hw
    exact hw w.1
  have hQ3 : (fun w : ParabolicPoint => pressureP3 η u c w.2 w.1) =ᵐ[
      volume.restrict (parabolicCylinder z.1 z.2 ρ)] R3 := by
    change (fun w : ParabolicPoint => pressureP3 η u c w.2 w.1) =ᵐ[
      volume.restrict (B ×ˢ T)] R3
    have hmeasureBT : volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) := by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    rw [hmeasureBT]
    have hprod := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot3
    filter_upwards [hprod] with w hw
    exact hw w.1
  have hQ4 : (fun w : ParabolicPoint => pressureP4 η u c w.2 w.1) =ᵐ[
      volume.restrict (parabolicCylinder z.1 z.2 ρ)] R4 := by
    change (fun w : ParabolicPoint => pressureP4 η u c w.2 w.1) =ᵐ[
      volume.restrict (B ×ˢ T)] R4
    have hmeasureBT : volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) := by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    rw [hmeasureBT]
    have hprod := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot4
    filter_upwards [hprod] with w hw
    exact hw w.1
  have hQ5 : (fun w : ParabolicPoint => pressureP5 η p w.2 w.1) =ᵐ[
      volume.restrict (parabolicCylinder z.1 z.2 ρ)] R5 := by
    change (fun w : ParabolicPoint => pressureP5 η p w.2 w.1) =ᵐ[
      volume.restrict (B ×ˢ T)] R5
    have hmeasureBT : volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) := by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    rw [hmeasureBT]
    have hprod := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot5
    filter_upwards [hprod] with w hw
    exact hw w.1
  have hQ6 : (fun w : ParabolicPoint => pressureP6 η p w.2 w.1) =ᵐ[
      volume.restrict (parabolicCylinder z.1 z.2 ρ)] R6 := by
    change (fun w : ParabolicPoint => pressureP6 η p w.2 w.1) =ᵐ[
      volume.restrict (B ×ˢ T)] R6
    have hmeasureBT : volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) := by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    rw [hmeasureBT]
    have hprod := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot6
    filter_upwards [hprod] with w hw
    exact hw w.1
  have hQ7 : (fun w : ParabolicPoint => pressureP7 η f w.2 w.1) =ᵐ[
      volume.restrict (parabolicCylinder z.1 z.2 ρ)] R7 := by
    change (fun w : ParabolicPoint => pressureP7 η f w.2 w.1) =ᵐ[
      volume.restrict (B ×ˢ T)] R7
    have hmeasureBT : volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) := by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    rw [hmeasureBT]
    have hprod := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot7
    filter_upwards [hprod] with w hw
    exact hw w.1
  have hQ8 : (fun w : ParabolicPoint => pressureP8 η f w.2 w.1) =ᵐ[
      volume.restrict (parabolicCylinder z.1 z.2 ρ)] R8 := by
    change (fun w : ParabolicPoint => pressureP8 η f w.2 w.1) =ᵐ[
      volume.restrict (B ×ˢ T)] R8
    have hmeasureBT : volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) := by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    rw [hmeasureBT]
    have hprod := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict B) (ν := volume.restrict T)).ae hpot8
    filter_upwards [hprod] with w hw
    exact hw w.1
  have hR7c : AEStronglyMeasurable R7
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) :=
    hR7.aestronglyMeasurable.restrict
  have hR8c : AEStronglyMeasurable R8
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) :=
    hR8.aestronglyMeasurable.restrict
  have hP7 := pressureP7_aestronglyMeasurable_on_cylinder hsol hρ hsub
  have hP8 : AEStronglyMeasurable
      (fun w : ParabolicPoint => pressureP8 η f w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    exact hR8c.congr hQ8.symm
  have hP2 : AEStronglyMeasurable
      (fun w : ParabolicPoint => pressureP2 η u c w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    exact hR2.aestronglyMeasurable.restrict.congr hQ2.symm
  have hP3 : AEStronglyMeasurable
      (fun w : ParabolicPoint => pressureP3 η u c w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    exact hR3.aestronglyMeasurable.restrict.congr hQ3.symm
  have hP4 : AEStronglyMeasurable
      (fun w : ParabolicPoint => pressureP4 η u c w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    exact hR4.aestronglyMeasurable.restrict.congr hQ4.symm
  have hP5 : AEStronglyMeasurable
      (fun w : ParabolicPoint => pressureP5 η p w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    exact hR5.aestronglyMeasurable.restrict.congr hQ5.symm
  have hP6 : AEStronglyMeasurable
      (fun w : ParabolicPoint => pressureP6 η p w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    exact hR6.aestronglyMeasurable.restrict.congr hQ6.symm
  let R1 : ParabolicPoint → ℝ := fun w =>
    η w.1 * pm (w.1, w.2) -
      (R2 w + R3 w + R4 w + R5 w + R6 w + R7 w + R8 w)
  have hR1 : AEMeasurable R1 volume := by
    dsimp [R1]
    fun_prop
  have hpQ : (fun w : ParabolicPoint => p w) =ᵐ[
      volume.restrict (parabolicCylinder z.1 z.2 ρ)]
      (fun w : ParabolicPoint => pm w) := by
    change p =ᵐ[volume.restrict (B ×ˢ T)] pm
    have hmeasureBT : volume.restrict (B ×ˢ T) =
        (volume.restrict B).prod (volume.restrict T) := by
      rw [Measure.prod_restrict B T,
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
    rw [hmeasureBT]
    exact hpBT
  have hP1ae : (fun w : ParabolicPoint => pressureP1 η u c p f w.2 w.1) =ᵐ[
      volume.restrict (parabolicCylinder z.1 z.2 ρ)] R1 := by
    filter_upwards [hpQ, hQ2, hQ3, hQ4, hQ5, hQ6, hQ7, hQ8]
      with w hp h2 h3 h4 h5 h6 h7 h8
    have hp' : p (w.1, w.2) = pm (w.1, w.2) := by
      change p w = pm w
      exact hp
    unfold pressureP1 R1
    rw [hp', h2, h3, h4, h5, h6, h7, h8]
  have hP1 : AEStronglyMeasurable
      (fun w : ParabolicPoint => pressureP1 η u c p f w.2 w.1)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    exact hR1.aestronglyMeasurable.restrict.congr hP1ae.symm
  refine ⟨B, T, η, c, rfl, rfl, rfl, ?_, hP1, hP2, hP3, hP4, hP5, hP6,
    hP7, hP8⟩
  intro s
  rfl

end CKN.Core.Step3
