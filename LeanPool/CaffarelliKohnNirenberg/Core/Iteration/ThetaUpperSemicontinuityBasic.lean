/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Iteration.UpperSemicontinuity
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Cylinders
public import Mathlib.MeasureTheory.Measure.ContinuousPreimage
public import Mathlib.MeasureTheory.Group.Prod

/-!
# Theta Upper Semicontinuity Basic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

/-- Continuous translation by the negative of a fixed parabolic point in product coordinates. -/
def subtractMapProd (z : ParabolicPoint) :
    C(Vec3 × ℝ, Vec3 × ℝ) :=
  ContinuousMap.mk (fun w : Vec3 × ℝ => (w.1 - z.1, w.2 - z.2))
    (by
      exact (continuous_fst.sub
        (continuous_const : Continuous (fun _ : Vec3 × ℝ => z.1))).prodMk
        (continuous_snd.sub
          (continuous_const : Continuous (fun _ : Vec3 × ℝ => z.2))))

private lemma continuous_subtractMapProd :
    Continuous (fun z : ParabolicPoint => subtractMapProd z) := by
  rw [continuous_iff_continuousAt]
  intro z
  apply (ContinuousMap.tendsto_nhds_compactOpen).2
  intro K hK U hU hmap
  let n : Set ((Vec3 × ℝ) × ParabolicPoint) :=
    (fun p => (p.1.1 - p.2.1, p.1.2 - p.2.2)) ⁻¹' U
  have hn : IsOpen n := by
    apply hU.preimage
    exact Continuous.prodMk
      ((continuous_fst.comp continuous_fst).sub
        (continuous_fst_parabolicPoint.comp continuous_snd))
      ((continuous_snd.comp continuous_fst).sub
        (continuous_snd_parabolicPoint.comp continuous_snd))
  have hprod : K ×ˢ ({z} : Set ParabolicPoint) ⊆ n := by
    intro p hp
    have hpz : p.2 = z := by simpa using hp.2
    change (p.1.1 - p.2.1, p.1.2 - p.2.2) ∈ U
    rw [hpz]
    have hm := hmap hp.1
    change (p.1.1 - z.1, p.1.2 - z.2) ∈ U at hm
    exact hm
  obtain ⟨u, v, hu, hv, hKu, hzv, huv⟩ :=
    generalized_tube_lemma hK isCompact_singleton hn hprod
  have hz : z ∈ v := hzv (by simp)
  have hev : ∀ᶠ z' in 𝓝 z, z' ∈ v := hv.mem_nhds hz
  filter_upwards [hev] with z' hz'
  intro x hx
  change (x, z') ∈ n
  exact huv (show (x, z') ∈ u ×ˢ v from ⟨hKu hx, hz'⟩)

private lemma subtractMapProd_preimage_cylinder (z : ParabolicPoint) (r : ℝ) :
    (subtractMapProd z ⁻¹' (parabolicCylinder (0 : Vec3) 0 r)) =
      parabolicCylinder z.1 z.2 r := by
  ext w
  change ((w.1 - z.1, w.2 - z.2) ∈ vec3Ball (0 : Vec3) r ×ˢ Ioc (0 - r ^ 2) 0) ↔
    w ∈ vec3Ball z.1 r ×ˢ Ioc (z.2 - r ^ 2) z.2
  simp only [Set.mem_prod, mem_vec3Ball, mem_Ioc]
  constructor
  · rintro ⟨hw, hlow, hupp⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hw
    · linarith only [hlow]
    · linarith only [hupp]
  · rintro ⟨hw, hlow, hupp⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hw
    · linarith only [hlow]
    · linarith only [hupp]

private lemma setIntegral_tendsto_of_symmDiff
    {g : ParabolicPoint → ℝ} {s : ParabolicPoint → Set ParabolicPoint}
    {z₀ : ParabolicPoint} (hg : Integrable g volume)
    (hs : ∀ z, MeasurableSet (s z))
    (hsm : Tendsto (fun z => volume (symmDiff (s z) (s z₀))) (𝓝 z₀) (𝓝 0)) :
    Tendsto (fun z => ∫ x in s z, g x) (𝓝 z₀) (𝓝 (∫ x in s z₀, g x)) := by
  let F : ParabolicPoint → ParabolicPoint → ℝ := fun z x => (s z).indicator g x
  have hFi : ∀ᶠ z in 𝓝 z₀, Integrable (F z) volume := by
    filter_upwards [] with z
    exact (integrable_indicator_iff (hs z)).2 hg.integrableOn
  have hdiff : Tendsto
      (fun z => ∫⁻ x, ‖F z x - F z₀ x‖ₑ) (𝓝 z₀) (𝓝 0) := by
    have hset := MeasureTheory.tendsto_setLIntegral_zero
      (ne_of_lt hg.norm.hasFiniteIntegral) hsm
    apply hset.congr'
    filter_upwards [] with z
    rw [← lintegral_indicator ((hs z).symmDiff (hs z₀))]
    apply lintegral_congr
    intro x
    by_cases hz : x ∈ s z <;> by_cases hz₀ : x ∈ s z₀ <;>
      simp [F, Set.indicator_of_mem, hz, hz₀, Set.mem_symmDiff]
  have hres := tendsto_setIntegral_of_L1 (F z₀)
    (hg.aestronglyMeasurable.indicator (hs z₀)) hFi hdiff Set.univ
  convert hres using 1
  · funext z
    simp only [Measure.restrict_univ]
    rw [integral_indicator (hs z)]
  · simp only [Measure.restrict_univ]
    rw [integral_indicator (hs z₀)]

private lemma cylinder_measurable (z : ParabolicPoint) {r : ℝ} :
    MeasurableSet (parabolicCylinder z.1 z.2 r) := by
  rw [parabolicCylinder]
  exact (vec3Ball_measurable _ _).prod measurableSet_Ioc

private lemma cylinder_integral_tendsto
    {g : ParabolicPoint → ℝ} {z₀ : ParabolicPoint} {r : ℝ}
    (hg : Integrable g volume) :
    Tendsto (fun z => ∫ x in parabolicCylinder z.1 z.2 r, g x)
      (𝓝 z₀) (𝓝 (∫ x in parabolicCylinder z₀.1 z₀.2 r, g x)) := by
  let s : ParabolicPoint → Set ParabolicPoint := fun z =>
    parabolicCylinder z.1 z.2 r
  have hs : ∀ z, MeasurableSet (s z) := fun z => cylinder_measurable z
  let S : Set (Vec3 × ℝ) := parabolicCylinder (0 : Vec3) 0 r
  have hS : MeasurableSet S := cylinder_measurable (0, 0)
  have hStop : volume S ≠ ⊤ :=
    (Integration.volume_parabolicCylinder_lt_top).ne
  have hsm0 := MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero
    (X := Vec3 × ℝ) (Y := Vec3 × ℝ)
    (continuous_subtractMapProd.tendsto z₀)
    (Filter.Eventually.of_forall (fun z => by
      have hprod := (measurePreserving_sub_right (volume : Measure Vec3) z.1).prod
        (measurePreserving_sub_right (volume : Measure ℝ) z.2)
      have hmp : MeasurePreserving (subtractMapProd z)
          (volume : Measure (Vec3 × ℝ)) (volume : Measure (Vec3 × ℝ)) := by
        change MeasurePreserving (fun w : Vec3 × ℝ => (w.1 - z.1, w.2 - z.2))
          (volume.prod volume) (volume.prod volume)
        convert hprod using 1
        all_goals rfl
      exact hmp))
    (by
      have hprod := (measurePreserving_sub_right (volume : Measure Vec3) z₀.1).prod
        (measurePreserving_sub_right (volume : Measure ℝ) z₀.2)
      have hmp : MeasurePreserving (subtractMapProd z₀)
          (volume : Measure (Vec3 × ℝ)) (volume : Measure (Vec3 × ℝ)) := by
        change MeasurePreserving (fun w : Vec3 × ℝ => (w.1 - z₀.1, w.2 - z₀.2))
          (volume.prod volume) (volume.prod volume)
        convert hprod using 1
        all_goals rfl
      exact hmp)
    hS.nullMeasurableSet hStop
  have hsm : Tendsto (fun z => volume (symmDiff (s z) (s z₀)))
      (𝓝 z₀) (𝓝 0) := by
    dsimp [s]
    have hsm0' := hsm0
    dsimp [S] at hsm0'
    convert hsm0' using 1
    funext z
    rw [subtractMapProd_preimage_cylinder z r,
      subtractMapProd_preimage_cylinder z₀ r]
    rfl
  exact setIntegral_tendsto_of_symmDiff hg hs hsm

private lemma euclidean_sq_le_three_sup_sq (v : Vec3) :
    vec3EuclideanNorm v ^ 2 ≤ 3 * ‖v‖ ^ 2 := by
  rw [show vec3EuclideanNorm v ^ 2 = ∑ i, v i ^ 2 by
    rw [vec3EuclideanNorm, Real.sq_sqrt]
    exact Finset.sum_nonneg (fun i _hi => sq_nonneg (v i))]
  rw [show (3 : ℝ) * ‖v‖ ^ 2 = ∑ _i : Fin 3, ‖v‖ ^ 2 by simp]
  apply Finset.sum_le_sum
  intro i hi
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v i) 2


lemma time_slice_energy_eq_ofReal
    {u : ParabolicPoint → Vec3} {x : Vec3} {r s : ℝ}
    (hInt : IntegrableOn
      (fun y : Vec3 => (vec3EuclideanNorm (u (y, s))) ^ 2)
      (vec3Ball x r) volume) :
    ENNReal.ofReal (∫ y in vec3Ball x r,
      (vec3EuclideanNorm (u (y, s))) ^ 2) =
      timeSliceBallEnergy x r s (fun w => vec3EuclideanNorm (u w)) := by
  have hmeas := hInt.aestronglyMeasurable
  have hnonneg : ∀ᵐ y ∂volume.restrict (vec3Ball x r),
      0 ≤ (vec3EuclideanNorm (u (y, s))) ^ 2 :=
    Filter.Eventually.of_forall (fun y => sq_nonneg _)
  have hfin : (∫⁻ y in vec3Ball x r,
      ENNReal.ofReal ((vec3EuclideanNorm (u (y, s))) ^ 2)) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mpr hInt
  have hlin : (∫⁻ y in vec3Ball x r,
      ENNReal.ofReal ((vec3EuclideanNorm (u (y, s))) ^ 2)) =
      timeSliceBallEnergy x r s (fun w => vec3EuclideanNorm (u w)) := by
    unfold timeSliceBallEnergy
    apply lintegral_congr
    intro y
    rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _),
      ← Real.rpow_natCast,
      ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _)
        (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hfinS : timeSliceBallEnergy x r s
      (fun w => vec3EuclideanNorm (u w)) ≠ ⊤ := by
    rw [← hlin]
    exact hfin
  rw [setIntegral_eq_toReal_setLIntegral_of_nonneg hInt hnonneg,
    hlin, ENNReal.ofReal_toReal hfinS]

lemma velocity_slice_integrable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    {x : Vec3} {r : ℝ} (hball : vec3Ball x r ⊆ Ω') :
    ∀ᵐ s ∂volume.restrict J,
      IntegrableOn (fun y : Vec3 => (vec3EuclideanNorm (u (y, s))) ^ 2)
        (vec3Ball x r) volume := by
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox
  have hmem := slice_memLp_ae_of_sws hsol hbox
  filter_upwards [hmem] with s hs
  have hu' := hs.1.aestronglyMeasurable
  have hsup : Integrable (fun y : Vec3 => ‖u (y, s)‖ ^ (2 : ℕ))
      (volume.restrict Ω') :=
    (memLp_two_iff_integrable_sq_norm hu').mp hs.1
  have hmeas : AEStronglyMeasurable
      (fun y : Vec3 => (vec3EuclideanNorm (u (y, s))) ^ (2 : ℕ))
      (volume.restrict Ω') := by
    have hcont : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact (hcont.comp_aestronglyMeasurable hu').pow 2
  have hthree : Integrable (fun y : Vec3 => 3 * ‖u (y, s)‖ ^ (2 : ℕ))
      (volume.restrict Ω') := hsup.const_mul 3
  have heu : Integrable
      (fun y : Vec3 => (vec3EuclideanNorm (u (y, s))) ^ (2 : ℕ))
      (volume.restrict Ω') := by
    apply hthree.mono' hmeas
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact euclidean_sq_le_three_sup_sq _
  exact heu.mono_measure (Measure.restrict_mono hball le_rfl)


lemma alpha_sq_le_of_essSup
    {u : ParabolicPoint → Vec3} {z : ParabolicPoint}
    {x₀ : Vec3} {rho r a b : ℝ}
    (hrho : 0 < rho)
    (hball : vec3Ball z.1 rho ⊆ vec3Ball x₀ r)
    (hinterval : Ioc (z.2 - rho ^ 2) z.2 ⊆ Ioc a b)
    (hInt : ∀ᵐ s ∂volume.restrict (Ioc a b),
      IntegrableOn (fun y : Vec3 => (vec3EuclideanNorm (u (y, s))) ^ 2)
        (vec3Ball x₀ r) volume)
    (hfinite : essSup (timeSliceBallEnergy x₀ r ·
        (fun w => vec3EuclideanNorm (u w)))
        (volume.restrict (Ioc a b)) ≠ ⊤) :
    alpha u z rho ^ 2 ≤ rho⁻¹ *
      (essSup (fun s => ENNReal.ofReal
        (∫ y in vec3Ball x₀ r, (vec3EuclideanNorm (u (y, s))) ^ 2))
        (volume.restrict (Ioc a b))).toReal := by
  have hInt' := ae_restrict_of_ae_restrict_of_subset hinterval hInt
  have hmono := essSup_mono_measure_and_ae
    (μ := volume.restrict (Ioc (z.2 - rho ^ 2) z.2))
    (ν := volume.restrict (Ioc a b))
    (Measure.restrict_mono hinterval le_rfl) (by
      filter_upwards [hInt'] with s hs
      have hreal : ∫ y in vec3Ball z.1 rho,
          (vec3EuclideanNorm (u (y, s))) ^ 2 ≤
          ∫ y in vec3Ball x₀ r,
            (vec3EuclideanNorm (u (y, s))) ^ 2 := by
        exact setIntegral_mono_set hs
          (Filter.Eventually.of_forall (fun y => sq_nonneg _))
          (Filter.Eventually.of_forall (fun y hy => hball hy))
      exact ENNReal.ofReal_le_ofReal hreal)
  have hIntMoving : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - rho ^ 2) z.2),
      IntegrableOn (fun y : Vec3 => (vec3EuclideanNorm (u (y, s))) ^ 2)
        (vec3Ball z.1 rho) volume := by
    filter_upwards [hInt'] with s hs
    have hs' : Integrable
        (fun y : Vec3 => (vec3EuclideanNorm (u (y, s))) ^ 2)
        (volume.restrict (vec3Ball x₀ r)) := hs
    exact hs'.mono_measure (Measure.restrict_mono hball le_rfl)
  have hEqMoving : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - rho ^ 2) z.2),
      timeSliceBallEnergy z.1 rho s (fun w => vec3EuclideanNorm (u w)) =
        ENNReal.ofReal (∫ y in vec3Ball z.1 rho,
          (vec3EuclideanNorm (u (y, s))) ^ 2) := by
    filter_upwards [hIntMoving] with s hs
    exact (time_slice_energy_eq_ofReal hs).symm
  have hEqFixed : ∀ᵐ s ∂volume.restrict (Ioc a b),
      timeSliceBallEnergy x₀ r s (fun w => vec3EuclideanNorm (u w)) =
        ENNReal.ofReal (∫ y in vec3Ball x₀ r,
          (vec3EuclideanNorm (u (y, s))) ^ 2) := by
    filter_upwards [hInt] with s hs
    exact (time_slice_energy_eq_ofReal hs).symm
  have htime : timeSliceEnergyEssSup z.1 z.2 rho
      (fun w => vec3EuclideanNorm (u w)) ≤
      essSup (timeSliceBallEnergy x₀ r ·
        (fun w => vec3EuclideanNorm (u w)))
        (volume.restrict (Ioc a b)) := by
    unfold timeSliceEnergyEssSup
    rw [essSup_congr_ae hEqMoving]
    calc
      _ ≤ essSup (fun s => ENNReal.ofReal
          (∫ y in vec3Ball x₀ r,
            (vec3EuclideanNorm (u (y, s))) ^ 2))
          (volume.restrict (Ioc a b)) := hmono
      _ = _ := (essSup_congr_ae hEqFixed).symm
  have hsq := alpha_sq_eq u z rho hrho
  have hto : (timeSliceEnergyEssSup z.1 z.2 rho
        (fun w => vec3EuclideanNorm (u w))).toReal ≤
      (essSup (timeSliceBallEnergy x₀ r ·
        (fun w => vec3EuclideanNorm (u w)))
        (volume.restrict (Ioc a b))).toReal := by
    apply ENNReal.toReal_mono hfinite
    exact htime
  have hEssEq := essSup_congr_ae hEqFixed
  rw [hsq]
  calc
    rho⁻¹ * (timeSliceEnergyEssSup z.1 z.2 rho
        (fun w => vec3EuclideanNorm (u w))).toReal ≤
        rho⁻¹ * (essSup (timeSliceBallEnergy x₀ r ·
          (fun w => vec3EuclideanNorm (u w)))
          (volume.restrict (Ioc a b))).toReal :=
      mul_le_mul_of_nonneg_left hto (by positivity)
    _ = rho⁻¹ * (essSup (fun s => ENNReal.ofReal
        (∫ y in vec3Ball x₀ r,
          (vec3EuclideanNorm (u (y, s))) ^ 2))
          (volume.restrict (Ioc a b))).toReal := by
      rw [hEssEq]

lemma eventually_cylinder_subset_of_open
    {z₀ : ParabolicPoint} {r : ℝ} {U : Set ParabolicPoint}
    (hr : 0 < r) (hU : IsOpen U)
    (hK : closure (parabolicCylinder z₀.1 z₀.2 r) ⊆ U) :
    ∀ᶠ z in 𝓝 z₀, parabolicCylinder z.1 z.2 r ⊆ U := by
  have hsp : IsCompact {y : Vec3 | vec3EuclideanNorm (y - z₀.1) ≤ r} := by
    have hclosed : IsClosed {y : Vec3 | vec3EuclideanNorm (y - z₀.1) ≤ r} := by
      have hc : Continuous (fun y : Vec3 => vec3EuclideanNorm (y - z₀.1)) := by
        unfold vec3EuclideanNorm
        fun_prop
      exact isClosed_Iic.preimage hc
    have hsub : {y : Vec3 | vec3EuclideanNorm (y - z₀.1) ≤ r} ⊆
        Metric.closedBall z₀.1 r := by
      intro y hy
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hr0 : 0 ≤ r := (vec3EuclideanNorm_nonneg _).trans hy
      rw [pi_norm_le_iff_of_nonneg hr0]
      intro i
      change |(y - z₀.1) i| ≤ r
      apply (Real.abs_le_sqrt ?_).trans hy
      exact Finset.single_le_sum (fun j _hj => sq_nonneg ((y - z₀.1) j))
        (Finset.mem_univ i)
    exact (isCompact_closedBall z₀.1 r).of_isClosed_subset hclosed hsub
  have hKc : IsCompact (closure (parabolicCylinder z₀.1 z₀.2 r)) := by
    rw [closure_parabolicCylinder hr]
    change IsCompact (parabolicHomeomorph ⁻¹'
      ({y : Vec3 | vec3EuclideanNorm (y - z₀.1) ≤ r} ×ˢ Icc
        (z₀.2 - r ^ 2) z₀.2))
    apply parabolicHomeomorph.isCompact_preimage.2
    exact hsp.prod isCompact_Icc
  let n : Set (ParabolicPoint × ParabolicPoint) :=
    (fun p => (p.1.1 + p.2.1 - z₀.1, p.1.2 + p.2.2 - z₀.2)) ⁻¹' U
  have hn : IsOpen n := by
    apply hU.preimage
    exact continuous_prod_to_parabolicPoint.comp
      (Continuous.prodMk
        (((continuous_fst_parabolicPoint.comp continuous_fst).add
          (continuous_fst_parabolicPoint.comp continuous_snd)).sub
            (continuous_const : Continuous
              (fun _ : ParabolicPoint × ParabolicPoint => z₀.1)))
        (((continuous_snd_parabolicPoint.comp continuous_fst).add
          (continuous_snd_parabolicPoint.comp continuous_snd)).sub
            (continuous_const : Continuous
              (fun _ : ParabolicPoint × ParabolicPoint => z₀.2))))
  have hprod : closure (parabolicCylinder z₀.1 z₀.2 r) ×ˢ
      ({z₀} : Set ParabolicPoint) ⊆ n := by
    intro p hp
    have hpz : p.2 = z₀ := by simpa using hp.2
    change (p.1.1 + p.2.1 - z₀.1, p.1.2 + p.2.2 - z₀.2) ∈ U
    rw [hpz]
    have hk := hK hp.1
    change (p.1.1, p.1.2) ∈ U at hk
    simpa [sub_eq_add_neg, add_left_comm, add_comm] using hk
  obtain ⟨u, v, hu, hv, hKu, hzv, huv⟩ :=
    generalized_tube_lemma hKc isCompact_singleton hn hprod
  have hz : z₀ ∈ v := hzv (by simp)
  have hev : ∀ᶠ z in 𝓝 z₀, z ∈ v := hv.mem_nhds hz
  filter_upwards [hev] with z hzv'
  intro x hx
  let w : ParabolicPoint :=
    (x.1 - z.1 + z₀.1, x.2 - z.2 + z₀.2)
  have hw : w ∈ closure (parabolicCylinder z₀.1 z₀.2 r) := by
    have himage : parabolicTranslate (z₀.1 - z.1) (z₀.2 - z.2) ''
        parabolicCylinder z.1 z.2 r = parabolicCylinder z₀.1 z₀.2 r := by
      rw [parabolicCylinder_translate]
      congr 2 <;> simp [sub_eq_add_neg, add_left_comm, add_comm]
    have hw' : parabolicTranslate (z₀.1 - z.1) (z₀.2 - z.2) x ∈
        parabolicCylinder z₀.1 z₀.2 r := by
      rw [← himage]
      exact ⟨x, hx, rfl⟩
    exact subset_closure (by simpa [w, parabolicTranslate,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hw')
  have h := huv (show (w, z) ∈ u ×ˢ v from ⟨hKu hw, hzv'⟩)
  change (w.1 + z.1 - z₀.1, w.2 + z.2 - z₀.2) ∈ U at h
  have hxU : (x.1, x.2) ∈ U := by
    simpa [w, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  change (x.1, x.2) ∈ U
  exact hxU

private lemma integrableOn_of_lintegral_ofReal
    {g : ParabolicPoint → ℝ} {K : Set ParabolicPoint}
    (hmeas : AEStronglyMeasurable g (volume.restrict K))
    (hnonneg : ∀ᵐ w ∂volume.restrict K, 0 ≤ g w)
    (hfin : (∫⁻ w in K, ENNReal.ofReal (g w)) ≠ ⊤) :
    IntegrableOn g K volume :=
  (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp hfin

lemma gradient_integrable_of_meas
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {K B : Set ParabolicPoint}
    (hmeasB : AEStronglyMeasurable (fun w => spatialGradientSq u Du w)
      (volume.restrict B)) (hKB : K ⊆ B)
    (hfin : (∫⁻ w in K, ENNReal.ofReal (spatialGradientSq u Du w)) ≠ ⊤) :
    IntegrableOn (fun w => spatialGradientSq u Du w) K volume := by
  have hmeas := hmeasB.mono_measure (Measure.restrict_mono hKB le_rfl)
  have hnonneg : ∀ᵐ w ∂volume.restrict K,
      0 ≤ spatialGradientSq u Du w :=
    Filter.Eventually.of_forall (fun w => by unfold spatialGradientSq; positivity)
  exact integrableOn_of_lintegral_ofReal hmeas hnonneg hfin

lemma pressure_integrable_of_meas
    {p : ParabolicPoint → ℝ} {K B : Set ParabolicPoint}
    (hmeasB : AEStronglyMeasurable (fun w => |p w| ^ (3 / 2 : ℝ))
      (volume.restrict B)) (hKB : K ⊆ B)
    (hfin : (∫⁻ w in K, ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) ≠ ⊤) :
    IntegrableOn (fun w => |p w| ^ (3 / 2 : ℝ)) K volume := by
  have hmeas := hmeasB.mono_measure (Measure.restrict_mono hKB le_rfl)
  have hnonneg : ∀ᵐ w ∂volume.restrict K,
      0 ≤ |p w| ^ (3 / 2 : ℝ) :=
    Filter.Eventually.of_forall (fun w => by positivity)
  exact integrableOn_of_lintegral_ofReal hmeas hnonneg hfin

lemma euclidean_triangle (a b : Vec3) :
    vec3EuclideanNorm (a + b) ≤ vec3EuclideanNorm a + vec3EuclideanNorm b := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
    vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
  exact norm_add_le _ _

lemma mem_euclideanClosedBall_of_vec3Norm_le
    {x y : Vec3} {R : ℝ} (hR : 0 ≤ R)
    (hxy : vec3EuclideanNorm (y - x) ≤ R) :
    y ∈ euclideanClosedBall x R := by
  apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR).2
  have heq : vecEuclideanNorm (y - x) = vec3EuclideanNorm (y - x) := by
    simp only [vecEuclideanNorm, vecNormSq, vecDot, Pi.sub_apply, vec3EuclideanNorm]
    apply congrArg Real.sqrt
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  exact hxy

lemma cylinder_integral_tendsto_of_open
    {g : ParabolicPoint → ℝ} {z₀ : ParabolicPoint} {r : ℝ}
    {G : Set ParabolicPoint} (hG : IsOpen G)
    (hr : 0 < r)
    (hK : closure (parabolicCylinder z₀.1 z₀.2 r) ⊆ G)
    (hg : IntegrableOn g G volume) :
    Tendsto (fun z => ∫ x in parabolicCylinder z.1 z.2 r, g x)
      (𝓝 z₀) (𝓝 (∫ x in parabolicCylinder z₀.1 z₀.2 r, g x)) := by
  have hGm : MeasurableSet G := hG.measurableSet
  let gb : ParabolicPoint → ℝ := G.indicator g
  have hgb : Integrable gb volume :=
    (integrable_indicator_iff hGm).2 hg
  have ht := cylinder_integral_tendsto (z₀ := z₀) (r := r) hgb
  have hev := eventually_cylinder_subset_of_open hr hG hK
  have heq : ∀ᶠ z in 𝓝 z₀,
      (∫ x in parabolicCylinder z.1 z.2 r, gb x) =
        ∫ x in parabolicCylinder z.1 z.2 r, g x := by
    filter_upwards [hev] with z hz
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (cylinder_measurable z (r := r))] with x hx
    change (G.indicator g) x = g x
    exact Set.indicator_of_mem (hz hx) g
  have heq0 : (∫ x in parabolicCylinder z₀.1 z₀.2 r, gb x) =
      ∫ x in parabolicCylinder z₀.1 z₀.2 r, g x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem
      (cylinder_measurable z₀ (r := r))] with x hx
    change (G.indicator g) x = g x
    exact Set.indicator_of_mem
      (hK (parabolicCylinder_subset_closure _ _ _ hx)) g
  have ht' := ht.congr' heq
  rw [heq0] at ht'
  exact ht'

end CKN
