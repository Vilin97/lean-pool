/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
import LeanPool.HardSphereNBC.HardSphereCompound
import LeanPool.HardSphereNBC.HardSphereTreeDifference
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace HsVirial

open Set
open Metric
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

abbrev HS3 := HSPosition 3
abbrev HS2 := HSPosition 2

def testSplit3 : HS3 ≃ᵐ (ℝ × HS2) := by
  let e0 := (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm
  let e1 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  let e2 := MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))
  exact e0.trans (e1.trans e2)

lemma testMeasurePreserving_split3 : MeasurePreserving testSplit3 := by
  let e0 := (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm
  let e1 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  let e2 := MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))
  have h0 : MeasurePreserving e0 :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have h1 : MeasurePreserving e1 :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h2a : MeasurePreserving (MeasurableEquiv.refl ℝ) :=
    MeasurePreserving.id volume
  have h2b : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) :=
    PiLp.volume_preserving_toLp (Fin 2)
  have h2 : MeasurePreserving e2 := h2a.prod h2b
  change MeasurePreserving (e0.trans (e1.trans e2)) volume volume
  exact h0.trans (h1.trans h2)

def testAxis3 (s : ℝ) (y : HS2) : HS3 := testSplit3.symm (s, y)

lemma testAxis3_apply (s : ℝ) (y : HS2) :
    testAxis3 s y = MeasurableEquiv.toLp 2 (Fin 3 → ℝ)
      (fun i => if i = 0 then s else
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm y (Fin.predAbove 0 i)) := by
  simp [testAxis3, testSplit3, MeasurableEquiv.trans_apply,
    MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodCongr,
    Fin.consEquiv]
  funext i
  fin_cases i <;> rfl

lemma testToLp_apply (z : Fin 3 → ℝ) (i : Fin 3) :
    ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) z).ofLp i = z i := by
  rfl

lemma testNorm_axis3_sq (s : ℝ) (y : HS2) :
    ‖testAxis3 s y‖ ^ 2 = s ^ 2 + ‖y‖ ^ 2 := by
  rw [testAxis3_apply, EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt]
  · simp only [Fin.sum_univ_succ]
    simp only [testToLp_apply]
    rw [EuclideanSpace.norm_eq y, Real.sq_sqrt]
    · simp [Fin.sum_univ_succ]
    · positivity
  · positivity

lemma testNorm_axis3 (s : ℝ) (y : HS2) (_hs : 0 ≤ s) :
    ‖testAxis3 s y‖ ^ 2 = s ^ 2 + ‖y‖ ^ 2 := by
  exact testNorm_axis3_sq s y

lemma testAxis3_sub_axis (t s : ℝ) (y : HS2) :
    testAxis3 t y - testAxis3 s 0 = testAxis3 (t - s) y := by
  apply PiLp.ext
  intro i
  change (testAxis3 t y).ofLp i - (testAxis3 s 0).ofLp i =
    (testAxis3 (t - s) y).ofLp i
  rw [testAxis3_apply, testAxis3_apply, testAxis3_apply]
  fin_cases i <;> simp

def testAxisIntersection (s : ℝ) : Set (ℝ × HS2) :=
  {p | p.1 ^ 2 + ‖p.2‖ ^ 2 < 1 ∧
    (p.1 - s) ^ 2 + ‖p.2‖ ^ 2 < 1}

lemma measurableSet_testAxisIntersection (s : ℝ) :
    MeasurableSet (testAxisIntersection s) := by
  rw [show testAxisIntersection s =
      {p : ℝ × HS2 | p.1 ^ 2 + ‖p.2‖ ^ 2 < (1 : ℝ)} ∩
        {p : ℝ × HS2 | (p.1 - s) ^ 2 + ‖p.2‖ ^ 2 < (1 : ℝ)} by
    ext p
    simp [testAxisIntersection]]
  have h0 : Measurable (fun p : ℝ × HS2 => p.1 ^ 2 + ‖p.2‖ ^ 2) := by
    fun_prop
  have h1 : Measurable
      (fun p : ℝ × HS2 => (p.1 - s) ^ 2 + ‖p.2‖ ^ 2) := by
    fun_prop
  exact (MeasurableSet.preimage measurableSet_Iio h0).inter
    (MeasurableSet.preimage measurableSet_Iio h1)

def testSectionRadius (s t : ℝ) : ℝ :=
  min (Real.sqrt (max 0 (1 - t ^ 2)))
    (Real.sqrt (max 0 (1 - (t - s) ^ 2)))

lemma testSectionRadius_sq (s t : ℝ) :
    testSectionRadius s t ^ 2 =
      min (max 0 (1 - t ^ 2)) (max 0 (1 - (t - s) ^ 2)) := by
  unfold testSectionRadius
  by_cases h : Real.sqrt (max 0 (1 - t ^ 2)) ≤
      Real.sqrt (max 0 (1 - (t - s) ^ 2))
  · have h' : max 0 (1 - t ^ 2) ≤ max 0 (1 - (t - s) ^ 2) := by
      have hsqrt := (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mpr h
      simpa [Real.sq_sqrt', max_comm] using hsqrt
    rw [min_eq_left h, Real.sq_sqrt', min_eq_left h']
    exact max_eq_left (le_max_left 0 _)
  · have h' : Real.sqrt (max 0 (1 - (t - s) ^ 2)) ≤
        Real.sqrt (max 0 (1 - t ^ 2)) := le_of_not_ge h
    have h'' : max 0 (1 - (t - s) ^ 2) ≤ max 0 (1 - t ^ 2) := by
      have hsqrt := (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mpr h'
      simpa [Real.sq_sqrt', max_comm] using hsqrt
    rw [min_eq_right h', Real.sq_sqrt', min_eq_right h'']
    exact max_eq_left (le_max_left 0 _)

lemma testSectionRadius_sq_eq_right (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hlo : s - 1 < t) (hmid : t ≤ s / 2) :
    testSectionRadius s t ^ 2 = 1 - (t - s) ^ 2 := by
  have htlow : -1 < t := by linarith
  have hthigh : t ≤ 1 := by linarith
  have htslow : -1 < t - s := by linarith
  have htshigh : t - s ≤ 1 := by linarith
  have hA : 0 ≤ 1 - t ^ 2 := by
    have hprod : 0 ≤ (t + 1) * (1 - t) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hB : 0 ≤ 1 - (t - s) ^ 2 := by
    have hprod : 0 ≤ (t - s + 1) * (1 - (t - s)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hBA : 1 - (t - s) ^ 2 ≤ 1 - t ^ 2 := by
    have hprod : 0 ≤ s * (s - 2 * t) :=
      mul_nonneg hs0 (by linarith)
    nlinarith
  rw [testSectionRadius_sq, max_eq_right hA, max_eq_right hB,
    min_eq_right hBA]

lemma testSectionRadius_sq_eq_left (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hmid : s / 2 < t) (htop : t ≤ 1) :
    testSectionRadius s t ^ 2 = 1 - t ^ 2 := by
  have htlow : -1 ≤ t := by linarith
  have htslow : -1 ≤ t - s := by linarith
  have htshigh : t - s ≤ 1 := by linarith
  have hA : 0 ≤ 1 - t ^ 2 := by
    have hprod : 0 ≤ (t + 1) * (1 - t) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hB : 0 ≤ 1 - (t - s) ^ 2 := by
    have hprod : 0 ≤ (t - s + 1) * (1 - (t - s)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hAB : 1 - t ^ 2 ≤ 1 - (t - s) ^ 2 := by
    have hprod : s * (s - 2 * t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs0 (by linarith)
    nlinarith
  rw [testSectionRadius_sq, max_eq_right hA, max_eq_right hB,
    min_eq_left hAB]

lemma testSectionRadius_sq_eq_zero_of_le (s t : ℝ) (h : t ≤ s - 1) :
    testSectionRadius s t ^ 2 = 0 := by
  have hB : 1 - (t - s) ^ 2 ≤ 0 := by
    have hprod : (t - s + 1) * (1 - (t - s)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    nlinarith
  rw [testSectionRadius_sq, max_eq_left hB]
  simp

lemma testSectionRadius_sq_eq_zero_of_gt (s t : ℝ) (h : 1 < t) :
    testSectionRadius s t ^ 2 = 0 := by
  have hA : 1 - t ^ 2 ≤ 0 := by
    have hprod : (t + 1) * (1 - t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    nlinarith
  rw [testSectionRadius_sq, max_eq_left hA]
  simp

lemma testSectionRadius_sq_eq_piecewise (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    testSectionRadius s t ^ 2 =
      (Ioc (s - 1) (s / 2)).indicator (fun u : ℝ => 1 - (u - s) ^ 2) t +
      (Ioc (s / 2) 1).indicator (fun u : ℝ => 1 - u ^ 2) t := by
  by_cases hleft : t ∈ Ioc (s - 1) (s / 2)
  · rw [Set.indicator_of_mem hleft]
    have hright : t ∉ Ioc (s / 2) 1 := by
      intro hright
      exact (not_lt_of_ge hleft.2) hright.1
    rw [Set.indicator_of_notMem hright, add_zero]
    exact testSectionRadius_sq_eq_right s t hs0 hs1 hleft.1 hleft.2
  · by_cases hright : t ∈ Ioc (s / 2) 1
    · rw [Set.indicator_of_notMem hleft, zero_add,
        Set.indicator_of_mem hright]
      exact testSectionRadius_sq_eq_left s t hs0 hs1 hright.1 hright.2
    · have hleft' : ¬(s - 1 < t ∧ t ≤ s / 2) := by
        simpa only [mem_Ioc] using hleft
      have hright' : ¬(s / 2 < t ∧ t ≤ 1) := by
        simpa only [mem_Ioc] using hright
      by_cases hlow : t ≤ s - 1
      · rw [Set.indicator_of_notMem hleft,
          Set.indicator_of_notMem hright, add_zero]
        exact testSectionRadius_sq_eq_zero_of_le s t hlow
      · have hmid : s / 2 < t := by
          by_contra hmid
          apply hleft'
          exact ⟨by linarith, le_of_not_gt hmid⟩
        have htop : 1 < t := by
          by_contra htop
          apply hright'
          exact ⟨hmid, le_of_not_gt htop⟩
        rw [Set.indicator_of_notMem hleft,
          Set.indicator_of_notMem hright, add_zero]
        exact testSectionRadius_sq_eq_zero_of_gt s t htop

lemma testSectionRadius_sq_integral (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ t : ℝ, testSectionRadius s t ^ 2) =
      (∫ t in (s - 1)..(s / 2), 1 - (t - s) ^ 2) +
      (∫ t in (s / 2)..1, 1 - t ^ 2) := by
  let f₀ : ℝ → ℝ := (Ioc (s - 1) (s / 2)).indicator
    (fun t => 1 - (t - s) ^ 2)
  let f₁ : ℝ → ℝ := (Ioc (s / 2) 1).indicator
    (fun t => 1 - t ^ 2)
  have hf₀ : Integrable f₀ := by
    apply (Continuous.continuousOn (by fun_prop :
      Continuous (fun t : ℝ => 1 - (t - s) ^ 2))).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self |>.integrable_indicator
    exact measurableSet_Ioc
  have hf₁ : Integrable f₁ := by
    apply (Continuous.continuousOn (by fun_prop :
      Continuous (fun t : ℝ => 1 - t ^ 2))).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self |>.integrable_indicator
    exact measurableSet_Ioc
  have hpoint : ∀ t, testSectionRadius s t ^ 2 = f₀ t + f₁ t := by
    intro t
    exact testSectionRadius_sq_eq_piecewise s t hs0 hs1
  calc
    (∫ t : ℝ, testSectionRadius s t ^ 2) = ∫ t : ℝ, f₀ t + f₁ t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = (∫ t : ℝ, f₀ t) + ∫ t : ℝ, f₁ t := integral_add hf₀ hf₁
    _ = (∫ t in (s - 1)..(s / 2), 1 - (t - s) ^ 2) +
        (∫ t in (s / 2)..1, 1 - t ^ 2) := by
      congr 1
      · change (∫ t : ℝ, (Ioc (s - 1) (s / 2)).indicator
          (fun t => 1 - (t - s) ^ 2) t) = _
        rw [integral_indicator measurableSet_Ioc]
        exact (intervalIntegral.integral_of_le (by linarith [hs1])).symm
      · change (∫ t : ℝ, (Ioc (s / 2) 1).indicator
          (fun t => 1 - t ^ 2) t) = _
        rw [integral_indicator measurableSet_Ioc]
        exact (intervalIntegral.integral_of_le (by linarith [hs1])).symm

lemma testAxisIntersection_section_integral_eq_lens (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ t : ℝ, Real.pi * testSectionRadius s t ^ 2) =
      hardSphereLens s := by
  rw [integral_const_mul, testSectionRadius_sq_integral s hs0 hs1]
  have hshift :
      (∫ t in (s - 1)..(s / 2), 1 - (t - s) ^ 2) =
        ∫ t in (-1 : ℝ)..(-s / 2), 1 - t ^ 2 := by
     convert intervalIntegral.integral_comp_sub_right
       (f := fun t : ℝ => 1 - t ^ 2) s using 1; ring_nf
  rw [hshift]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_pow 2),
    intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_pow 2)]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const,
    integral_pow, integral_pow]
  rw [hardSphereLens_eq_polynomial]
  norm_num
  ring

lemma testMem_ball_sqrt_max_iff (t : ℝ) (z : HS2) :
    z ∈ ball (0 : HS2) (Real.sqrt (max 0 (1 - t ^ 2))) ↔
      t ^ 2 + ‖z‖ ^ 2 < 1 := by
  rw [mem_ball_iff_norm]
  simp only [sub_zero]
  by_cases h : 0 ≤ 1 - t ^ 2
  · rw [max_eq_right h, Real.lt_sqrt (norm_nonneg z)]
    constructor <;> intro hz <;> nlinarith
  · rw [max_eq_left (le_of_not_ge h), Real.sqrt_zero]
    constructor
    · intro hz
      linarith [norm_nonneg z]
    · intro hz
      nlinarith [sq_nonneg t, sq_nonneg ‖z‖]

lemma testAxisIntersection_section (s t : ℝ) :
    Prod.mk t ⁻¹' testAxisIntersection s =
      ball (0 : HS2) (testSectionRadius s t) := by
  ext z
  change (t ^ 2 + ‖z‖ ^ 2 < 1 ∧
    (t - s) ^ 2 + ‖z‖ ^ 2 < 1) ↔
    z ∈ ball (0 : HS2) (testSectionRadius s t)
  rw [testSectionRadius, mem_ball_iff_norm, sub_zero, lt_min_iff]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨by simpa only [sub_zero] using
        (mem_ball_iff_norm.mp ((testMem_ball_sqrt_max_iff t z).mpr h0)),
      by simpa only [sub_zero] using
        (mem_ball_iff_norm.mp ((testMem_ball_sqrt_max_iff (t - s) z).mpr h1))⟩
  · rintro ⟨h0, h1⟩
    exact ⟨(testMem_ball_sqrt_max_iff t z).mp
        (mem_ball_iff_norm.mpr (by simpa only [sub_zero] using h0)),
      (testMem_ball_sqrt_max_iff (t - s) z).mp
        (mem_ball_iff_norm.mpr (by simpa only [sub_zero] using h1))⟩

lemma testAxisIntersection_section_volume (s t : ℝ) :
    volume (Prod.mk t ⁻¹' testAxisIntersection s) =
      (ENNReal.ofReal (testSectionRadius s t)) ^ 2 * ENNReal.ofReal Real.pi := by
  rw [testAxisIntersection_section, EuclideanSpace.volume_ball_fin_two]

lemma testAxis3_split_apply (s : ℝ) (y : HS2) :
    testSplit3 (testAxis3 s y) = (s, y) := by
  simp [testAxis3]

lemma testAxisIntersection_image (s : ℝ) (_hs : 0 ≤ s) :
    testSplit3 '' (ball (0 : HS3) 1 ∩ ball (testAxis3 s 0) 1) =
      testAxisIntersection s := by
  ext p
  constructor
  · rintro ⟨y, hy, rfl⟩
    let t := (testSplit3 y).1
    let z := (testSplit3 y).2
    have hy_eq : testAxis3 t z = y := by
      simp [t, z, testAxis3]
    have hnorm0 : ‖y‖ < (1 : ℝ) := by
      simpa only [sub_zero] using (mem_ball_iff_norm.mp hy.1)
    have hdiff : y - testAxis3 s 0 = testAxis3 (t - s) z := by
      rw [← hy_eq]
      exact testAxis3_sub_axis t s z
    have hnorm1 : ‖y - testAxis3 s 0‖ < (1 : ℝ) := by
      exact mem_ball_iff_norm.mp hy.2
    have hnorm0' : ‖testAxis3 t z‖ < (1 : ℝ) := by
      simpa [hy_eq] using hnorm0
    have hnorm1' : ‖testAxis3 (t - s) z‖ < (1 : ℝ) := by
      rw [← hdiff]
      exact hnorm1
    have hsq0 : ‖testAxis3 t z‖ ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).mpr hnorm0'
    have hsq1 : ‖testAxis3 (t - s) z‖ ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).mpr hnorm1'
    change t ^ 2 + ‖z‖ ^ 2 < 1 ∧ (t - s) ^ 2 + ‖z‖ ^ 2 < 1
    constructor
    · nlinarith [testNorm_axis3_sq t z]
    · nlinarith [testNorm_axis3_sq (t - s) z]
  · intro hp
    let y := testSplit3.symm p
    have hy_split : testSplit3 y = p := by
      simp [y]
    have hy0 : y ∈ ball (0 : HS3) 1 := by
      rw [mem_ball_iff_norm]
      simp only [sub_zero]
      have hnorm : ‖y‖ ^ 2 < (1 : ℝ) := by
        rw [show y = testAxis3 p.1 p.2 by simp [y, testAxis3]]
        rw [testNorm_axis3_sq]
        exact hp.1
      nlinarith [norm_nonneg y]
    have hdiff : y - testAxis3 s 0 = testAxis3 (p.1 - s) p.2 := by
      rw [show y = testAxis3 p.1 p.2 by simp [y, testAxis3]]
      exact testAxis3_sub_axis p.1 s p.2
    have hy1 : y ∈ ball (testAxis3 s 0) 1 := by
      change ‖y - testAxis3 s 0‖ < (1 : ℝ)
      have hnorm : ‖y - testAxis3 s 0‖ ^ 2 < (1 : ℝ) := by
        rw [hdiff, testNorm_axis3_sq]
        exact hp.2
      nlinarith [norm_nonneg (y - testAxis3 s 0)]
    refine ⟨y, ⟨hy0, hy1⟩, ?_⟩
    exact hy_split

lemma testAxisIntersection_volume_as_lintegral (s : ℝ) (hs : 0 ≤ s) :
    volume (ball (0 : HS3) 1 ∩ ball (testAxis3 s 0) 1) =
      ∫⁻ t : ℝ, volume (Prod.mk t ⁻¹' testAxisIntersection s) := by
  have hU : MeasurableSet (ball (0 : HS3) 1 ∩ ball (testAxis3 s 0) 1) :=
    measurableSet_ball.inter measurableSet_ball
  calc
    volume (ball (0 : HS3) 1 ∩ ball (testAxis3 s 0) 1) =
        volume (testSplit3 '' (ball (0 : HS3) 1 ∩ ball (testAxis3 s 0) 1)) := by
      symm
      exact measure_image_eq_of_measurePreserving testSplit3
        testMeasurePreserving_split3 hU
    _ = volume (testAxisIntersection s) := by
      rw [testAxisIntersection_image s hs]
    _ = ∫⁻ t : ℝ, volume (Prod.mk t ⁻¹' testAxisIntersection s) := by
      rw [Measure.volume_eq_prod]
      exact Measure.prod_apply (measurableSet_testAxisIntersection s)

lemma testAxisIntersection_section_volume_real (s t : ℝ) :
    (volume : Measure HS2).real (Prod.mk t ⁻¹' testAxisIntersection s) =
      Real.pi * testSectionRadius s t ^ 2 := by
  change (volume (Prod.mk t ⁻¹' testAxisIntersection s)).toReal = _
  rw [testAxisIntersection_section, EuclideanSpace.volume_ball_fin_two]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow]
  have hr : 0 ≤ testSectionRadius s t := by
    exact le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal Real.pi_nonneg]
  ring

lemma testAxisIntersection_volume_real_as_integral (s : ℝ) (hs : 0 ≤ s) :
    (volume : Measure HS3).real
        (ball (0 : HS3) 1 ∩ ball (testAxis3 s 0) 1) =
      ∫ t : ℝ, (volume : Measure HS2).real
        (Prod.mk t ⁻¹' testAxisIntersection s) := by
  let U : Set (ℝ × HS2) := testAxisIntersection s
  have hU : MeasurableSet U := measurableSet_testAxisIntersection s
  have hfinite : (volume : Measure (ℝ × HS2)) U ≠ ∞ := by
    have hsubset : U ⊆ closedBall (0 : ℝ × HS2) 2 := by
      intro p hp
      rw [mem_closedBall, dist_zero_right]
      have hp0 : p.1 ^ 2 < 1 :=
        lt_of_le_of_lt (le_add_of_nonneg_right (sq_nonneg ‖p.2‖)) hp.1
      have hp1 : (p.1 - s) ^ 2 < 1 :=
        lt_of_le_of_lt (le_add_of_nonneg_right (sq_nonneg ‖p.2‖)) hp.2
      have hpt : |p.1| ≤ 1 := by
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg p.1]
      have hpz : ‖p.2‖ ≤ 1 := by
        have hpzsq : ‖p.2‖ ^ 2 < 1 :=
          lt_of_le_of_lt (le_add_of_nonneg_left (sq_nonneg p.1)) hp.1
        nlinarith [sq_nonneg ‖p.2‖]
      have hdist : dist p (0 : ℝ × HS2) ≤ ‖p.1‖ + ‖p.2‖ := by
       rw [Prod.dist_eq]
       simp only [Prod.fst_zero, Prod.snd_zero, dist_eq_norm, sub_zero]
       exact max_le_add_of_nonneg (norm_nonneg p.1) (norm_nonneg p.2)
      have hpt' : ‖p.1‖ ≤ 1 := by
        simpa [Real.norm_eq_abs] using hpt
      have : dist p (0 : ℝ × HS2) ≤ 2 :=
        hdist.trans (by nlinarith)
      simpa [dist_eq_norm] using this
    exact (lt_of_le_of_lt (measure_mono hsubset)
      (isCompact_closedBall (0 : ℝ × HS2) 2).measure_lt_top).ne
  have hF : Integrable (U.indicator (fun _ : ℝ × HS2 => (1 : ℝ)))
      (volume : Measure (ℝ × HS2)) := by
    exact (integrableOn_const hfinite).integrable_indicator hU
  have hU3 : MeasurableSet
      (ball (0 : HS3) 1 ∩ ball (testAxis3 s 0) 1) :=
    measurableSet_ball.inter measurableSet_ball
  have hvol : (volume : Measure (ℝ × HS2)) U =
      (volume : Measure HS3)
        (ball (0 : HS3) 1 ∩ ball (testAxis3 s 0) 1) := by
    change (volume : Measure (ℝ × HS2)) (testAxisIntersection s) = _
    rw [← testAxisIntersection_image s hs]
    exact measure_image_eq_of_measurePreserving testSplit3
      testMeasurePreserving_split3 hU3
  calc
    (volume : Measure HS3).real
        (ball (0 : HS3) 1 ∩ ball (testAxis3 s 0) 1) =
      (volume : Measure (ℝ × HS2)).real U := by
        exact congrArg ENNReal.toReal hvol |>.symm
    _ = ∫ p : ℝ × HS2, U.indicator (fun _ => (1 : ℝ)) p := by
      symm
      exact integral_indicator_one hU
    _ = ∫ t : ℝ, ∫ z : HS2, U.indicator (fun _ => (1 : ℝ)) (t, z) := by
      exact integral_prod _ hF
    _ = ∫ t : ℝ, (volume : Measure HS2).real
        (Prod.mk t ⁻¹' U) := by
      apply integral_congr_ae
      filter_upwards with t
      exact integral_indicator_one (hU.preimage measurable_prodMk_left)

lemma testAxisIntersection_volume_real_eq_lens (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (volume : Measure HS3).real
        (ball (0 : HS3) 1 ∩ ball (testAxis3 s 0) 1) =
      hardSphereLens s := by
  calc
    (volume : Measure HS3).real
        (ball (0 : HS3) 1 ∩ ball (testAxis3 s 0) 1) =
      ∫ t : ℝ, (volume : Measure HS2).real
        (Prod.mk t ⁻¹' testAxisIntersection s) :=
      testAxisIntersection_volume_real_as_integral s hs0
    _ = ∫ t : ℝ, Real.pi * testSectionRadius s t ^ 2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun t => testAxisIntersection_section_volume_real s t)
    _ = hardSphereLens s :=
      testAxisIntersection_section_integral_eq_lens s hs0 hs1

lemma testAxis3_norm (s : ℝ) (hs : 0 ≤ s) :
    ‖testAxis3 s 0‖ = s := by
  have hsq := testNorm_axis3_sq s (0 : HS2)
  simp only [norm_zero] at hsq
  nlinarith [norm_nonneg (testAxis3 s (0 : HS2))]

lemma testBallIntersection_image_linearIsometry
    (R : HS3 ≃ₗᵢ[ℝ] HS3) (d : HS3) :
    R '' (ball (0 : HS3) 1 ∩ ball d 1) =
      ball (R 0) 1 ∩ ball (R d) 1 := by
  rw [image_inter R.injective, R.image_ball, R.image_ball]

lemma testBallIntersection_real_volume_eq_lens_norm (d : HS3)
    (hd : ‖d‖ ≤ 1) :
    (volume : Measure HS3).real (ball (0 : HS3) 1 ∩ ball d 1) =
      hardSphereLens ‖d‖ := by
  let axis : HS3 := testAxis3 ‖d‖ 0
  let R : HS3 ≃ₗᵢ[ℝ] HS3 :=
    (ℝ ∙ (d - axis))ᗮ.reflection
  have haxis : ‖axis‖ = ‖d‖ := by
    exact testAxis3_norm ‖d‖ (norm_nonneg d)
  have hRd : R d = axis := by
    exact Submodule.reflection_sub haxis.symm
  have hR0 : R 0 = (0 : HS3) := map_zero R
  let e : HS3 ≃ᵐ HS3 := R.toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e
      (volume : Measure HS3) (volume : Measure HS3) := by
    change MeasurePreserving R volume volume
    exact R.measurePreserving
  have himage : e '' (ball (0 : HS3) 1 ∩ ball d 1) =
      ball (0 : HS3) 1 ∩ ball axis 1 := by
    change R '' (ball (0 : HS3) 1 ∩ ball d 1) = _
    rw [testBallIntersection_image_linearIsometry R d, hR0, hRd]
  have hsource : MeasurableSet (ball (0 : HS3) 1 ∩ ball d 1) :=
    measurableSet_ball.inter measurableSet_ball
  calc
    (volume : Measure HS3).real (ball (0 : HS3) 1 ∩ ball d 1) =
        (volume : Measure HS3).real
          (e '' (ball (0 : HS3) 1 ∩ ball d 1)) := by
      exact (congrArg ENNReal.toReal
        (measure_image_eq_of_measurePreserving e he hsource)).symm
    _ = (volume : Measure HS3).real (ball (0 : HS3) 1 ∩ ball axis 1) := by
      rw [himage]
    _ = hardSphereLens ‖d‖ := by
      exact testAxisIntersection_volume_real_eq_lens ‖d‖
        (norm_nonneg d) hd

def testPairBlock (x : Fin 2 × Fin 3 → ℝ) (i : Fin 2) : HS3 :=
  MeasurableEquiv.toLp 2 (Fin 3 → ℝ) (fun a => x (i, a))

def testPairDifferencePositionMap (p : HS3 × HS3) : HS3 × HS3 :=
  Prod.swap (hardSpherePairCoordinateEquiv.symm
    (hardSpherePairDifferenceLinearMap (hardSpherePairCoordinateEquiv p)))

lemma testMeasurePreserving_pairDifferencePositionMap :
    MeasurePreserving testPairDifferencePositionMap
      (volume : Measure (HS3 × HS3)) (volume : Measure (HS3 × HS3)) := by
  let hcoord := measurePreserving_hardSpherePairCoordinateEquiv
  let hdiff := measurePreserving_hardSpherePairDifferenceLinearMap
  let hback : MeasurePreserving (hardSpherePairCoordinateEquiv.symm)
      (volume : Measure (Fin 2 × Fin 3 → ℝ))
      (volume : Measure (HS3 × HS3)) :=
    MeasurePreserving.symm hardSpherePairCoordinateEquiv hcoord
  have hswap : MeasurePreserving Prod.swap
      (volume : Measure (HS3 × HS3)) (volume : Measure (HS3 × HS3)) :=
    Measure.measurePreserving_swap
  change MeasurePreserving
    (Prod.swap ∘ (hardSpherePairCoordinateEquiv.symm ∘
      (hardSpherePairDifferenceLinearMap ∘ hardSpherePairCoordinateEquiv)))
      volume volume
  exact hswap.comp (hback.comp (hdiff.comp hcoord))

lemma testPairDifferencePositionMap_apply (p : HS3 × HS3) :
    testPairDifferencePositionMap p = (p.2 - p.1, p.1) := by
  rcases p with ⟨p, q⟩
  apply Prod.ext
  · change (hardSpherePairCoordinateEquiv.symm
      (hardSpherePairDifferenceLinearMap
        (hardSpherePairCoordinateEquiv (p, q)))).2 = q - p
    have houtput := (hardSpherePairCoordinate_block_one
      (hardSpherePairCoordinateEquiv.symm
        (hardSpherePairDifferenceLinearMap
          (hardSpherePairCoordinateEquiv (p, q))))).symm
    rw [show hardSpherePairCoordinateEquiv
        (hardSpherePairCoordinateEquiv.symm
          (hardSpherePairDifferenceLinearMap
            (hardSpherePairCoordinateEquiv (p, q)))) =
        hardSpherePairDifferenceLinearMap
          (hardSpherePairCoordinateEquiv (p, q)) by simp] at houtput
    have hdiff_one :
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
            (fun a => hardSpherePairDifferenceLinearMap
              (hardSpherePairCoordinateEquiv (p, q)) (1, a)) = q - p := by
      unfold hardSpherePairDifferenceLinearMap
      simp only [hardSphereParentDifferenceLinearMap_apply]
      simp [hardSpherePairParent, hardSpherePairCoordinateEquiv_apply_zero,
        hardSpherePairCoordinateEquiv_apply_one]
      apply PiLp.ext
      intro a
      rfl
    exact houtput.trans hdiff_one
  · change (hardSpherePairCoordinateEquiv.symm
      (hardSpherePairDifferenceLinearMap
        (hardSpherePairCoordinateEquiv (p, q)))).1 = p
    have houtput := (hardSpherePairCoordinate_block_zero
      (hardSpherePairCoordinateEquiv.symm
        (hardSpherePairDifferenceLinearMap
          (hardSpherePairCoordinateEquiv (p, q))))).symm
    rw [show hardSpherePairCoordinateEquiv
        (hardSpherePairCoordinateEquiv.symm
          (hardSpherePairDifferenceLinearMap
            (hardSpherePairCoordinateEquiv (p, q)))) =
        hardSpherePairDifferenceLinearMap
          (hardSpherePairCoordinateEquiv (p, q)) by simp] at houtput
    have hdiff_zero :
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
            (fun a => hardSpherePairDifferenceLinearMap
              (hardSpherePairCoordinateEquiv (p, q)) (0, a)) = p := by
      unfold hardSpherePairDifferenceLinearMap
      simp only [hardSphereParentDifferenceLinearMap_apply]
      simp [hardSpherePairParent, hardSpherePairCoordinateEquiv_apply_zero]
    exact houtput.trans hdiff_zero

def testClosePairDifferenceRegion : Set (HS3 × HS3) :=
  {p | p.1 ∈ ball (0 : HS3) 1 ∧ p.2 ∈ ball (0 : HS3) 1 ∧
    p.1 + p.2 ∈ ball (0 : HS3) 1}

lemma measurableSet_testClosePairDifferenceRegion :
    MeasurableSet testClosePairDifferenceRegion := by
  rw [show testClosePairDifferenceRegion =
      (Prod.fst ⁻¹' ball (0 : HS3) 1) ∩
        (Prod.snd ⁻¹' ball (0 : HS3) 1) ∩
          ((fun p : HS3 × HS3 => p.1 + p.2) ⁻¹' ball (0 : HS3) 1) by
    ext p
    simp [testClosePairDifferenceRegion, and_assoc]]
  have hfst : MeasurableSet
      (Prod.fst ⁻¹' ball (0 : HS3) 1) :=
    MeasurableSet.preimage measurableSet_ball
      (measurable_fst : Measurable (fun p : HS3 × HS3 => p.1))
  have hsnd : MeasurableSet
      (Prod.snd ⁻¹' ball (0 : HS3) 1) :=
    MeasurableSet.preimage measurableSet_ball
      (measurable_snd : Measurable (fun p : HS3 × HS3 => p.2))
  have hadd : MeasurableSet
      ((fun p : HS3 × HS3 => p.1 + p.2) ⁻¹' ball (0 : HS3) 1) :=
    MeasurableSet.preimage measurableSet_ball
      ((continuous_fst.add continuous_snd :
        Continuous (fun p : HS3 × HS3 => p.1 + p.2))).measurable
  exact (hfst.inter hsnd).inter hadd

lemma testPairDifferencePositionMap_preimage_close :
    testPairDifferencePositionMap ⁻¹' testClosePairDifferenceRegion =
      hardSphereClosePairRegion := by
  ext p
  change testPairDifferencePositionMap p ∈ testClosePairDifferenceRegion ↔
    p ∈ hardSphereClosePairRegion
  rw [testPairDifferencePositionMap_apply]
  change ((p.2 - p.1) ∈ ball (0 : HS3) 1 ∧
      p.1 ∈ ball (0 : HS3) 1 ∧
      (p.2 - p.1) + p.1 ∈ ball (0 : HS3) 1) ↔ _
  have hadd : (p.2 - p.1) + p.1 = p.2 := by abel
  rw [hadd]
  simp only [hardSphereClosePairRegion,
    Set.mem_setOf_eq, mem_ball_iff_norm, sub_zero]
  rw [norm_sub_rev]
  tauto

lemma testClosePairDifferenceRegion_real_volume :
    (volume : Measure (HS3 × HS3)).real
        testClosePairDifferenceRegion =
      ∫ d : HS3, (ball (0 : HS3) 1).indicator
        (fun d => hardSphereLens ‖d‖) d := by
  have hU : MeasurableSet testClosePairDifferenceRegion :=
    measurableSet_testClosePairDifferenceRegion
  have hsubset : testClosePairDifferenceRegion ⊆
      ball (0 : HS3) 1 ×ˢ ball (0 : HS3) 1 := by
    intro p hp
    exact ⟨hp.1, hp.2.1⟩
  have hball : (volume : Measure HS3) (ball (0 : HS3) 1) < ∞ :=
    measure_ball_lt_top
  have hprod : (volume : Measure (HS3 × HS3))
      (ball (0 : HS3) 1 ×ˢ ball (0 : HS3) 1) < ∞ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top hball hball
  have hfinite : (volume : Measure (HS3 × HS3))
      testClosePairDifferenceRegion ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono hsubset) hprod).ne
  have hF : Integrable
      (testClosePairDifferenceRegion.indicator (fun _ => (1 : ℝ)))
      (volume : Measure (HS3 × HS3)) := by
    exact (integrableOn_const hfinite).integrable_indicator hU
  calc
    (volume : Measure (HS3 × HS3)).real
        testClosePairDifferenceRegion =
      ∫ p : HS3 × HS3,
        testClosePairDifferenceRegion.indicator (fun _ => (1 : ℝ)) p := by
      symm
      exact integral_indicator_one hU
    _ = ∫ d : HS3, ∫ x : HS3,
        testClosePairDifferenceRegion.indicator (fun _ => (1 : ℝ)) (d, x) := by
      exact integral_prod _ hF
    _ = ∫ d : HS3, (volume : Measure HS3).real
        (Prod.mk d ⁻¹' testClosePairDifferenceRegion) := by
      apply integral_congr_ae
      filter_upwards with d
      exact integral_indicator_one (hU.preimage measurable_prodMk_left)
    _ = ∫ d : HS3, (ball (0 : HS3) 1).indicator
        (fun d => hardSphereLens ‖d‖) d := by
      apply integral_congr_ae
      filter_upwards with d
      by_cases hd : d ∈ ball (0 : HS3) 1
      · have hdnorm : ‖d‖ < 1 := by
          simpa [mem_ball_iff_norm] using hd
        have hsection :
            Prod.mk d ⁻¹' testClosePairDifferenceRegion =
              ball (0 : HS3) 1 ∩ ball (-d) 1 := by
          ext x
          change (d ∈ ball (0 : HS3) 1 ∧
              x ∈ ball (0 : HS3) 1 ∧
              d + x ∈ ball (0 : HS3) 1) ↔
            x ∈ ball (0 : HS3) 1 ∧ x ∈ ball (-d) 1
          constructor
          · rintro ⟨_, hx, hdx⟩
            refine ⟨hx, ?_⟩
            rw [mem_ball_iff_norm] at hdx ⊢
            simpa [sub_zero, add_comm] using hdx
          · rintro ⟨hx, hxd⟩
            refine ⟨hd, hx, ?_⟩
            rw [mem_ball_iff_norm] at hxd ⊢
            simpa [sub_zero, add_comm] using hxd
        have hdnorm' : ‖-d‖ ≤ 1 := by
          rw [norm_neg]
          linarith
        rw [hsection, indicator_of_mem hd,
          testBallIntersection_real_volume_eq_lens_norm (-d) hdnorm']
        simp only [norm_neg]
      · have hsection :
            Prod.mk d ⁻¹' testClosePairDifferenceRegion = (∅ : Set HS3) := by
          ext x
          change (d ∈ ball (0 : HS3) 1 ∧
              x ∈ ball (0 : HS3) 1 ∧
              d + x ∈ ball (0 : HS3) 1) ↔ False
          simp [hd]
        rw [hsection]
        simp [hd]

lemma testClosePairRegion_real_volume_eq_difference :
    (volume : Measure (HS3 × HS3)).real hardSphereClosePairRegion =
      (volume : Measure (HS3 × HS3)).real
        testClosePairDifferenceRegion := by
  have hmap := testMeasurePreserving_pairDifferencePositionMap
  have hU := measurableSet_testClosePairDifferenceRegion
  have hmeasure : (volume : Measure (HS3 × HS3))
      (testPairDifferencePositionMap ⁻¹' testClosePairDifferenceRegion) =
      volume testClosePairDifferenceRegion := by
    rw [← Measure.map_apply hmap.measurable hU, hmap.map_eq]
  calc
    (volume : Measure (HS3 × HS3)).real hardSphereClosePairRegion =
        (volume : Measure (HS3 × HS3)).real
          (testPairDifferencePositionMap ⁻¹' testClosePairDifferenceRegion) := by
      rw [testPairDifferencePositionMap_preimage_close]
    _ = (volume : Measure (HS3 × HS3)).real
        testClosePairDifferenceRegion := congrArg ENNReal.toReal hmeasure

lemma testClosePairDifferenceRegion_radial_volume :
    (volume : Measure (HS3 × HS3)).real
        testClosePairDifferenceRegion =
      3 * hardSphereKappa *
        (∫ s in (0 : ℝ)..1, hardSphereLens s * s ^ 2) := by
  let f : ℝ → ℝ := (Iio (1 : ℝ)).indicator hardSphereLens
  have hpoint :
      (fun d : HS3 => (ball (0 : HS3) 1).indicator
        (fun d => hardSphereLens ‖d‖) d) =
      (fun d : HS3 => f ‖d‖) := by
    funext d
    by_cases hd : ‖d‖ < 1
    · have hdball : d ∈ ball (0 : HS3) 1 := by
        simpa [mem_ball_iff_norm] using hd
      simp [f, hdball, hd]
    · have hdball : d ∉ ball (0 : HS3) 1 := by
        intro h
        exact hd (by simpa [mem_ball_iff_norm] using h)
      simp [f, hdball, hd]
  have hradial :
      (∫ s in Ioi (0 : ℝ),
        s ^ (Module.finrank ℝ HS3 - 1) • f s) =
        ∫ s in (0 : ℝ)..1, hardSphereLens s * s ^ 2 := by
    rw [finrank_euclideanSpace_fin]
    norm_num
    calc
      (∫ s in Ioi (0 : ℝ), s ^ 2 • f s) =
          ∫ s : ℝ, (Ioi (0 : ℝ)).indicator
            (fun s => s ^ 2 • f s) s := by
        rw [integral_indicator measurableSet_Ioi]
      _ = ∫ s : ℝ, (Ioo (0 : ℝ) 1).indicator
            (fun s => s ^ 2 * hardSphereLens s) s := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => by
          by_cases h0 : 0 < s <;> by_cases h1 : s < 1 <;>
            simp [f, h0, h1, smul_eq_mul])
      _ = ∫ s in Ioo (0 : ℝ) 1, s ^ 2 * hardSphereLens s :=
        integral_indicator measurableSet_Ioo
      _ = ∫ s in Ioc (0 : ℝ) 1, s ^ 2 * hardSphereLens s :=
        integral_Ioc_eq_integral_Ioo.symm
      _ = ∫ s in (0 : ℝ)..1, s ^ 2 * hardSphereLens s :=
        (intervalIntegral.integral_of_le (by norm_num)).symm
      _ = ∫ s in (0 : ℝ)..1, hardSphereLens s * s ^ 2 := by
        apply intervalIntegral.integral_congr
        intro s hs
        ring
  calc
    (volume : Measure (HS3 × HS3)).real
        testClosePairDifferenceRegion =
      ∫ d : HS3, (ball (0 : HS3) 1).indicator
        (fun d => hardSphereLens ‖d‖) d :=
      testClosePairDifferenceRegion_real_volume
    _ = ∫ d : HS3, f ‖d‖ := by rw [hpoint]
    _ = Module.finrank ℝ HS3 •
        (volume : Measure HS3).real (ball (0 : HS3) 1) •
          (∫ s in Ioi (0 : ℝ),
            s ^ (Module.finrank ℝ HS3 - 1) • f s) := by
      exact integral_fun_norm_addHaar (volume : Measure HS3) f
    _ = 3 * hardSphereKappa *
        (∫ s in (0 : ℝ)..1, hardSphereLens s * s ^ 2) := by
      rw [finrank_euclideanSpace_fin]
      have hradial' :
          (∫ s in Ioi (0 : ℝ), s ^ (3 - 1) • f s) =
            ∫ s in (0 : ℝ)..1, hardSphereLens s * s ^ 2 := by
        simpa only [finrank_euclideanSpace_fin] using hradial
      rw [hradial']
      simp only [nsmul_eq_mul, smul_eq_mul]
      change (3 : ℝ) *
          (hardSphereKappa * (∫ s in (0 : ℝ)..1,
            hardSphereLens s * s ^ 2)) = _
      ring

lemma testClosePairRegion_real_volume :
    (volume : Measure (HS3 × HS3)).real hardSphereClosePairRegion =
      5 * Real.pi ^ 2 / 6 := by
  calc
    (volume : Measure (HS3 × HS3)).real hardSphereClosePairRegion =
        (volume : Measure (HS3 × HS3)).real
          testClosePairDifferenceRegion :=
      testClosePairRegion_real_volume_eq_difference
    _ = 3 * hardSphereKappa *
        (∫ s in (0 : ℝ)..1, hardSphereLens s * s ^ 2) :=
      testClosePairDifferenceRegion_radial_volume
    _ = 5 * Real.pi ^ 2 / 6 := by
      rw [intervalIntegral_hardSphereLens_mul_sq, hardSphereKappa_eq]
      ring

lemma testSeparatedPairRegion_real_volume :
    (volume : Measure (HS3 × HS3)).real hardSphereSeparatedPairRegion =
      17 * Real.pi ^ 2 / 18 := by
  have hsum := hardSphereSeparatedPairRegion_real_add_close_volume
  rw [testClosePairRegion_real_volume, hardSphereKappa_eq] at hsum
  linarith

theorem hardSphereClosePairRegion_real_volume :
    (volume : Measure (HSPosition 3 × HSPosition 3)).real
        hardSphereClosePairRegion =
      5 * Real.pi ^ 2 / 6 := by
  exact testClosePairRegion_real_volume

theorem hardSphereSeparatedPairRegion_real_volume :
    (volume : Measure (HSPosition 3 × HSPosition 3)).real
        hardSphereSeparatedPairRegion =
      17 * Real.pi ^ 2 / 18 := by
  exact testSeparatedPairRegion_real_volume

theorem hardSphereSeparatedPairRegion_real_volume_ratio :
    (volume : Measure (HSPosition 3 × HSPosition 3)).real
        hardSphereSeparatedPairRegion =
      (17 / 32 : ℝ) * hardSphereKappa ^ 2 := by
  rw [hardSphereSeparatedPairRegion_real_volume, hardSphereSeparatedVolume_ratio_identity]

end

end HsVirial
