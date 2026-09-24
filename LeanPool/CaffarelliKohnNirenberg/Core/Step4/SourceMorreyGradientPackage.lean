/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CutoffDerivatives
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CutoffMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.OneSidedMeasurability
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceComponents
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyData
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.LocalizedEquationGradientMeasurability
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski
public import LeanPool.CaffarelliKohnNirenberg.Statements.MorreyVecMem
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

/-!
# Source Morrey Gradient Package

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-!
# Gradient-slot localized source package

The local Morrey source bounds for the pressure-gradient heat representation.
-/

private lemma norm_neg_test {P θ : ℝ} (g : ParabolicPoint → ℝ) :
    morreyNorm P θ (fun z => -g z) = morreyNorm P θ g := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg]

private lemma norm_sub_le_test {P θ : ℝ} (hP : 1 ≤ P)
    {f g : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) :
    morreyNorm P θ (fun z => f z - g z) ≤
      morreyNorm P θ f + morreyNorm P θ g := by
  have h := morrey_norm_add_le (τ := θ) hP hf hg.neg
  change morreyNorm P θ (fun z => f z + -g z) ≤
    morreyNorm P θ f + morreyNorm P θ (fun z => -g z) at h
  rw [norm_neg_test] at h
  simpa only [sub_eq_add_neg] using h

private lemma indicator_indicator_test {α β : Type} [Zero β]
    (B : Set α) (g : α → β) :
    B.indicator (fun z => B.indicator g z) = B.indicator g := by
  funext z
  by_cases hz : z ∈ B
  · simp only [indicator_of_mem hz]
  · simp only [indicator_of_notMem hz]

private lemma lower_carrier_test
    {P P₀ θ θ₀ : ℝ} {B : Set ParabolicPoint}
    {z₀ : ParabolicPoint} {R : ℝ} {g : ParabolicPoint → ℝ}
    (hP : 1 ≤ P) (hPP₀ : P ≤ P₀) (hP₀θ₀ : P₀ ≤ θ₀)
    (hPθ : P ≤ θ) (hθθ₀ : θ ≤ θ₀) (hR : 0 < R)
    (hB : B ⊆ parabolicCylinder z₀.1 z₀.2 R)
    (hAE : AEMeasurable g volume) (hzero : ∀ w ∉ B, g w = 0)
    (hN : morreyNorm P₀ θ₀ g < ∞) :
    morreyNorm P θ g < ∞ := by
  have hlowP := morreyNorm_lower_integrability (p' := P) (p := P₀)
    (q := θ₀) hP hPP₀ hP₀θ₀ hAE
  have hlowPN : morreyNorm P θ₀ g < ∞ := hlowP.trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg
      (sub_nonneg.mpr (one_div_le_one_div_of_le
        (lt_of_lt_of_le zero_lt_one hP) hPP₀))
      Integration.volume_parabolicCylinder_lt_top.ne) hN)
  have hsupp : ∀ w ∉ parabolicCylinder z₀.1 z₀.2 R, g w = 0 := by
    intro w hw
    exact hzero w (fun hBw => hw (hB hBw))
  have hle := morreyNorm_lower_morrey_exponent
    (p := P) (q := θ₀) (q' := θ) hP
      (hPP₀.trans hP₀θ₀) hPθ hθθ₀ hR hsupp
  exact hle.trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5)
        (sub_nonneg.mpr (one_div_le_one_div_of_le
          (lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hP) hPθ) hθθ₀)))
      ENNReal.ofReal_ne_top) hlowPN)

theorem localized_gradient_force_morrey_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J) (i : Fin 3) :
    morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (fun z => φ z * f z i) < ∞ := by
  rcases hsol with ⟨hΩ, hI, hIord, hq, hfSol, hdata, hS2, hS3, hS4⟩
  rcases hφ with ⟨hφd, hφc, hφΩ⟩
  let S : Set ParabolicPoint := spaceTimeSet Ω' J
  let φp : ParabolicPoint → ℝ := φ
  have hSmeas : MeasurableSet S := hbox.1.measurableSet.prod
    hbox.2.2.2.1.measurableSet
  obtain ⟨hu, hDu, hpmeas, hfmeas, hEssSup, henergy, hp, hf, hgrad⟩ :=
    hdata Ω' J hbox
  have hfcomp : MemLp (fun z => f z i) (ENNReal.ofReal q)
      (volume.restrict S) :=
    hf.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hφtop : MemLp φp ∞ volume :=
    hφd.continuous.memLp_top_of_hasCompactSupport hφc volume
  let μ : Measure ParabolicPoint := volume.restrict S
  letI : IsFiniteMeasure μ :=
    CKN.Core.Step3.local_box_isFiniteMeasure hbox.2.1 hbox.2.2.2.2.1
  have hprodLocal : MemLp (fun z : ParabolicPoint => φp z * f z i)
      (ENNReal.ofReal q) μ := by
    exact (hφtop.restrict S).mul (r := ENNReal.ofReal q) hfcomp
  have hθ : (6 / 5 : ℝ) ≤ min q (25 / 9 : ℝ) :=
    le_min (by linarith only [hq]) (by norm_num)
  have hlowLocal : MemLp (fun z : ParabolicPoint => φp z * f z i)
      (ENNReal.ofReal (min q (25 / 9 : ℝ))) μ := by
    apply hprodLocal.mono_exponent
    exact ENNReal.ofReal_le_ofReal (min_le_left q (25 / 9))
  have hlowIndicator : MemLp
      (S.indicator (fun z : ParabolicPoint => φp z * f z i))
      (ENNReal.ofReal (min q (25 / 9 : ℝ))) volume := by
    exact (memLp_indicator_iff_restrict hSmeas).2 hlowLocal
  have hzero : ∀ z ∉ S, φp z * f z i = 0 := by
    intro z hz
    have hzφ : φp z = 0 := by
      change φ (z.1, z.2) = 0
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      apply hz
      exact hφbox hm
    simp only [hzφ, zero_mul]
  have hlow : MemLp (fun z : ParabolicPoint => φp z * f z i)
      (ENNReal.ofReal (min q (25 / 9 : ℝ))) volume := by
    refine hlowIndicator.ae_eq ?_
    filter_upwards [] with z
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz, hzero z hz]
  have hnorm : eLpNorm'
      (fun z : ParabolicPoint => φp z * f z i)
      (min q (25 / 9 : ℝ)) volume < ∞ := by
    have htop := hlow.eLpNorm_lt_top
    rw [eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top
      hlow.aestronglyMeasurable] at htop
    change eLpNorm' _ (min q (25 / 9 : ℝ)) volume < ∞
    rw [← ENNReal.toReal_ofReal (by positivity : 0 ≤ min q (25 / 9 : ℝ))]
    exact htop
  have hm := morreyNorm_le_eLpNorm' (p := (6 / 5 : ℝ))
    (q := min q (25 / 9 : ℝ)) (by norm_num) hθ hlow.aemeasurable
  have hθpos : 0 < min q (25 / 9 : ℝ) := lt_of_lt_of_le (by norm_num) hθ
  have hexp : 0 ≤ (1 / (6 / 5 : ℝ) - 1 / min q (25 / 9 : ℝ)) :=
    sub_nonneg.mpr (one_div_le_one_div_of_le (by norm_num) hθ)
  have hfin := lt_of_le_of_lt hm (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hexp
      Integration.volume_parabolicCylinder_lt_top.ne) hnorm)
  exact hfin

theorem localized_gradient_source_package_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    (z₀ : ParabolicPoint) (R : ℝ) (hR : 0 < R) (hq : 5 / 2 < q)
    (hcarrier : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I)
    (hφcarrier : tsupport φ ⊆ parabolicHomeomorph.symm ⁻¹' Metric.ball z₀ R)
    (hU : morreyVecMem 3 25 (Metric.ball z₀ R) u)
    (hDuNorm : ∀ i, morreyVecMem 2 (25 / 8 : ℝ)
      (Metric.ball z₀ R) (fun z => Du z i))
    {Dp : ParabolicPoint → Vec3}
    (hDpAE : ∀ i, AEMeasurable (fun z => Dp z i)
      (volume.restrict (Metric.ball z₀ R)))
    (hDpN : morreyVecMem (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (Metric.ball z₀ R) Dp) :
    (∀ i, AEMeasurable
      (fun z => localizedGradientSourceG φ u Du f Dp z i) volume) ∧
    (∀ j i, AEMeasurable
      (fun z => localizedGradientSourceH φ u j z i) volume) ∧
    (∀ i, HasCompactSupport
      (fun z => localizedGradientSourceG φ u Du f Dp z i)) ∧
    (∀ j i, HasCompactSupport
      (fun z => localizedGradientSourceH φ u j z i)) ∧
    (∀ i, morreyNorm (6 / 5 : ℝ) (min q (25 / 9 : ℝ))
      (fun z => localizedGradientSourceG φ u Du f Dp z i) < ∞) ∧
    (∀ j i, morreyNorm (6 / 5 : ℝ) (25 / 3 : ℝ)
      (fun z => localizedGradientSourceH φ u j z i) < ∞) := by
  let B : Set ParabolicPoint := Metric.ball z₀ R
  let S : Set ParabolicPoint := spaceTimeSet Ω' J
  let φp : ParabolicPoint → ℝ := φ
  have _hcarrier := hcarrier
  have hBmeas : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hSmeas : MeasurableSet S := hbox.1.measurableSet.prod
    hbox.2.2.2.1.measurableSet
  obtain ⟨C, hC, hcoeff⟩ :=
    CKN.Core.Endgame.exists_cutoff_derivative_bound hφ.1 hφ.2.1
  have hnotphi (z : ParabolicPoint) (hz : z ∉ B) :
      (z.1, z.2) ∉ tsupport φ := by
    intro hm
    apply hz
    have hm' := hφcarrier hm
    change parabolicHomeomorph.symm (z.1, z.2) ∈ Metric.ball z₀ R at hm'
    change z ∈ Metric.ball z₀ R
    rw [show z = (z.1, z.2) from rfl]
    simpa only [parabolicHomeomorph_symm_apply] using hm'
  have hφzero (z : ParabolicPoint) (hz : z ∉ B) : φp z = 0 := by
    change φ (z.1, z.2) = 0
    exact image_eq_zero_of_notMem_tsupport (hnotphi z hz)
  have htimezero (z : ParabolicPoint) (hz : z ∉ B) : timePartial φ z = 0 :=
    timePartial_zero_of_not_mem_tsupport_public hφ.1 (hnotphi z hz)
  have hspzero (j : Fin 3) (z : ParabolicPoint) (hz : z ∉ B) :
      spatialPartial φ j z = 0 :=
    spatialPartial_zero_of_not_mem_tsupport_public hφ.1 (hnotphi z hz) j
  have hlapzero (z : ParabolicPoint) (hz : z ∉ B) :
      spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0 := by
    change (∑ j : Fin 3, spatialSecondPartial
      (show ParabolicPoint → ℝ from φ) j j z) = 0
    apply Finset.sum_eq_zero
    intro j hj
    exact spatialSecondPartial_zero_of_not_mem_tsupport_public hφ.1
      (hnotphi z hz) j j
  have hvalue (z : ParabolicPoint) : |φp z| ≤ C := by
    change |φ (z.1, z.2)| ≤ C
    exact (hcoeff (z.1, z.2)).1
  have htime (z : ParabolicPoint) : |timePartial φ z| ≤ C := by
    simpa only [timePartial] using (hcoeff (z.1, z.2)).2.1
  have hlap (z : ParabolicPoint) :
      |spatialLaplacian (fun x => φ (x, z.2)) z.1| ≤ C := by
    exact (hcoeff (z.1, z.2)).2.2.2
  have hsp (j : Fin 3) (z : ParabolicPoint) :
      |spatialPartial φ j z| ≤ C := by
    change |spatialPartial φ j (z.1, z.2)| ≤ C
    exact (hcoeff (z.1, z.2)).2.2.1 j
  have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
  obtain ⟨hu, hDuData, hpmeas, hfmeas, hEssSup, henergy, hp, hf, hgrad⟩ := hdata
  have hucomp (i : Fin 3) : AEMeasurable (fun z => u z i)
      (volume.restrict S) :=
    aemeasurable_pi_iff.mp hu.aemeasurable i
  have hDucomp (i j : Fin 3) : AEMeasurable (fun z => Du z i j)
      (volume.restrict S) :=
    aemeasurable_pi_iff.mp (aemeasurable_pi_iff.mp hDuData.aemeasurable i) j
  have hfcomp (i : Fin 3) : AEMeasurable (fun z => f z i)
      (volume.restrict S) :=
    aemeasurable_pi_iff.mp hfmeas.aemeasurable i
  have huBox (i : Fin 3) : AEMeasurable
      (S.indicator (fun z => u z i)) volume :=
    (aemeasurable_indicator_iff hSmeas).mpr (hucomp i)
  have hDuBox (i j : Fin 3) : AEMeasurable
      (S.indicator (fun z => Du z i j)) volume :=
    (aemeasurable_indicator_iff hSmeas).mpr (hDucomp i j)
  have hUBoxAE (i : Fin 3) : AEMeasurable
      (B.indicator (S.indicator (fun z => u z i))) volume :=
    (huBox i).indicator hBmeas
  have hDuBoxAE (i j : Fin 3) : AEMeasurable
      (B.indicator (S.indicator (fun z => Du z i j))) volume :=
    (hDuBox i j).indicator hBmeas
  have hUbase (i : Fin 3) : morreyNorm 3 25
      (B.indicator (fun z => u z i)) < ∞ := by
    exact (morreyNorm_le_morreyBallNorm (by norm_num) (by norm_num) _).trans_lt (hU i)
  have hDbase (i j : Fin 3) : morreyNorm 2 (25 / 8)
      (B.indicator (fun z => Du z i j)) < ∞ := by
    exact (morreyNorm_le_morreyBallNorm (by norm_num) (by norm_num) _).trans_lt (hDuNorm i j)
  have hUBle (i : Fin 3) : morreyNorm 3 25
      (B.indicator (S.indicator (fun z => u z i))) ≤
      morreyNorm 3 25 (B.indicator (fun z => u z i)) := by
    apply morreyNorm_mono (by norm_num)
    intro z
    by_cases hzB : z ∈ B
    · rw [indicator_of_mem hzB]
      by_cases hzS : z ∈ S
      · rw [indicator_of_mem hzS, indicator_of_mem hzB]
      · rw [indicator_of_notMem hzS, abs_zero]
        simpa only [abs_zero] using (abs_nonneg (B.indicator (fun z => u z i) z))
    · rw [indicator_of_notMem hzB]
      simpa only [abs_zero] using (abs_nonneg (B.indicator (fun z => u z i) z))
  have hDBle (i j : Fin 3) : morreyNorm 2 (25 / 8)
      (B.indicator (S.indicator (fun z => Du z i j))) ≤
      morreyNorm 2 (25 / 8) (B.indicator (fun z => Du z i j)) := by
    apply morreyNorm_mono (by norm_num)
    intro z
    by_cases hzB : z ∈ B
    · rw [indicator_of_mem hzB]
      by_cases hzS : z ∈ S
      · rw [indicator_of_mem hzS, indicator_of_mem hzB]
      · rw [indicator_of_notMem hzS, abs_zero]
        simpa only [abs_zero] using
          (abs_nonneg (B.indicator (fun z => Du z i j) z))
    · rw [indicator_of_notMem hzB]
      simpa only [abs_zero] using
        (abs_nonneg (B.indicator (fun z => Du z i j) z))
  have hUB (i : Fin 3) : morreyNorm 3 25
      (B.indicator (S.indicator (fun z => u z i))) < ∞ :=
    (hUBle i).trans_lt (hUbase i)
  have hDB (i j : Fin 3) : morreyNorm 2 (25 / 8)
      (B.indicator (S.indicator (fun z => Du z i j))) < ∞ :=
    (hDBle i j).trans_lt (hDbase i j)
  have hballC : B ⊆ parabolicCylinder z₀.1 (z₀.2 + R ^ 2) (2 * R) := by
    exact metricBall_subset_parabolicCylinder_doubled z₀ hR
  have hUθH (i : Fin 3) : morreyNorm 3 (25 / 3 : ℝ)
      (B.indicator (S.indicator (fun z => u z i))) < ∞ := by
    exact lower_carrier_test (P := 3) (P₀ := 3)
      (θ := 25 / 3) (θ₀ := 25) (B := B)
      (z₀ := (z₀.1, z₀.2 + R ^ 2)) (R := 2 * R)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by positivity) hballC
      (hUBoxAE i) (fun z hz => indicator_of_notMem hz _) (hUB i)
  have hUlow (θ : ℝ) (i : Fin 3) (hθ : 6 / 5 ≤ θ)
      (hθ25 : θ ≤ 25)
      : morreyNorm (6 / 5) θ
        (B.indicator (fun z => B.indicator (S.indicator (fun w => u w i)) z)) < ∞ := by
    have hUlow' : morreyNorm (6 / 5) θ
        (B.indicator (S.indicator (fun z => u z i))) < ∞ := by
      exact lower_carrier_test (P := (6 / 5 : ℝ)) (P₀ := 3)
        (θ := θ) (θ₀ := 25) (B := B)
        (z₀ := (z₀.1, z₀.2 + R ^ 2)) (R := 2 * R)
        (by norm_num) (by norm_num) (by norm_num) hθ hθ25
        (by positivity) hballC (hUBoxAE i)
        (fun z hz => by exact indicator_of_notMem hz _) (hUB i)
    simpa only [indicator_indicator_test] using hUlow'
  have hconvN (i : Fin 3) : morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
      (fun z => φp z * ∑ j, B.indicator (S.indicator (fun w => u w j)) z *
        B.indicator (S.indicator (fun w => Du w i j)) z) < ∞ := by
    have hprod (j : Fin 3) : morreyNorm (6 / 5) (25 / 9)
        (fun z => B.indicator (S.indicator (fun w => u w j)) z *
          B.indicator (S.indicator (fun w => Du w i j)) z) < ∞ := by
      exact (source_product_morrey_bound (P := (6 / 5 : ℝ))
        (P₁ := 3) (P₂ := 2) (θ := 25 / 9) (θ₁ := 25) (θ₂ := 25 / 8)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (hUBoxAE j) (hDuBoxAE i j) (hUB j) (hDB i j)).1
    have hprod_low (j : Fin 3) : morreyNorm (6 / 5) (min q (25 / 9))
        (fun z => B.indicator (S.indicator (fun w => u w j)) z *
          B.indicator (S.indicator (fun w => Du w i j)) z) < ∞ := by
      have hθmin : (6 / 5 : ℝ) ≤ min q (25 / 9) := by
        exact le_min (by linarith only [hq]) (by norm_num)
      exact lower_carrier_test (P := (6 / 5 : ℝ)) (P₀ := (6 / 5 : ℝ))
        (θ := min q (25 / 9)) (θ₀ := 25 / 9) (B := B)
        (z₀ := (z₀.1, z₀.2 + R ^ 2)) (R := 2 * R)
        (by norm_num) (by norm_num) (by norm_num) hθmin
        (min_le_right _ _) (by positivity) hballC
        ((hUBoxAE j).mul (hDuBoxAE i j))
        (fun z hz => by
          simp only [indicator_of_notMem hz, zero_mul])
        (hprod j)
    have hsum : morreyNorm (6 / 5) (min q (25 / 9))
        (fun z => ∑ j, B.indicator (S.indicator (fun w => u w j)) z *
          B.indicator (S.indicator (fun w => Du w i j)) z) < ∞ := by
      let t (j : Fin 3) : ParabolicPoint → ℝ := fun z =>
        B.indicator (S.indicator (fun w => u w j)) z *
          B.indicator (S.indicator (fun w => Du w i j)) z
      have htermAE (j : Fin 3) : AEMeasurable (t j) volume := by
        exact (hUBoxAE j).mul (hDuBoxAE i j)
      have h12le : morreyNorm (6 / 5) (min q (25 / 9)) (fun z =>
          t 1 z + t 2 z) ≤ morreyNorm (6 / 5) (min q (25 / 9)) (t 1) +
          morreyNorm (6 / 5) (min q (25 / 9)) (t 2) := by
        exact morrey_norm_add_le (P := (6 / 5 : ℝ))
          (τ := min q (25 / 9)) (by norm_num) (htermAE 1) (htermAE 2)
      have h12 : morreyNorm (6 / 5) (min q (25 / 9))
          (fun z => B.indicator (S.indicator (fun w => u w 1)) z *
            B.indicator (S.indicator (fun w => Du w i 1)) z +
            B.indicator (S.indicator (fun w => u w 2)) z *
            B.indicator (S.indicator (fun w => Du w i 2)) z) < ∞ :=
        h12le.trans_lt (ENNReal.add_lt_top.mpr ⟨hprod_low 1, hprod_low 2⟩)
      have hterm12AE : AEMeasurable (fun z => t 1 z + t 2 z) volume :=
        (htermAE 1).add (htermAE 2)
      have hallle : morreyNorm (6 / 5) (min q (25 / 9)) (fun z =>
          t 0 z + (t 1 z + t 2 z)) ≤ morreyNorm (6 / 5) (min q (25 / 9))
          (t 0) + morreyNorm (6 / 5) (min q (25 / 9)) (fun z => t 1 z + t 2 z) :=
        morrey_norm_add_le (P := (6 / 5 : ℝ)) (τ := min q (25 / 9))
          (by norm_num) (htermAE 0) hterm12AE
      have hall : morreyNorm (6 / 5) (min q (25 / 9))
          (fun z => ∑ j, B.indicator (S.indicator (fun w => u w j)) z *
            B.indicator (S.indicator (fun w => Du w i j)) z) < ∞ := by
        have hfinite := hallle.trans_lt
          (ENNReal.add_lt_top.mpr ⟨hprod_low 0, h12⟩)
        simpa [Fin.sum_univ_succ, t, add_assoc] using hfinite
      exact hall
    have hsum' : morreyNorm (6 / 5) (min q (25 / 9))
        (B.indicator (fun z => ∑ j,
          B.indicator (S.indicator (fun w => u w j)) z *
            B.indicator (S.indicator (fun w => Du w i j)) z)) < ∞ := by
      have heq : B.indicator (fun z => ∑ j,
          B.indicator (S.indicator (fun w => u w j)) z *
            B.indicator (S.indicator (fun w => Du w i j)) z) =
          (fun z => ∑ j, B.indicator (S.indicator (fun w => u w j)) z *
            B.indicator (S.indicator (fun w => Du w i j)) z) := by
        funext z
        by_cases hz : z ∈ B
        · simp only [indicator_of_mem hz]
        · simp only [indicator_of_notMem hz]
          simp only [zero_mul, Finset.sum_const_zero]
      rw [heq]
      exact hsum
    exact (morrey_norm_mul_le_indicator (6 / 5) (min q (25 / 9)) C
      (by norm_num) hC.le B φp
      (fun z => ∑ j, B.indicator (S.indicator (fun w => u w j)) z *
        B.indicator (S.indicator (fun w => Du w i j)) z)
      (hvalue) (fun z hz => hφzero z hz)).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum')
  have hforceN (i : Fin 3) : morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
      (fun z => φp z * f z i) < ∞ := by
    simpa only [φp] using localized_gradient_force_morrey_of_sws
      hsol hφ hbox hφbox i
  have hDpN' (i : Fin 3) : morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
      (fun z => φp z * Dp z i) < ∞ := by
    have hθmin : (6 / 5 : ℝ) ≤ min q (25 / 9) := by
      exact le_min (by linarith only [hq]) (by norm_num)
    have hN : morreyNorm (6 / 5) (min q (25 / 9 : ℝ))
        (B.indicator (fun z => Dp z i)) < ∞ := by
      exact (morreyNorm_le_morreyBallNorm (by norm_num)
        hθmin _).trans_lt (hDpN i)
    have hmul := morrey_norm_mul_le_indicator (6 / 5) (min q (25 / 9 : ℝ)) C
      (by norm_num) hC.le B φp (fun z => Dp z i) hvalue hφzero
    exact hmul.trans_lt (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top) hN)
  have hφAE : AEMeasurable φp volume := by
    exact (hφ.1.continuous.comp continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have htimeAE : AEMeasurable (fun z : ParabolicPoint => timePartial φ z) volume := by
    exact ((timePartial_contDiff_full hφ.1).continuous.comp
      continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have hspAE (j : Fin 3) : AEMeasurable
      (fun z : ParabolicPoint => spatialPartial φ j z) volume := by
    exact ((spatialPartial_contDiff hφ.1 j).continuous.comp
      continuous_parabolicPoint_to_prod).measurable.aemeasurable
  have hlapAE : AEMeasurable
      (fun z : ParabolicPoint => spatialLaplacian (fun x => φ (x, z.2)) z.1) volume := by
    change AEMeasurable (fun z : ParabolicPoint =>
      ∑ j, spatialSecondPartial (show ParabolicPoint → ℝ from φ) j j z) volume
    have h0 : AEMeasurable
        (fun z : ParabolicPoint => spatialSecondPartial φ 0 0 z) volume :=
      ((spatialSecondPartial_contDiff_full hφ.1 0 0).continuous.comp
        continuous_parabolicPoint_to_prod).measurable.aemeasurable
    have h1 : AEMeasurable
        (fun z : ParabolicPoint => spatialSecondPartial φ 1 1 z) volume :=
      ((spatialSecondPartial_contDiff_full hφ.1 1 1).continuous.comp
        continuous_parabolicPoint_to_prod).measurable.aemeasurable
    have h2 : AEMeasurable
        (fun z : ParabolicPoint => spatialSecondPartial φ 2 2 z) volume :=
      ((spatialSecondPartial_contDiff_full hφ.1 2 2).continuous.comp
        continuous_parabolicPoint_to_prod).measurable.aemeasurable
    simpa [Fin.sum_univ_succ, Pi.add_def] using h0.add (h1.add h2)
  have hnotphiS (z : ParabolicPoint) (hz : z ∉ S) :
      (z.1, z.2) ∉ tsupport φ := by
    intro hm
    apply hz
    exact hφbox hm
  have hφzeroS (z : ParabolicPoint) (hz : z ∉ S) : φp z = 0 := by
    change φ (z.1, z.2) = 0
    exact image_eq_zero_of_notMem_tsupport (hnotphiS z hz)
  have htimezeroS (z : ParabolicPoint) (hz : z ∉ S) :
      timePartial φ z = 0 := by
    exact timePartial_zero_of_not_mem_tsupport_public hφ.1 (hnotphiS z hz)
  have hspzeroS (j : Fin 3) (z : ParabolicPoint) (hz : z ∉ S) :
      spatialPartial φ j z = 0 := by
    exact spatialPartial_zero_of_not_mem_tsupport_public hφ.1 (hnotphiS z hz) j
  have hlapzeroS (z : ParabolicPoint) (hz : z ∉ S) :
      spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0 := by
    change (∑ j : Fin 3, spatialSecondPartial
      (show ParabolicPoint → ℝ from φ) j j z) = 0
    exact Finset.sum_eq_zero (fun j _ =>
      spatialSecondPartial_zero_of_not_mem_tsupport_public hφ.1
        (hnotphiS z hz) j j)
  have htimeMulAE (i : Fin 3) : AEMeasurable
      (fun z => timePartial φ z * u z i) volume :=
    aemeasurable_mul_of_restrict_of_zero_outside hSmeas htimeAE
      (hucomp i) htimezeroS
  have hlapMulAE (i : Fin 3) : AEMeasurable
      (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) volume :=
    aemeasurable_mul_of_restrict_of_zero_outside hSmeas hlapAE
      (hucomp i) hlapzeroS
  have hconvAE (i : Fin 3) : AEMeasurable
      (fun z => φp z * localizedConvection u Du z i) volume := by
    let c : ParabolicPoint → ℝ := fun z =>
      ∑ j, u z j * Du z i j
    have hc : AEMeasurable c (volume.restrict S) := by
      have h0 : AEMeasurable (fun z : ParabolicPoint => u z 0 * Du z i 0)
          (volume.restrict S) := (hucomp 0).mul (hDucomp i 0)
      have h1 : AEMeasurable (fun z : ParabolicPoint => u z 1 * Du z i 1)
          (volume.restrict S) := (hucomp 1).mul (hDucomp i 1)
      have h2 : AEMeasurable (fun z : ParabolicPoint => u z 2 * Du z i 2)
          (volume.restrict S) := (hucomp 2).mul (hDucomp i 2)
      simpa [c, Fin.sum_univ_succ, Pi.add_def] using
        h0.add (h1.add h2)
    have h := aemeasurable_mul_of_restrict_of_zero_outside hSmeas hφAE hc
      (fun z hz => by
        exact hφzeroS z hz)
    simpa only [c, localizedConvection] using h
  have hforceAE (i : Fin 3) : AEMeasurable (fun z => φp z * f z i) volume :=
    aemeasurable_mul_of_restrict_of_zero_outside hSmeas hφAE
      (hfcomp i) (fun z hz => hφzeroS z hz)
  have hDpAE' (i : Fin 3) : AEMeasurable
      (fun z => φp z * Dp z i) volume :=
    aemeasurable_mul_of_restrict_of_zero_outside hBmeas hφAE
      (hDpAE i) hφzero
  have hGae (i : Fin 3) : AEMeasurable
      (fun z => localizedGradientSourceG φ u Du f Dp z i) volume := by
    have hsum := ((htimeMulAE i).add (hlapMulAE i)).sub (hconvAE i)
    have hsum' := hsum.add (hforceAE i)
    have hsum'' := hsum'.sub (hDpAE' i)
    convert hsum'' using 1
    funext z
    dsimp [localizedGradientSourceG, localizedEquationG, localizedConvection, φp]
  have hHae (j i : Fin 3) : AEMeasurable
      (fun z => localizedGradientSourceH φ u j z i) volume := by
    have hcoeffAE : AEMeasurable
        (fun z : ParabolicPoint => -2 * spatialPartial φ j z) volume :=
      (hspAE j).const_mul (-2)
    have h := aemeasurable_mul_of_restrict_of_zero_outside hSmeas hcoeffAE
      (hucomp i) (fun z hz => by simp only [hspzeroS j z hz, mul_zero])
    simpa only [localizedGradientSourceH, localizedEquationH, Pi.smul_apply,
      smul_eq_mul] using h
  have hsupport_of_phi {V : Type} [Zero V] (v : ParabolicPoint → V)
      (hzv : ∀ z, parabolicHomeomorph z ∉ tsupport φ → v z = 0) :
      HasCompactSupport v := by
    let K : Set ParabolicPoint := parabolicHomeomorph ⁻¹' tsupport φ
    have hK : IsCompact K :=
      parabolicHomeomorph.isCompact_preimage.2 hφ.2.1.isCompact
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro z hz
    by_contra hnot
    apply hz
    apply hzv z
    simpa only [K, Set.mem_preimage, parabolicHomeomorph_apply] using hnot
  have hφzeroTs (z : ParabolicPoint)
      (hz : parabolicHomeomorph z ∉ tsupport φ) : φp z = 0 := by
    change φ (z.1, z.2) = 0
    exact image_eq_zero_of_notMem_tsupport (by
      simpa only [parabolicHomeomorph_apply] using hz)
  have htimezeroTs (z : ParabolicPoint)
      (hz : parabolicHomeomorph z ∉ tsupport φ) : timePartial φ z = 0 := by
    have hz' : (z.1, z.2) ∉ tsupport φ := by
      simpa only [parabolicHomeomorph_apply] using hz
    exact timePartial_zero_of_not_mem_tsupport_public hφ.1 hz'
  have hspzeroTs (j : Fin 3) (z : ParabolicPoint)
      (hz : parabolicHomeomorph z ∉ tsupport φ) : spatialPartial φ j z = 0 := by
    have hz' : (z.1, z.2) ∉ tsupport φ := by
      simpa only [parabolicHomeomorph_apply] using hz
    exact spatialPartial_zero_of_not_mem_tsupport_public hφ.1 hz' j
  have hlapzeroTs (z : ParabolicPoint)
      (hz : parabolicHomeomorph z ∉ tsupport φ) :
      spatialLaplacian (fun x => φ (x, z.2)) z.1 = 0 := by
    change (∑ j : Fin 3, spatialSecondPartial
      (show ParabolicPoint → ℝ from φ) j j z) = 0
    exact Finset.sum_eq_zero (fun j _ =>
      spatialSecondPartial_zero_of_not_mem_tsupport_public hφ.1 (by
        have hz' : (z.1, z.2) ∉ tsupport φ := by
          simpa only [parabolicHomeomorph_apply] using hz
        exact hz') j j)
  have hFc (i : Fin 3) : HasCompactSupport
      (fun z => localizedGradientSourceG φ u Du f Dp z i) := by
    apply hsupport_of_phi
    intro z hz
    dsimp [localizedGradientSourceG, localizedEquationG]
    have hpz : φ z = 0 := by
      change φp z = 0
      exact hφzeroTs z hz
    rw [hpz, htimezeroTs z hz]
    have hlapz := hlapzeroTs z hz
    have hconvz : localizedConvection u Du z i =
        ∑ j, u z j * Du z i j := rfl
    rw [hlapz]
    simp only [hconvz]
    ring
  have hHc (j i : Fin 3) : HasCompactSupport
      (fun z => localizedGradientSourceH φ u j z i) := by
    apply hsupport_of_phi
    intro z hz
    dsimp [localizedGradientSourceH, localizedEquationH]
    rw [hspzeroTs j z hz]
    simp
  have htimeEq (i : Fin 3) :
      (fun z => timePartial φ z * u z i) =
        (fun z => timePartial φ z *
          B.indicator (S.indicator (fun w => u w i)) z) := by
    funext z
    by_cases hzB : z ∈ B
    · rw [indicator_of_mem hzB]
      by_cases hzS : z ∈ S
      · rw [indicator_of_mem hzS]
      · rw [indicator_of_notMem hzS, htimezeroS z hzS]
        simp
    · rw [indicator_of_notMem hzB, htimezero z hzB]
      simp
  have hlapEq (i : Fin 3) :
      (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) =
        (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1 *
          B.indicator (S.indicator (fun w => u w i)) z) := by
    funext z
    by_cases hzB : z ∈ B
    · rw [indicator_of_mem hzB]
      by_cases hzS : z ∈ S
      · rw [indicator_of_mem hzS]
      · rw [indicator_of_notMem hzS, hlapzeroS z hzS]
        simp
    · rw [indicator_of_notMem hzB, hlapzero z hzB]
      simp
  have hUθmin (i : Fin 3) : morreyNorm (6 / 5) (min q (25 / 9))
      (B.indicator (fun z => B.indicator (S.indicator (fun w => u w i)) z)) < ∞ := by
    have hUθmin' : morreyNorm (6 / 5) (min q (25 / 9))
        (B.indicator (S.indicator (fun z => u z i))) < ∞ := by
      exact lower_carrier_test (P := (6 / 5 : ℝ)) (P₀ := 3)
        (θ := min q (25 / 9)) (θ₀ := 25) (B := B)
        (z₀ := (z₀.1, z₀.2 + R ^ 2)) (R := 2 * R)
        (by norm_num) (by norm_num) (by norm_num)
        (le_min (by linarith only [hq]) (by norm_num))
        ((min_le_right q (25 / 9)).trans (by norm_num))
        (by positivity) hballC (hUBoxAE i)
        (fun z hz => by exact indicator_of_notMem hz _) (hUB i)
    simpa only [indicator_indicator_test] using hUθmin'
  have htimeN (i : Fin 3) : morreyNorm (6 / 5) (min q (25 / 9))
      (fun z => timePartial φ z * u z i) < ∞ := by
    rw [htimeEq i]
    have hmul := morrey_norm_mul_le_indicator (6 / 5) (min q (25 / 9)) C
      (by norm_num) hC.le B (fun z => timePartial φ z)
      (fun z => B.indicator (S.indicator (fun w => u w i)) z) htime
      (fun z hz => htimezero z hz)
    exact hmul.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hUθmin i))
  have hlapN (i : Fin 3) : morreyNorm (6 / 5) (min q (25 / 9))
      (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) < ∞ := by
    rw [hlapEq i]
    have hmul := morrey_norm_mul_le_indicator (6 / 5) (min q (25 / 9)) C
      (by norm_num) hC.le B
      (fun z => spatialLaplacian (fun x => φ (x, z.2)) z.1)
      (fun z => B.indicator (S.indicator (fun w => u w i)) z) hlap
      (fun z hz => hlapzero z hz)
    exact hmul.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hUθmin i))
  have hconvEq (i : Fin 3) :
      (fun z => φp z * localizedConvection u Du z i) =
        (fun z => φp z * ∑ j, B.indicator (S.indicator (fun w => u w j)) z *
          B.indicator (S.indicator (fun w => Du w i j)) z) := by
    funext z
    by_cases hzB : z ∈ B
    · simp only [indicator_of_mem hzB]
      by_cases hzS : z ∈ S
      · simp only [indicator_of_mem hzS, localizedConvection]
      · simp only [indicator_of_notMem hzS, hφzeroS z hzS, zero_mul]
    · simp only [indicator_of_notMem hzB, hφzero z hzB, zero_mul]
  have hconvN' (i : Fin 3) : morreyNorm (6 / 5) (min q (25 / 9))
      (fun z => φp z * localizedConvection u Du z i) < ∞ := by
    rw [hconvEq i]
    exact hconvN i
  have hHtarget (j i : Fin 3) :
      (fun z => localizedGradientSourceH φ u j z i) =
        (fun z => (-2 * spatialPartial φ j z) *
          B.indicator (S.indicator (fun w => u w i)) z) := by
    funext z
    by_cases hzB : z ∈ B
    · simp only [indicator_of_mem hzB]
      by_cases hzS : z ∈ S
      · simp only [indicator_of_mem hzS, localizedGradientSourceH,
          localizedEquationH, Pi.smul_apply, smul_eq_mul]
      · simp only [indicator_of_notMem hzS, hspzeroS j z hzS,
          localizedGradientSourceH, localizedEquationH, Pi.smul_apply,
          smul_eq_mul, zero_mul, mul_zero]
    · simp only [indicator_of_notMem hzB, hspzero j z hzB,
        localizedGradientSourceH, localizedEquationH, Pi.smul_apply,
        smul_eq_mul, zero_mul, mul_zero]
  have hGnorm (i : Fin 3) : morreyNorm (6 / 5) (min q (25 / 9))
      (fun z => localizedGradientSourceG φ u Du f Dp z i) < ∞ := by
    have h12 : morreyNorm (6 / 5) (min q (25 / 9))
        (fun z => timePartial φ z * u z i +
          spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) < ∞ :=
      (morrey_norm_add_le (P := (6 / 5 : ℝ)) (τ := min q (25 / 9))
        (by norm_num) (htimeMulAE i) (hlapMulAE i)).trans_lt
        (ENNReal.add_lt_top.mpr ⟨htimeN i, hlapN i⟩)
    have h12ae : AEMeasurable (fun z => timePartial φ z * u z i +
        spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) volume :=
      (htimeMulAE i).add (hlapMulAE i)
    have h123le : morreyNorm (6 / 5) (min q (25 / 9))
        (fun z => (timePartial φ z * u z i +
          spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) -
          φp z * localizedConvection u Du z i) ≤
        morreyNorm (6 / 5) (min q (25 / 9))
          (fun z => timePartial φ z * u z i +
            spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) +
        morreyNorm (6 / 5) (min q (25 / 9))
          (fun z => φp z * localizedConvection u Du z i) :=
      norm_sub_le_test (by norm_num) h12ae (hconvAE i)
    have h123 : morreyNorm (6 / 5) (min q (25 / 9))
        (fun z => (timePartial φ z * u z i +
          spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) -
          φp z * localizedConvection u Du z i) < ∞ :=
      h123le.trans_lt (ENNReal.add_lt_top.mpr ⟨h12, hconvN' i⟩)
    have h123ae : AEMeasurable (fun z =>
        (timePartial φ z * u z i +
          spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) -
          φp z * localizedConvection u Du z i) volume :=
      h12ae.sub (hconvAE i)
    have h1234le : morreyNorm (6 / 5) (min q (25 / 9))
        (fun z => ((timePartial φ z * u z i +
          spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) -
          φp z * localizedConvection u Du z i) + φp z * f z i) ≤
        morreyNorm (6 / 5) (min q (25 / 9))
          (fun z => (timePartial φ z * u z i +
            spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) -
            φp z * localizedConvection u Du z i) +
        morreyNorm (6 / 5) (min q (25 / 9)) (fun z => φp z * f z i) :=
      morrey_norm_add_le (P := (6 / 5 : ℝ)) (τ := min q (25 / 9))
        (by norm_num) h123ae (hforceAE i)
    have h1234 : morreyNorm (6 / 5) (min q (25 / 9))
        (fun z => ((timePartial φ z * u z i +
          spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) -
          φp z * localizedConvection u Du z i) + φp z * f z i) < ∞ :=
      h1234le.trans_lt (ENNReal.add_lt_top.mpr ⟨h123, hforceN i⟩)
    have h1234ae : AEMeasurable (fun z =>
        ((timePartial φ z * u z i +
          spatialLaplacian (fun x => φ (x, z.2)) z.1 * u z i) -
          φp z * localizedConvection u Du z i) + φp z * f z i) volume :=
      h123ae.add (hforceAE i)
    have hGle := (norm_sub_le_test (P := (6 / 5 : ℝ))
        (θ := min q (25 / 9)) (by norm_num) h1234ae (hDpAE' i)).trans_lt
      (ENNReal.add_lt_top.mpr ⟨h1234, hDpN' i⟩)
    simpa [localizedGradientSourceG, localizedEquationG, localizedConvection,
      φp, sub_eq_add_neg] using hGle
  have hHnorm (j i : Fin 3) : morreyNorm (6 / 5) (25 / 3)
      (fun z => localizedGradientSourceH φ u j z i) < ∞ := by
    have hmul := morrey_norm_mul_le_indicator (6 / 5) (25 / 3) (2 * C)
      (by norm_num) (by positivity) B
      (fun z => -2 * spatialPartial φ j z)
      (fun z => B.indicator (S.indicator (fun w => u w i)) z)
      (fun z => by
        calc
          |(-2 : ℝ) * spatialPartial φ j z| =
              2 * |spatialPartial φ j z| := by
                rw [abs_mul]
                norm_num
          _ ≤ 2 * C := mul_le_mul_of_nonneg_left (hsp j z) (by norm_num))
      (fun z hz => by simp only [hspzero j z hz, mul_zero])
    have hbound := hmul.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hUlow (25 / 3) i (by norm_num) (by norm_num)))
    rw [hHtarget j i]
    simpa [localizedGradientSourceH, localizedEquationH, Pi.smul_apply,
      smul_eq_mul] using hbound
  exact ⟨(fun i => hGae i), (fun j i => hHae j i),
    (fun i => hFc i), (fun j i => hHc j i),
    (fun i => hGnorm i), (fun j i => hHnorm j i)⟩

end CKN.Core.Step4
