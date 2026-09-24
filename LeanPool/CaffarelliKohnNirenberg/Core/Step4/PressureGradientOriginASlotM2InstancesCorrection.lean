/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotCorrectionAssembly
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotM2Riesz
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotM2Split
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotM2MeanFree
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTInstanceInteriorCollar
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTSourceMeasurable
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPComparison
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotM2Data
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotM2EnergyMean

/-! # The centred source correction meets the first slot at the two instances

The correction splits into the divergence source, the cutoff-derivative
quadratic terms and the mean-gradient terms.  The first carries the established
affine budget; the second is measured by a Hölder product of the velocity
against the mean-free velocity, whose own budget is the gradient one through
the `L⁶` Sobolev–Poincaré display; the third pairs the gradient against the
slice mean.  The actual Riesz fields of the three sources then satisfy the
clipped-cell estimate above an explicit threshold depending on nothing.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Foundation.Euclidean
open CKN.Foundation.Heat CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- The absolute coefficient of the centred correction relative to the
divergence-source budget. -/
def originASlotM2Coefficient : ℝ≥0∞ :=
  3 + (9 * ENNReal.ofReal (128 * cutoffGradientConstant) *
      (ENNReal.ofReal (Real.pi * 4 / 3) ^ (1/3 : ℝ) * sobolevPoincareL6Constant) +
    3 * ENNReal.ofReal ((7/4 : ℝ) ^ 3))

/-- The Calderón–Zygmund threshold above which the centred correction meets
the affine first-slot budget. -/
def originASlotM2Threshold (_q : ℝ) : ℝ :=
  (pressureRieszMorreyConstant (25/9) * originASlotM2Coefficient).toReal

theorem originASlotM2Coefficient_lt_top : originASlotM2Coefficient < ⊤ := by
  unfold originASlotM2Coefficient
  have hS := sobolevPoincareL6Constant_lt_top
  finiteness

theorem originASlot_M2_correction_mass_instances :
∀ q τ C_CZ R₀ R₁ ε : ℝ, ∀ KU KD : ℝ≥0∞,
    5 / 2 < q → 25 / 3 ≤ τ → τ ≤ 25 → 0 ≤ C_CZ → originASlotM2Threshold q ≤ C_CZ →
    ∀ hinstances : (τ = 25 / 3 ∧ R₀ = 11 / 16 ∧ R₁ = 43 / 64) ∨
      (τ = 25 ∧ R₀ = 5 / 8 ∧ R₁ = 19 / 32),
    0 < R₁ → R₁ < R₀ → R₀ < 3 / 4 → 0 ≤ ε → KU < ⊤ → KD < ⊤ →
    ∀ {Ω : Set Vec3} {I : Set ℝ}
      {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
      (∀ i, morreyNorm 3 τ
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU) →
      (∀ i j, morreyNorm 2 (25 / 8 : ℝ)
        ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD) →
      ((∫⁻ z in parabolicCylinder 0 0 1,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) →
      ∀ i : Fin 3, ∀ z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁),
        ∀ r : ℝ, 0 < r → r ≤ 1 / 256 →
        let hρ : 0 < (R₀-R₁)/2 := by
          rcases hinstances with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num
        let η := mollifiedBallCutoff z.1 hρ
        let c := sourceSliceCentredMean z.1 ((R₀-R₁)/2) u
        (∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
          eLpNorm (fun x => ∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
            (rieszSecondL2_weak_type j i)
            (centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) η (spatialDeriv η)
              (fun y => u (y,s)) (fun y => f (y,s)) (fun y => Du (y,s)) (c s) j) x) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (vec3Ball z.1 r ∩ vec3Ball (0 : Vec3) R₁)) ^ (6 / 5 : ℝ)) ≤
          originKPAffineASlot q C_CZ ε KU KD * ENNReal.ofReal
            (r ^ (5 * (1 - (6 / 5 : ℝ) / min ((1 / τ + 8 / 25)⁻¹) q))) := by
  classical
  intro q τ C_CZ R₀ R₁ ε KU KD hq hτ hτhi hC0 hCM2 hinstances hR₁ hgap hR₀ hε hKU hKD Ω I u Du
    p f hsol hdom hU hD hsize i z hz r hr hcell hρ
  have hnum : (1 : ℝ)/128 ≤ (R₀-R₁)/2 ∧ (R₀-R₁)/2 ≤ 1 ∧ (1:ℝ)/256 ≤ (R₀-R₁)/4 ∧ R₀ ≤ 1 := by
    rcases hinstances with ⟨_, h₀, h₁⟩ | ⟨_, h₀, h₁⟩ <;> rw [h₀, h₁] <;> norm_num
  obtain ⟨hρlo, hρ1, hfit, hR₀le⟩ := hnum
  have hR₀pos : (0 : ℝ) < R₀ := hR₁.trans hgap
  -- carriers
  set ρ : ℝ := (R₀-R₁)/2 with hρdef
  set J : Set ℝ := Ioc (z.2 - ρ^2) z.2 with hJdef
  set S : Set ParabolicPoint := vec3Ball (0 : Vec3) R₀ ×ˢ J with hSdef
  set S₃ : Set ParabolicPoint := vec3Ball z.1 (3*ρ/4) ×ˢ J with hS₃def
  set Sρ : Set ParabolicPoint := parabolicCylinder z.1 z.2 ρ with hSρdef
  have hSρeq : Sρ = vec3Ball z.1 ρ ×ˢ J := rfl
  have hSm : MeasurableSet S :=
    (isOpen_vec3Ball _ _).measurableSet.prod measurableSet_Ioc
  have hS₃m : MeasurableSet S₃ :=
    (isOpen_vec3Ball _ _).measurableSet.prod measurableSet_Ioc
  have hSρm : MeasurableSet Sρ := measurableSet_parabolicCylinder _ _ _
  have hQ₀₁ : parabolicCylinder (0 : Vec3) 0 R₀ ⊆ parabolicCylinder (0 : Vec3) 0 1 :=
    parabolicCylinder_mono hR₀pos.le hR₀le
  have hSρQ : Sρ ⊆ parabolicCylinder (0 : Vec3) 0 R₀ := fun w hw =>
    half_gap_collar_closure_subset_outer hR₁ hgap hz (subset_closure hw)
  have hzmem : z.1 ∈ vec3Ball z.1 ρ := by
    rw [mem_vec3Ball, sub_self]
    simpa only [vec3EuclideanNorm_zero] using hρ
  have hJsub : J ⊆ Ioc (0 - R₀^2) 0 := by
    intro s hs
    have hmem : ((z.1, s) : ParabolicPoint) ∈ Sρ := ⟨hzmem, hs⟩
    exact (hSρQ hmem).2
  have hSQ : S ⊆ parabolicCylinder (0 : Vec3) 0 R₀ := fun w hw => ⟨hw.1, hJsub hw.2⟩
  have hS₃sub : S₃ ⊆ Sρ := fun w hw =>
    ⟨vec3Ball_mono (by linarith only [hρ]) hw.1, hw.2⟩
  have hcollar : closure Sρ ⊆ spaceTimeSet Ω I := fun w hw =>
    hdom (subset_closure (hQ₀₁ (half_gap_collar_closure_subset_outer hR₁ hgap hz hw)))
  -- slice data
  have hslice := centredSWS_slice_data hsol hρ hcollar
  have hpoin := originASlot_meanFree_L6_ae_of_sws hsol hρ hcollar
  have hmeask : ∀ k : Fin 3, ∀ᵐ s ∂volume.restrict J, AEStronglyMeasurable
      (fun y => u (y, s) k - sourceSliceCentredMean z.1 ρ u s k)
      (volume.restrict (vec3Ball z.1 ρ)) := by
    intro k
    filter_upwards [hslice] with s hs
    exact (hs.1.eval k).aestronglyMeasurable.sub aestronglyMeasurable_const
  have hDslk : ∀ k : Fin 3, ∀ᵐ t ∂volume.restrict J,
      AEStronglyMeasurable (fun y => Du (y, t) k) (volume.restrict (vec3Ball z.1 ρ)) := by
    intro k
    filter_upwards [hslice] with s hs
    exact (hs.2.1.eval k).aestronglyMeasurable
  -- measurability of the data on the three carriers
  have hdataS := originASlot_unit_box_data hsol hdom (hSQ.trans hQ₀₁)
  have hdataSρ := originASlot_unit_box_data hsol hdom (hSρQ.trans hQ₀₁)
  have hdataS₃ := originASlot_unit_box_data hsol hdom ((hS₃sub.trans hSρQ).trans hQ₀₁)
  have hcS : ∀ k, AEMeasurable
      (fun w : ParabolicPoint => sourceSliceCentredMean z.1 ρ u w.2 k) (volume.restrict S) :=
    fun k => originASlot_slice_mean_aemeasurable hsol hρ hcollar (vec3Ball (0 : Vec3) R₀) k
  have hcSρ : ∀ k, AEMeasurable
      (fun w : ParabolicPoint => sourceSliceCentredMean z.1 ρ u w.2 k) (volume.restrict Sρ) :=
    fun k => originASlot_slice_mean_aemeasurable hsol hρ hcollar (vec3Ball z.1 ρ) k
  have hcS₃ : ∀ k, AEMeasurable
      (fun w : ParabolicPoint => sourceSliceCentredMean z.1 ρ u w.2 k) (volume.restrict S₃) :=
    fun k => originASlot_slice_mean_aemeasurable hsol hρ hcollar (vec3Ball z.1 (3*ρ/4)) k
  obtain ⟨Bx, Jb, hbox, hQbox⟩ := exists_localBox_of_closure_subset hsol.1 hsol.2.1
    (by norm_num : (0 : ℝ) < 1) hdom
  have hdbox := hsol.2.2.2.2.2.1 Bx Jb hbox
  have hDuvec : ∀ k, AEMeasurable (fun w => Du w k) (volume.restrict Sρ) := fun k =>
    ((measurable_pi_apply k).comp_aemeasurable hdbox.2.1.aemeasurable).mono_measure
      (Measure.restrict_mono_set volume (((hSρQ.trans hQ₀₁).trans hQbox)))
  -- cutoff bounds
  have hcgnn : 0 ≤ cutoffGradientConstant / ρ :=
    (vecEuclideanNorm_nonneg _).trans (mollifiedBallCutoff_gradient_bound z.1 hρ z.1)
  have hcg : 0 ≤ cutoffGradientConstant := by
    have h := mul_nonneg hcgnn hρ.le
    rwa [div_mul_cancel₀ _ hρ.ne'] at h
  set Kη : ℝ := 128 * cutoffGradientConstant with hKηdef
  have hKηnn : 0 ≤ Kη := by positivity
  have hdηb : ∀ (k : Fin 3) (x : Vec3),
      |spatialDeriv (mollifiedBallCutoff z.1 hρ) k x| ≤ Kη := by
    intro k x
    refine le_trans ((abs_apply_le_vecEuclideanNorm
      (classicalGradient (mollifiedBallCutoff z.1 hρ) x) k).trans
      (mollifiedBallCutoff_gradient_bound z.1 hρ x)) ?_
    rw [hKηdef, div_le_iff₀ hρ]
    nlinarith only [hcg, hρlo, hρ]
  have hηsupp := originASlot_cutoff_zero_off_collar z.1 hρ
  have hdηsupp := originASlot_dcutoff_zero_off_collar z.1 hρ
  -- the four budgets
  set X : ℝ≥0∞ := 3*KU*KD + forceSourceMorreyBound q ε with hXdef
  set Mfree : ℝ≥0∞ := ENNReal.ofReal (Real.pi * 4 / 3) ^ (1/3 : ℝ) *
    sobolevPoincareL6Constant * (3 * KD) with hMfreedef
  set Mc : ℝ≥0∞ := ENNReal.ofReal ((7/4 : ℝ)^3) * KU with hMcdef
  have hQmeas : ∀ k, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
      (fun w : ParabolicPoint => u w k)) volume := fun k =>
    (aemeasurable_indicator_iff (measurableSet_parabolicCylinder _ _ _)).mpr
      ((originASlot_unit_box_data hsol hdom hQ₀₁).1 k)
  have hQDmeas : ∀ k l, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
      (fun w : ParabolicPoint => Du w k l)) volume := fun k l =>
    (aemeasurable_indicator_iff (measurableSet_parabolicCylinder _ _ _)).mpr
      ((originASlot_unit_box_data hsol hdom hQ₀₁).2.1 k l)
  have hGmeas : ∀ k, AEMeasurable (Sρ.indicator
      (fun w : ParabolicPoint => u w k - sourceSliceCentredMean z.1 ρ u w.2 k)) volume := fun k =>
    (aemeasurable_indicator_iff hSρm).mpr ((hdataSρ.1 k).sub (hcSρ k))
  have hwbound : ∀ k, morreyNorm 2 (25/8 : ℝ) (Sρ.indicator
      (fun w : ParabolicPoint => u w k - sourceSliceCentredMean z.1 ρ u w.2 k)) ≤ Mfree := by
    intro k
    exact originASlot_meanFree_morreyNorm_le_gradient_budget (R₀ := R₀) hρ hρ1 k
      hpoin (hmeask k) (hGmeas k) (hDuvec k).norm (hDslk k) hSρQ (hQDmeas k) (hD k)
  have hcbound : ∀ k, morreyNorm 3 τ (S₃.indicator
      (fun w : ParabolicPoint => sourceSliceCentredMean z.1 ρ u w.2 k)) ≤ Mc := by
    intro k
    exact gap_centred_mean_carrier_morreyNorm_le z.1 hρ (by linarith only [hτ])
      (half_gap_ball_subset_outer hR₁ hgap hz) k hKU.ne (hQmeas k) (hU k)
      (fun w hw => hw.1) (fun w hw => by simpa only [zero_sub] using hJsub hw.2)
  have hubound : ∀ j : Fin 3, morreyNorm 3 τ
      (S₃.indicator (fun w : ParabolicPoint => u w j)) ≤ KU := fun j =>
    (morreyNorm_indicator_mono_set (by norm_num : (0:ℝ) ≤ 3) (hS₃sub.trans hSρQ) _).trans (hU j)
  have hdbound : ∀ j k : Fin 3, morreyNorm 2 (25/8 : ℝ)
      (Sρ.indicator (fun w : ParabolicPoint => Du w j k)) ≤ KD := fun j k =>
    (morreyNorm_indicator_mono_set (by norm_num : (0:ℝ) ≤ 2) hSρQ _).trans (hD j k)
  have hAbound : ∀ j : Fin 3, morreyNorm (6/5 : ℝ) (min ((1/τ + 8/25 : ℝ)⁻¹) q)
      (S.indicator (fun v : ParabolicPoint => (∑ k, Du v j k * u v k) - f v j)) ≤ 3 * X :=
    fun j => originASlot_divergence_source_morreyNorm_le q τ R₀ ε KU KD hq hτ hR₀pos hR₀le
      hsol hdom hU hD hsize hSQ j
  -- the correction's majorant
  have hNraw : ∀ j : Fin 3, morreyNorm (6/5 : ℝ) (min ((1/τ + 8/25 : ℝ)⁻¹) q)
      (S.indicator (fun v : ParabolicPoint =>
        centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) (mollifiedBallCutoff z.1 hρ)
          (spatialDeriv (mollifiedBallCutoff z.1 hρ))
          (fun y => u (y, v.2)) (fun y => f (y, v.2)) (fun y => Du (y, v.2))
          (sourceSliceCentredMean z.1 ρ u v.2) j v.1)) ≤
      3 * X + ENNReal.ofReal Kη * (3 * (KU * Mfree)) + 3 * (KD * Mc) := by
    intro j
    refine originASlot_correction_morreyNorm_le (x₀ := z.1) (z₀ := z) (R := ρ)
      hτ hq hKηnn hρ hρ1
      (mollifiedBallCutoff_nonneg z.1 hρ) (mollifiedBallCutoff_le_one z.1 hρ) hdηb
      hηsupp hdηsupp (fun w hw => hw.1) (fun w hw hc' => show w ∈ S₃ from ⟨hc', hw.2⟩) hS₃sub hS₃sub j
      ((aemeasurable_indicator_iff hSm).mpr
        ((Finset.aemeasurable_fun_sum _ (fun k _ => (hdataS.2.1 j k).mul (hdataS.1 k))).sub
          (hdataS.2.2 j)))
      ((aemeasurable_indicator_iff hS₃m).mpr (hdataS₃.1 j))
      (fun k => hGmeas k)
      (fun k => (aemeasurable_indicator_iff hS₃m).mpr (hcS₃ k))
      (fun k => (aemeasurable_indicator_iff hSρm).mpr (hdataSρ.2.1 j k))
      (hAbound j) (hubound j) hwbound hcbound (hdbound j)
  -- absorb the coefficients into the source budget
  have hKUKD : KU * KD ≤ X := by
    rw [hXdef]
    refine le_trans ?_ le_self_add
    calc KU * KD = 1 * (KU * KD) := (one_mul _).symm
      _ ≤ 3 * (KU * KD) := mul_le_mul' (by norm_num) le_rfl
      _ = 3 * KU * KD := by ring
  have hcollapse : 3 * X + ENNReal.ofReal Kη * (3 * (KU * Mfree)) + 3 * (KD * Mc)
      ≤ originASlotM2Coefficient * X := by
    have e1 : ENNReal.ofReal Kη * (3 * (KU * Mfree)) =
        (9 * ENNReal.ofReal Kη *
          (ENNReal.ofReal (Real.pi * 4 / 3) ^ (1/3 : ℝ) * sobolevPoincareL6Constant)) *
            (KU * KD) := by
      rw [hMfreedef]; ring
    have e2 : 3 * (KD * Mc) =
        (3 * ENNReal.ofReal ((7/4 : ℝ) ^ 3)) * (KU * KD) := by
      rw [hMcdef]; ring
    rw [e1, e2, originASlotM2Coefficient, hKηdef]
    calc
      3 * X + 9 * ENNReal.ofReal (128 * cutoffGradientConstant) *
            (ENNReal.ofReal (Real.pi * 4 / 3) ^ (1/3 : ℝ) * sobolevPoincareL6Constant) *
            (KU * KD) + 3 * ENNReal.ofReal ((7/4 : ℝ) ^ 3) * (KU * KD)
          ≤ 3 * X + 9 * ENNReal.ofReal (128 * cutoffGradientConstant) *
            (ENNReal.ofReal (Real.pi * 4 / 3) ^ (1/3 : ℝ) * sobolevPoincareL6Constant) * X +
            3 * ENNReal.ofReal ((7/4 : ℝ) ^ 3) * X := by
        gcongr
      _ = (3 + (9 * ENNReal.ofReal (128 * cutoffGradientConstant) *
            (ENNReal.ofReal (Real.pi * 4 / 3) ^ (1/3 : ℝ) * sobolevPoincareL6Constant) +
            3 * ENNReal.ofReal ((7/4 : ℝ) ^ 3))) * X := by ring
  have hN : ∀ j : Fin 3, morreyNorm (6/5 : ℝ) (min ((1/τ + 8/25 : ℝ)⁻¹) q)
      (S.indicator (fun v : ParabolicPoint =>
        centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) (mollifiedBallCutoff z.1 hρ)
          (spatialDeriv (mollifiedBallCutoff z.1 hρ))
          (fun y => u (y, v.2)) (fun y => f (y, v.2)) (fun y => Du (y, v.2))
          (sourceSliceCentredMean z.1 ρ u v.2) j v.1)) ≤
      originASlotM2Coefficient * X := fun j => (hNraw j).trans hcollapse
  -- finiteness and the threshold
  have hXtop : X < ⊤ := by
    rw [hXdef]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) hKU) hKD,
      forceSourceMorreyBound_lt_top q ε hq⟩
  have hprodtop : pressureRieszMorreyConstant (25/9) * originASlotM2Coefficient ≠ ⊤ :=
    ENNReal.mul_ne_top (pressureRieszMorreyConstant_lt_top _).ne
      originASlotM2Coefficient_lt_top.ne
  have hcoef : pressureRieszMorreyConstant (25/9) * originASlotM2Coefficient ≤
      ENNReal.ofReal (|C_CZ| + 1) := by
    rw [← ENNReal.ofReal_toReal hprodtop]
    refine ENNReal.ofReal_le_ofReal ?_
    have habs := le_abs_self C_CZ
    have hdef : originASlotM2Threshold q =
        (pressureRieszMorreyConstant (25/9) * originASlotM2Coefficient).toReal := rfl
    rw [← hdef]
    linarith only [hCM2, habs]
  -- measurability and slice membership of the correction sources
  have hFm : ∀ j : Fin 3, AEMeasurable (S.indicator (fun v : ParabolicPoint =>
      centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) (mollifiedBallCutoff z.1 hρ)
        (spatialDeriv (mollifiedBallCutoff z.1 hρ))
        (fun y => u (y, v.2)) (fun y => f (y, v.2)) (fun y => Du (y, v.2))
        (sourceSliceCentredMean z.1 ρ u v.2) j v.1)) volume := fun j =>
    originASlot_correction_aemeasurable hρ hSm hdataS.1 hdataS.2.1 hdataS.2.2 hcS j
  have hsupp0 : ∀ j : Fin 3, ∀ w ∉ parabolicCylinder (0 : Vec3) 0 R₀,
      S.indicator (fun v : ParabolicPoint =>
        centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) (mollifiedBallCutoff z.1 hρ)
          (spatialDeriv (mollifiedBallCutoff z.1 hρ))
          (fun y => u (y, v.2)) (fun y => f (y, v.2)) (fun y => Du (y, v.2))
          (sourceSliceCentredMean z.1 ρ u v.2) j v.1) w = 0 := by
    intro j w hw
    exact Set.indicator_of_notMem (fun hc' => hw (hSQ hc')) _
  have hFs : ∀ j : Fin 3, ∀ᵐ s ∂volume, MemLp (fun y =>
      S.indicator (fun v : ParabolicPoint =>
        centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) (mollifiedBallCutoff z.1 hρ)
          (spatialDeriv (mollifiedBallCutoff z.1 hρ))
          (fun y => u (y, v.2)) (fun y => f (y, v.2)) (fun y => Du (y, v.2))
          (sourceSliceCentredMean z.1 ρ u v.2) j v.1) (y, s))
      (ENNReal.ofReal (6/5 : ℝ)) volume := by
    intro j
    refine glued_supported_source_slice_memLp (F := _)
      (κ := min ((1/τ + 8/25 : ℝ)⁻¹) q) (z₀ := ((0 : Vec3), (0 : ℝ))) (hFm j) ?_ hR₀pos
      (hsupp0 j)
    exact (hN j).trans_lt (ENNReal.mul_lt_top originASlotM2Coefficient_lt_top hXtop)
  exact originASlot_correction_mass_of_morrey_bound q τ C_CZ R₀ R₁ ε KU KD
    originASlotM2Coefficient hq hτ hτhi hcoef hR₁ hgap z hz i r hr (hcell.trans hfit) hρ
    _ (fun j => rfl) hFm hFs hN

end CKN.Core.Step4
