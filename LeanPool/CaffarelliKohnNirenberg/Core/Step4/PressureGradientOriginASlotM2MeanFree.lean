/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceCenteredSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceMeanNorm
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSWSData
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareRescale
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedTimeBounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseField
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientMorrey

/-! # The mean-free velocity field on the half-gap collar

On the collar ball the velocity minus its own spatial slice mean obeys the
`L⁶` Sobolev–Poincaré display, so its parabolic Morrey seminorm at the
exponent pair `(2, 25/8)` — the pair the velocity gradient carries — is
controlled by the gradient slice mass and not by the velocity size.  The
volume gain on a cell of radius `r` beats the Morrey normalisation by
`r^{1/10}`, uniformly over all cells and both large and small radii.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4

/-- The `L⁶` mean-free Sobolev–Poincaré display on a ball. -/
theorem originASlot_meanFree_L6_le_gradient
    (x : Vec3) {r : ℝ} (hr : 0 < r)
    (v : H1Function (euclideanBall x r)) :
    eLpNorm (fun y => v.toFun y - average (volume.restrict (euclideanBall x r)) v.toFun)
      6 (volume.restrict (euclideanBall x r)) ≤
      sobolevPoincareL6Constant * eLpNorm v.grad 2 (volume.restrict (euclideanBall x r)) :=
  sobolevPoincare_L6_ball_weak x hr v

/-- Suitable solutions supply the `L⁶` mean-free estimate on almost every slice. -/
theorem originASlot_meanFree_L6_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - r ^ 2) z.2), ∀ j : Fin 3,
      eLpNorm (fun y => u (y, s) j - sourceSliceCentredMean z.1 r u s j) 6
        (volume.restrict (vec3Ball z.1 r)) ≤
      sobolevPoincareL6Constant *
        eLpNorm (fun y => Du (y, s) j) 2 (volume.restrict (vec3Ball z.1 r)) := by
  have heq := euclideanBall_eq_vec3Ball_display (x₀ := z.1) hr
  let _ : IsFiniteMeasure (volume.restrict (vec3Ball z.1 r)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact Integration.volume_vec3Ball_lt_top⟩
  filter_upwards [centredSWS_slice_data hsol hr hsub] with s hs
  intro j
  have hu2 := (hs.1.eval j).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)
  let v : H1Function (euclideanBall z.1 r) :=
    { toFun := fun y => u (y, s) j
      grad := fun y => Du (y, s) j
      memL2 := by simpa only [heq] using hu2
      gradMemL2 := fun k => by simpa only [heq] using ((hs.2.1.eval j).eval k)
      hasWeakGradient := by simpa only [heq] using hs.2.2.2 j }
  simpa only [v, heq, sourceSliceCentredMean] using originASlot_meanFree_L6_le_gradient z.1 hr v

/-- The slice bound for the mean-free field on an arbitrary spatial ball. -/
theorem originASlot_meanFree_clipped_slice_bound
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ) (k : Fin 3)
    (hpoin : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ j : Fin 3,
      eLpNorm (fun y => u (y, s) j - sourceSliceCentredMean z.1 ρ u s j) 6
        (volume.restrict (vec3Ball z.1 ρ)) ≤
      sobolevPoincareL6Constant *
        eLpNorm (fun y => Du (y, s) j) 2 (volume.restrict (vec3Ball z.1 ρ)))
    (hmeas : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), AEStronglyMeasurable
      (fun y => u (y, s) k - sourceSliceCentredMean z.1 ρ u s k)
      (volume.restrict (vec3Ball z.1 ρ)))
    (x : Vec3) {rr : ℝ} (hrr : 0 < rr) :
    ∀ᵐ t ∂volume,
      eLpNorm (fun y => (parabolicCylinder z.1 z.2 ρ).indicator
        (fun w => u w k - sourceSliceCentredMean z.1 ρ u w.2 k) (y, t)) 2
          (volume.restrict (vec3Ball x rr)) ≤
        ENNReal.ofReal (min rr ρ) * ENNReal.ofReal (Real.pi * 4 / 3) ^ (1/3 : ℝ) *
          ((Ioc (z.2 - ρ ^ 2) z.2).indicator (fun t => sobolevPoincareL6Constant *
            eLpNorm (fun y => Du (y, t) k) 2 (volume.restrict (vec3Ball z.1 ρ))) t) := by
  classical
  set J : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2 with hJ
  set S : Set ParabolicPoint := parabolicCylinder z.1 z.2 ρ with hS
  set G : ParabolicPoint → ℝ :=
    S.indicator (fun w => u w k - sourceSliceCentredMean z.1 ρ u w.2 k) with hG
  have hae : ∀ᵐ t ∂volume, t ∈ J →
      (eLpNorm (fun y => u (y, t) k - sourceSliceCentredMean z.1 ρ u t k) 6
        (volume.restrict (vec3Ball z.1 ρ)) ≤
      sobolevPoincareL6Constant *
        eLpNorm (fun y => Du (y, t) k) 2 (volume.restrict (vec3Ball z.1 ρ))) ∧
      AEStronglyMeasurable (fun y => u (y, t) k - sourceSliceCentredMean z.1 ρ u t k)
        (volume.restrict (vec3Ball z.1 ρ)) := by
    rw [← ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hpoin, hmeas] with t ht htm using ⟨ht k, htm⟩
  have h1mem : ∀ (y : Vec3) (t : ℝ), y ∈ vec3Ball z.1 ρ → t ∈ J →
      ((y, t) : ParabolicPoint) ∈ S := fun y t hy ht => ⟨hy, ht⟩
  have hholder : ∀ (F : Vec3 → ℝ) (A : Set Vec3),
      AEStronglyMeasurable F (volume.restrict A) →
      eLpNorm F 2 (volume.restrict A) ≤
        volume A ^ (1/3 : ℝ) * eLpNorm F 6 (volume.restrict A) := by
    intro F A hF
    have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := volume.restrict A) (f := F) (p := 2) (q := 6) (by norm_num) hF
    norm_num only [ENNReal.toReal_ofNat, show (1/(2 : ℝ) - 1/6) = 1/3 by norm_num,
      Measure.restrict_apply_univ] at hh
    rw [mul_comm]
    exact hh
  have hvol : ∀ (c : Vec3) (a : ℝ), 0 ≤ a →
      volume (vec3Ball c a) ^ (1/3 : ℝ) =
        ENNReal.ofReal a * ENNReal.ofReal (Real.pi * 4 / 3) ^ (1/3 : ℝ) := by
    intro c a _
    rw [volume_vec3Ball_eq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.rpow_natCast (ENNReal.ofReal a) 3, ← ENNReal.rpow_mul]
    norm_num
  filter_upwards [hae] with t ht
  by_cases htJ : t ∈ J
  · -- inside the time window: the slice is the ball indicator of the mean-free field
    set W : Vec3 → ℝ := fun y => u (y, t) k - sourceSliceCentredMean z.1 ρ u t k with hW
    have hslice : (fun y => G (y, t)) = (vec3Ball z.1 ρ).indicator W := by
      funext y
      simp only [hG]
      by_cases hy : y ∈ vec3Ball z.1 ρ
      · exact (Set.indicator_of_mem (h1mem y t hy htJ) _).trans (Set.indicator_of_mem hy W).symm
      · exact (Set.indicator_of_notMem (fun hc => hy hc.1)
          (fun w : ParabolicPoint => u w k - sourceSliceCentredMean z.1 ρ u w.2 k)).trans
          (Set.indicator_of_notMem hy W).symm
    have hBm : MeasurableSet (vec3Ball z.1 ρ) := (isOpen_vec3Ball _ _).measurableSet
    have hWm : AEStronglyMeasurable W (volume.restrict (vec3Ball z.1 ρ)) := (ht htJ).2
    have hGm : AEStronglyMeasurable (fun y => G (y, t)) volume := by
      rw [hslice]
      exact (aestronglyMeasurable_indicator_iff hBm).mpr hWm
    have h6 : eLpNorm W 6 (volume.restrict (vec3Ball z.1 ρ)) ≤
        sobolevPoincareL6Constant *
          eLpNorm (fun y => Du (y, t) k) 2 (volume.restrict (vec3Ball z.1 ρ)) := (ht htJ).1
    rw [Set.indicator_of_mem htJ]
    rcases le_total rr ρ with hle | hle
    · rw [min_eq_left hle]
      refine (hholder _ (vec3Ball x rr) hGm.restrict).trans ?_
      rw [hvol x rr hrr.le]
      refine mul_le_mul' le_rfl ?_
      refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
      rw [hslice, eLpNorm_indicator_eq_eLpNorm_restrict hBm]
      exact h6
    · rw [min_eq_right hle]
      have h1 : eLpNorm (fun y => G (y, t)) 2 (volume.restrict (vec3Ball x rr)) ≤
          eLpNorm W 2 (volume.restrict (vec3Ball z.1 ρ)) := by
        refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
        rw [hslice, eLpNorm_indicator_eq_eLpNorm_restrict hBm]
      refine h1.trans ?_
      refine (hholder W (vec3Ball z.1 ρ) hWm).trans ?_
      rw [hvol z.1 ρ hρ.le]
      exact mul_le_mul' le_rfl h6
  · -- outside the time window the slice vanishes
    have hz : (fun y => G (y, t)) = fun _ => (0 : ℝ) := by
      funext y
      simp only [hG]
      exact Set.indicator_of_notMem (fun hc => htJ hc.2) _
    rw [hz]
    simp only [eLpNorm_fun_zero]
    exact bot_le



/-- A scaling inequality: the Morrey normalisation absorbs the smaller radius. -/
theorem originASlot_min_radius_scale_le_one {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ENNReal.ofReal r ^ (-(9/10) : ℝ) * ENNReal.ofReal (min r ρ) ≤ 1 := by
  have hm : 0 < min r ρ := lt_min hr hρ
  have hmne : ENNReal.ofReal (min r ρ) ≠ 0 := (ENNReal.ofReal_pos.mpr hm).ne'
  have hmtop : ENNReal.ofReal (min r ρ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrne : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsplit : ENNReal.ofReal (min r ρ) =
      ENNReal.ofReal (min r ρ) ^ (9/10 : ℝ) * ENNReal.ofReal (min r ρ) ^ (1/10 : ℝ) := by
    rw [← ENNReal.rpow_add _ _ hmne hmtop]
    norm_num
  calc
    ENNReal.ofReal r ^ (-(9/10) : ℝ) * ENNReal.ofReal (min r ρ)
        = ENNReal.ofReal r ^ (-(9/10) : ℝ) *
          (ENNReal.ofReal (min r ρ) ^ (9/10 : ℝ) * ENNReal.ofReal (min r ρ) ^ (1/10 : ℝ)) := by
      rw [← hsplit]
    _ ≤ ENNReal.ofReal r ^ (-(9/10) : ℝ) *
          (ENNReal.ofReal r ^ (9/10 : ℝ) * ENNReal.ofReal ρ ^ (1/10 : ℝ)) := by
      gcongr
      · exact min_le_left _ _
      · exact min_le_right _ _
    _ = ENNReal.ofReal ρ ^ (1/10 : ℝ) := by
      rw [← mul_assoc, ← ENNReal.rpow_add _ _ hrne hrtop]
      norm_num
    _ ≤ 1 := by
      apply ENNReal.rpow_le_one _ (by norm_num)
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal hρ1

/-- The mean-free field has a gradient-shaped Morrey seminorm at the exponent
pair `(2, 25/8)`, uniformly over all cells. -/
theorem originASlot_meanFree_morreyNorm_le
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (k : Fin 3)
    (hpoin : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ j : Fin 3,
      eLpNorm (fun y => u (y, s) j - sourceSliceCentredMean z.1 ρ u s j) 6
        (volume.restrict (vec3Ball z.1 ρ)) ≤
      sobolevPoincareL6Constant *
        eLpNorm (fun y => Du (y, s) j) 2 (volume.restrict (vec3Ball z.1 ρ)))
    (hmeas : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), AEStronglyMeasurable
      (fun y => u (y, s) k - sourceSliceCentredMean z.1 ρ u s k)
      (volume.restrict (vec3Ball z.1 ρ)))
    (hGm : AEMeasurable ((parabolicCylinder z.1 z.2 ρ).indicator
      (fun w => u w k - sourceSliceCentredMean z.1 ρ u w.2 k)) volume) :
    morreyNorm 2 (25/8 : ℝ) ((parabolicCylinder z.1 z.2 ρ).indicator
      (fun w => u w k - sourceSliceCentredMean z.1 ρ u w.2 k)) ≤
      ENNReal.ofReal (Real.pi * 4 / 3) ^ (1/3 : ℝ) *
        (∫⁻ t in Ioc (z.2 - ρ ^ 2) z.2, (sobolevPoincareL6Constant *
          eLpNorm (fun y => Du (y, t) k) 2 (volume.restrict (vec3Ball z.1 ρ))) ^ (2 : ℝ))
          ^ (1/2 : ℝ) := by
  classical
  set J : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2 with hJ
  set V13 : ℝ≥0∞ := ENNReal.ofReal (Real.pi * 4 / 3) ^ (1/3 : ℝ) with hV13
  set G : ParabolicPoint → ℝ := (parabolicCylinder z.1 z.2 ρ).indicator
    (fun w => u w k - sourceSliceCentredMean z.1 ρ u w.2 k) with hG
  set E : ℝ → ℝ≥0∞ := fun t => sobolevPoincareL6Constant *
    eLpNorm (fun y => Du (y, t) k) 2 (volume.restrict (vec3Ball z.1 ρ)) with hE
  set Mg : ℝ≥0∞ := ∫⁻ t in J, E t ^ (2 : ℝ) with hMg
  have hV13top : V13 ≠ ⊤ := by
    rw [hV13]; exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  unfold morreyNorm
  refine iSup_le fun z' => iSup_le fun rr => ?_
  set r : ℝ := rr.1 with hrdef
  have hr : 0 < r := rr.2
  have hslice := originASlot_meanFree_clipped_slice_bound (u := u) (Du := Du) (z := z) hρ k hpoin
    hmeas z'.1 hr
  have hprodm : AEStronglyMeasurable G
      ((volume.restrict (vec3Ball z'.1 r)).prod (volume.restrict (Ioc (z'.2 - r ^ 2) z'.2))) := by
    rw [← originClauseRestrict_prod_eq]
    exact hGm.restrict.aestronglyMeasurable
  have hid := (glued_slice_norm_power_integral (a := 2) (by norm_num) hprodm).2
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  rw [htwo] at hid
  have hcpi : cylinderPowerIntegral 2 G z' r =
      ∫⁻ t in Ioc (z'.2 - r ^ 2) z'.2,
        eLpNorm (fun y => G (y, t)) 2 (volume.restrict (vec3Ball z'.1 r)) ^ (2 : ℝ) := by
    rw [hid]
    simp only [cylinderPowerIntegral, parabolicCylinder, Real.enorm_eq_ofReal_abs]
    rfl
  set A : ℝ≥0∞ := ENNReal.ofReal (min r ρ) * V13 with hA
  have hAtop : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV13top
  have hkey : cylinderPowerIntegral 2 G z' r ≤ A ^ (2 : ℝ) * Mg := by
    rw [hcpi]
    calc
      (∫⁻ t in Ioc (z'.2 - r ^ 2) z'.2,
          eLpNorm (fun y => G (y, t)) 2 (volume.restrict (vec3Ball z'.1 r)) ^ (2 : ℝ))
          ≤ ∫⁻ t in Ioc (z'.2 - r ^ 2) z'.2, A ^ (2 : ℝ) * J.indicator (fun t => E t ^ (2 : ℝ)) t
            := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae hslice] with t htb
        have hind : A ^ (2 : ℝ) * J.indicator (fun t => E t ^ (2 : ℝ)) t =
            (A * J.indicator E t) ^ (2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg A (J.indicator E t) (by norm_num : (0:ℝ) ≤ 2)]
          congr 1
          by_cases ht : t ∈ J
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
          · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
            exact (ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)).symm
        rw [hind]
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        simpa only [hG, hA, hV13, hE, hJ] using htb
      _ ≤ A ^ (2 : ℝ) * Mg := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAtop)]
        refine mul_le_mul' le_rfl ?_
        rw [hMg]
        refine (lintegral_mono_set (Set.subset_univ _)).trans ?_
        rw [Measure.restrict_univ, lintegral_indicator measurableSet_Ioc]
  -- assemble the cell
  rw [morreyCell_eq]
  have hexp : -((5 : ℝ) * (1 - 2 / (25/8 : ℝ)) / 2) = -(9/10 : ℝ) := by norm_num
  rw [hexp]
  calc
    ENNReal.ofReal r ^ (-(9/10 : ℝ)) * cylinderPowerIntegral 2 G z' r ^ (1 / (2:ℝ))
        ≤ ENNReal.ofReal r ^ (-(9/10 : ℝ)) * (A ^ (2 : ℝ) * Mg) ^ (1 / (2:ℝ)) :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hkey (by norm_num))
    _ = (ENNReal.ofReal r ^ (-(9/10 : ℝ)) * ENNReal.ofReal (min r ρ)) *
          (V13 * Mg ^ (1/2 : ℝ)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / (2:ℝ)),
        ← ENNReal.rpow_mul, hA,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2 * (1 / (2:ℝ)))]
      norm_num
      ring
    _ ≤ 1 * (V13 * Mg ^ (1/2 : ℝ)) :=
      mul_le_mul' (originASlot_min_radius_scale_le_one hr hρ hρ1) le_rfl
    _ = V13 * Mg ^ (1/2 : ℝ) := one_mul _

/-- The time integral of the squared slice gradient norms is the cylinder mass. -/
theorem originASlot_gradient_time_mass_eq
    {Du : ParabolicPoint → Fin 3 → Vec3} {z : ParabolicPoint} {ρ : ℝ} (k : Fin 3)
    (hDm : AEMeasurable (fun w : ParabolicPoint => ‖Du w k‖)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)))
    (hsl : ∀ᵐ t ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      AEStronglyMeasurable (fun y => Du (y, t) k) (volume.restrict (vec3Ball z.1 ρ))) :
    (∫⁻ t in Ioc (z.2 - ρ ^ 2) z.2,
      eLpNorm (fun y => Du (y, t) k) 2 (volume.restrict (vec3Ball z.1 ρ)) ^ (2 : ℝ)) =
      cylinderPowerIntegral 2 (fun w => ‖Du w k‖) z ρ := by
  have hprodm : AEStronglyMeasurable (fun w : ParabolicPoint => ‖Du w k‖)
      ((volume.restrict (vec3Ball z.1 ρ)).prod
        (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2))) := by
    rw [← originClauseRestrict_prod_eq]
    exact hDm.aestronglyMeasurable
  have hid := (glued_slice_norm_power_integral (a := 2) (by norm_num) hprodm).2
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  rw [htwo] at hid
  have hcong : (∫⁻ t in Ioc (z.2 - ρ ^ 2) z.2,
      eLpNorm (fun y => Du (y, t) k) 2 (volume.restrict (vec3Ball z.1 ρ)) ^ (2 : ℝ)) =
      ∫⁻ t in Ioc (z.2 - ρ ^ 2) z.2,
        eLpNorm (fun y => ‖Du (y, t) k‖) 2 (volume.restrict (vec3Ball z.1 ρ)) ^ (2 : ℝ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hsl] with t ht
    congr 1
    exact (eLpNorm_norm (f := fun y => Du (y, t) k) ht).symm
  rw [hcong, hid]
  simp only [cylinderPowerIntegral, parabolicCylinder, Real.enorm_eq_ofReal_abs]
  rfl

end CKN.Core.Step4
