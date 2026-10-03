/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTSourceMeasurable
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseField
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPComparison
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotM2MeanFree
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotM2Split
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsBridge
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTCentredSourceCorrection

/-! # Data for the centred source correction on the half-gap collar

Joint measurability of the velocity, its gradient, the force and the spatial
slice mean; the divergence source's Morrey budget on any carrier inside the
outer cylinder; and the gradient-shaped budget for the mean-free velocity.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Foundation.Euclidean
open CKN.Foundation.Heat CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- Component measurability of the data on any subset of the unit cylinder. -/
theorem originASlot_unit_box_data
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    {S : Set ParabolicPoint} (hS : S ⊆ parabolicCylinder (0 : Vec3) 0 1) :
    (∀ i, AEMeasurable (fun w => u w i) (volume.restrict S)) ∧
    (∀ i j, AEMeasurable (fun w => Du w i j) (volume.restrict S)) ∧
    (∀ i, AEMeasurable (fun w => f w i) (volume.restrict S)) := by
  obtain ⟨B, J, hbox, hQbox⟩ := exists_localBox_of_closure_subset hsol.1 hsol.2.1
    (by norm_num : (0 : ℝ) < 1) hdom
  have hd := hsol.2.2.2.2.2.1 B J hbox
  have hm := Measure.restrict_mono_set volume (hS.trans hQbox)
  refine ⟨fun i => ?_, fun i j => ?_, fun i => ?_⟩
  · exact ((measurable_pi_apply i).comp_aemeasurable hd.1.aemeasurable).mono_measure hm
  · exact ((measurable_pi_apply j).comp_aemeasurable
      ((measurable_pi_apply i).comp_aemeasurable hd.2.1.aemeasurable)).mono_measure hm
  · exact ((measurable_pi_apply i).comp_aemeasurable hd.2.2.2.1.aemeasurable).mono_measure hm

/-- The slice mean is jointly measurable on every product carrier over the
collar time window. -/
theorem originASlot_slice_mean_aemeasurable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (A : Set Vec3) (i : Fin 3) :
    AEMeasurable (fun w : ParabolicPoint => sourceSliceCentredMean z.1 ρ u w.2 i)
      (volume.restrict (A ×ˢ Ioc (z.2 - ρ ^ 2) z.2)) := by
  set B : Set Vec3 := vec3Ball z.1 ρ with hB
  set J : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2 with hJ
  obtain ⟨Ω', J', hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J' hbox
  have hSsub : parabolicCylinder z.1 z.2 ρ ⊆ spaceTimeSet Ω' J' := prod_mono hball htime
  have hu := hdata.1.aemeasurable.mono_measure (Measure.restrict_mono_set volume hSsub)
  have hU : AEMeasurable (fun w => u w i) (volume.restrict (parabolicCylinder z.1 z.2 ρ)) :=
    (measurable_pi_apply i).comp_aemeasurable hu
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ J) =
      (volume.restrict B).prod ((volume : Measure ℝ).restrict J) := by
    rw [volume_eq_prod, ← Measure.prod_restrict]
  have hUi : AEStronglyMeasurable (fun w : Vec3 × ℝ => u w i)
      ((volume.restrict B).prod ((volume : Measure ℝ).restrict J)) := by
    rw [← hprod]
    exact hU.aestronglyMeasurable
  have hmm := hUi.prod_swap.integral_prod_right'.aemeasurable
  have ha : AEMeasurable (fun s => sourceSliceCentredMean z.1 ρ u s i)
      ((volume : Measure ℝ).restrict J) := by
    simp only [sourceSliceCentredMean, average_eq, smul_eq_mul]
    exact hmm.const_mul _
  have hl := ha.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_snd (μ := volume.restrict A))
  have hprodA : (volume : Measure (Vec3 × ℝ)).restrict (A ×ˢ J) =
      (volume.restrict A).prod ((volume : Measure ℝ).restrict J) := by
    rw [volume_eq_prod, ← Measure.prod_restrict]
  change AEMeasurable (fun w : Vec3 × ℝ => sourceSliceCentredMean z.1 ρ u w.2 i)
    ((volume : Measure (Vec3 × ℝ)).restrict (A ×ˢ J))
  rw [hprodA]
  exact hl

/-- A component of an indicator vector field is below the indicator norm. -/
theorem morreyNorm_indicator_component_le_vector {p κ : ℝ} (hp : 0 ≤ p)
    (S : Set ParabolicPoint) (G : ParabolicPoint → Vec3) (j : Fin 3) :
    morreyNorm p κ (S.indicator (fun w => G w j)) ≤
      morreyNorm p κ (fun w => vec3EuclideanNorm (S.indicator G w)) := by
  apply routeA_morreyNorm_mono_ae hp
  apply Filter.Eventually.of_forall
  intro w
  by_cases hw : w ∈ S
  · simp only [Set.indicator_of_mem hw, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact abs_apply_le_vec3EuclideanNorm (G w) j
  · simp only [Set.indicator_of_notMem hw, abs_zero]
    exact abs_nonneg _

/-- The divergence source on any carrier inside the outer cylinder has the
established affine Morrey budget. -/
theorem originASlot_divergence_source_morreyNorm_le
    (q τ R₀ ε : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hR₀ : 0 < R₀) (hR₀le : R₀ ≤ 1)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hU : ∀ i, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU)
    (hD : ∀ i j, morreyNorm 2 (25 / 8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD)
    (hsize : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε)
    {S : Set ParabolicPoint} (hS : S ⊆ parabolicCylinder (0 : Vec3) 0 R₀) (j : Fin 3) :
    morreyNorm (6/5 : ℝ) (min ((1/τ + 8/25 : ℝ)⁻¹) q)
      (S.indicator (fun v : ParabolicPoint => (∑ k, Du v j k * u v k) - f v j)) ≤
      3 * (3*KU*KD + forceSourceMorreyBound q ε) := by
  have hvec := (origin_divergence_source_numerical_bounds_of_sws q τ R₀ R₀ ε KU KD
    hq hτ hR₀ le_rfl hR₀le hsol hdom hU hD hsize).1
  refine le_trans (morreyNorm_indicator_mono_set (by norm_num : (0:ℝ) ≤ 6/5) hS _) ?_
  exact (morreyNorm_indicator_component_le_vector (by norm_num : (0:ℝ) ≤ 6/5)
    (parabolicCylinder (0 : Vec3) 0 R₀)
    (fun w => fun i => (∑ k, Du w i k * u w k) - f w i) j).trans hvec

/-- The collar gradient mass is controlled by the gradient Morrey budget. -/
theorem originASlot_gradient_mass_le
    {R₀ ρ : ℝ} {z : ParabolicPoint} (hρ : 0 < ρ) {KD : ℝ≥0∞} (k : Fin 3)
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hcyl : parabolicCylinder z.1 z.2 ρ ⊆ parabolicCylinder (0 : Vec3) 0 R₀)
    (hDm : ∀ l, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
      (fun w : ParabolicPoint => Du w k l)) volume)
    (hD : ∀ l, morreyNorm 2 (25/8 : ℝ) ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
      (fun w : ParabolicPoint => Du w k l)) ≤ KD) :
    cylinderPowerIntegral 2 (fun w : ParabolicPoint => ‖Du w k‖) z ρ ≤
      ENNReal.ofReal ρ ^ (5 * (1 - (2 : ℝ) / (25/8 : ℝ))) * (3 * KD) ^ (2 : ℝ) := by
  set Q : Set ParabolicPoint := parabolicCylinder (0 : Vec3) 0 R₀ with hQ
  set H : ParabolicPoint → ℝ := fun w => ∑ l, |Q.indicator (fun v : ParabolicPoint => Du v k l) w|
    with hH
  have hHm : AEMeasurable H volume := by
    refine Finset.aemeasurable_fun_sum _ fun l _ => ?_
    simpa only [Real.norm_eq_abs] using (hDm l).norm
  have hpt : ∀ w ∈ parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal ‖Du w k‖ ^ (2 : ℝ) ≤ ENNReal.ofReal |H w| ^ (2 : ℝ) := by
    intro w hw
    refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) (by norm_num)
    have hsum : ‖Du w k‖ ≤ ∑ l, |Du w k l| := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun l => ?_
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun l : Fin 3 => |Du w k l|)
        (fun l _ => abs_nonneg _) (Finset.mem_univ l)
    refine hsum.trans (le_trans (le_of_eq ?_) (le_abs_self _))
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Set.indicator_of_mem (hcyl hw)]
  have hmass : cylinderPowerIntegral 2 (fun w : ParabolicPoint => ‖Du w k‖) z ρ ≤
      cylinderPowerIntegral 2 H z ρ := by
    refine setLIntegral_mono_ae' (measurableSet_parabolicCylinder _ _ _) ?_
    refine Filter.Eventually.of_forall fun w hw => ?_
    have hx := hpt w hw
    rwa [abs_of_nonneg (norm_nonneg (Du w k))]
  refine hmass.trans ?_
  refine (cylinderPowerIntegral_le_morreyNorm_pow (q := (25/8 : ℝ))
    (by norm_num : (0:ℝ) < 2) hHm hρ).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ (by norm_num))
  refine (morreyNorm_sum_three_abs_le (by norm_num : (1:ℝ) ≤ 2)
    (fun l => hDm l)).trans ?_
  calc
    (∑ l, morreyNorm 2 (25/8 : ℝ) (Q.indicator (fun v : ParabolicPoint => Du v k l)))
        ≤ ∑ _l : Fin 3, KD := Finset.sum_le_sum fun l _ => hD l
    _ = 3 * KD := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num


/-- The mean-free factor carries the gradient budget, with an absolute
coefficient. -/
theorem originASlot_meanFree_morreyNorm_le_gradient_budget
    {R₀ ρ : ℝ} {z : ParabolicPoint} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {KD : ℝ≥0∞} (k : Fin 3)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hpoin : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ j : Fin 3,
      eLpNorm (fun y => u (y, s) j - sourceSliceCentredMean z.1 ρ u s j) 6
        (volume.restrict (vec3Ball z.1 ρ)) ≤
      sobolevPoincareL6Constant *
        eLpNorm (fun y => Du (y, s) j) 2 (volume.restrict (vec3Ball z.1 ρ)))
    (hmeas : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), AEStronglyMeasurable
      (fun y => u (y, s) k - sourceSliceCentredMean z.1 ρ u s k)
      (volume.restrict (vec3Ball z.1 ρ)))
    (hGm : AEMeasurable ((parabolicCylinder z.1 z.2 ρ).indicator
      (fun w => u w k - sourceSliceCentredMean z.1 ρ u w.2 k)) volume)
    (hDnorm : AEMeasurable (fun w : ParabolicPoint => ‖Du w k‖)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)))
    (hDsl : ∀ᵐ t ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      AEStronglyMeasurable (fun y => Du (y, t) k) (volume.restrict (vec3Ball z.1 ρ)))
    (hcyl : parabolicCylinder z.1 z.2 ρ ⊆ parabolicCylinder (0 : Vec3) 0 R₀)
    (hDm : ∀ l, AEMeasurable ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
      (fun w : ParabolicPoint => Du w k l)) volume)
    (hD : ∀ l, morreyNorm 2 (25/8 : ℝ) ((parabolicCylinder (0 : Vec3) 0 R₀).indicator
      (fun w : ParabolicPoint => Du w k l)) ≤ KD) :
    morreyNorm 2 (25/8 : ℝ) ((parabolicCylinder z.1 z.2 ρ).indicator
      (fun w => u w k - sourceSliceCentredMean z.1 ρ u w.2 k)) ≤
      ENNReal.ofReal (Real.pi * 4 / 3) ^ (1/3 : ℝ) * sobolevPoincareL6Constant * (3 * KD) := by
  classical
  set V13 : ℝ≥0∞ := ENNReal.ofReal (Real.pi * 4 / 3) ^ (1/3 : ℝ) with hV13
  set C : ℝ≥0∞ := sobolevPoincareL6Constant with hC
  set E : ℝ → ℝ≥0∞ := fun t =>
    eLpNorm (fun y => Du (y, t) k) 2 (volume.restrict (vec3Ball z.1 ρ)) with hE
  have hCtop : C ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) sobolevPoincareL6Constant_lt_top.ne
  have hsplit : (∫⁻ t in Ioc (z.2 - ρ ^ 2) z.2, (C * E t) ^ (2 : ℝ)) =
      C ^ (2 : ℝ) * ∫⁻ t in Ioc (z.2 - ρ ^ 2) z.2, E t ^ (2 : ℝ) := by
    rw [← lintegral_const_mul' _ _ hCtop]
    refine lintegral_congr fun t => ?_
    exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  have hid := originASlot_gradient_time_mass_eq (Du := Du) (z := z) (ρ := ρ) k hDnorm hDsl
  have hmass := originASlot_gradient_mass_le (R₀ := R₀) hρ k hcyl hDm hD
  refine (originASlot_meanFree_morreyNorm_le hρ hρ1 k hpoin hmeas hGm).trans ?_
  rw [hsplit, hid]
  have hstep : C ^ (2 : ℝ) * cylinderPowerIntegral 2 (fun w : ParabolicPoint => ‖Du w k‖) z ρ ≤
      C ^ (2 : ℝ) * (ENNReal.ofReal ρ ^ (5 * (1 - (2 : ℝ) / (25/8 : ℝ))) * (3 * KD) ^ (2 : ℝ)) :=
    mul_le_mul' le_rfl hmass
  refine (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hstep (by norm_num : (0:ℝ) ≤ 1/2))).trans ?_
  have hexp : (5 : ℝ) * (1 - (2 : ℝ) / (25/8 : ℝ)) = 9/5 := by norm_num
  rw [hexp, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num
  calc
    V13 * (C * (ENNReal.ofReal ρ ^ (9/10 : ℝ) * (3 * KD)))
        ≤ V13 * (C * (1 * (3 * KD))) := by
      gcongr
      refine ENNReal.rpow_le_one ?_ (by norm_num)
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal hρ1
    _ = V13 * C * (3 * KD) := by rw [one_mul, mul_assoc]

/-- The carrier-restricted centred correction is jointly measurable. -/
theorem originASlot_correction_aemeasurable
    {R₀ ρ : ℝ} {z : ParabolicPoint} (hρ : 0 < ρ) {S : Set ParabolicPoint}
    {u f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hSm : MeasurableSet S)
    (hu : ∀ i, AEMeasurable (fun w => u w i) (volume.restrict S))
    (hDu : ∀ i j, AEMeasurable (fun w => Du w i j) (volume.restrict S))
    (hf : ∀ i, AEMeasurable (fun w => f w i) (volume.restrict S))
    (hc : ∀ i, AEMeasurable (fun w : ParabolicPoint => sourceSliceCentredMean z.1 ρ u w.2 i)
      (volume.restrict S))
    (j : Fin 3) :
    AEMeasurable (S.indicator (fun v : ParabolicPoint =>
      centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) (mollifiedBallCutoff z.1 hρ)
        (spatialDeriv (mollifiedBallCutoff z.1 hρ))
        (fun y => u (y, v.2)) (fun y => f (y, v.2)) (fun y => Du (y, v.2))
        (sourceSliceCentredMean z.1 ρ u v.2) j v.1)) volume := by
  classical
  refine (aemeasurable_indicator_iff hSm).mpr ?_
  have hη : AEMeasurable (fun w : ParabolicPoint => mollifiedBallCutoff z.1 hρ w.1)
      (volume.restrict S) :=
    ((mollifiedBallCutoff_smooth z.1 hρ).continuous.measurable.comp measurable_fst).aemeasurable
  have hdη : ∀ k : Fin 3, AEMeasurable
      (fun w : ParabolicPoint => spatialDeriv (mollifiedBallCutoff z.1 hρ) k w.1)
      (volume.restrict S) := fun k =>
    ((contDiff_spatialDeriv_smooth (mollifiedBallCutoff_smooth z.1 hρ) k).continuous.measurable.comp
      measurable_fst).aemeasurable
  have hind : AEMeasurable
      (fun w : ParabolicPoint => (vec3Ball (0 : Vec3) R₀).indicator (fun _ => (1 : ℝ)) w.1)
      (volume.restrict S) :=
    ((measurable_const.indicator (isOpen_vec3Ball _ _).measurableSet).comp
      measurable_fst).aemeasurable
  have hbody : AEMeasurable (fun v : ParabolicPoint =>
      (mollifiedBallCutoff z.1 hρ v.1 -
        (vec3Ball (0 : Vec3) R₀).indicator (fun _ => (1 : ℝ)) v.1) *
        ((∑ k, Du v j k * u v k) - f v j) +
      (∑ k, spatialDeriv (mollifiedBallCutoff z.1 hρ) k v.1 * u v j *
        (u v k - sourceSliceCentredMean z.1 ρ u v.2 k)) -
      mollifiedBallCutoff z.1 hρ v.1 *
        (∑ k, Du v j k * sourceSliceCentredMean z.1 ρ u v.2 k)) (volume.restrict S) := by
    refine ((hη.sub hind).mul
      ((Finset.aemeasurable_fun_sum _ (fun k _ => (hDu j k).mul (hu k))).sub (hf j))).add ?_
      |>.sub (hη.mul (Finset.aemeasurable_fun_sum _ (fun k _ => (hDu j k).mul (hc k))))
    exact Finset.aemeasurable_fun_sum _ (fun k _ => ((hdη k).mul (hu j)).mul ((hu k).sub (hc k)))
  exact hbody

end CKN.Core.Step4
