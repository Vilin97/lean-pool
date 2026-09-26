/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTSuitableIdentification
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakGradientGluingTPressureMean
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedTimeBounds
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicPartBoundsAE
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-! # A temporal majorant for the fixed pressure remainder

The annular derivative estimate bounds the harmonic part by fixed energy
and pressure slice norms. The far-force derivative is bounded by the spatial
force integral. Their finite time moments follow from local suitability on
one fixed cylinder, without a pressure oscillation estimate on smaller cells.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4

private theorem time_add_three_halves
    {J : Set ℝ} {K L : ℝ → ℝ≥0∞}
    (hK : AEMeasurable K (volume.restrict J))
    (hL : AEMeasurable L (volume.restrict J))
    (hKn : (∫⁻ s in J, K s ^ (3 / 2 : ℝ)) < ⊤)
    (hLn : (∫⁻ s in J, L s ^ (3 / 2 : ℝ)) < ⊤) :
    (∫⁻ s in J, (K s + L s) ^ (3 / 2 : ℝ)) < ⊤ := by
  have hb : (∫⁻ s in J, (K s + L s) ^ (3 / 2 : ℝ)) ≤
      ∫⁻ s in J, (2 : ℝ≥0∞) ^ (3 / 2 : ℝ) *
        (K s ^ (3 / 2 : ℝ) + L s ^ (3 / 2 : ℝ)) :=
    lintegral_mono fun s => ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ (by norm_num)
  apply hb.trans_lt
  have hm : AEMeasurable (fun s => K s ^ (3 / 2 : ℝ) + L s ^ (3 / 2 : ℝ))
      (volume.restrict J) := (hK.pow_const _).add (hL.pow_const _)
  rw [lintegral_const_mul'' _ hm,
    lintegral_add_left' (hK.pow_const _)]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num))
    (ENNReal.add_lt_top.mpr ⟨hKn, hLn⟩)

private theorem slice_three_halves_time
    {B : Set Vec3} {J : Set ℝ} {F : ParabolicPoint → ℝ}
    (hF : MemLp F (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (B ×ˢ J))) :
    AEMeasurable (fun s => eLpNorm (fun x => F (x,s)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict B)) (volume.restrict J) ∧
    (∫⁻ s in J, eLpNorm (fun x => F (x,s)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict B) ^ (3 / 2 : ℝ)) < ⊤ ∧
    ∀ᵐ s ∂volume.restrict J, AEStronglyMeasurable (fun x => F (x,s)) (volume.restrict B) := by
  have hm : AEStronglyMeasurable F ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact hF.aestronglyMeasurable
  obtain ⟨hsm, hse⟩ := glued_slice_norm_power_integral (by norm_num : (0 : ℝ) < 3 / 2) hm
  refine ⟨hsm, ?_, hm.prodMk_right⟩
  rw [hse]
  have hn := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (by norm_num : ENNReal.ofReal (3 / 2 : ℝ) ≠ 0) ENNReal.ofReal_ne_top hF.eLpNorm_lt_top
  change (∫⁻ w : Vec3 × ℝ in B ×ˢ J, ‖F w‖ₑ ^ (ENNReal.ofReal (3 / 2 : ℝ)).toReal) < ⊤ at hn
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)] using hn

private theorem spatial_integral_le_slice_norm
    {B : Set Vec3} {g : Vec3 → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict B)) :
    ENNReal.ofReal (∫ x in B, g x) ≤
      volume B ^ (1 / 3 : ℝ) * eLpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B) := by
  have hi : ENNReal.ofReal (∫ x in B, g x) ≤ eLpNorm g 1 (volume.restrict B) := by
    rw [eLpNorm_one_eq_lintegral_enorm hg]
    have he := enorm_integral_le_lintegral_enorm (μ := volume.restrict B) g
    rw [Real.enorm_eq_ofReal_abs] at he
    exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans he
  have hp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ)) hg
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofReal, Measure.restrict_apply_univ] at hp
  simpa only [mul_comm] using hi.trans hp

/-- Suitability gives a measurable finite `3/2` time majorant for every
component of the gradient of the fixed harmonic and far-force remainder. -/
theorem fixed_remainder_temporal_majorant_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} (hq : 5 / 2 < q)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∃ M : ℝ → ℝ≥0∞,
      AEMeasurable M (volume.restrict (Ioc (z.2 - ρ ^ 2) z.2)) ∧
      (∫⁻ s in Ioc (z.2 - ρ ^ 2) z.2, M s ^ (3 / 2 : ℝ)) < ⊤ ∧
      ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
        ∀ i : Fin 3, ∀ x ∈ vec3Ball z.1 (ρ / 2),
          ‖classicalGradient
            (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
              (sourceSliceCentredMean z.1 ρ u) p s +
              pressureP8 (mollifiedBallCutoff z.1 hρ) f s) x i‖ₑ ≤ M s := by
  let B := vec3Ball z.1 ρ
  let J := Ioc (z.2 - ρ ^ 2) z.2
  let Q := parabolicCylinder z.1 z.2 ρ
  obtain ⟨Ω', J', hbox, hQsub⟩ := exists_localBox_of_closure_subset hsol.1 hsol.2.1 hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J' hbox
  have hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict Q) :=
    hdata.2.2.2.2.2.2.1.mono_measure (Measure.restrict_mono_set volume hQsub)
  have hfq : MemLp f (ENNReal.ofReal q) (volume.restrict Q) :=
    hdata.2.2.2.2.2.2.2.1.mono_measure (Measure.restrict_mono_set volume hQsub)
  have hQfinite : volume Q < ⊤ := by
    rw [volume_parabolicCylinder]
    exact ENNReal.mul_lt_top Integration.volume_vec3Ball_lt_top ENNReal.ofReal_lt_top
  let : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.mpr hQfinite.ne
  have hfsmall := hfq.mono_exponent (ENNReal.ofReal_le_ofReal
    (by linarith only [hq] : (3 / 2 : ℝ) ≤ q))
  have hf : MemLp (fun w => vec3EuclideanNorm (f w)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict Q) := by
    apply hfsmall.of_le_mul
      (continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hfsmall.aestronglyMeasurable)
    exact Eventually.of_forall fun w => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)] using
        vec3EuclideanNorm_le_sqrt_three_mul_norm (f w)
  have hpt := slice_three_halves_time hp
  have hft := slice_three_halves_time hf
  let P (s : ℝ) := eLpNorm (fun x => p (x,s)) (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B)
  let F (s : ℝ) := eLpNorm (fun x => vec3EuclideanNorm (f (x,s)))
    (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B)
  obtain ⟨C, hC, hCbound⟩ := exists_harmonicPressurePart_Ck_ae_of_sws 1
  let Ch := C * ρ ^ (-3 : ℝ)
  let Cf := 400 * sliceForcePotentialConstant * (cutoffGradientConstant / ρ) * (ρ ^ 2)⁻¹
  let H (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal Ch * (ENNReal.ofReal (alpha u z ρ ^ 2) + P s)
  let W (s : ℝ) : ℝ≥0∞ := (ENNReal.ofReal |Cf| * volume B ^ (1 / 3 : ℝ)) * F s
  have hCh : 0 ≤ Ch := mul_nonneg hC (Real.rpow_nonneg hρ.le _)
  have hJfinite : volume J < ⊤ := by simp only [J, Real.volume_Ioc, ENNReal.ofReal_lt_top]
  have he : (∫⁻ s in J, ENNReal.ofReal (alpha u z ρ ^ 2) ^ (3 / 2 : ℝ)) < ⊤ := by
    rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) hJfinite
  have hsum := time_add_three_halves aemeasurable_const hpt.1 he hpt.2.1
  obtain ⟨hHm, hHn⟩ := glued_time_const_mul_power (aemeasurable_const.add hpt.1)
    hsum (ENNReal.ofReal Ch) ENNReal.ofReal_lt_top
  have hcoef : ENNReal.ofReal |Cf| * volume B ^ (1 / 3 : ℝ) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) Integration.volume_vec3Ball_lt_top.ne)
  obtain ⟨hWm, hWn⟩ := glued_time_const_mul_power hft.1 hft.2.1 _ hcoef
  refine ⟨fun s => H s + W s, hHm.add hWm,
    time_add_three_halves hHm hWm hHn hWn, ?_⟩
  have hhar := hCbound hsol hρ hsub
  have hreg := slice_harmonic_part_contDiffOn_ae_of_sws hsol hρ hsub
  have hforce := slice_force_source_data_ae_of_sws hsol hρ hsub
  filter_upwards [hhar, hreg, hforce, hft.2.2] with s hhs hrs hfs hFmeas
  intro i x hx
  let η := mollifiedBallCutoff z.1 hρ
  let h := harmonicPressurePart η u (sourceSliceCentredMean z.1 ρ u) p s
  let v := pressureP8 η f s
  have hhalf := CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
    (x₀ := z.1) (by positivity : 0 < ρ / 2)
  rw [hhalf] at hrs
  have hd₁ := hrs.differentiableOn_one.differentiableAt ((isOpen_vec3Ball _ _).mem_nhds hx)
  have hd₂ := (contDiffOn_pressureP8_halfBall hρ hfs.2.2.1).differentiableOn_one.differentiableAt
    ((isOpen_vec3Ball _ _).mem_nhds hx)
  have hgrad : classicalGradient (h + v) x i = classicalGradient h x i + classicalGradient v x i :=
    congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) (hd₁.hasFDerivAt.add hd₂.hasFDerivAt).fderiv
  have hhb : ‖classicalGradient h x i‖ₑ ≤ H s := by
    have hh := hhs x hx
    rw [norm_iteratedFDeriv_one] at hh
    have hcomponent : ‖classicalGradient h x i‖ ≤ ‖fderiv ℝ h x‖ := by
      exact ((fderiv ℝ h x).le_opNorm (basisVec i)).trans
        (mul_le_of_le_one_right (norm_nonneg _) (norm_basisVec_le_one i))
    have hb : ‖classicalGradient h x i‖ ≤ Ch *
        (alpha u z ρ ^ 2 + lpNorm (fun y => p (y,s)) (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict B)) := by
      apply hcomponent.trans
      norm_num only [Nat.cast_one, show -(2 + (1 : ℝ)) = -3 by norm_num] at hh
      exact hh
    calc
      _ ≤ ENNReal.ofReal (Ch * (alpha u z ρ ^ 2 + lpNorm (fun y => p (y,s))
          (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B))) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hb
      _ ≤ H s := by
        rw [ENNReal.ofReal_mul hCh, ENNReal.ofReal_add (sq_nonneg _) lpNorm_nonneg]
        exact mul_le_mul' le_rfl (add_le_add le_rfl ENNReal.ofReal_toReal_le)
  have hA : 0 ≤ (cutoffGradientConstant / ρ) *
      ∫ y in B, vec3EuclideanNorm (f (y,s)) :=
    mul_nonneg ((vecEuclideanNorm_nonneg _).trans (mollifiedBallCutoff_gradient_bound z.1 hρ z.1))
      (integral_nonneg (fun _ => vec3EuclideanNorm_nonneg _))
  have hp8 := vec3EuclideanNorm_classicalGradient_pressureP8_le hρ hA
    hfs.2.2.1 hfs.2.2.2 hx
  have hvb : ‖classicalGradient v x i‖ₑ ≤ W s := by
    have hb : |classicalGradient v x i| ≤ Cf * ∫ y in B, vec3EuclideanNorm (f (y,s)) := by
      have ht := (abs_apply_le_vec3EuclideanNorm _ i).trans hp8
      dsimp only [Cf, B, v, η]
      nlinarith only [ht]
    have hb' := hb.trans (mul_le_mul_of_nonneg_right (le_abs_self Cf)
      (integral_nonneg (fun _ => vec3EuclideanNorm_nonneg _)))
    rw [Real.enorm_eq_ofReal_abs]
    apply (ENNReal.ofReal_le_ofReal hb').trans
    rw [ENNReal.ofReal_mul (abs_nonneg _)]
    exact (mul_le_mul' le_rfl (spatial_integral_le_slice_norm hFmeas)).trans_eq (mul_assoc _ _
      _).symm
  change ‖classicalGradient (h + v) x i‖ₑ ≤ H s + W s
  rw [hgrad]
  exact (enorm_add_le _ _).trans (add_le_add hhb hvb)

end CKN.Core.Step4
