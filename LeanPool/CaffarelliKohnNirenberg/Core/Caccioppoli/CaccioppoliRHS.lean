/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliEnergy
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# Caccioppoli RHS

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat


noncomputable section

namespace CKN

theorem caccioppoli_dot_abs_le
    (a b : Vec3) :
    |∑ i, a i * b i| ≤ vec3EuclideanNorm a * vec3EuclideanNorm b := by
  calc
    |∑ i, a i * b i| ≤
        ∑ i, |a i| * |b i| := by
      simpa only [abs_mul] using
        (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin 3)))
          (f := fun i : Fin 3 => a i * b i))
    _ ≤ Real.sqrt (∑ i, |a i| ^ 2) *
        Real.sqrt (∑ i, |b i| ^ 2) := by
      exact Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 3))
        (fun i : Fin 3 => |a i|) (fun i : Fin 3 => |b i|)
    _ = vec3EuclideanNorm a * vec3EuclideanNorm b := by
      unfold vec3EuclideanNorm
      congr 2
      · exact Finset.sum_congr rfl (fun i _ => sq_abs _)
      · exact Finset.sum_congr rfl (fun i _ => sq_abs _)

theorem caccioppoli_partial_sum_abs
    {u : ParabolicPoint → Vec3} {F : ParabolicPoint → ℝ} {z : ParabolicPoint} :
    |∑ i, u z i * spatialPartial F i z| ≤
      vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z| := by
  calc
    |∑ i, u z i * spatialPartial F i z| ≤
        ∑ i, |u z i| * |spatialPartial F i z| := by
      simpa only [abs_mul] using
        (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin 3)))
          (f := fun i : Fin 3 => u z i * spatialPartial F i z))
    _ ≤ ∑ i, vec3EuclideanNorm (u z) * |spatialPartial F i z| := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (by
          unfold vec3EuclideanNorm
          apply Real.abs_le_sqrt
          exact Finset.single_le_sum (fun j _ => sq_nonneg (u z j))
            (Finset.mem_univ i)) (abs_nonneg _)
    _ = vec3EuclideanNorm (u z) * ∑ i, |spatialPartial F i z| := by
      rw [Finset.mul_sum]

theorem caccioppoli_force_abs_le
    {u f : ParabolicPoint → Vec3} {F : ParabolicPoint → ℝ}
    {z : ParabolicPoint} (hF : 0 ≤ F z) :
    |2 * (∑ i, f z i * u z i) * F z| ≤
      2 * vec3EuclideanNorm (f z) * vec3EuclideanNorm (u z) * F z := by
  calc
    |2 * (∑ i, f z i * u z i) * F z| =
        2 * |∑ i, f z i * u z i| * F z := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num), abs_of_nonneg hF]
    _ ≤ 2 * (vec3EuclideanNorm (f z) * vec3EuclideanNorm (u z)) * F z := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (caccioppoli_dot_abs_le _ _)
          (by positivity)) hF
    _ = 2 * vec3EuclideanNorm (f z) * vec3EuclideanNorm (u z) * F z := by
      ring

theorem caccioppoli_heat_cutoff_tsupport_subset
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (_ : ContDiff ℝ (⊤ : ℕ∞)
      (backwardHeat_cutoff (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε)
        x₀ t₀ r)) :
    tsupport (backwardHeat_cutoff
        (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r) ⊆
      euclideanClosedBall x₀ (3 * ρ / 4) ×ˢ
        Icc (t₀ - ρ ^ 2) (t₀ + ε) := by
  let η : Vec3 × ℝ → ℝ :=
    caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε
  have hη : tsupport η ⊆
      euclideanClosedBall x₀ (3 * ρ / 4) ×ˢ
        Icc (t₀ - ρ ^ 2) (t₀ + ε) := by
    apply closure_minimal
    · intro z hz
      have hm := caccioppoli_heat_cutoff_support_subset x₀ t₀ ρ ε hρ hε hz
      have hx : vec3EuclideanNorm (z.1 - x₀) ≤ 3 * ρ / 4 := by
        have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt
          (by positivity)).1 hm.1 |>.le
        simpa [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot,
          pow_two] using hx'
      have hx' : CKN.vecEuclideanNorm (z.1 - x₀) ≤ 3 * ρ / 4 := by
        simpa [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot,
          pow_two] using hx
      exact ⟨(mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
          hx', ⟨hm.2.1.le, hm.2.2.le⟩⟩
    · exact IsClosed.prod (isClosed_euclideanClosedBall x₀ (3 * ρ / 4))
        isClosed_Icc
  exact (tsupport_mul_subset_left (f := η) (g := fun z : Vec3 × ℝ =>
    if z.2 - t₀ < r ^ 2 then
      backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) else 0)).trans hη

theorem caccioppoli_I1_heat_cutoff_raw_ne_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2) (hεr : ε < r ^ 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hfuture : Icc t₀ (t₀ + ε) ⊆ I) :
    (∫⁻ z in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ) *
        ENNReal.ofReal |timePartial (fun w : ParabolicPoint =>
          backwardHeat_cutoff
            (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) z +
          ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
            backwardHeat_cutoff
              (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i i z|) ≠ ∞ := by
  let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ
  let F : Vec3 × ℝ → ℝ := fun z =>
    backwardHeat_cutoff
      (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z
  let C : ℝ := (32 / ρ ^ 2 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
      (8000000 * r ^ 2 / ρ ^ 3) +
        6 * (cutoffGradientConstant / ρ) * (5000000 * r ^ 2 / ρ ^ 4)
  have htest := caccioppoli_heat_cutoff_testFunction hsol hρ hε hr hεr
    hsub hfuture
  have hnorm := (caccioppoli_cutoff_norm_measurable hsol hρ hsub).1
  have hU : AEMeasurable (fun z : ParabolicPoint =>
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ))
      (volume.restrict Q) := hnorm.pow_const (2 : ℝ)
  have hop : AEMeasurable (fun z : ParabolicPoint =>
      ENNReal.ofReal |timePartial F z + ∑ i, spatialSecondPartial F i i z|)
      (volume.restrict Q) := by
    have hcont : Continuous (fun z : Vec3 × ℝ =>
        ENNReal.ofReal |timePartial F z + ∑ i, spatialSecondPartial F i i z|) := by
      have htime := caccioppoli_timePartial_contDiff
        (show ContDiff ℝ (⊤ : ℕ∞) F by simpa only [F] using htest.1.1)
      have hsecond : ∀ i j : Fin 3, ContDiff ℝ (⊤ : ℕ∞)
          (fun z : Vec3 × ℝ => spatialSecondPartial F i j z) := by
        intro i j
        exact spatialPartial_contDiff (spatialPartial_contDiff
          (show ContDiff ℝ (⊤ : ℕ∞) F by simpa only [F] using htest.1.1) i) j
      have hsum : ContDiff ℝ (⊤ : ℕ∞)
          (fun z : Vec3 × ℝ => ∑ i, spatialSecondPartial F i i z) := by
        apply ContDiff.sum
        intro i hi
        exact hsecond i i
      exact ENNReal.continuous_ofReal.comp ((htime.add hsum).continuous.abs)
    exact hcont.aemeasurable
  have hUbound := caccioppoli_I1_velocity_energy_bound hsol (x₀, t₀) hρ hsub
  have hCbound : ∀ᵐ z ∂(volume.restrict Q),
      (ENNReal.ofReal |timePartial F z + ∑ i, spatialSecondPartial F i i z|) ≤
        ENNReal.ofReal C := by
    filter_upwards [ae_restrict_mem (measurableSet_parabolicCylinder _ _ _)]
      with z hz
    have hz' : (z.1 - x₀, z.2 - t₀) ∈ parabolicCylinder 0 0 ρ := by
      rcases mem_parabolicCylinder.mp hz with ⟨hx, ht⟩
      rw [mem_parabolicCylinder]
      exact ⟨by simpa [sub_zero] using hx, by linarith only [ht.1],
        by linarith only [ht.2]⟩
    have hpoint := caccioppoli_I1_heat_cutoff_pointwise_on_cylinder hρ hε hr
      hscale hεr (mem_parabolicCylinder.mp hz).2.2 hz'
    exact ENNReal.ofReal_le_ofReal hpoint
  have hprod := caccioppoli_I1_lintegral_bound
    (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top hCbound hUbound
  have hCfinite : ENNReal.ofReal C *
      ENNReal.ofReal (ρ ^ 3 * alpha u (x₀, t₀) ρ ^ 2) ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have htop : (∫⁻ z in Q,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ) *
        ENNReal.ofReal |timePartial F z + ∑ i, spatialSecondPartial F i i z|) < ∞ :=
    lt_of_le_of_lt hprod (lt_top_iff_ne_top.mpr hCfinite)
  have hne := htop.ne
  change (∫⁻ z in Q,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ) *
        ENNReal.ofReal |timePartial F z + ∑ i, spatialSecondPartial F i i z|) ≠ ∞
  exact hne

theorem caccioppoli_I2_heat_cutoff_raw_ne_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {c : ParabolicPoint → ℝ}
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hA : AEMeasurable (fun w => ENNReal.ofReal
      |(vec3EuclideanNorm (u w)) ^ 2 - c w|)
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hcenter :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| ^
          (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
        ENNReal.ofReal (poincareSobolevL1VectorConstant * ρ ^ (4 / 3 : ℝ) *
          alpha u (x₀, t₀) ρ * beta u Du (x₀, t₀) ρ))
    (hvelocity : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞) :
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
          backwardHeat_cutoff
            (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|)) ≠ ∞ := by
  let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ
  let G : ℝ := 3 * ((cutoffGradientConstant / ρ) * (1000 / r) +
    300000 * r ^ 2 / r ^ 4)
  have hCgrad : 0 ≤ cutoffGradientConstant := by
    by_contra hC'
    have hneg : cutoffGradientConstant / ρ < 0 :=
      div_neg_of_neg_of_pos (lt_of_not_ge hC') hρ
    have hbound := caccioppoli_spatial_cutoff_gradient_bound 0 ρ hρ 0
    have hnorm : 0 ≤ vecEuclideanNorm (classicalGradient
        (mollifiedBallCutoff 0 hρ) 0) := by
      exact vecEuclideanNorm_nonneg _
    exact (not_lt_of_ge hnorm) (hbound.trans_lt hneg)
  have hG : 0 ≤ G := by
    dsimp [G]
    positivity
  have hgrad : ∀ w ∈ Q,
      ∑ i, |spatialPartial (fun y : ParabolicPoint =>
        backwardHeat_cutoff
          (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w| ≤ G := by
    intro w hw
    exact caccioppoli_heat_cutoff_gradient_sum_bound
      (x₀ := x₀) (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r)
      hρ hε hr hscale hw
  have hU := (caccioppoli_cutoff_norm_measurable hsol hρ hsub).1
  have hGbound : ∀ᵐ w ∂(volume.restrict Q),
      ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
        backwardHeat_cutoff
          (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|) ≤
        ENNReal.ofReal G := by
    filter_upwards [ae_restrict_mem (measurableSet_parabolicCylinder _ _ _)]
      with w hw
    exact ENNReal.ofReal_le_ofReal (hgrad w hw)
  have hcenter_pow_top : (∫⁻ w in Q,
      ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| ^
        (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hcenter (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
  have hcenter_top : (∫⁻ w in Q,
      ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| ^
        (3 / 2 : ℝ)) ≠ ∞ := by
    intro htop
    apply hcenter_pow_top
    rw [htop]
    norm_num
  have hright_top : (ENNReal.ofReal G *
      (∫⁻ w in Q, ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| ^
        (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
      (∫⁻ w in Q, ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ^
        (1 / 3 : ℝ)) ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) hcenter_top))
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hvelocity)
  have hpoint : ∀ᵐ w ∂(volume.restrict Q),
      ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
          backwardHeat_cutoff
            (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|) ≤
      ENNReal.ofReal G *
        ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) := by
    filter_upwards [hGbound] with w hw
    calc
      _ = (ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
          ENNReal.ofReal (vec3EuclideanNorm (u w))) *
          ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
            backwardHeat_cutoff
              (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|) := by ring
      _ ≤ (ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
          ENNReal.ofReal (vec3EuclideanNorm (u w))) * ENNReal.ofReal G :=
        mul_le_mul_of_nonneg_left hw (by positivity)
      _ = _ := by ring
  have hle := lintegral_mono_ae hpoint
  have hbound := caccioppoli_I2_holder (C := ENNReal.ofReal G) hA hU
    ENNReal.ofReal_ne_top
  have hfinite : (∫⁻ w in Q, ENNReal.ofReal G *
      ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
        ENNReal.ofReal (vec3EuclideanNorm (u w))) < ∞ :=
    lt_of_le_of_lt hbound (lt_top_iff_ne_top.mpr hright_top)
  have hstrict : (∫⁻ w in Q,
      ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
          backwardHeat_cutoff
            (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|)) < ∞ :=
    lt_of_le_of_lt hle hfinite
  change (∫⁻ w in Q,
      ENNReal.ofReal |(vec3EuclideanNorm (u w)) ^ 2 - c w| *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
          backwardHeat_cutoff
            (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|)) ≠ ∞
  exact ne_of_lt hstrict

theorem caccioppoli_I3_heat_cutoff_raw_ne_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hvelocity : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞) :
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      (2 : ℝ≥0∞) * ENNReal.ofReal |p w| *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
          backwardHeat_cutoff
            (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|)) ≠ ∞ := by
  let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ
  let H : ℝ := 3 * ((cutoffGradientConstant / ρ) * (1000 / r) +
    300000 * r ^ 2 / r ^ 4)
  let G : ℝ := 2 * H
  have hCgrad : 0 ≤ cutoffGradientConstant := by
    by_contra hC'
    have hneg : cutoffGradientConstant / ρ < 0 :=
      div_neg_of_neg_of_pos (lt_of_not_ge hC') hρ
    have hbound := caccioppoli_spatial_cutoff_gradient_bound 0 ρ hρ 0
    have hnorm : 0 ≤ vecEuclideanNorm (classicalGradient
        (mollifiedBallCutoff 0 hρ) 0) := by
      exact vecEuclideanNorm_nonneg _
    exact (not_lt_of_ge hnorm) (hbound.trans_lt hneg)
  have hH : 0 ≤ H := by
    dsimp [H]
    positivity
  have hG : 0 ≤ G := by
    dsimp [G]
    positivity
  have hgrad : ∀ w ∈ Q, ∑ i, |spatialPartial (fun y : ParabolicPoint =>
      backwardHeat_cutoff
        (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w| ≤ H := by
    intro w hw
    have hbase := caccioppoli_heat_cutoff_gradient_sum_bound
      (x₀ := x₀) (t₀ := t₀) (ρ := ρ) (ε := ε) (r := r)
      hρ hε hr hscale hw
    exact hbase
  have hP := (caccioppoli_cutoff_norm_measurable hsol hρ hsub).2.1
  have hU := (caccioppoli_cutoff_norm_measurable hsol hρ hsub).1
  have hD : ∀ᵐ w ∂(volume.restrict Q),
      (2 : ℝ≥0∞) * ENNReal.ofReal (∑ i, |spatialPartial
        (fun y : ParabolicPoint =>
          backwardHeat_cutoff
            (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|) ≤
        ENNReal.ofReal G := by
    filter_upwards [ae_restrict_mem (measurableSet_parabolicCylinder _ _ _)]
      with w hw
    have hbase := ENNReal.ofReal_le_ofReal (hgrad w hw)
    calc
      (2 : ℝ≥0∞) * ENNReal.ofReal (∑ i, |spatialPartial
          (fun y : ParabolicPoint =>
            backwardHeat_cutoff
              (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|) =
          ENNReal.ofReal 2 * ENNReal.ofReal (∑ i, |spatialPartial
            (fun y : ParabolicPoint =>
              backwardHeat_cutoff
                (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|) := by
            rw [ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal H :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = ENNReal.ofReal G := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2)]
  have hpressure : (∫⁻ w in Q, ENNReal.ofReal |p w| ^
      (3 / 2 : ℝ)) ≠ ∞ := by
    change (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≠ ∞
    have hpressure' := sws_pressure_integral_lt_top (h := hsol)
      (z := (x₀, t₀)) (r := ρ) hρ hsub
    exact hpressure'.ne
  have hright : (ENNReal.ofReal G *
      (∫⁻ w in Q, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
      (∫⁻ w in Q, ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ^
        (1 / 3 : ℝ)) ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) hpressure))
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hvelocity)
  have hpoint : ∀ᵐ w ∂(volume.restrict Q),
      (2 : ℝ≥0∞) * ENNReal.ofReal |p w| *
          ENNReal.ofReal (vec3EuclideanNorm (u w)) *
          ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
            backwardHeat_cutoff
              (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|) ≤
        ENNReal.ofReal G * ENNReal.ofReal |p w| *
          ENNReal.ofReal (vec3EuclideanNorm (u w)) := by
    filter_upwards [hD] with w hw
    calc
      _ = ENNReal.ofReal |p w| * ENNReal.ofReal (vec3EuclideanNorm (u w)) *
          ((2 : ℝ≥0∞) * ENNReal.ofReal (∑ i, |spatialPartial
            (fun y : ParabolicPoint =>
              backwardHeat_cutoff
                (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|)) := by
            ring
      _ ≤ ENNReal.ofReal |p w| * ENNReal.ofReal (vec3EuclideanNorm (u w)) *
          ENNReal.ofReal G :=
        mul_le_mul_of_nonneg_left hw (by positivity)
      _ = _ := by ring
  have hle := lintegral_mono_ae hpoint
  have hbound := caccioppoli_I3_holder (C := ENNReal.ofReal G) hP hU
    ENNReal.ofReal_ne_top
  have hfinite : (∫⁻ w in Q, ENNReal.ofReal G *
      ENNReal.ofReal |p w| * ENNReal.ofReal (vec3EuclideanNorm (u w))) < ∞ :=
    lt_of_le_of_lt hbound (lt_top_iff_ne_top.mpr hright)
  have hstrict : (∫⁻ w in Q,
      (2 : ℝ≥0∞) * ENNReal.ofReal |p w| *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
          backwardHeat_cutoff
            (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|)) < ∞ :=
    lt_of_le_of_lt hle hfinite
  change (∫⁻ w in Q,
      (2 : ℝ≥0∞) * ENNReal.ofReal |p w| *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
          backwardHeat_cutoff
            (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|)) ≠ ∞
  exact ne_of_lt hstrict

theorem caccioppoli_I4_heat_cutoff_raw_ne_top
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hvelocity : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞) :
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      (2 : ℝ≥0∞) * ENNReal.ofReal (vec3EuclideanNorm (f w)) *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (backwardHeat_cutoff
          (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w)) ≠ ∞ := by
  let Q : Set ParabolicPoint := parabolicCylinder x₀ t₀ ρ
  let C : ℝ := 2000 / r
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hφ : ∀ w ∈ Q, backwardHeat_cutoff
      (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w ≤ 1000 / r := by
    intro w hw
    have htime : w.2 - t₀ < r ^ 2 := by
      have hupper := (mem_parabolicCylinder.mp hw).2.2
      linarith only [hupper, sq_pos_of_pos hr]
    have hψ : backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀) ≤
        1000 / r := by
      simpa only [centeredBackwardHeatTest] using
        (centeredBackwardHeatTest_upper_on_cylinder
          (x₀ := x₀) (t₀ := t₀) (r := r) (ρ := ρ) hr hρ hw)
    have hψ0 := backwardHeatTestFunction_nonneg
      (x := w.1 - x₀) (t := w.2 - t₀) hr htime
    have hη1 := caccioppoli_heat_cutoff_le_one x₀ t₀ ρ ε hρ hε (w.1, w.2)
    unfold backwardHeat_cutoff
    simp only [ite_eq_left htime]
    calc
      caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε w *
          backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀) ≤
        1 * backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀) :=
          mul_le_mul_of_nonneg_right hη1 hψ0
      _ ≤ 1 * (1000 / r) := mul_le_mul_of_nonneg_left hψ (by positivity)
      _ = 1000 / r := by ring
  have hφ0 : ∀ w ∈ Q, 0 ≤ backwardHeat_cutoff
      (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w := by
    intro w hw
    have htime : w.2 - t₀ < r ^ 2 := by
      have hupper := (mem_parabolicCylinder.mp hw).2.2
      linarith only [hupper, sq_pos_of_pos hr]
    have hη0 := caccioppoli_heat_cutoff_nonneg x₀ t₀ ρ ε hρ hε (w.1, w.2)
    have hψ0 := backwardHeatTestFunction_nonneg
      (x := w.1 - x₀) (t := w.2 - t₀) hr htime
    unfold backwardHeat_cutoff
    simp only [ite_eq_left htime]
    exact mul_nonneg hη0 hψ0
  have hF := (caccioppoli_cutoff_norm_measurable hsol hρ hsub).2.2
  have hU := (caccioppoli_cutoff_norm_measurable hsol hρ hsub).1
  have hD : ∀ᵐ w ∂(volume.restrict Q),
      (2 : ℝ≥0∞) * ENNReal.ofReal (backwardHeat_cutoff
        (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) ≤
        ENNReal.ofReal C := by
    filter_upwards [ae_restrict_mem (measurableSet_parabolicCylinder _ _ _)]
      with w hw
    have hnonneg := hφ0 w hw
    have hupper := hφ w hw
    calc
      (2 : ℝ≥0∞) * ENNReal.ofReal (backwardHeat_cutoff
          (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) =
          ENNReal.ofReal 2 * ENNReal.ofReal (backwardHeat_cutoff
            (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) := by
        rw [ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (1000 / r) :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hupper) (by positivity)
      _ = ENNReal.ofReal C := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2)]
        congr 1
        dsimp [C]
        ring
  have hq : 5 / 2 < q := hsol.2.2.2.1
  have hqpos : 0 < q := by linarith only [hq]
  have hq1 : 0 < q - 1 := by linarith only [hq]
  have hqp : 0 < q / (q - 1) := div_pos hqpos hq1
  have hqprime_le : q / (q - 1) ≤ 3 :=
    (caccioppoli_I4_qprime_lt hq).2.le
  have hforce : (∫⁻ w in Q, ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≠ ∞ := by
    change (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≠ ∞
    have hforce' := sws_force_integral_lt_top (h := hsol)
      (z := (x₀, t₀)) (r := ρ) hρ hsub
    exact hforce'.ne
  let μ : Measure ParabolicPoint := volume.restrict Q
  have hcompare := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ
    hqp hqprime_le hU.aestronglyMeasurable
  have hmeasure : μ Set.univ = volume Q := by
    simp [μ]
  have hqroot : (∫⁻ w in Q,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (q / (q - 1))) ^
        (1 / (q / (q - 1)) : ℝ) ≤
      (∫⁻ w in Q, ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ^
        (1 / 3 : ℝ) * (volume Q) ^
          (1 / (q / (q - 1)) - 1 / 3 : ℝ) := by
    rw [← hmeasure]
    simpa only [eLpNorm'_eq_lintegral_enorm, enorm_eq_self] using hcompare
  have hvolume : (volume Q) ≠ ∞ := by
    exact (volume_parabolicCylinder_lt_top (x := x₀) (t := t₀) (r := ρ)).ne
  have hexp : 0 ≤ 1 / (q / (q - 1)) - 1 / 3 := by
    have hlt := (caccioppoli_I4_qprime_lt hq).2
    apply sub_nonneg.mpr
    exact (le_div_iff₀ hqp).2 (by nlinarith only [hlt])
  have hqroot_top : (∫⁻ w in Q,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (q / (q - 1))) ^
        (1 / (q / (q - 1)) : ℝ) ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hqroot
      (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by positivity) hvelocity)
        (ENNReal.rpow_lt_top_of_nonneg hexp hvolume))
  have huq : (∫⁻ w in Q,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (q / (q - 1))) ≠ ∞ := by
    intro htop
    apply hqroot_top
    rw [htop]
    exact ENNReal.top_rpow_of_pos (by positivity)
  have hright : (ENNReal.ofReal C *
      (∫⁻ w in Q, ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ^
        (1 / q : ℝ) *
      (∫⁻ w in Q, ENNReal.ofReal (vec3EuclideanNorm (u w)) ^
        (q / (q - 1))) ^ ((q - 1) / q : ℝ)) ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) hforce))
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) huq)
  have hpoint : ∀ᵐ w ∂(volume.restrict Q),
      (2 : ℝ≥0∞) * ENNReal.ofReal (vec3EuclideanNorm (f w)) *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (backwardHeat_cutoff
          (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) ≤
      ENNReal.ofReal C * ENNReal.ofReal (vec3EuclideanNorm (f w)) *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) := by
    filter_upwards [hD] with w hw
    calc
      _ = ENNReal.ofReal (vec3EuclideanNorm (f w)) *
          ENNReal.ofReal (vec3EuclideanNorm (u w)) *
          ((2 : ℝ≥0∞) * ENNReal.ofReal (backwardHeat_cutoff
            (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w)) := by ring
      _ ≤ ENNReal.ofReal (vec3EuclideanNorm (f w)) *
          ENNReal.ofReal (vec3EuclideanNorm (u w)) * ENNReal.ofReal C :=
        mul_le_mul_of_nonneg_left hw (by positivity)
      _ = _ := by ring
  have hle := lintegral_mono_ae hpoint
  have hbound := caccioppoli_I4_holder (C := C) hq hF hU
    ENNReal.ofReal_ne_top
  have hfinite : (∫⁻ w in Q, ENNReal.ofReal C *
      ENNReal.ofReal (vec3EuclideanNorm (f w)) *
        ENNReal.ofReal (vec3EuclideanNorm (u w))) < ∞ :=
    lt_of_le_of_lt hbound (lt_top_iff_ne_top.mpr hright)
  have hstrict : (∫⁻ w in Q,
      (2 : ℝ≥0∞) * ENNReal.ofReal (vec3EuclideanNorm (f w)) *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (backwardHeat_cutoff
          (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w)) < ∞ :=
    lt_of_le_of_lt hle hfinite
  change (∫⁻ w in Q,
      (2 : ℝ≥0∞) * ENNReal.ofReal (vec3EuclideanNorm (f w)) *
        ENNReal.ofReal (vec3EuclideanNorm (u w)) *
        ENNReal.ofReal (backwardHeat_cutoff
          (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w)) ≠ ∞
  exact ne_of_lt hstrict

end CKN
