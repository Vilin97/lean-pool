/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Cutoff
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Derivatives

/-!
# Terms

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat


noncomputable section

namespace CKN

theorem caccioppoli_heat_cutoff_eq_one_on
    (x₀ : Vec3) (t₀ ρ ε r : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2)
    {z : Vec3 × ℝ}
    (hx : z.1 ∈ vec3Ball x₀ (ρ / 2))
    (ht : z.2 ∈ Ioc (t₀ - r ^ 2) (t₀ + ε / 2)) :
    caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε z = 1 := by
  unfold caccioppoli_heat_cutoff
  rw [mollifiedBallCutoff_eq_one_on_inner x₀ hρ]
  · rw [caccioppoli_asymmetricTimeCutoff_eq_one_on hρ hε hr hscale
      ⟨ht.1.le, ht.2.trans (by linarith only [hε])⟩]
    norm_num
  · apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    have hrad : ρ / 2 ≤ 13 * ρ / 20 := by linarith only [hρ]
    have hx' : CKN.vecEuclideanNorm (z.1 - x₀) < ρ / 2 := by
      have hnorm : ∀ v : Vec3, vec3EuclideanNorm v = CKN.vecEuclideanNorm v := by
        intro v
        simp [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot, pow_two]
      rw [← hnorm]
      exact mem_vec3Ball.mp hx
    exact (hx'.trans_le hrad)

private theorem caccioppoli_heat_cutoff_eq_one_near
    (x₀ : Vec3) (t₀ ρ ε r : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2) {z : Vec3 × ℝ}
    (hx : z.1 ∈ vec3Ball x₀ (ρ / 2))
    (ht : z.2 ∈ Ioc (t₀ - r ^ 2) t₀) :
    ∀ᶠ y in 𝓝 z,
      caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε y = 1 := by
  have hopen : IsOpen (vec3Ball x₀ (ρ / 2)) := by
    have hnorm : Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact isOpen_lt (hnorm.comp (continuous_id.sub continuous_const)) continuous_const
  have hspace : ∀ᶠ y in 𝓝 z, y.1 ∈ vec3Ball x₀ (ρ / 2) := by
    have hset : vec3Ball x₀ (ρ / 2) ∈ 𝓝 z.1 := hopen.mem_nhds hx
    exact continuous_fst.continuousAt.preimage_mem_nhds hset
  have htime : ∀ᶠ y in 𝓝 z,
      y.2 ∈ Ioo (t₀ - r ^ 2) (t₀ + ε / 2) := by
    apply continuous_snd.continuousAt.preimage_mem_nhds
    apply isOpen_Ioo.mem_nhds
    constructor
    · exact ht.1
    · linarith only [ht.2, hε]
  filter_upwards [hspace, htime] with y hyx hyt
  exact caccioppoli_heat_cutoff_eq_one_on x₀ t₀ ρ ε r hρ hε hr hscale
    hyx ⟨hyt.1, hyt.2.le⟩

theorem caccioppoli_heat_cutoff_derivatives_zero_on_inner
    (x₀ : Vec3) (t₀ ρ ε r : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2) {z : ParabolicPoint}
    (hx : z.1 ∈ vec3Ball x₀ (ρ / 2))
    (ht : z.2 ∈ Ioc (t₀ - r ^ 2) t₀) :
    timePartial (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) z = 0 ∧
      (∀ i : Fin 3,
        spatialPartial (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) i z = 0) ∧
      (∀ i j : Fin 3,
        spatialSecondPartial (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) i j z = 0) := by
  have hev := caccioppoli_heat_cutoff_eq_one_near x₀ t₀ ρ ε r hρ hε hr hscale hx ht
  have hev_time : (fun s : ℝ =>
      caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε (z.1, s)) =ᶠ[𝓝 z.2]
        (fun _ => (1 : ℝ)) := by
    have hmap : Continuous (fun s : ℝ => (z.1, s)) :=
      continuous_const.prodMk continuous_id
    filter_upwards [hmap.continuousAt.preimage_mem_nhds hev] with s hs
    exact hs
  have htime : timePartial (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) z = 0 := by
    unfold timePartial
    rw [hev_time.fderiv_eq, fderiv_const_apply]
    simp
  have hspace (i : Fin 3) :
      spatialPartial (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) i z = 0 := by
    unfold spatialPartial
    have hmap : Continuous (fun x : Vec3 => (x, z.2)) :=
      continuous_id.prodMk continuous_const
    have hev_space : (fun x : Vec3 =>
        caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε (x, z.2)) =ᶠ[𝓝 z.1]
          (fun _ => (1 : ℝ)) := by
      filter_upwards [hmap.continuousAt.preimage_mem_nhds hev] with x hx'
      exact hx'
    rw [hev_space.fderiv_eq, fderiv_const_apply]
    simp
  have hsecond (i j : Fin 3) :
      spatialSecondPartial (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) i j z = 0 := by
    unfold spatialSecondPartial
    change (fderiv ℝ (fun x : Vec3 =>
      spatialPartial (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) i (x, z.2))
      z.1) (basisVec j) = 0
    have hopen : IsOpen (vec3Ball x₀ (ρ / 2)) := by
      have hnorm : Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
        unfold vec3EuclideanNorm
        fun_prop
      exact isOpen_lt (hnorm.comp (continuous_id.sub continuous_const)) continuous_const
    have hinner : ∀ᶠ x in 𝓝 z.1, x ∈ vec3Ball x₀ (ρ / 2) := by
      have hset : vec3Ball x₀ (ρ / 2) ∈ 𝓝 z.1 := hopen.mem_nhds hx
      exact continuous_id.continuousAt.preimage_mem_nhds hset
    have hnear : (fun x : Vec3 =>
        spatialPartial (caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε) i (x, z.2)) =ᶠ[𝓝 z.1]
          (fun _ => (0 : ℝ)) := by
      filter_upwards [hinner] with x hxin
      unfold spatialPartial
      change (fderiv ℝ (fun y : Vec3 =>
        caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε (y, z.2)) x) (basisVec i) = 0
      have hlocal := caccioppoli_heat_cutoff_eq_one_near x₀ t₀ ρ ε r
        (z := (x, z.2)) hρ hε hr hscale hxin
        ⟨ht.1, ht.2.trans (by linarith only [hε])⟩
      have hmap : Continuous (fun y : Vec3 => (y, z.2)) :=
        continuous_id.prodMk continuous_const
      have hconst : (fun y : Vec3 =>
          caccioppoli_heat_cutoff x₀ t₀ ρ ε hρ hε (y, z.2)) =ᶠ[𝓝 x]
            (fun _ => (1 : ℝ)) :=
        hmap.continuousAt.preimage_mem_nhds hlocal
      rw [hconst.fderiv_eq, fderiv_const_apply]
      simp
    rw [hnear.fderiv_eq, fderiv_const_apply]
    simp
  exact ⟨htime, hspace, hsecond⟩

private lemma caccioppoli_heat_contDiffAt_spatial
    {x₀ : Vec3} {t₀ r : ℝ} {z : ParabolicPoint}
    (ht : z.2 - t₀ < r ^ 2) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => backwardHeatTestFunction r (x - x₀) (z.2 - t₀)) z.1 := by
  have hτ : 0 < r ^ 2 - (z.2 - t₀) := sub_pos.mpr ht
  have hformula : (fun x : Vec3 =>
      backwardHeatTestFunction r (x - x₀) (z.2 - t₀)) = fun x : Vec3 =>
        r ^ 2 * ((4 * Real.pi * (r ^ 2 - (z.2 - t₀))) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ j, (x - x₀) j ^ 2) /
            (4 * (r ^ 2 - (z.2 - t₀))))) := by
    funext x
    rw [backwardHeatTestFunction, heatKernel_eq_formula_sum hτ]
  rw [hformula]
  fun_prop (disch := positivity)

private lemma caccioppoli_heat_contDiffAt_time
    {x₀ : Vec3} {t₀ r : ℝ} {z : ParabolicPoint}
    (ht : z.2 - t₀ < r ^ 2) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun s : ℝ => backwardHeatTestFunction r (z.1 - x₀) (s - t₀)) z.2 := by
  let S : Set ℝ := {s | s - t₀ < r ^ 2}
  have hS : IsOpen S := by
    exact isOpen_lt (continuous_id.sub continuous_const) continuous_const
  have hA : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => (z.1 - x₀, r ^ 2 - (s - t₀))) := by
    fun_prop
  have hheat : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => heatKernel (z.1 - x₀) (r ^ 2 - (s - t₀))) S := by
    have hAon : ContDiffOn ℝ (⊤ : WithTop ℕ∞)
        (fun s : ℝ => (z.1 - x₀, r ^ 2 - (s - t₀))) S := by
      fun_prop
    have hcomp := heatKernel_contDiffOn_pos.comp hAon (by
      intro s hs
      change s - t₀ < r ^ 2 at hs
      exact ⟨mem_univ _, sub_pos.mpr hs⟩)
    have hcomp' := hcomp.of_le
      (show (⊤ : ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
    simpa only [Function.comp_def] using hcomp'
  have hψ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => backwardHeatTestFunction r (z.1 - x₀) (s - t₀)) S := by
    have hmul := (contDiff_const (c := r ^ 2)).contDiffOn.mul hheat
    simpa only [backwardHeatTestFunction, Function.comp_apply] using hmul
  have hψ' := (hψ z.2 ht).contDiffAt (hS.mem_nhds ht)
  exact hψ'

theorem caccioppoli_cutoff_heat_spatialPartial
    {η : Vec3 × ℝ → ℝ} {x₀ : Vec3} {t₀ r : ℝ}
    {z : ParabolicPoint} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (ht : z.2 - t₀ < r ^ 2) (i : Fin 3) :
    spatialPartial (backwardHeat_cutoff η x₀ t₀ r) i z =
      spatialPartial η i z *
          backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
        η z * (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) i) := by
  have hηd : DifferentiableAt ℝ (fun x : Vec3 => η (x, z.2)) z.1 := by
    exact (hη.contDiffAt.differentiableAt (by simp)).comp z.1
      ((contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2).contDiffAt.differentiableAt
        (by simp))
  have hΓc := caccioppoli_heat_contDiffAt_spatial (x₀ := x₀) (t₀ := t₀)
    (r := r) (z := z) ht
  have hΓd : DifferentiableAt ℝ (fun x : Vec3 =>
      backwardHeatTestFunction r (x - x₀) (z.2 - t₀)) z.1 :=
    hΓc.differentiableAt (by simp)
  unfold spatialPartial
  change (fderiv ℝ (fun x : Vec3 =>
      η (x, z.2) * (if z.2 - t₀ < r ^ 2 then
        backwardHeatTestFunction r (x - x₀) (z.2 - t₀) else 0)) z.1)
      (basisVec i) = _
  simp only [ht, ↓reduceIte]
  change (fderiv ℝ ((fun x : Vec3 => η (x, z.2)) * (fun x : Vec3 =>
      backwardHeatTestFunction r (x - x₀) (z.2 - t₀))) z.1) (basisVec i) = _
  rw [fderiv_mul hηd hΓd]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [show fderiv ℝ (fun x : Vec3 => η (x, z.2)) z.1 =
      fderiv ℝ (fun x : Vec3 => η (x, z.2)) z.1 from rfl]
  have hηpartial :
      (fderiv ℝ (fun x : Vec3 => η (x, z.2)) z.1) (basisVec i) =
        spatialPartial η i z := by
    rfl
  have hΓpartial := caccioppoli_heat_spatialPartial (x₀ := x₀) (t₀ := t₀)
    (r := r) (z := z) ht i
  rw [hηpartial]
  have hΓvalue :
      backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) =
        backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) := rfl
  rw [hΓvalue]
  have hcomp :
      (fderiv ℝ (fun x : Vec3 => backwardHeatTestFunction r
        (x - x₀) (z.2 - t₀)) z.1) (basisVec i) =
        r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) i := by
    change spatialPartial (fun w : ParabolicPoint =>
      backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀)) i z = _
    exact hΓpartial
  rw [hcomp]
  have hz : η z = η (z.1, z.2) := by rfl
  rw [hz]
  ring

theorem caccioppoli_cutoff_heat_timePartial
    {η : Vec3 × ℝ → ℝ} {x₀ : Vec3} {t₀ r : ℝ}
    {z : ParabolicPoint} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (ht : z.2 - t₀ < r ^ 2) :
    timePartial (backwardHeat_cutoff η x₀ t₀ r) z =
      timePartial η z *
          backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
        η z * (-r ^ 2 * heatKernelTimeDerivative (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀))) := by
  have hηd : DifferentiableAt ℝ (fun s : ℝ => η (z.1, s)) z.2 := by
    exact (hη.contDiffAt.differentiableAt (by simp)).comp z.2
      ((contDiff_prodMk_right (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.1).contDiffAt.differentiableAt
        (by simp))
  have hΓc := caccioppoli_heat_contDiffAt_time (x₀ := x₀) (t₀ := t₀)
    (r := r) (z := z) ht
  have hΓd : DifferentiableAt ℝ (fun s : ℝ =>
      backwardHeatTestFunction r (z.1 - x₀) (s - t₀)) z.2 :=
    hΓc.differentiableAt (by simp)
  unfold timePartial
  change (fderiv ℝ (fun s : ℝ =>
      η (z.1, s) * (if s - t₀ < r ^ 2 then
        backwardHeatTestFunction r (z.1 - x₀) (s - t₀) else 0)) z.2) 1 = _
  have hS : IsOpen {s : ℝ | s - t₀ < r ^ 2} := by
    exact isOpen_lt (continuous_id.sub continuous_const) continuous_const
  have hev : (fun s : ℝ => η (z.1, s) * (if s - t₀ < r ^ 2 then
      backwardHeatTestFunction r (z.1 - x₀) (s - t₀) else 0)) =ᶠ[𝓝 z.2]
      (fun s : ℝ => η (z.1, s) *
        backwardHeatTestFunction r (z.1 - x₀) (s - t₀)) := by
    filter_upwards [hS.mem_nhds ht] with s hs
    simp only [hs, ↓reduceIte]
  rw [Filter.EventuallyEq.fderiv_eq hev]
  change (fderiv ℝ ((fun s : ℝ => η (z.1, s)) * (fun s : ℝ =>
      backwardHeatTestFunction r (z.1 - x₀) (s - t₀))) z.2) 1 = _
  rw [fderiv_mul hηd hΓd]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  have hηpartial :
      (fderiv ℝ (fun s : ℝ => η (z.1, s)) z.2) 1 = timePartial η z := rfl
  rw [hηpartial]
  have hΓpartial := caccioppoli_heat_timePartial (x₀ := x₀) (t₀ := t₀)
    (r := r) (z := z) ht
  have hΓvalue :
      backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) =
        backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) := rfl
  rw [hΓvalue]
  have hcomp :
      (fderiv ℝ (fun s : ℝ => backwardHeatTestFunction r
        (z.1 - x₀) (s - t₀)) z.2) 1 =
        -r ^ 2 * heatKernelTimeDerivative (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) := by
    change timePartial (fun w : ParabolicPoint =>
      backwardHeatTestFunction r (w.1 - x₀) (w.2 - t₀)) z = _
    exact hΓpartial
  rw [hcomp]
  have hz : η z = η (z.1, z.2) := by rfl
  rw [hz]
  ring

theorem caccioppoli_cutoff_le_one
    {x₀ : Vec3} {t₀ ρ R : ℝ} (hρ : 0 < ρ) (hR : ρ / 2 < R)
    (z : Vec3 × ℝ) :
    caccioppoli_cutoff x₀ t₀ ρ R hρ hR z ≤ 1 := by
  unfold caccioppoli_cutoff
  calc
    mollifiedBallCutoff x₀ hρ z.1 * timeCutoff t₀ (ρ / 2) R z.2 ≤
        1 * timeCutoff t₀ (ρ / 2) R z.2 :=
      mul_le_mul_of_nonneg_right (mollifiedBallCutoff_le_one x₀ hρ z.1)
        (timeCutoff_nonneg t₀ (ρ / 2) R z.2)
    _ ≤ 1 * 1 :=
      mul_le_mul_of_nonneg_left
        (timeCutoff_le_one t₀ (ρ / 2) R z.2) (by positivity)
    _ = 1 := by ring

theorem caccioppoli_heat_function_upper_on_annulus
    {x₀ : Vec3} {t₀ ρ r : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hscale : r ≤ ρ / 2) {z : ParabolicPoint}
    (hp : (z.1 - x₀, z.2 - t₀) ∈
      parabolicCylinder 0 0 ρ \ parabolicCylinder 0 0 (ρ / 2)) :
    backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) ≤
      8000000 * r ^ 2 / ρ ^ 3 := by
  simpa only [sub_zero] using
    (backwardHeatTestFunction_upper_on_annulus hr hρ hscale hp)

theorem caccioppoli_heat_spatial_derivative_abs_on_annulus
    {x₀ : Vec3} {t₀ ρ r : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hscale : r ≤ ρ / 2) {z : ParabolicPoint} (i : Fin 3)
    (hp : (z.1 - x₀, z.2 - t₀) ∈
      parabolicCylinder 0 0 ρ \ parabolicCylinder 0 0 (ρ / 2)) :
    |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
        (r ^ 2 - (z.2 - t₀)) i| ≤
      5000000 * r ^ 2 / ρ ^ 4 := by
  have hgrad := backwardHeatTestGradient_upper_on_annulus hr hρ hscale hp
  have hcoord : |heatKernelSpaceDerivative (z.1 - x₀)
      (r ^ 2 - (z.2 - t₀)) i| ≤
      heatKernelGradientNorm (z.1 - x₀) (r ^ 2 - (z.2 - t₀)) := by
    unfold heatKernelGradientNorm
    exact Finset.single_le_sum (f := fun j =>
      |heatKernelSpaceDerivative (z.1 - x₀)
        (r ^ 2 - (z.2 - t₀)) j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  rw [abs_mul]
  rw [abs_of_nonneg (sq_nonneg r)]
  calc
    r ^ 2 * |heatKernelSpaceDerivative (z.1 - x₀)
        (r ^ 2 - (z.2 - t₀)) i| ≤
        r ^ 2 * heatKernelGradientNorm (z.1 - x₀)
          (r ^ 2 - (z.2 - t₀)) := by
      gcongr
    _ = backwardHeatTestGradientNorm r (z.1 - x₀) (z.2 - t₀) := by
      rfl
    _ ≤ 5000000 * r ^ 2 / ρ ^ 4 := hgrad

theorem caccioppoli_cutoff_spatial_partial_abs_on_annulus
    {x₀ : Vec3} {t₀ ρ R r : ℝ} (hρ : 0 < ρ) (hR : ρ / 2 < R)
    (hr : 0 < r) (hscale : r ≤ ρ / 2) {z : ParabolicPoint} (i : Fin 3)
    (hp : (z.1 - x₀, z.2 - t₀) ∈
      parabolicCylinder 0 0 ρ \ parabolicCylinder 0 0 (ρ / 2)) :
    |spatialPartial (backwardHeat_cutoff
        (caccioppoli_cutoff x₀ t₀ ρ R hρ hR) x₀ t₀ r) i z| ≤
      5000000 * r ^ 2 / ρ ^ 4 +
        8000000 * cutoffGradientConstant * r ^ 2 / ρ ^ 4 := by
  have hht := caccioppoli_cutoff_heat_spatialPartial
    (η := caccioppoli_cutoff x₀ t₀ ρ R hρ hR) (x₀ := x₀) (t₀ := t₀) (r := r)
    (z := z) (caccioppoli_cutoff_smooth x₀ t₀ ρ R hρ hR)
    (by
      have hp' := (mem_parabolicCylinder.mp hp.1).2.2
      simpa only [sub_zero] using
        (lt_of_le_of_lt hp' (sq_pos_of_pos hr)) ) i
  have hη := caccioppoli_cutoff_spatial_partial_bound x₀ t₀ ρ R hρ hR z i
  have hΓ := caccioppoli_heat_function_upper_on_annulus hr hρ hscale hp
  have hD := caccioppoli_heat_spatial_derivative_abs_on_annulus hr hρ hscale i hp
  have hη0 := caccioppoli_cutoff_nonneg x₀ t₀ ρ R hρ hR z
  have hη1 := caccioppoli_cutoff_le_one (x₀ := x₀) (t₀ := t₀) hρ hR z
  have hhtime : z.2 - t₀ < r ^ 2 := by
    have hp' := (mem_parabolicCylinder.mp hp.1).2.2
    exact lt_of_le_of_lt (by simpa only [sub_zero] using hp') (sq_pos_of_pos hr)
  have hΓ0 := backwardHeatTestFunction_nonneg
    (x := z.1 - x₀) (t := z.2 - t₀) hr hhtime
  have hC : 0 ≤ cutoffGradientConstant := by
    by_contra hC'
    have hneg : cutoffGradientConstant / ρ < 0 :=
      div_neg_of_neg_of_pos (lt_of_not_ge hC') hρ
    have hbound := caccioppoli_spatial_cutoff_gradient_bound x₀ ρ hρ 0
    have hnorm : 0 ≤ vecEuclideanNorm (classicalGradient
        (mollifiedBallCutoff x₀ hρ) 0) := vecEuclideanNorm_nonneg _
    linarith only [hbound, hnorm, hneg]
  have hCρ : 0 ≤ cutoffGradientConstant / ρ := div_nonneg hC hρ.le
  rw [hht]
  calc
    |spatialPartial (caccioppoli_cutoff x₀ t₀ ρ R hρ hR) i z *
          backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
        caccioppoli_cutoff x₀ t₀ ρ R hρ hR z *
          (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i)| ≤
      |spatialPartial (caccioppoli_cutoff x₀ t₀ ρ R hρ hR) i z *
          backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀)| +
        |caccioppoli_cutoff x₀ t₀ ρ R hρ hR z *
          (r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i)| := abs_add_le _ _
    _ = |spatialPartial (caccioppoli_cutoff x₀ t₀ ρ R hρ hR) i z| *
          backwardHeatTestFunction r (z.1 - x₀) (z.2 - t₀) +
        caccioppoli_cutoff x₀ t₀ ρ R hρ hR z *
          |r ^ 2 * heatKernelSpaceDerivative (z.1 - x₀)
            (r ^ 2 - (z.2 - t₀)) i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hΓ0, abs_of_nonneg hη0]
    _ ≤ (cutoffGradientConstant / ρ) *
          (8000000 * r ^ 2 / ρ ^ 3) +
        1 * (5000000 * r ^ 2 / ρ ^ 4) := by
      gcongr
    _ = 5000000 * r ^ 2 / ρ ^ 4 +
        8000000 * cutoffGradientConstant * r ^ 2 / ρ ^ 4 := by
      field_simp [hρ.ne']
      ring

end CKN
