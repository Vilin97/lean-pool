/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34SliceCore

/-!
# Lin34 Slice Pointwise

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

/-!
# The pointwise-in-time oscillation estimate `eq:lin34-pointwise`

This file proves, at one time slice, the estimate `eq:lin34-pointwise` of
`prop:lin34` in `paper/ckn.tex`, in the form that also carries the force group
`p₇ + p₈` needed for part (ii-b) of that proposition.  The only analytic input
that is named rather than proved is the Calderón--Zygmund bound `ext:CZ` for
the centred first potential.
-/

private lemma lin34_euclideanBall_eq_vec3Ball' {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

private lemma lin34_lpNorm_restrict_le_global
    {g : Vec3 → ℝ} {x₀ : Vec3} {r : ℝ}
    (hg : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) volume) :
    lpNorm g (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ r)) ≤
      lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
  rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm]
  exact ENNReal.toReal_mono hg.eLpNorm_lt_top.ne
    (eLpNorm_mono_measure g Measure.restrict_le_self)

private lemma lin34_integral_eq_lpNorm_rpow
    {g : Vec3 → ℝ} {x₀ : Vec3} {r : ℝ}
    (hg : MemLp g (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r))) :
    (∫ x in euclideanBall x₀ r, |g x| ^ (3 / 2 : ℝ)) =
      lpNorm g (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ r)) ^ (3 / 2 : ℝ) := by
  have h := integral_rpow_norm_eq_lpNorm_rpow
    (p := ENNReal.ofReal (3 / 2 : ℝ))
    (μ := volume.restrict (euclideanBall x₀ r))
    (hp0 := by norm_num) (hpTop := by norm_num) hg
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
    Real.norm_eq_abs] using h

/-- The Calderón--Zygmund bound `ext:CZ` of `prop:lin34` transferred from the
whole space to the inner ball. -/
theorem lin34_p1_slice_integral_bound
    {p₁ : Vec3 → ℝ} {x₀ : Vec3} {r C E : ℝ}
    (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hp₁ : MemLp p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hCZ : lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      C * E ^ (2 / 3 : ℝ)) :
    ∫ x in euclideanBall x₀ r, |p₁ x| ^ (3 / 2 : ℝ) ≤ C ^ (3 / 2 : ℝ) * E := by
  have hp₁r : MemLp p₁ (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)) :=
    hp₁.mono_measure Measure.restrict_le_self
  have hnorm : lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)) ≤
      lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    lin34_lpNorm_restrict_le_global hp₁
  have hpow := Real.rpow_le_rpow (lpNorm_nonneg) hCZ
    (by norm_num : (0 : ℝ) ≤ 3 / 2)
  calc
    ∫ x in euclideanBall x₀ r, |p₁ x| ^ (3 / 2 : ℝ) =
        lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ r)) ^ (3 / 2 : ℝ) :=
      lin34_integral_eq_lpNorm_rpow hp₁r
    _ ≤ lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (lpNorm_nonneg) hnorm (by norm_num)
    _ ≤ (C * E ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) := hpow
    _ = C ^ (3 / 2 : ℝ) * E := by
      rw [Real.mul_rpow hC (Real.rpow_nonneg hE _), ← Real.rpow_mul hE]
      norm_num

/-- The constant `C₁₈` of `eq:lin34-pointwise` in `paper/ckn.tex`, with the
Calderón--Zygmund constant of `ext:CZ` exposed. -/
def lin34PointwiseConstant (C₁₁ : ℝ) : ℝ :=
  2 + 2 * C₁₁ ^ (3 / 2 : ℝ) + 2 * lin34RemainderConstant

theorem lin34PointwiseConstant_nonneg {C₁₁ : ℝ} (hC₁₁ : 0 ≤ C₁₁) :
    0 ≤ lin34PointwiseConstant C₁₁ := by
  have h₁ : (0 : ℝ) ≤ C₁₁ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hC₁₁ _
  have h₂ := lin34RemainderConstant_nonneg
  unfold lin34PointwiseConstant
  linarith only [h₁, h₂]

private lemma lin34_slice_pointwise_algebra
    {ρ r C₁₁ Ip V P IJ : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2) (hC₁₁ : 0 ≤ C₁₁)
    (hV : 0 ≤ V) (hP : 0 ≤ P) (hIJ : 0 ≤ IJ)
    (htotal : Ip ≤ 2 * (C₁₁ ^ (3 / 2 : ℝ) * V +
      lin34RemainderConstant * (r / ρ) ^ (3 : ℕ) * (V + P) + IJ)) :
    r⁻¹ ^ 2 * Ip ≤ lin34PointwiseConstant C₁₁ *
      ((ρ / r) ^ (2 : ℕ) * (ρ⁻¹ ^ 2 * V) + (r / ρ) * (ρ⁻¹ ^ 2 * P) +
        r⁻¹ ^ 2 * IJ) := by
  have hc₁ : (0 : ℝ) ≤ C₁₁ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hC₁₁ _
  have hCR : (0 : ℝ) ≤ lin34RemainderConstant := lin34RemainderConstant_nonneg
  have hq1 : r / ρ ≤ 1 := by
    rw [div_le_one hρ]
    linarith only [hhalf, hρ]
  have hone : (1 : ℝ) ≤ ρ / r := by
    rw [le_div_iff₀ hr]
    linarith only [hhalf, hr]
  have hsq : (1 : ℝ) ≤ (ρ / r) ^ (2 : ℕ) := by
    simpa using one_le_pow₀ hone (n := 2)
  have hX : (0 : ℝ) ≤ (ρ / r) ^ (2 : ℕ) * (ρ⁻¹ ^ 2 * V) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) hV)
  have hY : (0 : ℝ) ≤ (r / ρ) * (ρ⁻¹ ^ 2 * P) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) hP)
  have hZ : (0 : ℝ) ≤ r⁻¹ ^ 2 * IJ :=
    mul_nonneg (by positivity) hIJ
  have hYV : (0 : ℝ) ≤ (r / ρ) * (ρ⁻¹ ^ 2 * V) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) hV)
  have hmain : r⁻¹ ^ 2 * Ip ≤
      r⁻¹ ^ 2 * (2 * (C₁₁ ^ (3 / 2 : ℝ) * V +
        lin34RemainderConstant * (r / ρ) ^ (3 : ℕ) * (V + P) + IJ)) :=
    mul_le_mul_of_nonneg_left htotal (by positivity)
  have hexpand : r⁻¹ ^ 2 * (2 * (C₁₁ ^ (3 / 2 : ℝ) * V +
        lin34RemainderConstant * (r / ρ) ^ (3 : ℕ) * (V + P) + IJ)) =
      (2 * C₁₁ ^ (3 / 2 : ℝ)) * ((ρ / r) ^ (2 : ℕ) * (ρ⁻¹ ^ 2 * V)) +
        (2 * lin34RemainderConstant) * ((r / ρ) * (ρ⁻¹ ^ 2 * V)) +
        (2 * lin34RemainderConstant) * ((r / ρ) * (ρ⁻¹ ^ 2 * P)) +
        2 * (r⁻¹ ^ 2 * IJ) := by
    field_simp
    ring
  have hswap : (2 * lin34RemainderConstant) * ((r / ρ) * (ρ⁻¹ ^ 2 * V)) ≤
      (2 * lin34RemainderConstant) *
        ((ρ / r) ^ (2 : ℕ) * (ρ⁻¹ ^ 2 * V)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hCR])
    refine mul_le_mul_of_nonneg_right (hq1.trans hsq) ?_
    exact mul_nonneg (by positivity) hV
  have hcoefX : 2 * C₁₁ ^ (3 / 2 : ℝ) + 2 * lin34RemainderConstant ≤
      lin34PointwiseConstant C₁₁ := by
    unfold lin34PointwiseConstant
    linarith only []
  have hcoefY : 2 * lin34RemainderConstant ≤ lin34PointwiseConstant C₁₁ := by
    unfold lin34PointwiseConstant
    linarith only [hc₁]
  have hcoefZ : (2 : ℝ) ≤ lin34PointwiseConstant C₁₁ := by
    unfold lin34PointwiseConstant
    linarith only [hc₁, hCR]
  calc
    r⁻¹ ^ 2 * Ip ≤ _ := hmain
    _ = (2 * C₁₁ ^ (3 / 2 : ℝ)) * ((ρ / r) ^ (2 : ℕ) * (ρ⁻¹ ^ 2 * V)) +
        (2 * lin34RemainderConstant) * ((r / ρ) * (ρ⁻¹ ^ 2 * V)) +
        (2 * lin34RemainderConstant) * ((r / ρ) * (ρ⁻¹ ^ 2 * P)) +
        2 * (r⁻¹ ^ 2 * IJ) := hexpand
    _ ≤ (2 * C₁₁ ^ (3 / 2 : ℝ)) * ((ρ / r) ^ (2 : ℕ) * (ρ⁻¹ ^ 2 * V)) +
        (2 * lin34RemainderConstant) *
          ((ρ / r) ^ (2 : ℕ) * (ρ⁻¹ ^ 2 * V)) +
        (2 * lin34RemainderConstant) * ((r / ρ) * (ρ⁻¹ ^ 2 * P)) +
        2 * (r⁻¹ ^ 2 * IJ) := by
      exact add_le_add (add_le_add (add_le_add le_rfl hswap) le_rfl) le_rfl
    _ = (2 * C₁₁ ^ (3 / 2 : ℝ) + 2 * lin34RemainderConstant) *
          ((ρ / r) ^ (2 : ℕ) * (ρ⁻¹ ^ 2 * V)) +
        (2 * lin34RemainderConstant) * ((r / ρ) * (ρ⁻¹ ^ 2 * P)) +
        2 * (r⁻¹ ^ 2 * IJ) := by ring
    _ ≤ lin34PointwiseConstant C₁₁ * ((ρ / r) ^ (2 : ℕ) * (ρ⁻¹ ^ 2 * V)) +
        lin34PointwiseConstant C₁₁ * ((r / ρ) * (ρ⁻¹ ^ 2 * P)) +
        lin34PointwiseConstant C₁₁ * (r⁻¹ ^ 2 * IJ) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hcoefX hX)
        (mul_le_mul_of_nonneg_right hcoefY hY))
        (mul_le_mul_of_nonneg_right hcoefZ hZ)
    _ = lin34PointwiseConstant C₁₁ *
        ((ρ / r) ^ (2 : ℕ) * (ρ⁻¹ ^ 2 * V) + (r / ρ) * (ρ⁻¹ ^ 2 * P) +
          r⁻¹ ^ 2 * IJ) := by ring

private lemma lin34_inner_ball_subset {x₀ : Vec3} {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2) :
    euclideanBall x₀ r ⊆ euclideanBall x₀ (13 * ρ / 20) := by
  intro x hx
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
  exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx).trans_le
    (by linarith only [hhalf, hρ])

private lemma lin34_ball_subset_outer {x₀ : Vec3} {ρ r : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2) :
    euclideanBall x₀ r ⊆ euclideanBall x₀ ρ := by
  intro x hx
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
  exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx).trans_le
    (by linarith only [hhalf, hρ])

/-- **The pointwise-in-time oscillation estimate `eq:lin34-pointwise`.**

For one time slice `s`, with the decomposition of
`prop:pressure-decomposition` run with the centred tensor `eq:Uhat` of
`lem:delta-p-centred`, the normalised `L^{3/2}` mass of the pressure on the
inner ball is controlled by `(ρ/r)²` times the velocity oscillation `eq:Chat`,
`r/ρ` times the pressure mass on the outer ball, and the force group
`p₇ + p₈`.  The Calderón--Zygmund estimate `ext:CZ` for the centred first
potential is the single named input `hCZ_p1`. -/
theorem lin34_slice_pointwise_bound
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ r C₁₁ s : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2) (hC₁₁ : 0 ≤ C₁₁)
    (hp : MemLp (fun y : Vec3 => p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hu : MemLp (fun y : Vec3 => u (y, s)) 2 (volume.restrict (vec3Ball x₀ ρ)))
    (humeas : AEMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hVint : Integrable (fun y : Vec3 =>
      vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hforce : MemLp (lin34ForcePart f x₀ ρ hρ s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (vec3Ball x₀ r)))
    (hp₁ : MemLp (lin34CentredP1 u p f x₀ ρ hρ s)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hCZ_p1 : lpNorm (lin34CentredP1 u p f x₀ ρ hρ s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      C₁₁ * (∫ y in vec3Ball x₀ ρ,
        vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ)) ^ (2 / 3 : ℝ)) :
    r⁻¹ ^ 2 * ∫ x in vec3Ball x₀ r, |p (x, s)| ^ (3 / 2 : ℝ) ≤
      lin34PointwiseConstant C₁₁ *
        ((ρ / r) ^ (2 : ℕ) * (ρ⁻¹ ^ 2 *
            ∫ y in vec3Ball x₀ ρ,
              vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ)) +
          (r / ρ) * (ρ⁻¹ ^ 2 *
            ∫ y in vec3Ball x₀ ρ, |p (y, s)| ^ (3 / 2 : ℝ)) +
          r⁻¹ ^ 2 * ∫ x in vec3Ball x₀ r,
            |lin34ForcePart f x₀ ρ hρ s x| ^ (3 / 2 : ℝ)) := by
  have hBr : euclideanBall x₀ r = vec3Ball x₀ r :=
    lin34_euclideanBall_eq_vec3Ball' hr
  have hBρ : euclideanBall x₀ ρ = vec3Ball x₀ ρ :=
    lin34_euclideanBall_eq_vec3Ball' hρ
  rw [← hBr]
  rw [← hBr] at hforce
  have hone : (1 : ENNReal) ≤ ENNReal.ofReal (3 / 2 : ℝ) := by
    rw [show (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have : IsFiniteMeasure (volume.restrict (vec3Ball x₀ ρ)) := by
    refine isFiniteMeasure_restrict.mpr ?_
    rw [volume_vec3Ball_eq]
    exact (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
      ENNReal.ofReal_lt_top).ne
  have hpint1 : Integrable (fun y : Vec3 => |p (y, s)|)
      (volume.restrict (vec3Ball x₀ ρ)) := (hp.integrable hone).abs
  have hpm : AEStronglyMeasurable (fun y : Vec3 => p (y, s))
      (volume.restrict (vec3Ball x₀ ρ)) := hp.aestronglyMeasurable
  have hPint : Integrable (fun y : Vec3 => |p (y, s)| ^ (3 / 2 : ℝ))
      (volume.restrict (vec3Ball x₀ ρ)) := by
    have h := hp.integrable_norm_rpow (by norm_num) (by norm_num)
    simpa only [Real.norm_eq_abs,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)] using h
  have hsubr : euclideanBall x₀ r ⊆ vec3Ball x₀ ρ := by
    rw [← hBρ]
    exact lin34_ball_subset_outer hρ hr hhalf
  have hpr : MemLp (fun y : Vec3 => p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)) :=
    hp.mono_measure (Measure.restrict_mono_set volume hsubr)
  have hp₁r : MemLp (lin34CentredP1 u p f x₀ ρ hρ s)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)) :=
    hp₁.mono_measure Measure.restrict_le_self
  have hrep : (fun x : Vec3 => p (x, s)) =ᵐ[
      volume.restrict (euclideanBall x₀ r)]
      (lin34CentredP1 u p f x₀ ρ hρ s +
        lin34CentredRemainder u p x₀ ρ hρ s + lin34ForcePart f x₀ ρ hρ s) :=
    ae_restrict_of_ae_restrict_of_subset
      (lin34_inner_ball_subset hρ hr hhalf)
      (lin34_centred_decomposition_on_inner (u := u) (p := p) (f := f)
        (x₀ := x₀) (s := s) hρ)
  have hHmem : MemLp (lin34CentredRemainder u p x₀ ρ hρ s)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ r)) := by
    have hsub : MemLp ((fun x : Vec3 => p (x, s)) -
        lin34CentredP1 u p f x₀ ρ hρ s - lin34ForcePart f x₀ ρ hρ s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ r)) :=
      (hpr.sub hp₁r).sub hforce
    refine hsub.ae_eq ?_
    filter_upwards [hrep] with x hx
    change p (x, s) - lin34CentredP1 u p f x₀ ρ hρ s x -
      lin34ForcePart f x₀ ρ hρ s x =
      lin34CentredRemainder u p x₀ ρ hρ s x
    have hx' : p (x, s) = lin34CentredP1 u p f x₀ ρ hρ s x +
        lin34CentredRemainder u p x₀ ρ hρ s x +
        lin34ForcePart f x₀ ρ hρ s x := hx
    rw [hx']
    ring
  have hV0 : 0 ≤ ∫ y in vec3Ball x₀ ρ,
      vec3EuclideanNorm (meanFreeVec u x₀ ρ s y) ^ (3 : ℕ) :=
    integral_nonneg (fun y => pow_nonneg (vec3EuclideanNorm_nonneg _) 3)
  have hP0 : 0 ≤ ∫ y in vec3Ball x₀ ρ, |p (y, s)| ^ (3 / 2 : ℝ) :=
    integral_nonneg (fun y => by positivity)
  have hI₁ := lin34_p1_slice_integral_bound (x₀ := x₀) (r := r)
    hV0 hC₁₁ hp₁ hCZ_p1
  have hIH := lin34_centred_remainder_integral_bound hρ hr hhalf hu humeas
    hpint1 hpm hVint hPint hHmem
  have htotal := pressure_oscillation_integral_of_components_force hr hpr hp₁r
    hHmem hforce hrep hI₁ hIH (le_refl (∫ x in euclideanBall x₀ r,
      |lin34ForcePart f x₀ ρ hρ s x| ^ (3 / 2 : ℝ)))
  exact lin34_slice_pointwise_algebra hρ hr hhalf hC₁₁ hV0 hP0
    (integral_nonneg (fun x => by positivity)) htotal

end CKN
