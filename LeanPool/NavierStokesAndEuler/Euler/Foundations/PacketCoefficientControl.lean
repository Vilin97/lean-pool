/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketRay
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Packet Coefficient Control
-/

@[expose] public section

noncomputable section

open Set

namespace EulerPacketCoefficientControl

open Real EulerPacketRay

/-- A derivative bound controls the change of a scalar coefficient on
the entire finite time interval. -/
theorem motion_displacement_bound
    {Θ L : ℝ} {f f₁ : ℝ → ℝ} (_hΘ : 0 ≤ Θ) (hL : 0 ≤ L)
    (hf : ∀ t ∈ Icc 0 Θ, HasDerivAt f (f₁ t) t)
    (hb : ∀ t ∈ Icc 0 Θ, |f₁ t| ≤ L) :
    ∀ t ∈ Icc 0 Θ, |f t - f 0| ≤ L * Θ := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hf t ht).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hb t (Ico_subset_Icc_self ht))
  intro t ht
  have h := hh t ht
  simp only [Real.norm_eq_abs, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left ht.2 hL)

/-- A multiplicative differential bound keeps the normalized shear near
one.  Positivity or an a priori shear bound is not assumed. -/
theorem multiplicative_motion_bound
    {Θ k : ℝ} {H H₁ : ℝ → ℝ}
    (hΘ : 0 ≤ Θ) (hk : 0 ≤ k) (hsmall : k * Θ ≤ 1 / 2)
    (hH : ∀ t ∈ Icc 0 Θ, HasDerivAt H (H₁ t) t)
    (hH0 : H 0 = 1) (hb : ∀ t ∈ Icc 0 Θ, |H₁ t| ≤ k * |H t|) :
    ∀ t ∈ Icc 0 Θ, |H t| ≤ 2 ∧ |H t - 1| ≤ 2 * k * Θ := by
  have hc : ContinuousOn H (Icc 0 Θ) := fun t ht => (hH t ht).continuousAt.continuousWithinAt
  obtain ⟨c, hci, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hΘ⟩⟩ hc.abs
  have hbound : ∀ t ∈ Icc 0 Θ, |H₁ t| ≤ k * |H c| := by
    intro t ht
    exact (hb t ht).trans (mul_le_mul_of_nonneg_left (hmax ht) hk)
  have hdiff := motion_displacement_bound hΘ (mul_nonneg hk (abs_nonneg _)) hH hbound
  have hcdiff := hdiff c hci
  rw [hH0] at hcdiff
  have htri := abs_add_le (H c - 1) 1
  norm_num at htri
  have hscaled := mul_le_mul_of_nonneg_right hsmall (abs_nonneg (H c))
  have hM : |H c| ≤ 2 := by nlinarith only [hcdiff, htri, hscaled]
  intro t ht
  refine ⟨(hmax ht).trans hM, ?_⟩
  have hh := hdiff t ht
  rw [hH0] at hh
  have hm := mul_le_mul_of_nonneg_right hM (mul_nonneg hk hΘ)
  nlinarith only [hh, hm]

/-- Raw moving-frame coefficient motion implies the normalized error
bounds used in the ray and velocity reductions. -/
theorem normalized_motion_errors
    {a ε Θ G d β : ℝ} {B E : ℝ → Fin 3 → Fin 3 → ℝ}
    {h h₁ b₁ k₁ : ℝ → ℝ}
    (ha : 1 / 2 ≤ a) (hε : 0 < ε) (hΘ : 1 ≤ Θ) (hG : 1 ≤ G) (hd : 0 ≤ d)
    (hsmall : 16 * (ε * Θ * G ^ 2 + d) ≤ 1)
    (hB : ∀ t ∈ Icc 0 Θ, ∀ i j, |B t i j| ≤ G)
    (hE : ∀ t ∈ Icc 0 Θ, ∀ i j, |E t i j| ≤ d)
    (hb : ∀ t ∈ Icc 0 Θ, HasDerivAt (fun s => B s 0 1) (b₁ t) t)
    (hk : ∀ t ∈ Icc 0 Θ, HasDerivAt (fun s => B s 2 1) (k₁ t) t)
    (hbBound : ∀ t ∈ Icc 0 Θ, |b₁ t| ≤ 2 * ε * G ^ 2)
    (hkBound : ∀ t ∈ Icc 0 Θ, |k₁ t| ≤ 2 * ε * G ^ 2)
    (hShear : ∀ t ∈ Icc 0 Θ, HasDerivAt h (h₁ t) t)
    (hShearBound : ∀ t ∈ Icc 0 Θ, |h₁ t| ≤ (4 * ε * G) * |h t|)
    (hb0 : B 0 0 1 = a) (hk0 : B 0 2 1 = a * β) (hh0 : h 0 = a / ε ^ 2) :
    let e := 16 * (ε * Θ * G ^ 2 + d)
    ε ≤ e ∧ ∀ t ∈ Icc 0 Θ,
      (∀ i j, |ε * B t i j / a| ≤ e) ∧
      (∀ i j, |E t i j / a| ≤ e) ∧
      |ε ^ 2 * h t / a - 1| ≤ e ∧
      |B t 0 1 / a - 1| ≤ e ∧ |B t 2 1 / a - β| ≤ e := by
  let e := 16 * (ε * Θ * G ^ 2 + d)
  have haPos : 0 < a := by linarith
  have haNe : a ≠ 0 := ne_of_gt haPos
  have hεNe : ε ≠ 0 := ne_of_gt hε
  have hΘ0 : 0 ≤ Θ := by linarith
  have hG0 : 0 ≤ G := by linarith
  have hG2 : G ≤ G ^ 2 := by nlinarith only [hG]
  have hΘG2 : G ^ 2 ≤ Θ * G ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hΘ (sq_nonneg G)
    nlinarith only [hh]
  have hεG : ε * G ≤ ε * Θ * G ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (hG2.trans hΘG2) hε.le
    nlinarith only [hh]
  have hεBase : ε ≤ ε * Θ * G ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hG hε.le
    nlinarith only [hh, hεG]
  have hbase0 : 0 ≤ ε * Θ * G ^ 2 := by positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hεe : ε ≤ e := by dsimp [e]; nlinarith only [hεBase, hd, hε]
  have hShearSmall : (4 * ε * G) * Θ ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hG2 (by positivity : 0 ≤ ε * Θ)
    nlinarith only [hh, hsmall, hd]
  let H : ℝ → ℝ := fun t => ε ^ 2 * h t / a
  let H₁ : ℝ → ℝ := fun t => ε ^ 2 * h₁ t / a
  have hH : ∀ t ∈ Icc 0 Θ, HasDerivAt H (H₁ t) t := by
    intro t ht
    exact ((hShear t ht).const_mul (ε ^ 2)).div_const a
  have hH0 : H 0 = 1 := by dsimp [H]; rw [hh0]; field_simp
  have hHbound : ∀ t ∈ Icc 0 Θ, |H₁ t| ≤ (4 * ε * G) * |H t| := by
    intro t ht
    have hm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hShearBound t ht) (sq_nonneg ε)) haPos.le
    dsimp [H₁, H]
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg ε), abs_of_pos haPos,
      abs_div, abs_mul, abs_of_nonneg (sq_nonneg ε), abs_of_pos haPos]
    convert! hm using 1
    ring
  have hHclose := multiplicative_motion_bound hΘ0 (by positivity : 0 ≤ 4 * ε * G)
    hShearSmall hH hH0 hHbound
  have hBclose := motion_displacement_bound hΘ0 (by positivity : 0 ≤ 2 * ε * G ^ 2) hb hbBound
  have hKclose := motion_displacement_bound hΘ0 (by positivity : 0 ≤ 2 * ε * G ^ 2) hk hkBound
  refine ⟨hεe, ?_⟩
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [abs_div, abs_mul, abs_of_pos hε, abs_of_pos haPos, div_le_iff₀ haPos]
    have hm := mul_le_mul_of_nonneg_left (hB t ht i j) hε.le
    have heA := mul_le_mul_of_nonneg_left ha he
    dsimp [e] at heA ⊢
    nlinarith only [hm, heA, hεG, hd, hbase0]
  · intro i j
    rw [abs_div, abs_of_pos haPos, div_le_iff₀ haPos]
    have heA := mul_le_mul_of_nonneg_left ha he
    have hbb := hE t ht i j
    have hpos : 0 ≤ ε * Θ * G ^ 2 := by positivity
    dsimp [e] at heA ⊢
    nlinarith only [hbb, heA, hpos, hd]
  · have hh := (hHclose t ht).2
    have hm := mul_le_mul_of_nonneg_left hG2 (by positivity : 0 ≤ ε * Θ)
    dsimp [H, e] at hh ⊢
    nlinarith only [hh, hm, hd, hbase0]
  · have hh := hBclose t ht
    rw [hb0] at hh
    have hid : B t 0 1 / a - 1 = (B t 0 1 - a) / a := by field_simp
    rw [hid, abs_div, abs_of_pos haPos, div_le_iff₀ haPos]
    have heA := mul_le_mul_of_nonneg_left ha he
    have hpos : 0 ≤ ε * Θ * G ^ 2 := by positivity
    dsimp [e] at heA ⊢
    nlinarith only [hh, heA, hd, hpos]
  · have hh := hKclose t ht
    rw [hk0] at hh
    have hid : B t 2 1 / a - β = (B t 2 1 - a * β) / a := by field_simp
    rw [hid, abs_div, abs_of_pos haPos, div_le_iff₀ haPos]
    have heA := mul_le_mul_of_nonneg_left ha he
    have hpos : 0 ≤ ε * Θ * G ^ 2 := by positivity
    dsimp [e] at heA ⊢
    nlinarith only [hh, heA, hd, hpos]

/-- The exact raw moving-frame matrices satisfy the coefficient-error
hypotheses of the controlled-stage theorem. -/
theorem raw_frame_matrix_errors
    {a ε e β h : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (ha : a ≠ 0) (hε : 0 < ε) (hεe : ε ≤ e) (he : 0 ≤ e) (heSmall : e ≤ 1)
    (hB : ∀ i j, |ε * B i j / a| ≤ e) (hE : ∀ i j, |E i j / a| ≤ e)
    (hH : |ε ^ 2 * h / a - 1| ≤ e) (hα : |B 0 1 / a - 1| ≤ e)
    (hκ : |B 2 1 / a - β| ≤ e) :
    (∀ i j, |scaledRayEntry a ε (parentEntry B E h) (frameSkew B) i j - idealRayEntry β i j| ≤ 4 *
        e) ∧
    (∀ i j, |scaledVelocityEntry a ε (parentEntry B E h) i j - idealVelocityEntry β i j| ≤ 3 * e) ∧
    (∀ j,
      |scaledVelocityEntry a ε (fun i j => parentEntry B E h i j + frameSkew B i j) 0 j -
        idealUnprojectedEntry 0 j| ≤ 5 * e ∧
      |scaledVelocityEntry a ε (fun i j => parentEntry B E h i j + frameSkew B i j) 1 j -
        idealUnprojectedEntry 1 j| ≤ 5 * e) := by
  have hεupper : ε ≤ 1 := hεe.trans heSmall
  refine ⟨scaled_ray_entry_error ha hε hεupper he hB hE hH hκ, ?_, ?_⟩
  · intro i j
    rw [scaled_velocity_entry_identity ha]
    exact normalized_velocity_entry_error hε.le hεupper he hB hE hH hα hκ i j
  · intro j
    have hids := scaled_unprojected_entry_identity (B := B) (E := E) (h := h) (ε := ε) ha j
    have hbound := normalized_unprojected_entry_error hε.le hεe he heSmall hB hE hH hα
    constructor
    · rw [hids.1]
      exact hbound 0 j
    · rw [hids.2]
      exact hbound 1 j

end EulerPacketCoefficientControl
