/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketPerturbation
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
The triangular ray system and its perturbation estimates.  These results
derive ray closeness from the differential equations and coefficient errors.
-/

@[expose] public section

noncomputable section

namespace EulerPacketRay

open Set Filter Real EulerPacketPerturbation
open scoped Topology

/-- The sum norm of three scalar coordinates. -/
def norm3 (p q n : ℝ) : ℝ := |p| + |q| + |n|

/-- Exact Duhamel formulas for the triangular ray system. -/
theorem triangular_ray_formula
    {β T : ℝ} {P Q N f g h : ℝ → ℝ}
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t)
    (hfc : ContinuousOn f (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hhc : ContinuousOn h (Icc 0 T)) :
    ∀ t ∈ Icc 0 T,
      P t = P 0 - t * Q 0 + β * t ^ 2 * N 0 +
        ∫ s in (0 : ℝ)..t, f s - (t - s) * g s + β * (t - s) ^ 2 * h s ∧
      Q t = Q 0 - 2 * β * t * N 0 +
        ∫ s in (0 : ℝ)..t, g s - 2 * β * (t - s) * h s ∧
      N t = N 0 + ∫ s in (0 : ℝ)..t, h s := by
  intro t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have htc : ContinuousOn (fun s : ℝ => t - s) (Icc 0 T) := by fun_prop
  have hPc : ContinuousOn (fun s => f s - (t - s) * g s + β * (t - s) ^ 2 * h s) (Icc 0 T) :=
    (hfc.sub (htc.mul hgc)).add ((continuousOn_const.mul (htc.pow 2)).mul hhc)
  have hQc : ContinuousOn (fun s => g s - 2 * β * (t - s) * h s) (Icc 0 T) :=
    hgc.sub ((continuousOn_const.mul htc).mul hhc)
  have hPi : IntervalIntegrable (fun s => f s - (t - s) * g s + β * (t - s) ^ 2 * h s)
      MeasureTheory.volume 0 t := (hPc.mono hsub).intervalIntegrable
  have hQi : IntervalIntegrable (fun s => g s - 2 * β * (t - s) * h s)
      MeasureTheory.volume 0 t := (hQc.mono hsub).intervalIntegrable
  have hNi : IntervalIntegrable h MeasureTheory.volume 0 t := (hhc.mono hsub).intervalIntegrable
  have hdP : ∀ s ∈ uIcc 0 t,
      HasDerivAt (fun r => P r - (t - r) * Q r + β * (t - r) ^ 2 * N r)
        (f s - (t - s) * g s + β * (t - s) ^ 2 * h s) s := by
    intro s hs
    have hsab := hsub hs
    have hd := (hasDerivAt_id s).const_sub t
    apply (((hP s hsab).sub (hd.mul (hQ s hsab))).add
      (((hd.fun_pow 2).const_mul β).mul (hN s hsab))).congr_deriv
    dsimp
    ring
  have hdQ : ∀ s ∈ uIcc 0 t,
      HasDerivAt (fun r => Q r - 2 * β * (t - r) * N r)
        (g s - 2 * β * (t - s) * h s) s := by
    intro s hs
    have hsab := hsub hs
    have hd := ((hasDerivAt_id s).const_sub t).const_mul (2 * β)
    apply ((hQ s hsab).sub (hd.mul (hN s hsab))).congr_deriv
    dsimp
    ring
  have hFP := intervalIntegral.integral_eq_sub_of_hasDerivAt hdP hPi
  have hFQ := intervalIntegral.integral_eq_sub_of_hasDerivAt hdQ hQi
  have hFN := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hN s (hsub hs)) hNi
  simp only [sub_self, zero_mul, mul_zero, zero_pow (by
      decide : 2 ≠ 0), add_zero, sub_zero] at hFP hFQ
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The triangular ray propagator has a polynomial norm bound. -/
theorem triangular_ray_kernel_bound
    {β Θ d p q n : ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hd : 0 ≤ d) (hdΘ : d ≤ Θ) :
    norm3 (p - d * q + β * d ^ 2 * n) (q - 2 * β * d * n) n ≤
      4 * Θ ^ 2 * norm3 p q n := by
  have hΘ0 : 0 ≤ Θ := le_trans zero_le_one hΘ
  have hd2 : d ^ 2 ≤ Θ ^ 2 := (sq_le_sq₀ hd hΘ0).mpr hdΘ
  have h1 := abs_add_le (p - d * q) (β * d ^ 2 * n)
  have h2 : |p - d * q| ≤ |p| + |d * q| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le p (d * q)
  have h3 : |q - 2 * β * d * n| ≤ |q| + |2 * β * d * n| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le q (2 * β * d * n)
  simp only [abs_mul, abs_of_nonneg hβ, abs_of_nonneg hd, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (sq_nonneg d)] at h1 h2 h3
  have hcol1 : 1 ≤ 4 * Θ ^ 2 := by nlinarith
  have hcol2 : d + 1 ≤ 4 * Θ ^ 2 := by nlinarith
  have hβd2 : β * d ^ 2 ≤ Θ ^ 2 :=
    (mul_le_mul_of_nonneg_right hβupper (sq_nonneg d)).trans (by simpa using hd2)
  have hβd : β * d ≤ Θ :=
    (mul_le_mul_of_nonneg_right hβupper hd).trans (by simpa using hdΘ)
  have hcol3 : β * d ^ 2 + 2 * β * d + 1 ≤ 4 * Θ ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hcol1 (abs_nonneg p)
  have hq := mul_le_mul_of_nonneg_right hcol2 (abs_nonneg q)
  have hn := mul_le_mul_of_nonneg_right hcol3 (abs_nonneg n)
  unfold norm3
  linarith

/-- The exact triangular ray equations imply a polynomial Duhamel bound. -/
theorem triangular_ray_forced_bound
    {β Θ T : ℝ} {P Q N f g h : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT : T ≤ Θ)
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t)
    (hfc : ContinuousOn f (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hhc : ContinuousOn h (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, norm3 (P t) (Q t) (N t) ≤
      4 * Θ ^ 2 * norm3 (P 0) (Q 0) (N 0) +
        4 * Θ ^ 2 * ∫ s in (0 : ℝ)..t, norm3 (f s) (g s) (h s) := by
  intro t ht
  have hformula := triangular_ray_formula hP hQ hN hfc hgc hhc t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have htc : ContinuousOn (fun s : ℝ => t - s) (Icc 0 T) := by fun_prop
  have hc1 : ContinuousOn (fun s => f s - (t - s) * g s + β * (t - s) ^ 2 * h s) (Icc 0 T) :=
    (hfc.sub (htc.mul hgc)).add ((continuousOn_const.mul (htc.pow 2)).mul hhc)
  have hc2 : ContinuousOn (fun s => g s - 2 * β * (t - s) * h s) (Icc 0 T) :=
    hgc.sub ((continuousOn_const.mul htc).mul hhc)
  have hi1 : IntervalIntegrable (fun s => |f s - (t - s) * g s + β * (t - s) ^ 2 * h s|)
      MeasureTheory.volume 0 t := (hc1.abs.mono hsub).intervalIntegrable
  have hi2 : IntervalIntegrable (fun s => |g s - 2 * β * (t - s) * h s|)
      MeasureTheory.volume 0 t := (hc2.abs.mono hsub).intervalIntegrable
  have hi3 : IntervalIntegrable (fun s => |h s|) MeasureTheory.volume 0 t :=
    (hhc.abs.mono hsub).intervalIntegrable
  have himajor : IntervalIntegrable (fun s => (4 * Θ ^ 2) * norm3 (f s) (g s) (h s))
      MeasureTheory.volume 0 t :=
    (((hfc.abs.add hgc.abs).add hhc.abs).mono hsub).intervalIntegrable.const_mul (4 * Θ ^ 2)
  have hpoint : ∀ s ∈ Icc 0 t,
      norm3 (f s - (t - s) * g s + β * (t - s) ^ 2 * h s)
        (g s - 2 * β * (t - s) * h s) (h s) ≤ 4 * Θ ^ 2 * norm3 (f s) (g s) (h s) := by
    intro s hs
    apply triangular_ray_kernel_bound hβ hβupper hΘ
    · linarith [hs.2]
    · linarith [hs.1, ht.2]
  have hmono := intervalIntegral.integral_mono_on ht.1 ((hi1.add hi2).add hi3) himajor hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have hI :
      |∫ s in (0 : ℝ)..t, f s - (t - s) * g s + β * (t - s) ^ 2 * h s| +
      |∫ s in (0 : ℝ)..t, g s - 2 * β * (t - s) * h s| + |∫ s in (0 : ℝ)..t, h s| ≤
      ∫ s in (0 : ℝ)..t, norm3 (f s - (t - s) * g s + β * (t - s) ^ 2 * h s)
        (g s - 2 * β * (t - s) * h s) (h s) := by
    unfold norm3
    rw [intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2]
    exact add_le_add (add_le_add (intervalIntegral.abs_integral_le_integral_abs ht.1)
      (intervalIntegral.abs_integral_le_integral_abs ht.1))
          (intervalIntegral.abs_integral_le_integral_abs ht.1)
  have hbase := triangular_ray_kernel_bound (p := P 0) (q := Q 0) (n := N 0)
    hβ hβupper hΘ ht.1 (ht.2.trans hT)
  have hPt : |P t| ≤ |P 0 - t * Q 0 + β * t ^ 2 * N 0| +
      |∫ s in (0 : ℝ)..t, f s - (t - s) * g s + β * (t - s) ^ 2 * h s| := by
    rw [hformula.1]
    exact abs_add_le _ _
  have hQt : |Q t| ≤ |Q 0 - 2 * β * t * N 0| +
      |∫ s in (0 : ℝ)..t, g s - 2 * β * (t - s) * h s| := by
    rw [hformula.2.1]
    exact abs_add_le _ _
  have hNt : |N t| ≤ |N 0| + |∫ s in (0 : ℝ)..t, h s| := by
    rw [hformula.2.2]
    exact abs_add_le _ _
  unfold norm3 at hbase hI hmono ⊢
  linarith

/-- A small perturbation of the triangular ray system remains polynomially
bounded on the whole interval. -/
theorem triangular_ray_perturbed_bound
    {β Θ T δ : ℝ} {P Q N f g h : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT0 : 0 ≤ T) (hT : T ≤ Θ)
    (hδ : 0 ≤ δ) (hsmall : 4 * Θ ^ 2 * δ * T ≤ 1 / 2)
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t)
    (hfc : ContinuousOn f (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hhc : ContinuousOn h (Icc 0 T))
    (hforcing : ∀ t ∈ Icc 0 T, norm3 (f t) (g t) (h t) ≤ δ * norm3 (P t) (Q t) (N t)) :
    ∀ t ∈ Icc 0 T, norm3 (P t) (Q t) (N t) ≤ 8 * Θ ^ 2 * norm3 (P 0) (Q 0) (N 0) := by
  have hPc : ContinuousOn P (Icc 0 T) := fun t ht => (hP t ht).continuousAt.continuousWithinAt
  have hQc : ContinuousOn Q (Icc 0 T) := fun t ht => (hQ t ht).continuousAt.continuousWithinAt
  have hNc : ContinuousOn N (Icc 0 T) := fun t ht => (hN t ht).continuousAt.continuousWithinAt
  have hstate : ContinuousOn (fun t => norm3 (P t) (Q t) (N t)) (Icc 0 T) :=
    (hPc.abs.add hQc.abs).add hNc.abs
  have hforce : ContinuousOn (fun t => norm3 (f t) (g t) (h t)) (Icc 0 T) :=
    (hfc.abs.add hgc.abs).add hhc.abs
  have hforced := triangular_ray_forced_bound hβ hβupper hΘ hT hP hQ hN hfc hgc hhc
  have hineq : ∀ t ∈ Icc 0 T, norm3 (P t) (Q t) (N t) ≤
      4 * Θ ^ 2 * norm3 (P 0) (Q 0) (N 0) +
        (4 * Θ ^ 2 * δ) * ∫ s in (0 : ℝ)..t, norm3 (P s) (Q s) (N s) := by
    intro t ht
    have hsub : uIcc 0 t ⊆ Icc 0 T := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hFi : IntervalIntegrable (fun s => norm3 (f s) (g s) (h s)) MeasureTheory.volume 0 t :=
      (hforce.mono hsub).intervalIntegrable
    have hSi : IntervalIntegrable (fun s => δ * norm3 (P s) (Q s) (N s)) MeasureTheory.volume 0 t :=
      ((hstate.mono hsub).intervalIntegrable).const_mul δ
    have hi := intervalIntegral.integral_mono_on ht.1 hFi hSi
      (fun s hs => hforcing s ⟨hs.1, hs.2.trans ht.2⟩)
    rw [intervalIntegral.integral_const_mul] at hi
    have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ 4 * Θ ^ 2 by positivity)
    linarith [hforced t ht]
  have hresult := integral_absorb
    (g := fun t => norm3 (P t) (Q t) (N t))
    (A := 4 * Θ ^ 2 * norm3 (P 0) (Q 0) (N 0)) (K := 4 * Θ ^ 2 * δ)
    hT0 hstate (fun _ _ => by unfold norm3; positivity) (by positivity)
    (by simpa using hsmall) hineq
  intro t ht
  linarith [hresult t ht]

/-- Ray closeness is derived from the ODE and the forcing bound, with a
polynomial loss and arbitrary small initial ray error. -/
theorem triangular_ray_difference_bound
    {β Θ T δ η : ℝ} {P Q N f g h : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT0 : 0 ≤ T) (hT : T ≤ Θ)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hsmall : 4 * Θ ^ 2 * δ * T ≤ 1 / 2)
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t)
    (hfc : ContinuousOn f (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hhc : ContinuousOn h (Icc 0 T))
    (hforcing : ∀ t ∈ Icc 0 T, norm3 (f t) (g t) (h t) ≤ δ * norm3 (P t) (Q t) (N t))
    (hinitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ η) :
    ∀ t ∈ Icc 0 T, norm3 (P t - β * t ^ 2) (Q t + 2 * β * t) (N t - 1) ≤
      4 * Θ ^ 2 * η + 32 * δ * Θ ^ 5 * (1 + η) := by
  have hnorm0 : norm3 (P 0) (Q 0) (N 0) ≤ 1 + η := by
    have hn : |N 0| ≤ |N 0 - 1| + 1 := by
      have := abs_add_le (N 0 - 1) 1
      simpa using this
    unfold norm3 at hinitial ⊢
    linarith
  have hstate := triangular_ray_perturbed_bound hβ hβupper hΘ hT0 hT hδ hsmall
    hP hQ hN hfc hgc hhc hforcing
  have hPe : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => P s - β * s ^ 2) (-(Q t + 2 * β * t) + f t) t := by
    intro t ht
    apply ((hP t ht).sub (((hasDerivAt_id t).fun_pow 2).const_mul β)).congr_deriv
    dsimp
    ring
  have hQe : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => Q s + 2 * β * s) (-2 * β * (N t - 1) + g t) t := by
    intro t ht
    apply ((hQ t ht).add ((hasDerivAt_id t).const_mul (2 * β))).congr_deriv
    ring
  have hNe : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => N s - 1) (h t) t :=
    fun t ht => (hN t ht).sub_const 1
  have herror := triangular_ray_forced_bound hβ hβupper hΘ hT hPe hQe hNe hfc hgc hhc
  have hforce : ContinuousOn (fun t => norm3 (f t) (g t) (h t)) (Icc 0 T) :=
    (hfc.abs.add hgc.abs).add hhc.abs
  intro t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hFi : IntervalIntegrable (fun s => norm3 (f s) (g s) (h s)) MeasureTheory.volume 0 t :=
    (hforce.mono hsub).intervalIntegrable
  have hpoint : ∀ s ∈ Icc 0 t, norm3 (f s) (g s) (h s) ≤ δ * (8 * Θ ^ 2 * (1 + η)) := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    have hm := mul_le_mul_of_nonneg_left hnorm0 (show 0 ≤ 8 * Θ ^ 2 by positivity)
    have hbound : norm3 (P s) (Q s) (N s) ≤ 8 * Θ ^ 2 * (1 + η) := (hstate s hsT).trans hm
    exact (hforcing s hsT).trans (mul_le_mul_of_nonneg_left hbound hδ)
  have hi := intervalIntegral.integral_mono_on ht.1 hFi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => δ * (8 * Θ ^ 2 * (1 + η)))
      MeasureTheory.volume 0 t) hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hi
  have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ 4 * Θ ^ 2 by positivity)
  have htΘ : t ≤ Θ := ht.2.trans hT
  have htime := mul_le_mul_of_nonneg_left htΘ (show 0 ≤ 32 * δ * Θ ^ 4 * (1 + η) by positivity)
  have hinit := mul_le_mul_of_nonneg_left hinitial (show 0 ≤ 4 * Θ ^ 2 by positivity)
  have herr := herror t ht
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, add_zero] at herr
  linarith

/-- Entries of the triangular ideal ray generator. -/
def idealRayEntry (β : ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 ∧ j = 1 then -1 else if i = 1 ∧ j = 2 then -2 * β else 0

theorem three_term_bound {a b c p q n e : ℝ}
    (ha : |a| ≤ e) (hb : |b| ≤ e) (hc : |c| ≤ e) :
    |a * p + b * q + c * n| ≤ e * norm3 p q n := by
  have h1 := abs_add_le (a * p + b * q) (c * n)
  have h2 := abs_add_le (a * p) (b * q)
  simp only [abs_mul] at h1 h2
  have hp := mul_le_mul_of_nonneg_right ha (abs_nonneg p)
  have hq := mul_le_mul_of_nonneg_right hb (abs_nonneg q)
  have hn := mul_le_mul_of_nonneg_right hc (abs_nonneg n)
  unfold norm3
  linarith

/-- The ray closeness estimate follows from entrywise coefficient error.
No closeness of the ray itself is assumed.  The third component stays away
from zero, as required to eliminate the third velocity coordinate. -/
theorem ray_closeness_of_coefficient_error
    {β Θ T e : ℝ} {A : ℝ → Fin 3 → Fin 3 → ℝ} {P Q N : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT0 : 0 ≤ T) (hT : T ≤ Θ)
    (he : 0 ≤ e) (hsmall : 400 * e * Θ ^ 5 ≤ 1)
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P
      (A t 0 0 * P t + A t 0 1 * Q t + A t 0 2 * N t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q
      (A t 1 0 * P t + A t 1 1 * Q t + A t 1 2 * N t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N
      (A t 2 0 * P t + A t 2 1 * Q t + A t 2 2 * N t) t)
    (hclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealRayEntry β i j| ≤ e)
    (hinitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e) :
    ∀ t ∈ Icc 0 T,
      norm3 (P t - β * t ^ 2) (Q t + 2 * β * t) (N t - 1) ≤ 200 * e * Θ ^ 5 ∧
        1 / 2 ≤ N t := by
  let f : ℝ → ℝ := fun t => A t 0 0 * P t + (A t 0 1 + 1) * Q t + A t 0 2 * N t
  let g : ℝ → ℝ := fun t => A t 1 0 * P t + A t 1 1 * Q t + (A t 1 2 + 2 * β) * N t
  let h : ℝ → ℝ := fun t => A t 2 0 * P t + A t 2 1 * Q t + A t 2 2 * N t
  have hPc : ContinuousOn P (Icc 0 T) := fun t ht => (hP t ht).continuousAt.continuousWithinAt
  have hQc : ContinuousOn Q (Icc 0 T) := fun t ht => (hQ t ht).continuousAt.continuousWithinAt
  have hNc : ContinuousOn N (Icc 0 T) := fun t ht => (hN t ht).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Icc 0 T) := by unfold f; fun_prop
  have hgc : ContinuousOn g (Icc 0 T) := by unfold g; fun_prop
  have hhc : ContinuousOn h (Icc 0 T) := by unfold h; fun_prop
  have hPf : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t := by
    intro t ht
    apply (hP t ht).congr_deriv
    dsimp [f]
    ring
  have hQg : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t := by
    intro t ht
    apply (hQ t ht).congr_deriv
    dsimp [g]
    ring
  have hNh : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t := hN
  have hforcing : ∀ t ∈ Icc 0 T, norm3 (f t) (g t) (h t) ≤ (3 * e) * norm3 (P t) (Q t) (N t) := by
    intro t ht
    have hf : |f t| ≤ e * norm3 (P t) (Q t) (N t) := by
      apply three_term_bound
      · simpa [idealRayEntry] using hclose t ht 0 0
      · simpa [idealRayEntry] using hclose t ht 0 1
      · simpa [idealRayEntry] using hclose t ht 0 2
    have hg : |g t| ≤ e * norm3 (P t) (Q t) (N t) := by
      apply three_term_bound
      · simpa [idealRayEntry] using hclose t ht 1 0
      · simpa [idealRayEntry] using hclose t ht 1 1
      · simpa [idealRayEntry] using hclose t ht 1 2
    have hh : |h t| ≤ e * norm3 (P t) (Q t) (N t) := by
      apply three_term_bound
      · simpa [idealRayEntry] using hclose t ht 2 0
      · simpa [idealRayEntry] using hclose t ht 2 1
      · simpa [idealRayEntry] using hclose t ht 2 2
    unfold norm3
    unfold norm3 at hf hg hh
    linarith
  have hΘ0 : 0 ≤ Θ := le_trans zero_le_one hΘ
  have hpow35 : Θ ^ 3 ≤ Θ ^ 5 := pow_le_pow_right₀ hΘ (by norm_num)
  have hpow25 : Θ ^ 2 ≤ Θ ^ 5 := pow_le_pow_right₀ hΘ (by norm_num)
  have hpow5 : 1 ≤ Θ ^ 5 := one_le_pow₀ hΘ
  have he1 : e ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hpow5 he
    linarith
  have hsm : 4 * Θ ^ 2 * (3 * e) * T ≤ 1 / 2 := by
    have ht := mul_le_mul_of_nonneg_left hT (show 0 ≤ 12 * e * Θ ^ 2 by positivity)
    have hp := mul_le_mul_of_nonneg_left hpow35 (show 0 ≤ 12 * e by positivity)
    linarith
  have hdiff := triangular_ray_difference_bound hβ hβupper hΘ hT0 hT
    (by positivity : 0 ≤ 3 * e) he hsm hPf hQg hNh hfc hgc hhc hforcing hinitial
  intro t ht
  have hbound : norm3 (P t - β * t ^ 2) (Q t + 2 * β * t) (N t - 1) ≤ 200 * e * Θ ^ 5 := by
    have h1 := mul_le_mul_of_nonneg_left hpow25 (show 0 ≤ 4 * e by positivity)
    have h2 := mul_le_mul_of_nonneg_left (show 1 + e ≤ 2 by linarith)
      (show 0 ≤ 96 * e * Θ ^ 5 by positivity)
    have hp : 0 ≤ e * Θ ^ 5 := by positivity
    linarith [hdiff t ht]
  refine ⟨hbound, ?_⟩
  have hNabs : |N t - 1| ≤ 200 * e * Θ ^ 5 := by
    unfold norm3 at hbound
    linarith [abs_nonneg (P t - β * t ^ 2), abs_nonneg (Q t + 2 * β * t)]
  have hn := (abs_le.mp hNabs).1
  linarith

/-- The skew matrix of the moving orthonormal frame in the source. -/
def frameSkew (B : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 then (if j = 1 then B 0 1 else if j = 2 then B 0 2 else 0)
  else if i = 1 then (if j = 0 then -B 0 1 else if j = 2 then B 2 1 else 0)
  else if j = 0 then -B 0 2 else if j = 1 then -B 2 1 else 0

/-- The older gradient plus rank-one parent shear and error. -/
def parentEntry (B E : Fin 3 → Fin 3 → ℝ) (h : ℝ) (i j : Fin 3) : ℝ :=
  B i j + E i j + (if i = 1 ∧ j = 0 then h else 0)

/-- Coordinate scaling for the normalized ray. -/
def rayScale (ε : ℝ) (i : Fin 3) : ℝ := if i = 1 then ε else 1

/-- Coefficients after the moving-frame transformation and the scaling
`m/s₀=(P,εQ,N)`, `dt/dτ=ε/a`. -/
noncomputable def scaledRayEntry (a ε : ℝ) (M S : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  -(ε / a) * (rayScale ε j / rayScale ε i) * (M j i - S j i)

/-- The scaled moving-frame ray entries in normalized coefficients. -/
def normalizedRayEntry (ε H κ : ℝ) (B E : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 then
    (if j = 0 then -B 0 0 - ε * E 0 0
      else if j = 1 then -H - ε * B 1 0 - ε * B 0 1 - ε ^ 2 * E 1 0
      else -B 2 0 - B 0 2 - ε * E 2 0)
  else if i = 1 then
    (if j = 0 then -E 0 1 else if j = 1 then -B 1 1 - ε * E 1 1 else -2 * κ - E 2 1)
  else if j = 0 then -ε * E 0 2
    else if j = 1 then -ε * B 1 2 + ε * B 2 1 - ε ^ 2 * E 1 2
    else -B 2 2 - ε * E 2 2

/-- Exact entries of the scaled moving-frame ray matrix. -/
theorem scaled_ray_entry_identity
    {a ε h : ℝ} {B E : Fin 3 → Fin 3 → ℝ} (ha : a ≠ 0) (hε : ε ≠ 0) :
    ∀ i j, scaledRayEntry a ε (parentEntry B E h) (frameSkew B) i j =
      normalizedRayEntry ε (ε ^ 2 * h / a) (B 2 1 / a)
        (fun i j => ε * B i j / a) (fun i j => E i j / a) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>
    norm_num [scaledRayEntry, parentEntry, frameSkew, rayScale, normalizedRayEntry,
      Fin.ext_iff] <;>
    field_simp <;> ring

/-- Each scaled matrix entry is close to the triangular ideal matrix when
the normalized older-gradient, error, shear, and coupling coefficients are
small. -/
theorem normalized_ray_entry_error
    {ε H κ β e : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (hε : 0 ≤ ε) (hεupper : ε ≤ 1) (he : 0 ≤ e)
    (hB : ∀ i j, |B i j| ≤ e) (hE : ∀ i j, |E i j| ≤ e)
    (hH : |H - 1| ≤ e) (hκ : |κ - β| ≤ e) :
    ∀ i j, |normalizedRayEntry ε H κ B E i j - idealRayEntry β i j| ≤ 4 * e := by
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hεBn : ∀ i j, |ε * B i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    have hm := mul_le_mul hεupper (hB i j) (abs_nonneg _) zero_le_one
    simpa using hm
  have hεEn : ∀ i j, |ε * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    have hm := mul_le_mul hεupper (hE i j) (abs_nonneg _) zero_le_one
    simpa using hm
  have hε2En : ∀ i j, |ε ^ 2 * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    have hm := mul_le_mul hε2 (hE i j) (abs_nonneg _) zero_le_one
    simpa using hm
  have b00 := abs_le.mp (hB 0 0)
  have b02 := abs_le.mp (hB 0 2)
  have b11 := abs_le.mp (hB 1 1)
  have b20 := abs_le.mp (hB 2 0)
  have b22 := abs_le.mp (hB 2 2)
  have bε10 := abs_le.mp (hεBn 1 0)
  have bε01 := abs_le.mp (hεBn 0 1)
  have bε12 := abs_le.mp (hεBn 1 2)
  have bε21 := abs_le.mp (hεBn 2 1)
  have e01 := abs_le.mp (hE 0 1)
  have e21 := abs_le.mp (hE 2 1)
  have eε00 := abs_le.mp (hεEn 0 0)
  have eε11 := abs_le.mp (hεEn 1 1)
  have eε20 := abs_le.mp (hεEn 2 0)
  have eε02 := abs_le.mp (hεEn 0 2)
  have eε22 := abs_le.mp (hεEn 2 2)
  have eε210 := abs_le.mp (hε2En 1 0)
  have eε212 := abs_le.mp (hε2En 1 2)
  have hHb := abs_le.mp hH
  have hκb := abs_le.mp hκ
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [normalizedRayEntry, idealRayEntry, Fin.ext_iff, -abs_mul] <;>
    apply abs_le.mpr <;> constructor <;>
    linarith only [he, b00, b02, b11, b20, b22, bε10, bε01, bε12, bε21,
      e01, e21, eε00, eε11, eε20, eε02, eε22, eε210, eε212, hHb, hκb]

/-- The original moving-frame entries imply the coefficient hypothesis of
`ray_closeness_of_coefficient_error`. -/
theorem scaled_ray_entry_error
    {a ε h β e : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (ha : a ≠ 0) (hε : 0 < ε) (hεupper : ε ≤ 1) (he : 0 ≤ e)
    (hB : ∀ i j, |ε * B i j / a| ≤ e) (hE : ∀ i j, |E i j / a| ≤ e)
    (hH : |ε ^ 2 * h / a - 1| ≤ e) (hκ : |B 2 1 / a - β| ≤ e) :
    ∀ i j, |scaledRayEntry a ε (parentEntry B E h) (frameSkew B) i j - idealRayEntry β i j| ≤ 4 * e
        := by
  intro i j
  rw [scaled_ray_entry_identity ha (ne_of_gt hε)]
  exact normalized_ray_entry_error hε.le hεupper he hB hE hH hκ i j

/-- A product difference estimate used to control the projection denominator. -/
theorem abs_product_difference
    {a b c d ea eb A B : ℝ}
    (ha : |a - c| ≤ ea) (hb : |b - d| ≤ eb)
    (hc : |c| ≤ A) (hd : |b| ≤ B) :
    |a * b - c * d| ≤ ea * B + A * eb := by
  have hea : 0 ≤ ea := le_trans (abs_nonneg _) ha
  have hA : 0 ≤ A := le_trans (abs_nonneg _) hc
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by congr 1; ring
    _ ≤ |a - c| * |b| + |c| * |b - d| := by
      simpa only [abs_mul] using abs_add_le ((a - c) * b) (c * (b - d))
    _ ≤ ea * B + A * eb := add_le_add
      (mul_le_mul ha hd (abs_nonneg _) hea)
      (mul_le_mul hc hb (abs_nonneg _) hA)

/-- The third velocity coordinate imposed by ray orthogonality. -/
noncomputable def velocityThird (P Q N U V : ℝ) : ℝ := -(P * U + Q * V) / N

/-- Squared norm of the scaled ray. -/
def rayDenominator (ε P Q N : ℝ) : ℝ := P ^ 2 + ε ^ 2 * Q ^ 2 + N ^ 2

/-- Elimination of the third velocity component and the denominator estimate
are consequences of the proved ray error. -/
theorem ray_geometric_bounds
    {Θ ρ ε P Q N P₀ Q₀ U V : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hρupper : ρ ≤ 1 / 2)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ ρ) (hQ : |Q - Q₀| ≤ ρ) (hN : |N - 1| ≤ ρ) :
    1 / 2 ≤ N ∧ |P| ≤ 2 * Θ ^ 2 ∧ |Q| ≤ 3 * Θ ^ 2 ∧ |N| ≤ 2 ∧
      |velocityThird P Q N U V| ≤ 6 * Θ ^ 2 * (|U| + |V|) ∧
      1 / 4 ≤ rayDenominator ε P Q N ∧
      |rayDenominator ε P Q N - (1 + P₀ ^ 2)| ≤
        6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4 := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hn : 1 / 2 ≤ N := by have := (abs_le.mp hN).1; linarith
  have hnpos : 0 < N := by linarith
  have hp : |P| ≤ 2 * Θ ^ 2 := by
    have hh := abs_add_le (P - P₀) P₀
    have hh' : |P| ≤ ρ + Θ ^ 2 := by
      calc
        |P| = |(P - P₀) + P₀| := by congr 1; ring
        _ ≤ |P - P₀| + |P₀| := hh
        _ ≤ ρ + Θ ^ 2 := add_le_add hP hP₀
    linarith
  have hq : |Q| ≤ 3 * Θ ^ 2 := by
    have hh' : |Q| ≤ ρ + 2 * Θ ^ 2 := by
      calc
        |Q| = |(Q - Q₀) + Q₀| := by congr 1; ring
        _ ≤ |Q - Q₀| + |Q₀| := abs_add_le _ _
        _ ≤ ρ + 2 * Θ ^ 2 := add_le_add hQ hQ₀
    linarith
  have hnabs : |N| ≤ 2 := by rw [abs_of_pos hnpos]; have := (abs_le.mp hN).2; linarith
  have hL : 0 ≤ |U| + |V| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hw : |velocityThird P Q N U V| ≤ 6 * Θ ^ 2 * (|U| + |V|) := by
    unfold velocityThird
    rw [abs_div, abs_neg, abs_of_pos hnpos, div_le_iff₀ hnpos]
    have hb : |P * U + Q * V| ≤ 3 * Θ ^ 2 * (|U| + |V|) := by
      calc
        |P * U + Q * V| ≤ |P| * |U| + |Q| * |V| := by
            simpa only [abs_mul] using abs_add_le (P * U) (Q * V)
        _ ≤ (2 * Θ ^ 2) * |U| + (3 * Θ ^ 2) * |V| :=
          add_le_add (mul_le_mul_of_nonneg_right hp (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hq (abs_nonneg _))
        _ ≤ 3 * Θ ^ 2 * (|U| + |V|) := by
          nlinarith only [mul_nonneg (sq_nonneg Θ) (abs_nonneg U)]
    have hmul := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 6 * Θ ^ 2 * (|U| + |V|))
    linarith only [hb, hmul]
  have hD : 1 / 4 ≤ rayDenominator ε P Q N := by
    unfold rayDenominator
    nlinarith only [hn, sq_nonneg P, mul_nonneg (sq_nonneg ε) (sq_nonneg Q)]
  have hPsum : |P + P₀| ≤ 3 * Θ ^ 2 := by linarith [abs_add_le P P₀]
  have hNsum : |N + 1| ≤ 3 := by have hh := abs_add_le N 1; norm_num at hh; linarith
  have hPsq : |P ^ 2 - P₀ ^ 2| ≤ 3 * ρ * Θ ^ 2 := by
    calc
      |P ^ 2 - P₀ ^ 2| = |P - P₀| * |P + P₀| := by rw [← abs_mul]; congr 1; ring
      _ ≤ ρ * (3 * Θ ^ 2) := mul_le_mul hP hPsum (abs_nonneg _) hρ
      _ = 3 * ρ * Θ ^ 2 := by ring
  have hNsq : |N ^ 2 - 1| ≤ 3 * ρ := by
    calc
      |N ^ 2 - 1| = |N - 1| * |N + 1| := by rw [← abs_mul]; congr 1; ring
      _ ≤ ρ * 3 := mul_le_mul hN hNsum (abs_nonneg _) hρ
      _ = 3 * ρ := by ring
  have hQsq : Q ^ 2 ≤ 9 * Θ ^ 4 := by
    have hsq := sq_le_sq₀ (abs_nonneg Q) (by positivity : 0 ≤ 3 * Θ ^ 2)
    have hh := hsq.mpr hq
    rw [sq_abs] at hh
    linarith only [hh]
  refine ⟨hn, hp, hq, hnabs, hw, hD, ?_⟩
  calc
    |rayDenominator ε P Q N - (1 + P₀ ^ 2)| =
        |(P ^ 2 - P₀ ^ 2) + (N ^ 2 - 1) + ε ^ 2 * Q ^ 2| := by
      unfold rayDenominator; congr 1; ring
    _ ≤ |P ^ 2 - P₀ ^ 2| + |N ^ 2 - 1| + ε ^ 2 * Q ^ 2 := by
      have h₁ := abs_add_le (P ^ 2 - P₀ ^ 2) (N ^ 2 - 1)
      have h₂ := abs_add_le ((P ^ 2 - P₀ ^ 2) + (N ^ 2 - 1)) (ε ^ 2 * Q ^ 2)
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg ε) (sq_nonneg Q))] at h₂
      linarith
    _ ≤ 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4 := by
      have hqq := mul_le_mul_of_nonneg_left hQsq (sq_nonneg ε)
      have hrr := mul_le_mul_of_nonneg_left hΘ2 (by positivity : 0 ≤ 3 * ρ)
      linarith only [hPsq, hNsq, hqq, hrr]

/-- The three rows entering `J_v`, with the middle row multiplied by ε. -/
def normalizedVelocityEntry (ε H α κ : ℝ) (B E : Fin 3 → Fin 3 → ℝ)
    (i j : Fin 3) : ℝ :=
  if i = 0 then
    (if j = 0 then B 0 0 + ε * E 0 0 else if j = 1 then α + E 0 1
      else B 0 2 + ε * E 0 2)
  else if i = 1 then
    (if j = 0 then H + ε * B 1 0 + ε ^ 2 * E 1 0
      else if j = 1 then B 1 1 + ε * E 1 1 else ε * B 1 2 + ε ^ 2 * E 1 2)
  else if j = 0 then B 2 0 + ε * E 2 0
    else if j = 1 then κ + E 2 1 else B 2 2 + ε * E 2 2

/-- The ideal scaled parent action on velocity coordinates. -/
def idealVelocityEntry (β : ℝ) (i j : Fin 3) : ℝ :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1
  else if i = 2 ∧ j = 1 then β else 0

/-- Parent-gradient entries after ray and velocity rescaling. -/
noncomputable def scaledVelocityEntry (a ε : ℝ) (M : Fin 3 → Fin 3 → ℝ)
    (i j : Fin 3) : ℝ :=
  (if i = 1 then ε else 1) * (if j = 1 then 1 else ε) * M i j / a

theorem scaled_velocity_entry_identity
    {a ε h : ℝ} {B E : Fin 3 → Fin 3 → ℝ} (ha : a ≠ 0) :
    ∀ i j, scaledVelocityEntry a ε (parentEntry B E h) i j =
      normalizedVelocityEntry ε (ε ^ 2 * h / a) (B 0 1 / a) (B 2 1 / a)
        (fun i j => ε * B i j / a) (fun i j => E i j / a) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>
    norm_num [scaledVelocityEntry, parentEntry, normalizedVelocityEntry, Fin.ext_iff] <;>
    field_simp
  all_goals ring

theorem normalized_velocity_entry_error
    {ε H α κ β e : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (hε : 0 ≤ ε) (hεupper : ε ≤ 1) (he : 0 ≤ e)
    (hB : ∀ i j, |B i j| ≤ e) (hE : ∀ i j, |E i j| ≤ e)
    (hH : |H - 1| ≤ e) (hα : |α - 1| ≤ e) (hκ : |κ - β| ≤ e) :
    ∀ i j, |normalizedVelocityEntry ε H α κ B E i j - idealVelocityEntry β i j| ≤ 3 * e := by
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hεBn : ∀ i j, |ε * B i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    simpa using mul_le_mul hεupper (hB i j) (abs_nonneg _) zero_le_one
  have hεEn : ∀ i j, |ε * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    simpa using mul_le_mul hεupper (hE i j) (abs_nonneg _) zero_le_one
  have hε2En : ∀ i j, |ε ^ 2 * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    simpa using mul_le_mul hε2 (hE i j) (abs_nonneg _) zero_le_one
  have b00 := abs_le.mp (hB 0 0)
  have b02 := abs_le.mp (hB 0 2)
  have b11 := abs_le.mp (hB 1 1)
  have b20 := abs_le.mp (hB 2 0)
  have b22 := abs_le.mp (hB 2 2)
  have bε10 := abs_le.mp (hεBn 1 0)
  have bε12 := abs_le.mp (hεBn 1 2)
  have e01 := abs_le.mp (hE 0 1)
  have e21 := abs_le.mp (hE 2 1)
  have eε00 := abs_le.mp (hεEn 0 0)
  have eε02 := abs_le.mp (hεEn 0 2)
  have eε11 := abs_le.mp (hεEn 1 1)
  have eε20 := abs_le.mp (hεEn 2 0)
  have eε22 := abs_le.mp (hεEn 2 2)
  have eε210 := abs_le.mp (hε2En 1 0)
  have eε212 := abs_le.mp (hε2En 1 2)
  have hHb := abs_le.mp hH
  have hαb := abs_le.mp hα
  have hκb := abs_le.mp hκ
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [normalizedVelocityEntry, idealVelocityEntry, Fin.ext_iff, -abs_mul] <;>
    apply abs_le.mpr <;> constructor <;>
    linarith only [he, b00, b02, b11, b20, b22, bε10, bε12,
      e01, e21, eε00, eε02, eε11, eε20, eε22, eε210, eε212, hHb, hαb, hκb]

/-- The scalar pressure numerator in the scaled coordinates. -/
def velocityNumerator (A : Fin 3 → Fin 3 → ℝ) (P Q N U V W : ℝ) : ℝ :=
  P * (A 0 0 * U + A 0 1 * V + A 0 2 * W) +
  Q * (A 1 0 * U + A 1 1 * V + A 1 2 * W) +
  N * (A 2 0 * U + A 2 1 * V + A 2 2 * W)

theorem velocity_numerator_error
    {A : Fin 3 → Fin 3 → ℝ} {Θ ρ e β P Q N P₀ Q₀ U V W : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (he : 0 ≤ e) (hβ : |β| ≤ 1)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ e)
    (hp : |P| ≤ 2 * Θ ^ 2) (hq : |Q| ≤ 3 * Θ ^ 2) (hn : |N| ≤ 2)
    (hP : |P - P₀| ≤ ρ) (hQ : |Q - Q₀| ≤ ρ) (hN : |N - 1| ≤ ρ)
    (hw : |W| ≤ 6 * Θ ^ 2 * (|U| + |V|)) :
    |velocityNumerator A P Q N U V W - ((P₀ + β) * V + Q₀ * U)| ≤
      (49 * e * Θ ^ 4 + 2 * ρ) * (|U| + |V|) := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hL : 0 ≤ |U| + |V| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hnorm : norm3 U V W ≤ 7 * Θ ^ 2 * (|U| + |V|) := by
    unfold norm3
    have hm := mul_le_mul_of_nonneg_right hΘ2 hL
    linarith only [hw, hm]
  have hrow : ∀ i, |(A i 0 - idealVelocityEntry β i 0) * U +
      (A i 1 - idealVelocityEntry β i 1) * V +
      (A i 2 - idealVelocityEntry β i 2) * W| ≤
      7 * e * Θ ^ 2 * (|U| + |V|) := by
    intro i
    have hh := three_term_bound (p := U) (q := V) (n := W) (hA i 0) (hA i 1) (hA i 2)
    have hm := mul_le_mul_of_nonneg_left hnorm he
    linarith only [hh, hm]
  have hrow0 := hrow 0
  have hrow1 := hrow 1
  have hrow2 := hrow 2
  norm_num [idealVelocityEntry, Fin.ext_iff] at hrow0 hrow1 hrow2
  have hJnear : |velocityNumerator A P Q N U V W - (P * V + Q * U + N * β * V)| ≤
      49 * e * Θ ^ 4 * (|U| + |V|) := by
    let r0 := A 0 0 * U + (A 0 1 - 1) * V + A 0 2 * W
    let r1 := (A 1 0 - 1) * U + A 1 1 * V + A 1 2 * W
    let r2 := A 2 0 * U + (A 2 1 - β) * V + A 2 2 * W
    have htri : |P * r0 + Q * r1 + N * r2| ≤
        (|P| + |Q| + |N|) * (7 * e * Θ ^ 2 * (|U| + |V|)) := by
      have h0 := mul_le_mul_of_nonneg_left hrow0 (abs_nonneg P)
      have h1 := mul_le_mul_of_nonneg_left hrow1 (abs_nonneg Q)
      have h2 := mul_le_mul_of_nonneg_left hrow2 (abs_nonneg N)
      have ht0 := abs_add_le (P * r0) (Q * r1)
      have ht1 := abs_add_le (P * r0 + Q * r1) (N * r2)
      simp only [abs_mul] at ht0 ht1
      dsimp [r0, r1, r2] at *
      linarith only [h0, h1, h2, ht0, ht1]
    have hs : |P| + |Q| + |N| ≤ 7 * Θ ^ 2 := by linarith
    have hm := mul_le_mul_of_nonneg_right hs
      (by positivity : 0 ≤ 7 * e * Θ ^ 2 * (|U| + |V|))
    have hid : velocityNumerator A P Q N U V W - (P * V + Q * U + N * β * V) =
        P * r0 + Q * r1 + N * r2 := by unfold velocityNumerator r0 r1 r2; ring
    rw [hid]
    linarith only [htri, hm]
  have hRay : |P * V + Q * U + N * β * V - ((P₀ + β) * V + Q₀ * U)| ≤
      2 * ρ * (|U| + |V|) := by
    have hNb : |(N - 1) * β| ≤ ρ := by
      rw [abs_mul]
      exact (mul_le_mul hN hβ (abs_nonneg _) hρ).trans_eq (mul_one ρ)
    have hv : |P - P₀ + (N - 1) * β| ≤ 2 * ρ := by linarith [abs_add_le (P - P₀) ((N - 1) * β)]
    have hu : |Q - Q₀| ≤ 2 * ρ := by linarith
    have hh := three_term_bound (p := V) (q := U) (n := (0 : ℝ)) hv hu
      (show |(0 : ℝ)| ≤ 2 * ρ by simpa using (show 0 ≤ 2 * ρ by positivity))
    have hid : P * V + Q * U + N * β * V - ((P₀ + β) * V + Q₀ * U) =
        (P - P₀ + (N - 1) * β) * V + (Q - Q₀) * U + 0 * 0 := by ring
    rw [hid]
    simpa only [norm3, abs_zero, add_zero, add_comm] using hh
  have ht := abs_add_le
    (velocityNumerator A P Q N U V W - (P * V + Q * U + N * β * V))
    (P * V + Q * U + N * β * V - ((P₀ + β) * V + Q₀ * U))
  have hid : velocityNumerator A P Q N U V W - (P * V + Q * U + N * β * V) +
      (P * V + Q * U + N * β * V - ((P₀ + β) * V + Q₀ * U)) =
      velocityNumerator A P Q N U V W - ((P₀ + β) * V + Q₀ * U) := by ring
  rw [hid] at ht
  linarith only [ht, hJnear, hRay]

/-- The first two velocity rows before pressure projection. -/
def normalizedUnprojectedEntry (ε H α : ℝ) (B E : Fin 3 → Fin 3 → ℝ)
    (i j : Fin 3) : ℝ :=
  if i = 0 then
    (if j = 0 then B 0 0 + ε * E 0 0 else if j = 1 then 2 * α + E 0 1
      else 2 * B 0 2 + ε * E 0 2)
  else if j = 0 then H + ε * B 1 0 - ε ^ 2 * α + ε ^ 2 * E 1 0
    else if j = 1 then B 1 1 + ε * E 1 1
    else ε * B 1 2 + ε * B 2 1 + ε ^ 2 * E 1 2

/-- Ideal entries of the unprojected two-component velocity equation. -/
def idealUnprojectedEntry (i j : Fin 3) : ℝ :=
  if i = 0 then (if j = 1 then 2 else 0) else if j = 0 then 1 else 0

/-- Exact first and second rows of the moving-frame velocity operator. -/
theorem scaled_unprojected_entry_identity
    {a ε h : ℝ} {B E : Fin 3 → Fin 3 → ℝ} (ha : a ≠ 0) :
    ∀ j, (scaledVelocityEntry a ε
        (fun i j => parentEntry B E h i j + frameSkew B i j) 0 j =
      normalizedUnprojectedEntry ε (ε ^ 2 * h / a) (B 0 1 / a)
        (fun i j => ε * B i j / a) (fun i j => E i j / a) 0 j) ∧
      (scaledVelocityEntry a ε
        (fun i j => parentEntry B E h i j + frameSkew B i j) 1 j =
      normalizedUnprojectedEntry ε (ε ^ 2 * h / a) (B 0 1 / a)
        (fun i j => ε * B i j / a) (fun i j => E i j / a) 1 j) := by
  intro j
  fin_cases j <;> constructor <;>
    simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>
    norm_num [scaledVelocityEntry, parentEntry, frameSkew,
      normalizedUnprojectedEntry, Fin.ext_iff] <;> field_simp <;> ring

theorem normalized_unprojected_entry_error
    {ε H α e : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (hε : 0 ≤ ε) (hεe : ε ≤ e) (he : 0 ≤ e) (heupper : e ≤ 1)
    (hB : ∀ i j, |B i j| ≤ e) (hE : ∀ i j, |E i j| ≤ e)
    (hH : |H - 1| ≤ e) (hα : |α - 1| ≤ e) :
    ∀ i j, |normalizedUnprojectedEntry ε H α B E i j - idealUnprojectedEntry i j| ≤ 5 * e := by
  have hεupper : ε ≤ 1 := hεe.trans heupper
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hε2e : ε ^ 2 ≤ e := by nlinarith
  have hεBn : ∀ i j, |ε * B i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    simpa using mul_le_mul hεupper (hB i j) (abs_nonneg _) zero_le_one
  have hεEn : ∀ i j, |ε * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    simpa using mul_le_mul hεupper (hE i j) (abs_nonneg _) zero_le_one
  have hε2En : ∀ i j, |ε ^ 2 * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    simpa using mul_le_mul hε2 (hE i j) (abs_nonneg _) zero_le_one
  have hαabs : |α| ≤ 2 := by
    have hh := abs_add_le (α - 1) 1
    norm_num at hh
    linarith
  have hαε : |ε ^ 2 * α| ≤ 2 * e := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    have hh := mul_le_mul hε2e hαabs (abs_nonneg α) he
    linarith only [hh]
  have b00 := abs_le.mp (hB 0 0)
  have b02 := abs_le.mp (hB 0 2)
  have b11 := abs_le.mp (hB 1 1)
  have bε10 := abs_le.mp (hεBn 1 0)
  have bε12 := abs_le.mp (hεBn 1 2)
  have bε21 := abs_le.mp (hεBn 2 1)
  have e01 := abs_le.mp (hE 0 1)
  have eε00 := abs_le.mp (hεEn 0 0)
  have eε02 := abs_le.mp (hεEn 0 2)
  have eε11 := abs_le.mp (hεEn 1 1)
  have eε210 := abs_le.mp (hε2En 1 0)
  have eε212 := abs_le.mp (hε2En 1 2)
  have hHb := abs_le.mp hH
  have hαb := abs_le.mp hα
  have hαεb := abs_le.mp hαε
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [normalizedUnprojectedEntry, idealUnprojectedEntry, Fin.ext_iff, -abs_mul] <;>
    apply abs_le.mpr <;> constructor <;>
    linarith only [he, b00, b02, b11, bε10, bε12, bε21,
      e01, eε00, eε02, eε11, eε210, eε212, hHb, hαb, hαεb]

/-- A quotient difference bound requiring only the quantitative lower
bounds actually available for the ray denominator. -/
theorem quotient_difference_bound
    {P P₀ D D₀ ρ d A : ℝ}
    (hD : 1 / 4 ≤ D) (hD₀ : 1 ≤ D₀)
    (hP : |P - P₀| ≤ ρ) (hP₀ : |P₀| ≤ A) (hDD : |D - D₀| ≤ d) :
    |P / D - P₀ / D₀| ≤ 4 * ρ + 4 * A * d := by
  have hDp : 0 < D := by linarith
  have hD₀p : 0 < D₀ := by linarith
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans hP
  have hd : 0 ≤ d := (abs_nonneg _).trans hDD
  have hA : 0 ≤ A := (abs_nonneg _).trans hP₀
  have hprod : 1 / 4 ≤ D * D₀ := by nlinarith only [hD, hD₀, hDp]
  have hn := abs_product_difference hP
    (show |D₀ - D| ≤ d by simpa only [abs_sub_comm] using hDD)
    hP₀ (le_of_eq (abs_of_pos hD₀p))
  have hid : P / D - P₀ / D₀ = (P * D₀ - P₀ * D) / (D * D₀) := by field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos hDp hD₀p), div_le_iff₀ (mul_pos hDp hD₀p)]
  have h₁ := mul_le_mul_of_nonneg_left hD (mul_nonneg hρ hD₀p.le)
  have h₂ := mul_le_mul_of_nonneg_left hprod (mul_nonneg hA hd)
  linarith only [hn, h₁, h₂]

/-- Quantitative stability of the two pressure projection components. -/
theorem velocity_projection_error
    {Θ ρ d j ε P Q D P₀ D₀ J J₀ U V : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hd : 0 ≤ d) (_hj : 0 ≤ j) (hjupper : j ≤ 1)
    (hD : 1 / 4 ≤ D) (hD₀ : 1 ≤ D₀)
    (hP : |P - P₀| ≤ ρ) (hP₀ : |P₀| ≤ Θ ^ 2)
    (hp : |P| ≤ 2 * Θ ^ 2) (hq : |Q| ≤ 3 * Θ ^ 2)
    (hDD : |D - D₀| ≤ d) (hJ : |J - J₀| ≤ j * (|U| + |V|))
    (hJ₀ : |J₀| ≤ 2 * Θ ^ 2 * (|U| + |V|)) :
    |2 * P * J / D - 2 * P₀ * J₀ / D₀| + |2 * ε ^ 2 * Q * J / D| ≤
      (16 * Θ ^ 2 * j + 16 * ρ * Θ ^ 2 + 16 * Θ ^ 4 * d +
        72 * ε ^ 2 * Θ ^ 4) * (|U| + |V|) := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hL : 0 ≤ |U| + |V| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hDp : 0 < D := by linarith
  have hD₀p : 0 < D₀ := by linarith
  have hratio := quotient_difference_bound hD hD₀ hP hP₀ hDD
  have hratio0 : |P₀ / D₀| ≤ Θ ^ 2 := by
    rw [abs_div, abs_of_pos hD₀p, div_le_iff₀ hD₀p]
    have hm := mul_le_mul_of_nonneg_left hD₀ (sq_nonneg Θ)
    linarith only [hP₀, hm]
  have hJabs : |J| ≤ 3 * Θ ^ 2 * (|U| + |V|) := by
    have ht := abs_add_le (J - J₀) J₀
    have hid : J - J₀ + J₀ = J := by ring
    rw [hid] at ht
    have hm₁ := mul_le_mul_of_nonneg_right hjupper hL
    have hm₂ := mul_le_mul_of_nonneg_right hΘ2 hL
    linarith only [ht, hJ, hJ₀, hm₁, hm₂]
  have hratioP : |P / D| ≤ 8 * Θ ^ 2 := by
    rw [abs_div, abs_of_pos hDp, div_le_iff₀ hDp]
    have hm := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 8 * Θ ^ 2)
    linarith only [hp, hm]
  have hU : |2 * P * J / D - 2 * P₀ * J₀ / D₀| ≤
      (16 * Θ ^ 2 * j + 16 * ρ * Θ ^ 2 + 16 * Θ ^ 4 * d) * (|U| + |V|) := by
    have hh := abs_product_difference hratio hJ hratio0 hJabs
    have hbetter : |(P / D) * J - (P₀ / D₀) * J₀| ≤
        (8 * Θ ^ 2) * (j * (|U| + |V|)) +
          (4 * ρ + 4 * Θ ^ 2 * d) * (2 * Θ ^ 2 * (|U| + |V|)) := by
      have ht := abs_add_le ((P / D) * (J - J₀)) (((P / D) - (P₀ / D₀)) * J₀)
      have h₁ := mul_le_mul hratioP hJ (abs_nonneg _) (by positivity : 0 ≤ 8 * Θ ^ 2)
      have h₂ := mul_le_mul hratio hJ₀ (abs_nonneg _)
        (by positivity : 0 ≤ 4 * ρ + 4 * Θ ^ 2 * d)
      have hid : (P / D) * (J - J₀) + ((P / D) - (P₀ / D₀)) * J₀ =
          (P / D) * J - (P₀ / D₀) * J₀ := by ring
      rw [hid] at ht
      simp only [abs_mul] at ht
      linarith only [ht, h₁, h₂]
    have hid : 2 * P * J / D - 2 * P₀ * J₀ / D₀ =
        2 * ((P / D) * J - (P₀ / D₀) * J₀) := by ring
    rw [hid, abs_mul]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [hbetter]
  have hV : |2 * ε ^ 2 * Q * J / D| ≤ 72 * ε ^ 2 * Θ ^ 4 * (|U| + |V|) := by
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (sq_nonneg ε), abs_of_pos hDp, div_le_iff₀ hDp]
    have hh := mul_le_mul hq hJabs (abs_nonneg J) (by positivity : 0 ≤ 3 * Θ ^ 2)
    have hm₁ := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * ε ^ 2)
    have hm₂ := mul_le_mul_of_nonneg_left hD
      (by positivity : 0 ≤ 72 * ε ^ 2 * Θ ^ 4 * (|U| + |V|))
    linarith only [hm₁, hm₂]
  linarith only [hU, hV]

/-- The first normalized velocity equation with pressure projection. -/
noncomputable def velocityFirstRhs
    (A C : Fin 3 → Fin 3 → ℝ) (ε P Q N U V : ℝ) : ℝ :=
  let W := velocityThird P Q N U V;
  -(C 0 0 * U + C 0 1 * V + C 0 2 * W) +
    2 * P * velocityNumerator A P Q N U V W / rayDenominator ε P Q N

/-- The second normalized velocity equation with pressure projection. -/
noncomputable def velocitySecondRhs
    (A C : Fin 3 → Fin 3 → ℝ) (ε P Q N U V : ℝ) : ℝ :=
  let W := velocityThird P Q N U V;
  -(C 1 0 * U + C 1 1 * V + C 1 2 * W) +
    2 * ε ^ 2 * Q * velocityNumerator A P Q N U V W / rayDenominator ε P Q N

/-- The full pressure projection is a small matrix perturbation, with an
explicit constant and the power of Θ used in the source. -/
theorem velocity_rhs_error
    {A C : Fin 3 → Fin 3 → ℝ} {Θ e ε β P Q N P₀ Q₀ U V : ℝ}
    (hΘ : 1 ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hsmall : 10000 * e * Θ ^ 5 ≤ 1) (hβ : |β| ≤ 1)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ 3 * e)
    (hC : ∀ i j, |C i j - idealUnprojectedEntry i j| ≤ 5 * e)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q - Q₀| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5) :
    |velocityFirstRhs A C ε P Q N U V -
        (-2 * V + 2 * P₀ * ((P₀ + β) * V + Q₀ * U) / (1 + P₀ ^ 2))| +
      |velocitySecondRhs A C ε P Q N U V + U| ≤
        200000 * e * Θ ^ 12 * (|U| + |V|) := by
  have hΘ0 : 0 ≤ Θ := by linarith
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hΘ5 : 1 ≤ Θ ^ 5 := one_le_pow₀ hΘ
  have heupper : e ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hΘ5 he
    linarith only [hsmall, hm]
  have hεupper : ε ≤ 1 := hεe.trans heupper
  have hε2e : ε ^ 2 ≤ e := by nlinarith only [hε, hεupper, hεe]
  let ρ := 800 * e * Θ ^ 5
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρupper : ρ ≤ 1 / 2 := by dsimp [ρ]; linarith only [hsmall]
  obtain ⟨hn, hp, hq, hnabs, hw, hD, hDD⟩ :=
    ray_geometric_bounds (ε := ε) (U := U) (V := V) hΘ hρ hρupper hP₀ hQ₀ hP hQ hN
  let W := velocityThird P Q N U V
  let D := rayDenominator ε P Q N
  let D₀ := 1 + P₀ ^ 2
  let J := velocityNumerator A P Q N U V W
  let J₀ := (P₀ + β) * V + Q₀ * U
  let j := 147 * e * Θ ^ 4 + 2 * ρ
  let d := 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4
  have hj : 0 ≤ j := by dsimp [j]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have h45 : Θ ^ 4 ≤ Θ ^ 5 := pow_le_pow_right₀ hΘ (by decide)
  have hjupper : j ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left h45 (by positivity : 0 ≤ 147 * e)
    dsimp [j, ρ]
    linarith only [hsmall, hm]
  have hJ : |J - J₀| ≤ j * (|U| + |V|) := by
    have hh := velocity_numerator_error hΘ hρ (by
        positivity : 0 ≤ 3 * e) hβ hA hp hq hnabs hP hQ hN hw
    dsimp [J, J₀, W, j]
    linarith only [hh]
  have hJ₀ : |J₀| ≤ 2 * Θ ^ 2 * (|U| + |V|) := by
    have hcoef : |P₀ + β| ≤ 2 * Θ ^ 2 := by linarith [abs_add_le P₀ β]
    have hh := three_term_bound (p := V) (q := U) (n := (0 : ℝ)) hcoef hQ₀
      (show |(0 : ℝ)| ≤ 2 * Θ ^ 2 by
          simp only [abs_zero]; positivity)
    dsimp [J₀]
    simpa only [zero_mul, add_zero, norm3, abs_zero, add_comm] using hh
  have hD₀ : 1 ≤ D₀ := by dsimp [D₀]; linarith [sq_nonneg P₀]
  have hproj := velocity_projection_error (ε := ε) hΘ hρ hd hj hjupper hD hD₀ hP hP₀ hp hq hDD hJ
      hJ₀
  have hL : 0 ≤ |U| + |V| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hnorm : norm3 U V W ≤ 7 * Θ ^ 2 * (|U| + |V|) := by
    unfold norm3
    have hm := mul_le_mul_of_nonneg_right hΘ2 hL
    linarith only [hw, hm]
  have hrow : ∀ i, |(C i 0 - idealUnprojectedEntry i 0) * U +
      (C i 1 - idealUnprojectedEntry i 1) * V +
      (C i 2 - idealUnprojectedEntry i 2) * W| ≤
      35 * e * Θ ^ 2 * (|U| + |V|) := by
    intro i
    have hh := three_term_bound (p := U) (q := V) (n := W) (hC i 0) (hC i 1) (hC i 2)
    have hm := mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ 5 * e)
    linarith only [hh, hm]
  have hu := hrow 0
  have hv := hrow 1
  norm_num [idealUnprojectedEntry, Fin.ext_iff] at hu hv
  have htU := abs_add_le (-(C 0 0 * U + (C 0 1 - 2) * V + C 0 2 * W))
    (2 * P * J / D - 2 * P₀ * J₀ / D₀)
  have htV := abs_add_le (-((C 1 0 - 1) * U + C 1 1 * V + C 1 2 * W))
    (2 * ε ^ 2 * Q * J / D)
  rw [abs_neg] at htU htV
  have hUeq : velocityFirstRhs A C ε P Q N U V -
      (-2 * V + 2 * P₀ * ((P₀ + β) * V + Q₀ * U) / (1 + P₀ ^ 2)) =
      -(C 0 0 * U + (C 0 1 - 2) * V + C 0 2 * W) +
        (2 * P * J / D - 2 * P₀ * J₀ / D₀) := by
    dsimp [velocityFirstRhs, W, J, J₀, D, D₀]; ring
  have hVeq : velocitySecondRhs A C ε P Q N U V + U =
      -((C 1 0 - 1) * U + C 1 1 * V + C 1 2 * W) + 2 * ε ^ 2 * Q * J / D := by
    dsimp [velocitySecondRhs, W, J, D]; ring
  rw [hUeq, hVeq]
  have hcoefficient : 70 * e * Θ ^ 2 +
      (16 * Θ ^ 2 * j + 16 * ρ * Θ ^ 2 + 16 * Θ ^ 4 * d + 72 * ε ^ 2 * Θ ^ 4) ≤
      200000 * e * Θ ^ 12 := by
    have h2 : Θ ^ 2 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h4 : Θ ^ 4 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h6 : Θ ^ 6 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h7 : Θ ^ 7 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h8 : Θ ^ 8 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h11 : Θ ^ 11 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have he2 := mul_le_mul_of_nonneg_left h2 he
    have he4 := mul_le_mul_of_nonneg_left h4 he
    have he6 := mul_le_mul_of_nonneg_left h6 he
    have he7 := mul_le_mul_of_nonneg_left h7 he
    have he8 := mul_le_mul_of_nonneg_left h8 he
    have he11 := mul_le_mul_of_nonneg_left h11 he
    have hε4 := mul_le_mul_of_nonneg_right hε2e (by positivity : 0 ≤ Θ ^ 4)
    have hε8 := mul_le_mul_of_nonneg_right hε2e (by positivity : 0 ≤ Θ ^ 8)
    dsimp [j, d, ρ]
    linarith only [he2, he4, he6, he7, he8, he11, hε4, hε8,
      mul_nonneg he (pow_nonneg hΘ0 12)]
  have hm := mul_le_mul_of_nonneg_right hcoefficient hL
  linarith only [htU, htV, hu, hv, hproj, hm]

end EulerPacketRay
