/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.Bohr
import LeanPool.QuadraticCarleson.QuadraticCarleson.WavePacket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The quadratic kernel away from a wave packet

This file formalizes the first (nonoscillatory) estimate in the first lemma of
Section 3 of the paper. An interval is represented by its centre `s` and its
positive length `t`. The hypothesis that `x` is outside that interval makes
the singular kernel an ordinary integrable function on the support of the
packet.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson

/-- The nonsingular integral which represents `C₂^λ φ_Q(x)` when `x ∉ Q`.
The integration variable is the packet variable (the change of variables
`u = x - y` has already been made). -/
noncomputable def offSupportKernelAction (modulation s t x : ℝ) : ℂ :=
  ∫ u : ℝ, (wavePacket s t u : ℂ) *
    phase (modulation * (x - u) ^ 2) / ((x - u : ℝ) : ℂ)

/-- The same action in the kernel variable used in the paper. -/
theorem offSupportKernelAction_eq_integral_kernel_variable
    (modulation s t x : ℝ) :
    offSupportKernelAction modulation s t x =
      ∫ y : ℝ, (wavePacket s t (x - y) : ℂ) *
        phase (modulation * y ^ 2) / (y : ℂ) := by
  let F : ℝ → ℂ := fun y ↦ (wavePacket s t (x - y) : ℂ) *
    phase (modulation * y ^ 2) / (y : ℂ)
  rw [offSupportKernelAction,
    ← integral_sub_left_eq_self F volume x]
  congr 1
  funext u
  dsimp only [F]
  ring_nf

/-- The normalization `e(a)=exp(2πia)` is `2π`-Lipschitz. -/
theorem norm_phase_sub_phase_le (a b : ℝ) :
    ‖phase a - phase b‖ ≤ 2 * Real.pi * |a - b| := by
  have hid : phase a = phase b * phase (a - b) := by
    simp only [phase, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hid, show phase b * phase (a - b) - phase b =
      phase b * (phase (a - b) - 1) by ring, norm_mul, norm_phase, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le
      (x := 2 * Real.pi * (a - b))
  rw [phase, show (((2 * Real.pi * (a - b) : ℝ) : ℂ) * Complex.I) =
      Complex.I * ((2 * Real.pi * (a - b) : ℝ) : ℂ) by ring]
  calc
    ‖Complex.exp (Complex.I * ((2 * Real.pi * (a - b) : ℝ) : ℂ)) - 1‖ ≤
        ‖2 * Real.pi * (a - b)‖ := h
    _ = 2 * Real.pi * |a - b| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity),
        abs_of_nonneg Real.pi_pos.le]

/-- Points in the support of the packet are at most `t/4` from its centre. -/
theorem abs_sub_center_le_of_wavePacket_ne_zero {s t u : ℝ} (ht : 0 < t)
    (hu : wavePacket s t u ≠ 0) : |u - s| ≤ t / 4 := by
  have hsupp := wavePacket_support ht hu
  rw [abs_le]
  constructor <;> linarith [hsupp.1, hsupp.2]

/-- If `x` lies outside the interval of centre `s` and length `t`, its
distance from the centre is at least half the length. -/
theorem half_length_le_abs_sub_center {s t x : ℝ} (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2)) : t / 2 ≤ |x - s| := by
  rw [mem_Icc, not_and_or] at hx
  rcases hx with hx | hx
  · rw [abs_of_nonpos]
    · linarith
    · linarith
  · rw [abs_of_nonneg]
    · linarith
    · linarith

/-- On the packet support, the kernel variable `x-u` stays at least half as
far from zero as the centre variable `x-s`. -/
theorem half_abs_sub_center_le_abs_sub {s t x u : ℝ} (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2))
    (hu : wavePacket s t u ≠ 0) : |x - s| / 2 ≤ |x - u| := by
  have hus := abs_sub_center_le_of_wavePacket_ne_zero ht hu
  have hts := half_length_le_abs_sub_center ht hx
  have htri : |x - s| ≤ |x - u| + |u - s| := by
    calc
      |x - s| = |(x - u) + (u - s)| := by ring_nf
      _ ≤ |x - u| + |u - s| := abs_add_le _ _
  linarith

/-- The zero-fold case of the oscillatory estimate in the paper. It is also
the uniform off-support size bound for the kernel action. -/
theorem offSupportKernelAction_norm_le {modulation s t x : ℝ} (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2)) :
    ‖offSupportKernelAction modulation s t x‖ ≤ 2 / |x - s| := by
  have hdist : t / 2 ≤ |x - s| := half_length_le_abs_sub_center ht hx
  have hdistpos : 0 < |x - s| := lt_of_lt_of_le (half_pos ht) hdist
  let g : ℝ → ℝ := fun u ↦ wavePacket s t u * (2 / |x - s|)
  have hgIntegrable : Integrable g :=
    (wavePacket_integrable s ht).mul_const (2 / |x - s|)
  have hbound : ∀ u : ℝ,
      ‖(wavePacket s t u : ℂ) * phase (modulation * (x - u) ^ 2) /
          ((x - u : ℝ) : ℂ)‖ ≤ g u := by
    intro u
    by_cases hu : wavePacket s t u = 0
    · simp [g, hu]
    · have hsep := half_abs_sub_center_le_abs_sub ht hx hu
      have hseppos : 0 < |x - u| := lt_of_lt_of_le (half_pos hdistpos) hsep
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, norm_phase,
        abs_of_nonneg (wavePacket_nonneg s u ht), mul_one]
      dsimp only [g]
      apply mul_le_mul_of_nonneg_left _ (wavePacket_nonneg s u ht)
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hseppos).2
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hdistpos).2
      nlinarith
  rw [offSupportKernelAction]
  calc
    ‖∫ u : ℝ, (wavePacket s t u : ℂ) * phase (modulation * (x - u) ^ 2) /
        ((x - u : ℝ) : ℂ)‖ ≤ ∫ u : ℝ, g u :=
      MeasureTheory.norm_integral_le_of_norm_le hgIntegrable (ae_of_all _ hbound)
    _ = (∫ u : ℝ, wavePacket s t u) * (2 / |x - s|) :=
      integral_mul_const _ _
    _ = 2 / |x - s| := by rw [wavePacket_integral s ht, one_mul]

private theorem kernel_difference_bound {modulation s t x u : ℝ} (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2))
    (hu : wavePacket s t u ≠ 0) :
    ‖phase (modulation * (x - u) ^ 2) / ((x - u : ℝ) : ℂ) -
        phase (modulation * (x - s) ^ 2) / ((x - s : ℝ) : ℂ)‖ ≤
      6 * Real.pi * |modulation| * |u - s| +
        2 * |u - s| / |x - s| ^ 2 := by
  let a := x - u
  let b := x - s
  have htb : t / 2 ≤ |b| := half_length_le_abs_sub_center ht hx
  have hbpos : 0 < |b| := lt_of_lt_of_le (half_pos ht) htb
  have hba : |b| / 2 ≤ |a| := half_abs_sub_center_le_abs_sub ht hx hu
  have hapos : 0 < |a| := lt_of_lt_of_le (half_pos hbpos) hba
  have hba' : |b| ≤ 2 * |a| := by linarith
  have hab : |a - b| = |u - s| := by
    rw [show a - b = -(u - s) by dsimp [a, b]; ring, abs_neg]
  have habsum : |a + b| ≤ 3 * |a| := by
    calc
      |a + b| ≤ |a| + |b| := abs_add_le _ _
      _ ≤ |a| + 2 * |a| := add_le_add (le_refl _) hba'
      _ = 3 * |a| := by ring
  have hphase :
      ‖phase (modulation * a ^ 2) - phase (modulation * b ^ 2)‖ ≤
        6 * Real.pi * |modulation| * |u - s| * |a| := by
    calc
      ‖phase (modulation * a ^ 2) - phase (modulation * b ^ 2)‖ ≤
          2 * Real.pi * |modulation * a ^ 2 - modulation * b ^ 2| :=
        norm_phase_sub_phase_le _ _
      _ = 2 * Real.pi * |modulation| * |a - b| * |a + b| := by
        rw [show modulation * a ^ 2 - modulation * b ^ 2 =
            modulation * (a - b) * (a + b) by ring, abs_mul, abs_mul]
        ring
      _ = 2 * Real.pi * |modulation| * |u - s| * |a + b| := by rw [hab]
      _ ≤ 2 * Real.pi * |modulation| * |u - s| * (3 * |a|) := by
        exact mul_le_mul_of_nonneg_left habsum (by positivity)
      _ = 6 * Real.pi * |modulation| * |u - s| * |a| := by ring
  have hfirst :
      ‖(phase (modulation * a ^ 2) - phase (modulation * b ^ 2)) /
          (a : ℂ)‖ ≤ 6 * Real.pi * |modulation| * |u - s| := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    exact (div_le_iff₀ hapos).2 (by simpa [mul_assoc] using hphase)
  have hrecip :
      ‖phase (modulation * b ^ 2) * ((1 / (a : ℂ)) - (1 / (b : ℂ)))‖ ≤
        2 * |u - s| / |b| ^ 2 := by
    have ha0r : a ≠ 0 := abs_pos.mp hapos
    have hb0r : b ≠ 0 := abs_pos.mp hbpos
    have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0r
    have hb0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb0r
    rw [norm_mul, norm_phase, one_mul, one_div, one_div, inv_sub_inv ha0 hb0,
      norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have hcastnorm : ‖(b : ℂ) - (a : ℂ)‖ = |b - a| := by
      rw [show (b : ℂ) - (a : ℂ) = ((b - a : ℝ) : ℂ) by exact_mod_cast rfl,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hcastnorm, abs_sub_comm, hab]
    by_cases hus0 : |u - s| = 0
    · simp [hus0]
    · apply (div_le_div_iff₀ (mul_pos hapos hbpos) (sq_pos_of_pos hbpos)).2
      have huspos : 0 < |u - s| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hus0)
      calc
        |u - s| * |b| ^ 2 = (|u - s| * |b|) * |b| := by ring
        _ ≤ (|u - s| * |b|) * (2 * |a|) :=
          mul_le_mul_of_nonneg_left hba' (mul_nonneg huspos.le (abs_nonneg _))
        _ = 2 * |u - s| * (|a| * |b|) := by ring
  have hdecomp :
      phase (modulation * a ^ 2) / (a : ℂ) -
          phase (modulation * b ^ 2) / (b : ℂ) =
        (phase (modulation * a ^ 2) - phase (modulation * b ^ 2)) / (a : ℂ) +
          phase (modulation * b ^ 2) * ((1 / (a : ℂ)) - (1 / (b : ℂ))) := by
    have ha0r : a ≠ 0 := abs_pos.mp hapos
    have hb0r : b ≠ 0 := abs_pos.mp hbpos
    have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0r
    have hb0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb0r
    field_simp
    ring
  change ‖phase (modulation * a ^ 2) / (a : ℂ) -
      phase (modulation * b ^ 2) / (b : ℂ)‖ ≤ _
  rw [hdecomp]
  exact (norm_add_le _ _).trans (add_le_add hfirst hrecip)

/-- The first estimate in the off-support wave-packet lemma, with an explicit
absolute constant. This is the paper's
`e(λ(x-c_Q)²)/(x-c_Q) + O(max{|λ|ℓ_Q, ℓ_Q/|x-c_Q|²})`.

The value `7` is inessential; the paper suppresses it in `O(·)` notation. -/
theorem offSupportKernelAction_sub_main_le {modulation s t x : ℝ} (ht : 0 < t)
    (hx : x ∉ Icc (s - t / 2) (s + t / 2)) :
    ‖offSupportKernelAction modulation s t x -
        phase (modulation * (x - s) ^ 2) / ((x - s : ℝ) : ℂ)‖ ≤
      7 * max (|modulation| * t) (t / |x - s| ^ 2) := by
  let main : ℂ := phase (modulation * (x - s) ^ 2) / ((x - s : ℝ) : ℂ)
  let err : ℝ → ℂ := fun u ↦ (wavePacket s t u : ℂ) *
    (phase (modulation * (x - u) ^ 2) / ((x - u : ℝ) : ℂ) - main)
  let moment : ℝ → ℝ := fun u ↦ wavePacket s t u * |u - s|
  let C : ℝ := 6 * Real.pi * |modulation| + 2 / |x - s| ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmomentContinuous : Continuous moment := by
    exact (continuous_wavePacket s t).mul ((continuous_id.sub continuous_const).abs)
  have hmomentCompact : HasCompactSupport moment := by
    change HasCompactSupport (wavePacket s t * fun u : ℝ ↦ |u - s|)
    exact (wavePacket_hasCompactSupport s ht).mul_right
  have hmomentIntegrable : Integrable moment :=
    hmomentContinuous.integrable_of_hasCompactSupport hmomentCompact
  have hmajorantIntegrable : Integrable (fun u ↦ C * moment u) :=
    hmomentIntegrable.const_mul C
  have herrMeasurable : AEStronglyMeasurable err := by
    apply Measurable.aestronglyMeasurable
    dsimp only [err, main]
    have hwp : Measurable (fun u : ℝ ↦ (wavePacket s t u : ℂ)) :=
      Complex.measurable_ofReal.comp (continuous_wavePacket s t).measurable
    have hphase : Measurable (fun u : ℝ ↦
        phase (modulation * (x - u) ^ 2)) := by
      apply Continuous.measurable
      unfold phase
      fun_prop
    have hdenom : Measurable (fun u : ℝ ↦ ((x - u : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (continuous_const.sub continuous_id).measurable
    exact hwp.mul ((hphase.div hdenom).sub measurable_const)
  have herrBound : ∀ u, ‖err u‖ ≤ C * moment u := by
    intro u
    by_cases hu : wavePacket s t u = 0
    · simp [err, moment, hu]
    · have hkernel := kernel_difference_bound (modulation := modulation) ht hx hu
      dsimp only [err, main, C, moment]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (wavePacket_nonneg s u ht)]
      calc
        wavePacket s t u *
            ‖phase (modulation * (x - u) ^ 2) / ↑(x - u) -
              phase (modulation * (x - s) ^ 2) / ↑(x - s)‖ ≤
            wavePacket s t u *
              (6 * Real.pi * |modulation| * |u - s| +
                2 * |u - s| / |x - s| ^ 2) :=
          mul_le_mul_of_nonneg_left hkernel (wavePacket_nonneg s u ht)
        _ = C * moment u := by dsimp [C, moment]; ring
  have herrIntegrable : Integrable err :=
    hmajorantIntegrable.mono' herrMeasurable (ae_of_all _ herrBound)
  have hpacketComplex : Integrable (fun u : ℝ ↦ (wavePacket s t u : ℂ)) :=
    (@RCLike.ofRealLI ℂ _).toContinuousLinearMap.integrable_comp
      (wavePacket_integrable s ht)
  have hmainIntegrable : Integrable (fun u : ℝ ↦ (wavePacket s t u : ℂ) * main) :=
    hpacketComplex.mul_const main
  have hactionIntegrable : Integrable (fun u : ℝ ↦
      (wavePacket s t u : ℂ) * phase (modulation * (x - u) ^ 2) /
        ((x - u : ℝ) : ℂ)) := by
    have heq : (fun u : ℝ ↦
        (wavePacket s t u : ℂ) * phase (modulation * (x - u) ^ 2) /
          ((x - u : ℝ) : ℂ)) =
        fun u ↦ err u + (wavePacket s t u : ℂ) * main := by
      funext u
      dsimp only [err]
      ring
    rw [heq]
    exact herrIntegrable.add hmainIntegrable
  have herrorIdentity :
      offSupportKernelAction modulation s t x -
          phase (modulation * (x - s) ^ 2) / ((x - s : ℝ) : ℂ) =
        ∫ u : ℝ, err u := by
    change offSupportKernelAction modulation s t x - main = ∫ u : ℝ, err u
    have hmainIntegral :
        (∫ u : ℝ, (wavePacket s t u : ℂ) * main) = main := by
      rw [integral_mul_const, integral_complex_ofReal, wavePacket_integral s ht]
      simp
    rw [offSupportKernelAction, ← hmainIntegral,
      ← integral_sub hactionIntegrable hmainIntegrable]
    congr 1
    funext u
    dsimp only [err]
    ring
  rw [herrorIdentity]
  calc
    ‖∫ u : ℝ, err u‖ ≤ ∫ u : ℝ, C * moment u :=
      MeasureTheory.norm_integral_le_of_norm_le hmajorantIntegrable
        (ae_of_all _ herrBound)
    _ = C * ∫ u : ℝ, moment u := integral_const_mul _ _
    _ ≤ C * (t / 4) := by
      gcongr
      exact wavePacket_firstMoment_le s ht
    _ ≤ 7 * max (|modulation| * t) (t / |x - s| ^ 2) := by
      have hpi : Real.pi ≤ 4 := Real.pi_le_four
      have hA : 0 ≤ |modulation| * t := mul_nonneg (abs_nonneg _) ht.le
      have hB : 0 ≤ t / |x - s| ^ 2 := div_nonneg ht.le (sq_nonneg _)
      have hAmax : |modulation| * t ≤
          max (|modulation| * t) (t / |x - s| ^ 2) := le_max_left _ _
      have hBmax : t / |x - s| ^ 2 ≤
          max (|modulation| * t) (t / |x - s| ^ 2) := le_max_right _ _
      have hmax : 0 ≤ max (|modulation| * t) (t / |x - s| ^ 2) :=
        hA.trans hAmax
      have hpicoeff : (3 / 2 : ℝ) * Real.pi ≤ 6 := by nlinarith
      dsimp [C]
      rw [show (6 * Real.pi * |modulation| + 2 / |x - s| ^ 2) * (t / 4) =
          (3 / 2 : ℝ) * Real.pi * (|modulation| * t) +
            (1 / 2 : ℝ) * (t / |x - s| ^ 2) by ring]
      calc
        (3 / 2 : ℝ) * Real.pi * (|modulation| * t) +
            (1 / 2 : ℝ) * (t / |x - s| ^ 2) ≤
            6 * (|modulation| * t) + (1 / 2 : ℝ) * (t / |x - s| ^ 2) := by
          exact add_le_add (mul_le_mul_of_nonneg_right hpicoeff hA) (le_refl _)
        _ ≤ 6 * max (|modulation| * t) (t / |x - s| ^ 2) +
            (1 / 2 : ℝ) * max (|modulation| * t) (t / |x - s| ^ 2) := by
          gcongr
        _ ≤ 7 * max (|modulation| * t) (t / |x - s| ^ 2) := by
          nlinarith

end QuadraticCarleson
