/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Distributions.Exponential

/-!
# Exponential Stein identity

This file isolates the integration-by-parts step behind the local
exponential transfer identity used in the proof of Theorem 2.1.  The main
theorem is a one-sided identity on the positive half-line.  Its assumptions
expose exactly the two weighted integrability
conditions and the boundary condition at infinity needed for improper
integration by parts.
-/

open MeasureTheory Real Set Filter Topology

namespace Feige

namespace ExponentialStein

/-- A uniformly unit-bounded continuous function, composed with an
affine path and multiplied by the exponential density, is integrable on
the positive half-line. -/
theorem integrableOn_comp_mul_exp
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hbound : ∀ x, ‖φ x‖ ≤ 1)
    (y a : ℝ) :
    IntegrableOn (fun e : ℝ => φ (y + a * e) * exp (-e)) (Ioi 0) := by
  apply (exp_neg_integrableOn_Ioi 0 one_pos).mono'
  · exact ((hφ.comp (continuous_const.add (continuous_const.mul continuous_id))).mul
      (continuous_exp.comp continuous_id.neg)).aestronglyMeasurable
  · filter_upwards with e
    rw [norm_mul, norm_of_nonneg (exp_pos _).le]
    simpa only [one_mul, neg_mul] using
      mul_le_mul_of_nonneg_right (hbound (y + a * e)) (exp_pos _).le

/-- The same exponential damping forces the affine composite to vanish
at infinity. -/
theorem tendsto_comp_mul_exp_atTop
    {φ : ℝ → ℝ} (hbound : ∀ x, ‖φ x‖ ≤ 1) (y a : ℝ) :
    Tendsto (fun e : ℝ => φ (y + a * e) * exp (-e)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (g := fun e : ℝ => exp (-e))
  · intro e
    exact norm_nonneg _
  · intro e
    rw [norm_mul, norm_of_nonneg (exp_pos _).le]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hbound (y + a * e)) (exp_pos _).le
  · simpa only [one_mul, Function.comp_def] using
      (tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)

/-- One-sided exponential integration by parts.

For a differentiable function `φ`, this says

`∫₀∞ φ(y + a e)e⁻ᵉ de - φ(y)
    = a ∫₀∞ φ'(y + a e)e⁻ᵉ de`.

The hypotheses are deliberately stated as the precise weighted
integrability and boundary requirements.  Bounded `φ` and bounded `φ'`
satisfy them, as do many unbounded test functions.
-/
theorem integral_Ioi_comp_exp_sub
    {φ φ' : ℝ → ℝ} {y a : ℝ}
    (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hintφ : IntegrableOn
      (fun e : ℝ => φ (y + a * e) * exp (-e)) (Ioi 0))
    (hintφ' : IntegrableOn
      (fun e : ℝ => a * φ' (y + a * e) * exp (-e)) (Ioi 0))
    (hzero : Tendsto
      (fun e : ℝ => φ (y + a * e) * exp (-e))
      (𝓝[>] (0 : ℝ)) (𝓝 (φ y)))
    (htop : Tendsto
      (fun e : ℝ => φ (y + a * e) * exp (-e)) atTop (𝓝 0)) :
    (∫ e : ℝ in Ioi 0, φ (y + a * e) * exp (-e)) - φ y =
      ∫ e : ℝ in Ioi 0, a * φ' (y + a * e) * exp (-e) := by
  let u : ℝ → ℝ := fun e => φ (y + a * e)
  let u' : ℝ → ℝ := fun e => a * φ' (y + a * e)
  let v : ℝ → ℝ := fun e => exp (-e)
  let v' : ℝ → ℝ := fun e => -exp (-e)
  have hu : ∀ e ∈ Ioi (0 : ℝ), HasDerivAt u (u' e) e := by
    intro e _
    have haff : HasDerivAt (fun x : ℝ => y + a * x) a e := by
      simpa using
        ((hasDerivAt_const_mul a :
          HasDerivAt (fun x : ℝ => a * x) a e).const_add y)
    simpa [u, u', Function.comp_def, mul_comm] using
      (hφ (y + a * e)).comp e haff
  have hv : ∀ e ∈ Ioi (0 : ℝ), HasDerivAt v (v' e) e := by
    intro e _
    simpa [v, v'] using ((hasDerivAt_id e).neg.exp)
  have huv' : IntegrableOn (u * v') (Ioi (0 : ℝ)) := by
    rw [show u * v' = fun e => -(φ (y + a * e) * exp (-e)) by
      funext e
      simp [u, v']]
    exact hintφ.neg
  have hu'v : IntegrableOn (u' * v) (Ioi (0 : ℝ)) := by
    rw [show u' * v = fun e => a * φ' (y + a * e) * exp (-e) by
      funext e
      rfl]
    exact hintφ'
  have hzero' : Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 (φ y)) := by
    rw [show u * v = fun e => φ (y + a * e) * exp (-e) by
      funext e
      rfl]
    exact hzero
  have htop' : Tendsto (u * v) atTop (𝓝 (0 : ℝ)) := by
    rw [show u * v = fun e => φ (y + a * e) * exp (-e) by
      funext e
      rfl]
    exact htop
  have hip := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero' htop'
  dsimp [u, u', v, v'] at hip
  simp_rw [mul_neg] at hip
  rw [integral_neg] at hip
  linear_combination -hip

/-- Two-sided exponential Stein identity at a fixed value of `y`.

This is the two-sided identity before averaging over the law of `Y`.  The
first four analytic hypotheses are the one-sided requirements for `y + aE`;
the next four are those for `y - bE`.
-/
theorem two_sided_integral_Ioi
    {φ φ' : ℝ → ℝ} {y a b : ℝ}
    (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hintPlus : IntegrableOn
      (fun e : ℝ => φ (y + a * e) * exp (-e)) (Ioi 0))
    (hintDerivPlus : IntegrableOn
      (fun e : ℝ => a * φ' (y + a * e) * exp (-e)) (Ioi 0))
    (hzeroPlus : Tendsto
      (fun e : ℝ => φ (y + a * e) * exp (-e))
      (𝓝[>] (0 : ℝ)) (𝓝 (φ y)))
    (htopPlus : Tendsto
      (fun e : ℝ => φ (y + a * e) * exp (-e)) atTop (𝓝 0))
    (hintMinus : IntegrableOn
      (fun e : ℝ => φ (y - b * e) * exp (-e)) (Ioi 0))
    (hintDerivMinus : IntegrableOn
      (fun e : ℝ => (-b) * φ' (y - b * e) * exp (-e)) (Ioi 0))
    (hzeroMinus : Tendsto
      (fun e : ℝ => φ (y - b * e) * exp (-e))
      (𝓝[>] (0 : ℝ)) (𝓝 (φ y)))
    (htopMinus : Tendsto
      (fun e : ℝ => φ (y - b * e) * exp (-e)) atTop (𝓝 0)) :
    (∫ e : ℝ in Ioi 0, φ (y + a * e) * exp (-e)) -
        (∫ e : ℝ in Ioi 0, φ (y - b * e) * exp (-e)) =
      (∫ e : ℝ in Ioi 0, a * φ' (y + a * e) * exp (-e)) +
        b * (∫ e : ℝ in Ioi 0, φ' (y - b * e) * exp (-e)) := by
  have hplus := integral_Ioi_comp_exp_sub hφ hintPlus hintDerivPlus
    hzeroPlus htopPlus
  have hminusRaw := integral_Ioi_comp_exp_sub (y := y) (a := -b) hφ
    (by simpa [sub_eq_add_neg, neg_mul] using hintMinus)
    (by simpa [sub_eq_add_neg, neg_mul] using hintDerivMinus)
    (by simpa [sub_eq_add_neg, neg_mul] using hzeroMinus)
    (by simpa [sub_eq_add_neg, neg_mul] using htopMinus)
  have hminus :
      (∫ e : ℝ in Ioi 0, φ (y - b * e) * exp (-e)) - φ y =
        -b * (∫ e : ℝ in Ioi 0, φ' (y - b * e) * exp (-e)) := by
    rw [← integral_const_mul]
    simpa [sub_eq_add_neg, neg_mul, mul_assoc] using hminusRaw
  linear_combination hplus - hminus

/-- Improper integration by parts with one possible nondifferentiability
point `k` in the positive half-line.  The finite interval theorem does
not require differentiability at its right endpoint, and the improper
tail theorem does not require it at its left endpoint, so the two pieces
join using continuity alone. -/
theorem integral_Ioi_mul_deriv_one_kink
    {u v u' v' : ℝ → ℝ} {k a' b' : ℝ}
    (hk : 0 < k)
    (hu_cont : Continuous u) (hv_cont : Continuous v)
    (hu : ∀ x, 0 < x → x ≠ k → HasDerivAt u (u' x) x)
    (hv : ∀ x, 0 < x → HasDerivAt v (v' x) x)
    (hu'_fin : IntervalIntegrable u' volume 0 k)
    (hv'_fin : IntervalIntegrable v' volume 0 k)
    (huv'_int : IntegrableOn (u * v') (Ioi 0))
    (hu'v_int : IntegrableOn (u' * v) (Ioi 0))
    (h_zero : u 0 * v 0 = a')
    (h_top : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ x in Ioi (0 : ℝ), u x * v' x =
      b' - a' - ∫ x in Ioi (0 : ℝ), u' x * v x := by
  have hfin := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := 0) (b := k) hu_cont.continuousOn hv_cont.continuousOn
    (fun x hx => by
      have hx' : x ∈ Ioo (0 : ℝ) k := by simpa [min_eq_left hk.le, max_eq_right hk.le] using hx
      exact hu x hx'.1 hx'.2.ne)
    (fun x hx => by
      have hx' : x ∈ Ioo (0 : ℝ) k := by simpa [min_eq_left hk.le, max_eq_right hk.le] using hx
      exact hv x hx'.1)
    hu'_fin hv'_fin
  have hright : Tendsto (u * v) (𝓝[>] k) (𝓝 (u k * v k)) := by
    exact (hu_cont.continuousAt.mul hv_cont.continuousAt).tendsto.mono_left inf_le_left
  have htail := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := k) (a' := u k * v k) (b' := b')
    (fun x hx => hu x (lt_trans hk hx) (ne_of_gt hx))
    (fun x hx => hv x (lt_trans hk hx))
    (huv'_int.mono_set (Ioi_subset_Ioi hk.le))
    (hu'v_int.mono_set (Ioi_subset_Ioi hk.le))
    hright h_top
  have hset : Ioi (0 : ℝ) = Ioc 0 k ∪ Ioi k := by
    ext x
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx
      by_cases hxk : x ≤ k
      · exact Or.inl ⟨hx, hxk⟩
      · exact Or.inr (lt_of_not_ge hxk)
    · rintro (hx | hx) <;> linarith
  have hdisj : Disjoint (Ioc (0 : ℝ) k) (Ioi k) := by
    exact Set.disjoint_left.2 fun x hx₁ hx₂ => (not_lt_of_ge hx₁.2) hx₂
  have hsplit₁ :
      (∫ x in Ioi (0 : ℝ), u x * v' x) =
        (∫ x in Ioc 0 k, u x * v' x) +
          ∫ x in Ioi k, u x * v' x := by
    rw [hset]
    exact setIntegral_union₀ hdisj.aedisjoint measurableSet_Ioi.nullMeasurableSet
      (huv'_int.mono_set (Ioc_subset_Ioi_self))
      (huv'_int.mono_set (Ioi_subset_Ioi hk.le))
  have hsplit₂ :
      (∫ x in Ioi (0 : ℝ), u' x * v x) =
        (∫ x in Ioc 0 k, u' x * v x) +
          ∫ x in Ioi k, u' x * v x := by
    rw [hset]
    exact setIntegral_union₀ hdisj.aedisjoint measurableSet_Ioi.nullMeasurableSet
      (hu'v_int.mono_set (Ioc_subset_Ioi_self))
      (hu'v_int.mono_set (Ioi_subset_Ioi hk.le))
  rw [h_zero] at hfin
  calc
    (∫ x in Ioi (0 : ℝ), u x * v' x) =
        (∫ x in Ioc 0 k, u x * v' x) +
          ∫ x in Ioi k, u x * v' x := hsplit₁
    _ = (∫ x in (0 : ℝ)..k, u x * v' x) +
          ∫ x in Ioi k, u x * v' x := by
        rw [intervalIntegral.integral_of_le hk.le]
    _ = b' - a' -
        ((∫ x in (0 : ℝ)..k, u' x * v x) +
          ∫ x in Ioi k, u' x * v x) := by rw [hfin, htail]; ring
    _ = b' - a' -
        ((∫ x in Ioc 0 k, u' x * v x) +
          ∫ x in Ioi k, u' x * v x) := by
        rw [intervalIntegral.integral_of_le hk.le]
    _ = b' - a' - ∫ x in Ioi (0 : ℝ), u' x * v x := by rw [hsplit₂]

end ExponentialStein

end Feige
