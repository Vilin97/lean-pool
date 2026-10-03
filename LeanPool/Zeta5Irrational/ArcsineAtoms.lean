/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.Zeta5Irrational.CircleAtoms
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # The arcsine atoms: factorisation and the potential formula (A.1)

For `w = e^{iθ}` and `y(θ) = m + r cos θ`, one has
`z - y(θ) = -(r/(2w)) (w - q₁)(w - q₂)` where `q₁ + q₂ = 2ζ`, `q₁ q₂ = 1`, `ζ = (z - m)/r`.
Hence `∫₀^{2π} log ‖z - y(θ)‖ dθ = 2π (log (r/2) + log⁺ ‖q₁‖ + log⁺ ‖q₂‖)` by Mathlib's
circle-average identity, which gives the closed form `Uω` of (A.1) for real `z`.
-/

public section

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace Zeta5Irrational

/-- The arcsine curve `θ ↦ m + r cos θ` (as a complex number). -/
@[expose] noncomputable def arcCurve (m r : ℝ) (θ : ℝ) : ℂ :=
  ((m + r * Real.cos θ : ℝ) : ℂ)

lemma continuous_arcCurve (m r : ℝ) : Continuous (arcCurve m r) := by unfold arcCurve; fun_prop

lemma norm_arcCurve_le (m r θ : ℝ) : ‖arcCurve m r θ‖ ≤ |m| + |r| := by
  unfold arcCurve
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    |m + r * Real.cos θ| ≤ |m| + |r * Real.cos θ| := abs_add_le _ _
    _ ≤ |m| + |r| := by
      rw [abs_mul]
      have := Real.abs_cos_le_one θ
      nlinarith [abs_nonneg r]

/-- The factorisation of `z - y(θ)`. -/
lemma sub_arcCurve_eq {z : ℂ} {m r : ℝ} (hr : r ≠ 0) (θ : ℝ) {sq : ℂ}
    (hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1) :
    z - arcCurve m r θ =
      -(r / (2 * circleMap 0 1 θ)) *
        ((circleMap 0 1 θ - ((z - m) / r + sq)) * (circleMap 0 1 θ - ((z - m) / r - sq))) := by
  have hw : circleMap 0 1 θ ≠ 0 := by
    intro h; have := norm_circleMap_zero_one θ; rw [h] at this;
    simp at this
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have e1 :
    (circleMap 0 1 θ - ((z - m) / r + sq)) * (circleMap 0 1 θ - ((z - m) / r - sq)) =
      circleMap 0 1 θ ^ 2 - 2 * ((z - m) / r) * circleMap 0 1 θ + 1 :=
    by linear_combination (-1 : ℂ) * hsq
  rw [e1]
  simp only [arcCurve, Complex.ofReal_add, Complex.ofReal_mul]
  rw [cos_eq_half_add_inv]
  field_simp
  ring

lemma norm_sub_arcCurve {z : ℂ} {m r : ℝ} (hr : 0 < r) (θ : ℝ) {sq : ℂ}
    (hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1) :
    ‖z - arcCurve m r θ‖ =
      r / 2 * (‖circleMap 0 1 θ - ((z - m) / r + sq)‖ * ‖circleMap 0 1 θ - ((z - m) / r - sq)‖) :=
  by
  rw [sub_arcCurve_eq hr.ne' θ hsq, norm_mul, norm_neg, norm_div, norm_mul, norm_mul,
    norm_circleMap_zero_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  simp

/-- The exceptional set is countable. -/
lemma arc_exceptional_countable (q₁ q₂ : ℂ) :
    ({θ : ℝ | circleMap 0 1 θ = q₁ ∨ circleMap 0 1 θ = q₂}).Countable := by
  have :
    {θ : ℝ | circleMap 0 1 θ = q₁ ∨ circleMap 0 1 θ = q₂} =
      circleMap 0 1 ⁻¹' { q₁ } ∪ circleMap 0 1 ⁻¹' { q₂ } :=
    by ext θ; simp
  rw [this]
  exact
    (circleMap_preimage_countable 0 one_ne_zero q₁).union
      (circleMap_preimage_countable 0 one_ne_zero q₂)

lemma arc_log_ae {z : ℂ} {m r : ℝ} (hr : 0 < r) {sq : ℂ} (hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1) :
    ∀ᵐ θ ∂(volume : Measure ℝ),
      Real.log ‖z - arcCurve m r θ‖ =
        Real.log (r / 2) + Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖ +
          Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖ := by
  have h0 :=
    (arc_exceptional_countable ((z - m) / r + sq) ((z - m) / r - sq)).measure_zero
      (volume : Measure ℝ)
  filter_upwards [compl_mem_ae_iff.mpr h0] with θ hθ
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_or] at hθ
  rw [norm_sub_arcCurve hr θ hsq,
    Real.log_mul (by positivity)
      (by apply mul_ne_zero <;> exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (by tauto))),
    Real.log_mul (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hθ.1))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hθ.2)),
    add_assoc]

lemma arc_log_integrable {z : ℂ} {m r : ℝ} (hr : 0 < r) :
    IntervalIntegrable (fun θ => Real.log ‖z - arcCurve m r θ‖) volume 0 (2 * π) := by
  set sq : ℂ := (((z - m) / r) ^ 2 - 1) ^ ((2 : ℕ) : ℂ)⁻¹ with hsq_def
  have hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1 := Complex.cpow_nat_inv_pow _ two_ne_zero
  have hg :
    IntervalIntegrable
      (fun θ =>
        Real.log (r / 2) + Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖ +
          Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖)
      volume 0 (2 * π) :=
    (intervalIntegrable_const.add (circle_log_integrable 0 _ 1)).add (circle_log_integrable 0 _ 1)
  refine hg.congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [arc_log_ae hr hsq] with θ hθ
  exact hθ.symm

/-- The arcsine potential at a complex point: `∫₀^{2π} log ‖z - y(θ)‖ dθ`. -/
lemma arc_log_integral {z : ℂ} {m r : ℝ} (hr : 0 < r) {sq : ℂ}
    (hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1) :
    ∫ θ in (0 : ℝ)..2 * π, Real.log ‖z - arcCurve m r θ‖ =
      2 * π * (Real.log (r / 2) + log⁺ ‖(z - m) / r + sq‖ + log⁺ ‖(z - m) / r - sq‖) := by
  rw [intervalIntegral.integral_congr_ae (g := fun θ =>
      Real.log (r / 2) + Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖ +
        Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖)
      (by
        filter_upwards [arc_log_ae hr hsq] with θ hθ _
        exact hθ)]
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add (circle_log_integrable 0 _ 1))
      (circle_log_integrable 0 _ 1),
    intervalIntegral.integral_add intervalIntegrable_const (circle_log_integrable 0 _ 1),
    intervalIntegral.integral_const, circle_log_integral_zero_one, circle_log_integral_zero_one]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- A uniform bound for `∫₀^{2π} |log ‖z - y(θ)‖| dθ`. -/
lemma arc_abs_log_integral_le {z : ℂ} {m r : ℝ} (hr : 0 < r) {sq : ℂ}
    (hsq : sq ^ 2 = ((z - m) / r) ^ 2 - 1) :
    ∫ θ in (0 : ℝ)..2 * π, |Real.log ‖z - arcCurve m r θ‖| ≤
      2 * π * |Real.log (r / 2)| + 4 * π * Real.log (1 + ‖(z - m) / r + sq‖) +
        4 * π * Real.log (1 + ‖(z - m) / r - sq‖) := by
  rw [intervalIntegral.integral_congr_ae (g := fun θ =>
      |Real.log (r / 2) + Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖ +
          Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖|)
      (by
        filter_upwards [arc_log_ae hr hsq] with θ hθ _
        rw [hθ])]
  have h1 := abs_log_circle_integral_le ((z - m) / r + sq)
  have h2 := abs_log_circle_integral_le ((z - m) / r - sq)
  have hi1 := (circle_log_integrable 0 ((z - m) / r + sq) 1).abs
  have hi2 := (circle_log_integrable 0 ((z - m) / r - sq) 1).abs
  have hmono :
    (∫ θ in (0 : ℝ)..2 * π,
        |Real.log (r / 2) + Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖ +
            Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖|) ≤
      ∫ θ in (0 : ℝ)..2 * π,
        (|Real.log (r / 2)| + |Real.log ‖circleMap 0 1 θ - ((z - m) / r + sq)‖| +
          |Real.log ‖circleMap 0 1 θ - ((z - m) / r - sq)‖|) := by
    apply integral_mono_on (by positivity)
    · exact
        ((intervalIntegrable_const.add (circle_log_integrable 0 _ 1)).add
            (circle_log_integrable 0 _ 1)).abs
    · exact (intervalIntegrable_const.add hi1).add hi2
    intro θ _
    exact abs_add_three _ _ _
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add hi1) hi2,
    intervalIntegral.integral_add intervalIntegrable_const hi1, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] at hmono
  linarith

end Zeta5Irrational
