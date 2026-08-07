/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The planar log-branch atom (`abel-weak-solutions`, D2 / §6.1)

Unit: abel-weak-solutions (`docs/design/abel-weak-solutions.md` §6.1). Pure `ℂ → ℂ`, no manifold
imports (matches `Path/Planar.lean`'s hygiene). Two facts:

* `exists_logBranch_disk` — the disk case: a holomorphic, non-vanishing function on a ball has a
  logarithm branch there (`Complex.exp ∘ L = h`), built from mathlib's disk-Morera primitive
  (`DifferentiableOn.isExactOn_ball`) plus a zero-derivative/uniqueness argument. No branch-cut
  case analysis on `Complex.log`/`Complex.arg` anywhere. Spike-verified in `scratch_abelweak.lean`.
* `exists_exteriorLogBranch` — the exterior case Forster's construction actually needs: a log
  branch of `(z - b)/(z - a)` on `{ρ < ‖z‖}` for `a, b` inside `ball 0 ρ`, obtained by transporting
  the disk case through the inversion `w = 1/z` (turning the exterior region into a genuine disk
  containing no singularity of the transported function at all — no winding-number/homotopy
  machinery needed).
-/

open Complex Metric Set

noncomputable section

namespace RS.AbelWeak

/-- **The disk log-branch lemma** (§6.1, disk case, spiked in `scratch_abelweak.lean`): a function
`h` differentiable and non-vanishing on `ball c₀ r` has a primitive `L` of `h'/h` there with
`Complex.exp ∘ L = h` on the ball. -/
theorem exists_logBranch_disk {c₀ : ℂ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (ball c₀ r)) (hne : ∀ z ∈ ball c₀ r, h z ≠ 0) :
    ∃ L : ℂ → ℂ, (∀ z ∈ ball c₀ r, HasDerivAt L (deriv h z / h z) z) ∧
      ∀ z ∈ ball c₀ r, Complex.exp (L z) = h z := by
  have hc₀ : c₀ ∈ ball c₀ r := mem_ball_self hr
  -- `deriv h / h` is differentiable on the ball (h differentiable, nonvanishing there).
  have hd : DifferentiableOn ℂ (fun z => deriv h z / h z) (ball c₀ r) := by
    have hderiv : DifferentiableOn ℂ (deriv h) (ball c₀ r) :=
      (hh.analyticOnNhd isOpen_ball).deriv.differentiableOn
    exact hderiv.div hh hne
  obtain ⟨L, hL0, hL⟩ := hd.isExactOn_ball.with_val_at c₀ (Complex.log (h c₀))
  refine ⟨L, hL, fun z hz => ?_⟩
  -- `φ z := h z * exp (-(L z))` has zero derivative throughout the ball.
  set φ : ℂ → ℂ := fun z => h z * Complex.exp (-(L z)) with hφ_def
  have hφderiv : ∀ z ∈ ball c₀ r, HasDerivAt φ 0 z := by
    intro z hz
    have hhz : HasDerivAt h (deriv h z) z :=
        (hh.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hLz : HasDerivAt L (deriv h z / h z) z := hL z hz
    have hexpz : HasDerivAt (fun w => Complex.exp (-(L w)))
        (Complex.exp (-(L z)) * -(deriv h z / h z)) z := hLz.neg.cexp
    have hprod := hhz.mul hexpz
    have hval : deriv h z * Complex.exp (-(L z)) +
        h z * (Complex.exp (-(L z)) * -(deriv h z / h z)) = 0 := by
      have hne' := hne z hz
      field_simp
      ring
    rwa [hval] at hprod
  have hφdiffOn : DifferentiableOn ℂ φ (ball c₀ r) :=
    fun x hx => (hφderiv x hx).differentiableAt.differentiableWithinAt
  have hconst : φ z = φ c₀ := by
    apply Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℂ) (convex_ball c₀ r) hφdiffOn
      (fun x hx => ?_) hz hc₀
    rw [fderivWithin_of_isOpen isOpen_ball hx, (hφderiv x hx).hasFDerivAt.fderiv]
    ext
    simp []
  have hφc₀ : φ c₀ = 1 := by
    have hne' := hne c₀ hc₀
    change h c₀ * Complex.exp (-(L c₀)) = 1
    rw [hL0, Complex.exp_neg, Complex.exp_log hne', mul_inv_cancel₀ hne']
  have hz' : φ z = 1 := hφc₀ ▸ hconst
  change Complex.exp (L z) = h z
  have hexpz := congrArg (· * Complex.exp (L z)) hz'
  simp only [φ, one_mul, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
    mul_one] at hexpz
  exact hexpz.symm

/-- Auxiliary: for `‖a‖ < ρ` and `‖w‖ < ρ⁻¹`, `1 - a * w ≠ 0`. -/
private theorem one_sub_mul_ne_zero {a w : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (ha : ‖a‖ < ρ) (hw : ‖w‖ < ρ⁻¹) : 1 - a * w ≠ 0 := by
  intro h
  have haw : a * w = 1 := by linear_combination -h
  have hnorm : ‖a‖ * ‖w‖ = 1 := by
    rw [← norm_mul, haw, norm_one]
  have hlt : ‖a‖ * ‖w‖ < ρ * ρ⁻¹ := by
    apply mul_lt_mul' ha.le hw (norm_nonneg w) hρ |>.trans_eq
    · ring
  rw [mul_inv_cancel₀ hρ.ne'] at hlt
  rw [hnorm] at hlt
  exact absurd hlt (lt_irrefl 1)

/-- **The exterior log-branch lemma** (§6.1, the engine Forster's construction actually needs): a
log branch of `(z - b)/(z - a)` on `{ρ < ‖z‖}` for `a, b` inside `ball 0 ρ`, via the substitution
`w = 1/z` turning the exterior region into a genuine disk `ball 0 ρ⁻¹` containing no singularity
of the transported function `H w := (1 - b*w)/(1 - a*w)` at all. -/
theorem exists_exteriorLogBranch {a b : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (ha : a ∈ ball (0 : ℂ) ρ) (hb : b ∈ ball (0 : ℂ) ρ) :
    ∃ L : ℂ → ℂ, (∀ z : ℂ, ρ < ‖z‖ → HasDerivAt L (1 / (z - b) - 1 / (z - a)) z) ∧
      ∀ z : ℂ, ρ < ‖z‖ → Complex.exp (L z) = (z - b) / (z - a) := by
  rw [mem_ball, dist_zero_right] at ha hb
  set H : ℂ → ℂ := fun w => (1 - b * w) / (1 - a * w) with hH_def
  have hρ' : (0 : ℝ) < ρ⁻¹ := inv_pos.mpr hρ
  have hden_ne : ∀ w ∈ ball (0 : ℂ) ρ⁻¹, (1 : ℂ) - a * w ≠ 0 := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw
    exact one_sub_mul_ne_zero hρ ha hw
  have hnum_ne : ∀ w ∈ ball (0 : ℂ) ρ⁻¹, (1 : ℂ) - b * w ≠ 0 := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw
    exact one_sub_mul_ne_zero hρ hb hw
  have hH_diff : DifferentiableOn ℂ H (ball (0 : ℂ) ρ⁻¹) := by
    intro w hw
    exact (((differentiableAt_const 1).sub
      ((differentiableAt_const b).mul differentiableAt_fun_id)).div
      ((differentiableAt_const 1).sub
        ((differentiableAt_const a).mul differentiableAt_fun_id)) (hden_ne w
            hw)).differentiableWithinAt
  have hH_ne : ∀ w ∈ ball (0 : ℂ) ρ⁻¹, H w ≠ 0 := by
    intro w hw
    exact div_ne_zero (hnum_ne w hw) (hden_ne w hw)
  obtain ⟨Lext, hLext, hexpLext⟩ := exists_logBranch_disk hρ' hH_diff hH_ne
  have hzmem : ∀ z : ℂ, ρ < ‖z‖ → z ≠ 0 ∧ z⁻¹ ∈ ball (0 : ℂ) ρ⁻¹ := by
    intro z hz
    have hzpos : (0 : ℝ) < ‖z‖ := hρ.trans hz
    have hzne : z ≠ 0 := norm_pos_iff.mp hzpos
    refine ⟨hzne, ?_⟩
    rw [mem_ball, dist_zero_right, norm_inv]
    exact (inv_lt_inv₀ hzpos hρ).2 hz
  have haz : ∀ z : ℂ, ρ < ‖z‖ → z - a ≠ 0 := by
    intro z hz h
    obtain ⟨hzne, hwmem⟩ := hzmem z hz
    apply hden_ne z⁻¹ hwmem
    have ha' : a = z := by linear_combination -h
    rw [ha', mul_inv_cancel₀ hzne, sub_self]
  have hbz : ∀ z : ℂ, ρ < ‖z‖ → z - b ≠ 0 := by
    intro z hz h
    obtain ⟨hzne, hwmem⟩ := hzmem z hz
    apply hnum_ne z⁻¹ hwmem
    have hb' : b = z := by linear_combination -h
    rw [hb', mul_inv_cancel₀ hzne, sub_self]
  refine ⟨fun z => Lext z⁻¹, fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨hzne, hwmem⟩ := hzmem z hz
    have hHw := hLext z⁻¹ hwmem
    have hinv : HasDerivAt (fun y : ℂ => y⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hzne
    have hcomp := HasDerivAt.comp z hHw hinv
    have hden0 := hden_ne z⁻¹ hwmem
    have hnum0 := hnum_ne z⁻¹ hwmem
    have hratio : deriv H z⁻¹ / H z⁻¹ = (a - b) / ((1 - a * z⁻¹) * (1 - b * z⁻¹)) := by
      have hderivH : HasDerivAt H ((-b * (1 - a * z⁻¹) - (1 - b * z⁻¹) * (-a))
          / (1 - a * z⁻¹) ^ 2) z⁻¹ := by
        have h1 : HasDerivAt (fun w : ℂ => (1 : ℂ) - b * w) (-b) z⁻¹ := by
          simpa using (hasDerivAt_id z⁻¹).const_mul b |>.const_sub (1 : ℂ)
        have h2 : HasDerivAt (fun w : ℂ => (1 : ℂ) - a * w) (-a) z⁻¹ := by
          simpa using (hasDerivAt_id z⁻¹).const_mul a |>.const_sub (1 : ℂ)
        exact h1.div h2 hden0
      rw [hderivH.deriv]
      change ((-b * (1 - a * z⁻¹) - (1 - b * z⁻¹) * (-a)) / (1 - a * z⁻¹) ^ 2)
          / ((1 - b * z⁻¹) / (1 - a * z⁻¹)) = (a - b) / ((1 - a * z⁻¹) * (1 - b * z⁻¹))
      field_simp
      ring
    rw [hratio] at hcomp
    have hfinal : (a - b) / ((1 - a * z⁻¹) * (1 - b * z⁻¹)) * -(z ^ 2)⁻¹
        = 1 / (z - b) - 1 / (z - a) := by
      have haz' := haz z hz
      have hbz' := hbz z hz
      have e1 : (1 : ℂ) - a * z⁻¹ = (z - a) / z := by field_simp
      have e2 : (1 : ℂ) - b * z⁻¹ = (z - b) / z := by field_simp
      rw [e1, e2]
      have hzne2 : (z : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hzne
      field_simp
      ring
    have hcomp' : HasDerivAt (Lext ∘ Inv.inv)
        (1 / (z - b) - 1 / (z - a)) z := hfinal ▸ hcomp
    exact hcomp'
  · obtain ⟨hzne, hwmem⟩ := hzmem z hz
    have heq := hexpLext z⁻¹ hwmem
    rw [hH_def] at heq
    change Complex.exp (Lext z⁻¹) = (z - b) / (z - a)
    rw [heq]
    have haz' := haz z hz
    have e1 : (1 : ℂ) - a * z⁻¹ = (z - a) / z := by field_simp
    have e2 : (1 : ℂ) - b * z⁻¹ = (z - b) / z := by field_simp
    change (1 - b * z⁻¹) / (1 - a * z⁻¹) = (z - b) / (z - a)
    rw [e1, e2]
    field_simp

end RS.AbelWeak

end
