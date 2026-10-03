/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Weight
public import LeanPool.Zeta5Irrational.Construction
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

/-! # The polynomial moments of the weight `w` (first half of Proposition 2.2)

`∫₀^∞ y^{2e} w(y) dy = μ(t^e) = (-1)^e B_{2e+2} (2e+3)(2e+4)(2e+5) / 24`, from the Gamma
integral, term-wise integration of the series defining `w`, and Euler's formula
`ζ(2k) = (-1)^{k+1} 2^{2k-1} π^{2k} B_{2k} / (2k)!` (`hasSum_zeta_nat` in Mathlib).
-/

public section

open MeasureTheory Set Filter Topology Finset

namespace Zeta5Irrational

/-- `∫₀^∞ y^m e^{-ry} dy = m! / r^(m+1)`. -/
lemma integral_pow_mul_exp_neg_mul (m : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ y in Ioi 0, y ^ m * Real.exp (-(r * y)) = (m.factorial : ℝ) / r ^ (m + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (m : ℝ) + 1) (by positivity) hr
  rw [Real.Gamma_nat_eq_factorial, add_sub_cancel_right] at h
  have hL :
    ∫ y in Ioi 0, y ^ m * Real.exp (-(r * y)) = ∫ t in Ioi 0, t ^ (m : ℝ) * Real.exp (-(r * t)) :=
  by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [Real.rpow_natCast]
  rw [hL, h]
  have : (1 / r) ^ ((m : ℝ) + 1) = (1 / r) ^ (m + 1) := by
    rw [show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [this, one_div_pow, div_mul_eq_mul_div, one_mul]

lemma integrableOn_pow_mul_exp_neg_mul (m : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y : ℝ => y ^ m * Real.exp (-(r * y))) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (m : ℝ) + 1) (by positivity)
  rw [add_sub_cancel_right] at h
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-(r * x)) * (r * x) ^ (m : ℝ)) (Ioi 0) := by
    have :=
      (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x) * x ^ (m : ℝ)) 0 hr).mpr
        (by simpa using h)
    simpa using this
  have h3 :
    IntegrableOn (fun x : ℝ => (1 / r ^ m) * (Real.exp (-(r * x)) * (r * x) ^ (m : ℝ))) (Ioi 0) :=
    h2.const_mul _
  refine h3.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx : 0 < x := hx
  simp only
  rw [Real.rpow_natCast, mul_pow]
  field_simp

/-- The summand `y^{2e} · (2π)⁴ y⁵ / 12 · (ℓ+1)⁴ e^{-2π(ℓ+1)y}`. -/
noncomputable def momTerm (e ℓ : ℕ) (y : ℝ) : ℝ :=
  (2 * Real.pi) ^ 4 / 12 * ((ℓ : ℝ) + 1) ^ 4 *
    (y ^ (2 * e + 5) * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y)))

lemma momTerm_eq (e ℓ : ℕ) (y : ℝ) :
    momTerm e ℓ y =
      y ^ (2 * e) * ((2 * Real.pi) ^ 4 * y ^ 5 / 12) *
        (((ℓ : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y))) :=
  by unfold momTerm; ring

lemma integrableOn_momTerm (e ℓ : ℕ) : IntegrableOn (momTerm e ℓ) (Ioi 0) := by
  unfold momTerm
  exact
    (integrableOn_pow_mul_exp_neg_mul (2 * e + 5) (r := 2 * Real.pi * ((ℓ : ℝ) + 1))
          (by positivity)).const_mul
      _

lemma integral_momTerm (e ℓ : ℕ) :
    ∫ y in Ioi 0, momTerm e ℓ y =
      (2 * Real.pi) ^ 4 / 12 * ((2 * e + 5).factorial : ℝ) / (2 * Real.pi) ^ (2 * e + 6) *
        (1 / ((ℓ : ℝ) + 1) ^ (2 * e + 2)) := by
  unfold momTerm
  rw [integral_const_mul, integral_pow_mul_exp_neg_mul _ (by positivity)]
  have hl : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [mul_pow (2 * Real.pi) ((ℓ : ℝ) + 1)]
  have hsplit :
    ((ℓ : ℝ) + 1) ^ (2 * e + 5 + 1) = ((ℓ : ℝ) + 1) ^ 4 * ((ℓ : ℝ) + 1) ^ (2 * e + 2) := by ring
  rw [hsplit]
  field_simp

lemma momTerm_nonneg (e ℓ : ℕ) {y : ℝ} (hy : 0 < y) : 0 ≤ momTerm e ℓ y := by
  unfold momTerm;
  positivity

/-- **The polynomial moments**: `∫₀^∞ y^{2e} w(y) dy = μ(t^e)`, with integrability. -/
theorem mono_moment (e : ℕ) :
    IntegrableOn (fun y => y ^ (2 * e) * w y) (Ioi 0) ∧
      ∫ y in Ioi 0, y ^ (2 * e) * w y = ((μmono e : ℚ) : ℝ) := by
  have hpt : ∀ y, y ^ (2 * e) * w y = ∑' ℓ, momTerm e ℓ y := by
    intro y
    simp_rw [momTerm_eq]
    rw [tsum_mul_left]
    unfold w wS; ring
  have hnorm : ∀ ℓ, ∫ y in Ioi 0, ‖momTerm e ℓ y‖ = ∫ y in Ioi 0, momTerm e ℓ y := by
    intro ℓ
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    exact Real.norm_of_nonneg (momTerm_nonneg e ℓ hy)
  have hsum : Summable fun ℓ => ∫ y in Ioi 0, ‖momTerm e ℓ y‖ := by
    simp_rw [hnorm, integral_momTerm]
    refine Summable.mul_left _ ?_
    have :=
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2 * e + 2))
    refine this.congr fun ℓ => ?_
    push_cast; ring
  have hint := integral_tsum_of_summable_integral_norm (fun ℓ => integrableOn_momTerm e ℓ) hsum
  constructor
  · -- integrability by domination
    have hg :
      IntegrableOn
        (fun y : ℝ =>
          32 * (y ^ (2 * e + 1) * Real.exp (-(Real.pi * y))) +
            11 * (y ^ (2 * e) * Real.exp (-(Real.pi * y))))
        (Ioi 0) :=
      ((integrableOn_pow_mul_exp_neg_mul (2 * e + 1) Real.pi_pos).const_mul 32).add
        ((integrableOn_pow_mul_exp_neg_mul (2 * e) Real.pi_pos).const_mul 11)
    refine
      hg.mono' ((measurable_id.pow_const _).aemeasurable.mul aemeasurable_w).aestronglyMeasurable
        ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    have hy : 0 < y := hy
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (w_pos hy).le)]
    have := mul_le_mul_of_nonneg_left (w_le hy) (by positivity : (0 : ℝ) ≤ y ^ (2 * e))
    calc
      y ^ (2 * e) * w y ≤ y ^ (2 * e) * ((32 * y + 11) * Real.exp (-(Real.pi * y))) := this
      _ = _ := by ring
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => hpt y), ← hint]
    simp_rw [integral_momTerm]
    rw [tsum_mul_left]
      -- Euler's formula
    have hz := hasSum_zeta_nat (k := e + 1) (by omega)
    have hz1 := (hasSum_nat_add_iff' 1).mpr hz
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, Nat.mul_eq_zero,
      OfNat.ofNat_ne_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, or_self,
      not_false_eq_true, zero_pow, div_zero, sub_zero] at hz1
    have hS :
      ∑' ℓ : ℕ, 1 / ((ℓ : ℝ) + 1) ^ (2 * e + 2) =
        (-1 : ℝ) ^ (e + 1 + 1) * (2 : ℝ) ^ (2 * (e + 1) - 1) * Real.pi ^ (2 * (e + 1)) *
            (bernoulli (2 * (e + 1)) : ℝ) /
          (2 * (e + 1)).factorial := by
      rw [← hz1.tsum_eq]
      refine tsum_congr fun ℓ => ?_
      push_cast
      ring_nf
    rw [hS]
    have hfac :
      ((2 * e + 5).factorial : ℝ) =
        ((2 * e + 5) * (2 * e + 4) * (2 * e + 3) : ℕ) * ((2 * e + 2).factorial : ℝ) := by
      rw [show 2 * e + 5 = (2 * e + 4) + 1 from rfl, Nat.factorial_succ,
        show 2 * e + 4 = (2 * e + 3) + 1 from rfl, Nat.factorial_succ,
        show 2 * e + 3 = (2 * e + 2) + 1 from rfl, Nat.factorial_succ]
      push_cast; ring
    rw [show 2 * (e + 1) = 2 * e + 2 by ring, show 2 * e + 2 - 1 = 2 * e + 1 by omega, hfac]
    unfold μmono
    push_cast
    have hfac2 : (0 : ℝ) < ((2 * e + 2).factorial : ℝ) := by positivity
    have hpi : 0 < Real.pi := Real.pi_pos
    field_simp
    ring

end Zeta5Irrational
