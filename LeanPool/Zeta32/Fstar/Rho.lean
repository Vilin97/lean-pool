/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Fstar.Wt
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! the proof notes, 5.4 (Lemma 12), the density `ρ_a`.
For `0 < x ≤ a`: `G(c,x) = 2·arsinh(√(a²−x²)/√(c²+x²))`, so `ρ_a(x)` is a nondecreasing function of
`s = √(a²−x²)` with coefficients `x ↦ √(c²+x²)` independent of `a`; this gives `ρ_a ≥ 0` and
monotonicity in `a`.
Monotonicity in `x` uses the log form with `U_c = √(c²+a²)` fixed and the identity
`(U₁+s)(U₂+t)(U₁−t)(U₂−s) − (U₁+t)(U₂+s)(U₁−s)(U₂−t) = 2(s−t)(U₂−U₁)(U₁U₂+st)`.
Integrability: `ρ_a = fc − log x/(6π)` on `(0, a]` with `fc` continuous. Written from scratch. -/

public section

open Real MeasureTheory
namespace Zeta32.Fstar
noncomputable section

theorem Gfun_eq_arsinh {a c x : ℝ} (hx : 0 < x) (hxa : x ≤ a) :
    Gfun a c x = 2 * arsinh (√(a^2 - x^2) / √(c^2 + x^2)) := by
  have hs0 : 0 ≤ √(a^2 - x^2) := sqrt_nonneg _
  have hs2 : √(a^2 - x^2) ^ 2 = a^2 - x^2 := sq_sqrt (by nlinarith)
  have hk : 0 < √(c^2 + x^2) := sqrt_pos.mpr (by positivity)
  have hk2 : √(c^2 + x^2) ^ 2 = c^2 + x^2 := sq_sqrt (by positivity)
  have hU0 : 0 ≤ √(c^2 + a^2) := sqrt_nonneg _
  have hU2 : √(c^2 + a^2) ^ 2 = c^2 + a^2 := sq_sqrt (by positivity)
  set s := √(a^2 - x^2)
  set k := √(c^2 + x^2)
  set U := √(c^2 + a^2)
  have hUs : s < U := by
    by_contra h; push Not at h
    nlinarith [mul_le_mul h h hU0 hs0]
  have h1 : √(1 + (s/k)^2) = U/k := by
    rw [show 1 + (s/k)^2 = (U/k)^2 by
      rw [div_pow, div_pow, hU2, hs2]; field_simp; rw [hk2]; ring]
    exact sqrt_sq (div_nonneg hU0 hk.le)
  unfold Gfun arsinh
  rw [h1, ← add_div, show (2:ℝ) * log ((s + U) / k) = log (((s + U) / k)^2) by
    rw [Real.log_pow]; norm_num]
  congr 1
  rw [div_pow, hk2, div_eq_div_iff (by linarith) (by positivity)]
  linear_combination (-(U + s)) * (hU2 - hs2)

theorem hasDerivAt_arsinh_div {k : ℝ} (hk : 0 < k) (s : ℝ) :
    HasDerivAt (fun s => arsinh (s / k)) (1 / √(k^2 + s^2)) s := by
  have := ((hasDerivAt_id s).div_const k).arsinh
  have e : √(1 + (s/k)^2) = √(k^2 + s^2) / k := by
    rw [show 1 + (s/k)^2 = (k^2 + s^2) / k^2 by field_simp, sqrt_div (by positivity), sqrt_sq hk.le]
  have hp : 0 < √(k^2 + s^2) := sqrt_pos.mpr (by positivity)
  convert this using 1
  · rfl
  change 1 / √(k^2 + s^2) = (√(1 + (s/k)^2))⁻¹ * (1/k)
  rw [e]
  field_simp

theorem arsinh_div_sub_monotone {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (h₁₂ : k₁ ≤ k₂) :
    Monotone (fun s => arsinh (s / k₁) - arsinh (s / k₂)) := by
  apply monotone_of_hasDerivAt_nonneg
    (fun s => (hasDerivAt_arsinh_div hk₁ s).sub (hasDerivAt_arsinh_div (hk₁.trans_le h₁₂) s))
  intro s
  simp only [Pi.zero_apply, sub_nonneg]
  exact one_div_le_one_div_of_le (sqrt_pos.mpr (by positivity))
    (sqrt_le_sqrt (by nlinarith))

/-- `ρ_a(x)` written through `s = √(a² − x²)` (arsinh form, valid for `0 < x ≤ a`). -/
def Rs (x s : ℝ) : ℝ :=
  ((1/3) * (2 * arsinh (s / √(0^2 + x^2)) - 2 * arsinh (s / √(1^2 + x^2)))
    + (5/3) * (2 * arsinh (s / √(1^2 + x^2)) - 2 * arsinh (s / √(5^2 + x^2)))
    + (4/3) * (2 * arsinh (s / √(5^2 + x^2)))) / (4 * π)

theorem rhoA_eq_Rs {a x : ℝ} (hx : 0 < x) (hxa : x ≤ a) : rhoA a x = Rs x √(a^2 - x^2) := by
  unfold rhoA Rs
  rw [Gfun_eq_arsinh hx hxa, Gfun_eq_arsinh hx hxa, Gfun_eq_arsinh hx hxa]

theorem Rs_monotone {x : ℝ} (hx : 0 < x) : Monotone (Rs x) := by
  intro s t hst
  have hk0 : 0 < √((0:ℝ)^2 + x^2) := sqrt_pos.mpr (by positivity)
  have hk1 : 0 < √((1:ℝ)^2 + x^2) := sqrt_pos.mpr (by positivity)
  have hk5 : 0 < √((5:ℝ)^2 + x^2) := sqrt_pos.mpr (by positivity)
  have m01 := arsinh_div_sub_monotone (k₂ := √((1:ℝ)^2 + x^2)) hk0 (sqrt_le_sqrt (by norm_num)) hst
  have m15 := arsinh_div_sub_monotone (k₂ := √((5:ℝ)^2 + x^2)) hk1 (sqrt_le_sqrt (by norm_num)) hst
  have m5 : arsinh (s / √((5:ℝ)^2 + x^2)) ≤ arsinh (t / √((5:ℝ)^2 + x^2)) :=
    arsinh_le_arsinh.mpr (div_le_div_of_nonneg_right hst hk5.le)
  simp only at m01 m15
  unfold Rs
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

theorem Rs_zero (x : ℝ) : Rs x 0 = 0 := by simp [Rs]

theorem rhoA_nonneg {a x : ℝ} (hx : 0 < x) (hxa : x ≤ a) : 0 ≤ rhoA a x := by
  rw [rhoA_eq_Rs hx hxa, ← Rs_zero x]
  exact Rs_monotone hx (sqrt_nonneg _)

/-- `ρ_a(x)` is nondecreasing in `a` for fixed `x`. -/
theorem rhoA_mono_a {a b x : ℝ} (hx : 0 < x) (hxb : x ≤ b) (hba : b ≤ a) : rhoA b x ≤ rhoA a x := by
  rw [rhoA_eq_Rs hx hxb, rhoA_eq_Rs hx (hxb.trans hba)]
  exact Rs_monotone hx (sqrt_le_sqrt (by nlinarith))

theorem log_ratio_mono {U t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (hsU : s < U) :
    log ((U + t) / (U - t)) ≤ log ((U + s) / (U - s)) := by
  apply log_le_log (div_pos (by linarith) (by linarith))
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem log_ratio_sub_mono {U₁ U₂ t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (hsU : s < U₁) (hU : U₁ ≤
  U₂) :
    log ((U₁ + t) / (U₁ - t)) - log ((U₂ + t) / (U₂ - t))
      ≤ log ((U₁ + s) / (U₁ - s)) - log ((U₂ + s) / (U₂ - s)) := by
  have p1 : 0 < U₁ - s := by linarith
  have p2 : 0 < U₁ - t := by linarith
  have p3 : 0 < U₂ - s := by linarith
  have p4 : 0 < U₂ - t := by linarith
  have q1 : 0 < U₁ + t := by linarith
  have q2 : 0 < U₂ + s := by linarith
  have q3 : 0 < U₁ + s := by linarith
  have q4 : 0 < U₂ + t := by linarith
  have key : log ((U₁ + t) / (U₁ - t) * ((U₂ + s) / (U₂ - s)))
      ≤ log ((U₁ + s) / (U₁ - s) * ((U₂ + t) / (U₂ - t))) := by
    apply log_le_log (by positivity)
    rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have hid : (U₁ + s) * (U₂ + t) * ((U₁ - t) * (U₂ - s)) - (U₁ + t) * (U₂ + s) * ((U₁ - s) *
      (U₂ - t))
        = 2 * (s - t) * (U₂ - U₁) * (U₁ * U₂ + s * t) := by ring
    have : 0 ≤ 2 * (s - t) * (U₂ - U₁) * (U₁ * U₂ + s * t) := by
      apply mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
      nlinarith
    linarith
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity)] at key
  linarith

/-- `ρ_a(x)` is nonincreasing in `x` on `(0, a]`. -/
theorem rhoA_anti_x {a x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hya : y ≤ a) : rhoA a y ≤ rhoA a x := by
  have ha : 0 < a := hx.trans_le (hxy.trans hya)
  have ht : 0 ≤ √(a^2 - y^2) := sqrt_nonneg _
  have hts : √(a^2 - y^2) ≤ √(a^2 - x^2) := sqrt_le_sqrt (by nlinarith)
  have hs0 : √(a^2 - x^2) < √((0:ℝ)^2 + a^2) := sqrt_lt_sqrt (by nlinarith) (by nlinarith)
  have h01 : √((0:ℝ)^2 + a^2) ≤ √((1:ℝ)^2 + a^2) := sqrt_le_sqrt (by norm_num)
  have h15 : √((1:ℝ)^2 + a^2) ≤ √((5:ℝ)^2 + a^2) := sqrt_le_sqrt (by norm_num)
  have e1 := log_ratio_sub_mono ht hts hs0 h01
  have e2 := log_ratio_sub_mono ht hts (hs0.trans_le h01) h15
  have e3 := log_ratio_mono ht hts ((hs0.trans_le h01).trans_le h15)
  unfold rhoA Gfun
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

theorem Gfun_zero_eq {a x : ℝ} (hx : 0 < x) (hxa : x ≤ a) :
    Gfun a 0 x = 2 * log (a + √(a^2 - x^2)) - 2 * log x := by
  have ha : 0 < a := hx.trans_le hxa
  have hs0 : 0 ≤ √(a^2 - x^2) := sqrt_nonneg _
  have hs2 : √(a^2 - x^2) ^ 2 = a^2 - x^2 := sq_sqrt (by nlinarith)
  unfold Gfun
  rw [show (0:ℝ)^2 + a^2 = a^2 by ring, sqrt_sq ha.le]
  set s := √(a^2 - x^2)
  have hsa : s < a := by nlinarith
  rw [show (a + s) / (a - s) = (a + s)^2 / x^2 by
    rw [div_eq_div_iff (by linarith) (by positivity)]; linear_combination (a + s) * hs2]
  rw [log_div (by positivity) (by positivity), log_pow, log_pow]
  push_cast; ring

theorem continuous_Gfun {a c : ℝ} (ha : 0 < a) (hc : 0 < c) : Continuous (fun x => Gfun a c x) := by
  have hsa : ∀ x : ℝ, √(a^2 - x^2) ≤ a := fun x => by
    calc √(a^2 - x^2) ≤ √(a^2) := sqrt_le_sqrt (by nlinarith)
      _ = a := sqrt_sq ha.le
  have hU : a < √(c^2 + a^2) := by
    calc a = √(a^2) := (sqrt_sq ha.le).symm
      _ < √(c^2 + a^2) := sqrt_lt_sqrt (by positivity) (by nlinarith)
  have hden : ∀ x : ℝ, √(c^2 + a^2) - √(a^2 - x^2) ≠ 0 := fun x => by linarith [hsa x]
  have hpos : ∀ x : ℝ, (√(c^2 + a^2) + √(a^2 - x^2)) / (√(c^2 + a^2) - √(a^2 - x^2)) ≠ 0 :=
    fun x => (div_pos (by linarith [sqrt_nonneg (a^2 - x^2)]) (by linarith [hsa x])).ne'
  unfold Gfun
  exact (Continuous.div (by fun_prop) (by fun_prop) hden).log hpos

/-- The continuous part of `ρ_a` on `(0, a]`. -/
def fc (a x : ℝ) : ℝ :=
  ((1/3) * (2 * log (a + √(a^2 - x^2)) - Gfun a 1 x) + (5/3) * (Gfun a 1 x - Gfun a 5 x)
    + (4/3) * Gfun a 5 x) / (4 * π)

theorem rhoA_eq_fc {a x : ℝ} (hx : 0 < x) (hxa : x ≤ a) :
    rhoA a x = fc a x - log x / (6 * π) := by
  unfold rhoA fc
  rw [Gfun_zero_eq hx hxa]
  field_simp
  ring

theorem continuous_fc {a : ℝ} (ha : 0 < a) : Continuous (fc a) := by
  have h1 := continuous_Gfun ha one_pos
  have h5 := continuous_Gfun ha (by norm_num : (0:ℝ) < 5)
  have hl : Continuous (fun x => log (a + √(a^2 - x^2))) :=
    Continuous.log (by fun_prop) (fun x => by positivity)
  unfold fc
  fun_prop

theorem intervalIntegrable_Wt_rhoA {a : ℝ} (ha : 0 < a) :
    IntervalIntegrable (fun x => Wt x * rhoA a x) volume 0 a := by
  have hg : IntervalIntegrable (fun x => W2 x * fc a x - (1 / (6 * π)) * (W2 x * log x)) volume
    0 a :=
    ((continuous_W2.mul (continuous_fc ha)).intervalIntegrable 0 a).sub
      ((intervalIntegral.intervalIntegrable_log'.continuousOn_mul
        continuous_W2.continuousOn).const_mul _)
  refine (intervalIntegrable_congr_uIoo ?_).mpr hg
  intro x hx
  rw [Set.uIoo_of_le ha.le] at hx
  simp only
  rw [Wt_eq_W2 hx.1.le, rhoA_eq_fc hx.1 hx.2.le]
  ring

theorem Wt_mul_rhoA_nonneg {a x : ℝ} (hx : 0 ≤ x) (hxa : x ≤ a) : 0 ≤ Wt x * rhoA a x := by
  rcases hx.lt_or_eq with hx | hx
  · exact mul_nonneg (Wt_nonneg hx.le) (rhoA_nonneg hx hxa)
  · subst hx; simp [Wt_zero]

end
end Zeta32.Fstar
