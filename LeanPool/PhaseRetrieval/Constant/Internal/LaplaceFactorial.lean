/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # LaplaceFactorial.lean
  Laplace/Stirling-type bounds for factorials via saddle-point estimates.
  Scaffolding notes: ElementaryLemmas/laplace_factorial.md

  Dependencies: Mathlib only

  Public API:
  - `rStar`              (r_n = √(n + 1/2))
  - `phiFunc`            (φ_n(r) = (2n+1) log r − r²)
  - `phiFunc_concavity`  (Theorem 2.7)
  - `phiFunc_quad_bound` (Theorem 2.8)
  - `exp_phi_le_factorial` (Theorem 2.9)
  - `monomial_integral_bound` (Corollary 2.10)
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.Parity

/-! # LaplaceFactorial -/


open Real MeasureTheory Set

noncomputable section

namespace FockSPR

/-! ## Definitions -/

/-- `r_n = √(n + 1/2)`, the saddle point of `φ_n`. -/
def rStar (n : ℕ) : ℝ := Real.sqrt (n + 1 / 2)

/-- `φ_n(r) = (2n + 1) log(r) − r²` for `r > 0`.
Note: `r^{2n+1} exp(−r²) = exp(φ_n(r))`. -/
def phiFunc (n : ℕ) (r : ℝ) : ℝ := (2 * n + 1) * Real.log r - r ^ 2

/-! ## Private lemmas -/

private lemma rStar_sq {n : ℕ} : (rStar n) ^ 2 = ↑n + 1 / 2 := by
  unfold rStar; rw [sq]; exact Real.mul_self_sqrt (by positivity)

/-- `r_n > 1` for `n ≥ 1`. -/
private lemma rStar_gt_one {n : ℕ} (hn : 1 ≤ n) : rStar n > 1 := by
  unfold rStar
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ < Real.sqrt (↑n + 1 / 2) := Real.sqrt_lt_sqrt (by norm_num)
        (by have : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn; linarith)

private lemma rStar_pos {n : ℕ} (hn : 1 ≤ n) : 0 < rStar n :=
  lt_trans one_pos (rStar_gt_one hn)

/-- The derivative `φ_n'(r) = (2n+1)/r − 2r` as a `HasDerivAt` statement. -/
private lemma hasDerivAt_phiFunc (n : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (phiFunc n) ((2 * ↑n + 1) / r - 2 * r) r := by
  unfold phiFunc
  have h1 := (Real.hasDerivAt_log (ne_of_gt hr)).const_mul (2 * ↑n + 1 : ℝ)
  have h2 : HasDerivAt (fun r => r ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have h3 := h1.sub h2
  rw [show (2 * (n : ℝ) + 1) / r - 2 * r = (2 * ↑n + 1) * r⁻¹ - 2 * r by
    rw [div_eq_mul_inv]]
  exact h3

/-- Derivative: `φ_n'(r) = (2n+1)/r − 2r`, vanishing at `r = r_n`. -/
private lemma phiFunc_deriv {n : ℕ} (_hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (phiFunc n) ((2 * ↑n + 1) / r - 2 * r) r :=
  hasDerivAt_phiFunc n hr

/-! ## Theorem 2.7: Concavity of φ_n

`φ_n''(r) = −(2n+1)/r² − 2 ≤ −2` for `r > 0`.
In particular, `φ_n` is strictly concave on `(0, ∞)`.
-/
theorem phiFunc_concavity {n : ℕ} (hn : 1 ≤ n) :
    StrictConcaveOn ℝ (Ioi 0) (phiFunc n) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
  · unfold phiFunc
    apply ContinuousOn.sub
    · apply ContinuousOn.mul continuousOn_const
      exact Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)
    · exact continuousOn_pow 2
  · rw [interior_Ioi]
    intro a ha b hb hab
    have ha' : (0 : ℝ) < a := ha
    have hb' : (0 : ℝ) < b := hb
    rw [(hasDerivAt_phiFunc n ha').deriv, (hasDerivAt_phiFunc n hb').deriv]
    have hnn : (0 : ℝ) < 2 * ↑n + 1 := by positivity
    linarith [div_lt_div_of_pos_left hnn ha' hab]

/-! ## Theorem 2.8: Quadratic upper bound

`φ_n(r) ≤ φ_n(r_n) − (r − r_n)²` for all `n ≥ 1`, `r > 0`.

**Proof**: Define `h(r) = φ_n(r) + (r − r_n)²`. Then `h'(r) = (2n+1)/r − 2r_n`,
which is strictly decreasing and vanishes at `r_n`. By concavity of `h`,
`h(r) ≤ h(r_n) = φ_n(r_n)` for all `r > 0`.
-/

/-- Auxiliary: `h(r) = φ_n(r) + (r − r_n)²`. -/
private def hFunc (n : ℕ) (r : ℝ) : ℝ := phiFunc n r + (r - rStar n) ^ 2

private lemma hasDerivAt_hFunc (n : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (hFunc n) ((2 * ↑n + 1) / r - 2 * rStar n) r := by
  unfold hFunc
  have hsq : HasDerivAt (fun r => (r - rStar n) ^ 2) (2 * (r - rStar n)) r := by
    have h : HasDerivAt (fun x : ℝ => (x - rStar n) ^ 2)
        ((2 : ℕ) * (r - rStar n) ^ (2 - 1) * (1 - 0)) r :=
      ((hasDerivAt_id r).sub (hasDerivAt_const r (rStar n))).pow 2
    have hval : ((2 : ℕ) : ℝ) * (r - rStar n) ^ (2 - 1) * (1 - 0)
        = 2 * (r - rStar n) := by
      norm_num
    rwa [hval] at h
  have hadd := (hasDerivAt_phiFunc n hr).add hsq
  rw [show ((2 * ↑n + 1) / r - 2 * r) + 2 * (r - rStar n)
      = (2 * (↑n : ℝ) + 1) / r - 2 * rStar n by ring] at hadd
  exact hadd

private lemma hFunc_deriv_val {n : ℕ} (_hn : 1 ≤ n) :
    (2 * ↑n + 1 : ℝ) / rStar n - 2 * rStar n = 0 := by
  have : (2 * ↑n + 1 : ℝ) = 2 * (rStar n) ^ 2 := by rw [rStar_sq]; ring
  rw [this]; field_simp; ring

private lemma hFunc_deriv_eq_zero {n : ℕ} (hn : 1 ≤ n) :
    HasDerivAt (hFunc n) 0 (rStar n) := by
  rw [show (0 : ℝ) = (2 * ↑n + 1 : ℝ) / rStar n - 2 * rStar n from
    (hFunc_deriv_val hn).symm]
  exact hasDerivAt_hFunc n (rStar_pos hn)

private lemma hFunc_concaveOn {n : ℕ} (hn : 1 ≤ n) :
    ConcaveOn ℝ (Ioi 0) (hFunc n) := by
  apply (StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0) _ _).concaveOn
  · unfold hFunc phiFunc
    exact ((continuousOn_const.mul
      (Real.continuousOn_log.mono (fun x hx => ne_of_gt hx))).sub
      (continuousOn_pow 2)).add ((continuousOn_id.sub continuousOn_const).pow 2)
  · rw [interior_Ioi]
    intro a ha b hb hab
    rw [(hasDerivAt_hFunc n (show (0:ℝ) < a from ha)).deriv,
        (hasDerivAt_hFunc n (show (0:ℝ) < b from hb)).deriv]
    linarith [div_lt_div_of_pos_left
      (show (0 : ℝ) < 2 * ↑n + 1 from by positivity)
      (show (0:ℝ) < a from ha) hab]

private lemma hFunc_le {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    hFunc n r ≤ hFunc n (rStar n) := by
  rcases lt_trichotomy r (rStar n) with hlt | heq | hgt
  · exact (slope_nonneg_iff_of_le hlt.le).mp
      ((hFunc_concaveOn hn).le_slope_of_hasDerivAt
        (show r ∈ Ioi 0 from hr) (show rStar n ∈ Ioi 0 from rStar_pos hn)
        hlt (hFunc_deriv_eq_zero hn))
  · rw [heq]
  · exact (slope_nonpos_iff_of_le hgt.le).mp
      ((hFunc_concaveOn hn).slope_le_of_hasDerivAt
        (show rStar n ∈ Ioi 0 from rStar_pos hn) (show r ∈ Ioi 0 from hr)
        hgt (hFunc_deriv_eq_zero hn))

theorem phiFunc_quad_bound {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    phiFunc n r ≤ phiFunc n (rStar n) - (r - rStar n) ^ 2 := by
  have h := hFunc_le hn hr
  unfold hFunc at h
  linarith [sq_nonneg (r - rStar n)]

/-! ## Theorem 2.9: Factorial upper bound on exp(φ_n(r_n))

`exp(φ_n(r_n)) ≤ exp(1/4) * n! / 2` for all `n ≥ 1`.

**Proof** (via Stirling's lower bound):
We show `φ_n(r_n) ≤ log(n!) − log 2 + 1/4` by combining:
1. `φ_n(r_n) = (n+1/2) log(n+1/2) − (n+1/2) ≤ n log n + (1/2) log n − n + 1/4`
   (using `log(1+x) ≤ x` and `n ≥ 1`)
2. Stirling: `n log n − n + (1/2) log n + (1/2) log(2π) ≤ log(n!)`
3. `(1/2) log(2π) ≥ log 2` (since `π ≥ 2`)
-/

private lemma phiFunc_rStar (n : ℕ) : phiFunc n (rStar n) =
    ((n : ℝ) + 1 / 2) * Real.log ((n : ℝ) + 1 / 2) - ((n : ℝ) + 1 / 2) := by
  unfold phiFunc rStar
  rw [Real.log_sqrt (by positivity : (0:ℝ) ≤ ↑n + 1 / 2),
      sq, Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ ↑n + 1 / 2)]
  ring

private lemma phiFunc_rStar_le {n : ℕ} (hn : 1 ≤ n) :
    phiFunc n (rStar n) ≤
    (n : ℝ) * Real.log (n : ℝ) + (1 / 2) * Real.log (n : ℝ) - (n : ℝ) + 1 / 4 := by
  rw [phiFunc_rStar]
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have h1 : (0 : ℝ) < 1 + 1 / (2 * (n : ℝ)) := by positivity
  have h_expand : ((n : ℝ) + 1 / 2) * Real.log ((n : ℝ) + 1 / 2) =
      (n : ℝ) * Real.log (n : ℝ) + (1 / 2) * Real.log (n : ℝ) +
      ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / (2 * (n : ℝ))) := by
    rw [show (n : ℝ) + 1 / 2 = (n : ℝ) * (1 + 1 / (2 * (n : ℝ))) from by field_simp,
        Real.log_mul (ne_of_gt hn_pos) (ne_of_gt h1)]
    ring_nf; rw [mul_inv_cancel₀ (ne_of_gt hn_pos)]; ring
  have h_log_bound : ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / (2 * (n : ℝ))) ≤ 3 / 4 := by
    calc ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / (2 * (n : ℝ)))
        ≤ ((n : ℝ) + 1 / 2) * (1 / (2 * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (by linarith [Real.log_le_sub_one_of_pos h1]) (by linarith)
      _ = 1 / 2 + 1 / (4 * (n : ℝ)) := by field_simp; ring
      _ ≤ 3 / 4 := by
          linarith [div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
            (by norm_num : (0:ℝ) < 4)
            (show (4:ℝ) ≤ 4 * (n:ℝ) from by
              nlinarith [show (1:ℝ) ≤ (n:ℝ) from by exact_mod_cast hn])]
  linarith [h_expand]

private lemma stirling_log_bound {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log (n : ℝ) + (1 / 2) * Real.log (n : ℝ) - (n : ℝ) ≤
    Real.log (n.factorial : ℝ) - Real.log 2 := by
  have h_stirling := @Stirling.le_log_factorial_stirling n (by omega)
  have h_pi : Real.log 2 ≤ (1 / 2) * Real.log (2 * π) := by
    have : Real.log 4 ≤ Real.log (2 * π) :=
      Real.log_le_log (by norm_num) (by linarith [Real.two_le_pi])
    linarith [show Real.log 4 = 2 * Real.log 2 from by
      rw [show (4:ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
      simp only [Nat.cast_ofNat]]
  linarith

theorem exp_phi_le_factorial {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (phiFunc n (rStar n)) ≤
    Real.exp (1 / 4) * (Nat.factorial n : ℝ) / 2 := by
  have h3 : phiFunc n (rStar n) ≤
      Real.log (n.factorial : ℝ) - Real.log 2 + 1 / 4 := by
    linarith [phiFunc_rStar_le hn, stirling_log_bound hn]
  have h_fact_pos : (0 : ℝ) < (n.factorial : ℝ) :=
    Nat.cast_pos.mpr n.factorial_pos
  calc Real.exp (phiFunc n (rStar n))
      ≤ Real.exp (Real.log (n.factorial : ℝ) - Real.log 2 + 1 / 4) :=
        Real.exp_le_exp.mpr h3
    _ = Real.exp (1 / 4 + Real.log ((n.factorial : ℝ) / 2)) := by
        congr 1
        rw [Real.log_div (ne_of_gt h_fact_pos) (by norm_num)]
        ring
    _ = Real.exp (1 / 4) * ((n.factorial : ℝ) / 2) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
    _ = Real.exp (1 / 4) * (n.factorial : ℝ) / 2 := by ring

/-! ## Corollary 2.10: Monomial integral upper bound

For `n ≥ 1` and integer `j ≥ 0`:
  `∫_j^{j+1} r^{2n+1} exp(−r²) dr ≤ (exp(1/4) * n!/2) * exp(−dist(r_n, [j, j+1])²)`

where `dist(r_n, [j, j+1]) = max(j − r_n, r_n − (j+1), 0)`.

**Proof**: By Theorem 2.8: `r^{2n+1} exp(−r²) = exp(φ_n(r)) ≤ exp(φ_n(r_n)) exp(−(r−r_n)²)`.
For `r ∈ [j, j+1]`: `|r − r_n| ≥ dist(r_n, [j,j+1])`, so `exp(−(r−r_n)²) ≤ exp(−dist(…)²)`.
Integrating over an interval of length 1 and applying Theorem 2.9.
-/

/-- Distance from a point to a closed interval `[j, j+1]`. -/
def distToInterval (x : ℝ) (j : ℕ) : ℝ :=
  max (max ((j : ℝ) - x) (x - (j + 1 : ℝ))) 0

private lemma distToInterval_nonneg (x : ℝ) (j : ℕ) : 0 ≤ distToInterval x j :=
  le_max_right _ _

private lemma distToInterval_le_abs_sub (x r : ℝ) (j : ℕ)
    (hrj : (j : ℝ) ≤ r) (hrj1 : r ≤ (j : ℝ) + 1) :
    distToInterval x j ≤ |r - x| := by
  unfold distToInterval
  exact max_le
    (max_le (by linarith [le_abs_self (r - x)]) (by linarith [neg_le_abs (r - x)]))
    (abs_nonneg _)

private lemma distToInterval_sq_le_sq (x r : ℝ) (j : ℕ)
    (hrj : (j : ℝ) ≤ r) (hrj1 : r ≤ (j : ℝ) + 1) :
    distToInterval x j ^ 2 ≤ (r - x) ^ 2 := by
  have h1 := distToInterval_le_abs_sub x r j hrj hrj1
  have h2 := distToInterval_nonneg x j
  calc distToInterval x j ^ 2
      ≤ |r - x| ^ 2 := by nlinarith [sq_nonneg (|r - x| - distToInterval x j)]
    _ = (r - x) ^ 2 := sq_abs _

/-- Pointwise integrand bound for `r ∈ [j, j+1]`. -/
private lemma pointwise_bound {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    {j : ℕ} (hrj : (j : ℝ) ≤ r) (hrj1 : r ≤ (j : ℝ) + 1) :
    r ^ (2 * n + 1) * Real.exp (-r ^ 2) ≤
    Real.exp (1 / 4) * (Nat.factorial n : ℝ) / 2 *
      Real.exp (-(distToInterval (rStar n) j) ^ 2) := by
  by_cases hr : r = 0
  · subst hr
    simp only [zero_pow (by omega : 2 * n + 1 ≠ 0), zero_mul]
    positivity
  · have hr_pos : 0 < r :=
      lt_of_le_of_ne (le_trans (Nat.cast_nonneg j) hrj) (Ne.symm hr)
    have h_eq : r ^ (2 * n + 1) * Real.exp (-r ^ 2) = Real.exp (phiFunc n r) := by
      unfold phiFunc
      have : r ^ (2 * n + 1) = Real.exp ((2 * ↑n + 1 : ℝ) * Real.log r) := by
        rw [← Real.exp_log hr_pos, ← Real.exp_nsmul]
        simp only [nsmul_eq_mul, Real.log_exp, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat, Nat.cast_one]
      rw [this, ← Real.exp_add]; ring_nf
    rw [h_eq]
    calc Real.exp (phiFunc n r)
        ≤ Real.exp (phiFunc n (rStar n) - distToInterval (rStar n) j ^ 2) :=
          Real.exp_le_exp.mpr
            (by linarith [phiFunc_quad_bound hn hr_pos,
                distToInterval_sq_le_sq (rStar n) r j hrj hrj1])
      _ = Real.exp (phiFunc n (rStar n)) *
          Real.exp (-(distToInterval (rStar n) j ^ 2)) := by
          rw [sub_eq_add_neg, Real.exp_add]
      _ ≤ (Real.exp (1 / 4) * ↑n.factorial / 2) *
          Real.exp (-(distToInterval (rStar n) j ^ 2)) :=
          mul_le_mul_of_nonneg_right (exp_phi_le_factorial hn)
            (le_of_lt (Real.exp_pos _))
      _ = Real.exp (1 / 4) * ↑n.factorial / 2 *
          Real.exp (-(distToInterval (rStar n) j) ^ 2) := by ring

theorem monomial_integral_bound {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    ∫ r in (j : ℝ)..(j + 1 : ℝ), r ^ (2 * n + 1) * Real.exp (-r ^ 2) ≤
      Real.exp (1 / 4) * (Nat.factorial n : ℝ) / 2 *
        Real.exp (-(distToInterval (rStar n) j) ^ 2) := by
  set C := Real.exp (1 / 4) * (Nat.factorial n : ℝ) / 2 *
    Real.exp (-(distToInterval (rStar n) j) ^ 2)
  have h_const : ∫ r in (j : ℝ)..(↑j + 1), C = C := integral_const_on_unit_interval
  rw [← h_const]
  apply intervalIntegral.integral_mono_on (by linarith : (j : ℝ) ≤ ↑j + 1)
  · apply ContinuousOn.intervalIntegrable
    exact (continuousOn_pow _).mul
      ((Real.continuous_exp.comp
        (continuous_neg.comp (continuous_pow 2))).continuousOn)
  · exact ContinuousOn.intervalIntegrable continuousOn_const
  · intro r hr
    exact pointwise_bound hn hr.1 hr.2

end FockSPR
