/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

public import LeanPool.Zeta5Irrational.Weight
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Towards Hermite's formula at `s = 5`: the calculus ingredients

* the closed form `∑_{ℓ ≥ 1} ℓ⁴ x^ℓ = x (1 + 11x + 11x² + x³) / (1 - x)⁵` for `0 ≤ x < 1`;
* `F(y) = 1 / (e^{2πy} - 1)` and its derivatives `F₁, …, F₄` (explicit rational functions of
  `q = e^{2πy}`), with `w(y) = y⁵ F₄(y) / 12`;
* `g(y) = y⁵ / (12 (y² + a²))` and its derivatives `g₁, …, g₄`.
-/

public section

open Filter Topology Finset

namespace Zeta5Irrational

/-! ### The series `∑ ℓ⁴ x^ℓ` -/

/--
The telescoping polynomial: `(1 - x)⁵ ∑_{ℓ < N} (ℓ+1)⁴ x^{ℓ+1} = x(1+11x+11x²+x³) - x^{N+1} P(N,
x)`. -/
noncomputable def Ptel (N x : ℝ) : ℝ :=
  N ^ 4 * x ^ 4 - 4 * N ^ 4 * x ^ 3 + 6 * N ^ 4 * x ^ 2 - 4 * N ^ 4 * x + N ^ 4 -
                                  4 * N ^ 3 * x ^ 3 +
                                12 * N ^ 3 * x ^ 2 -
                              12 * N ^ 3 * x +
                            4 * N ^ 3 +
                          6 * N ^ 2 * x ^ 3 -
                        6 * N ^ 2 * x ^ 2 -
                      6 * N ^ 2 * x +
                    6 * N ^ 2 -
                  4 * N * x ^ 3 -
                12 * N * x ^ 2 +
              12 * N * x +
            4 * N +
          x ^ 3 +
        11 * x ^ 2 +
      11 * x +
    1

lemma telescope (x : ℝ) (N : ℕ) :
    (1 - x) ^ 5 * ∑ ℓ ∈ range N, ((ℓ : ℝ) + 1) ^ 4 * x ^ (ℓ + 1) =
      x * (1 + 11 * x + 11 * x ^ 2 + x ^ 3) - x ^ (N + 1) * Ptel N x := by
  induction N with
  | zero => simp [Ptel]; ring
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    unfold Ptel
    ring

lemma tendsto_pow_mul_Ptel {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun N : ℕ => x ^ (N + 1) * Ptel N x) atTop (𝓝 0) := by
  have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have h : ∀ k : ℕ, Tendsto (fun N : ℕ => (N : ℝ) ^ k * x ^ N) atTop (𝓝 0) := fun k =>
    tendsto_pow_const_mul_const_pow_of_abs_lt_one k habs
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3; have h4 := h 4
  have :
    (fun N : ℕ => x ^ (N + 1) * Ptel N x) = fun N : ℕ =>
      ((N : ℝ) ^ 4 * x ^ N) * (x ^ 5 - 4 * x ^ 4 + 6 * x ^ 3 - 4 * x ^ 2 + x) +
              ((N : ℝ) ^ 3 * x ^ N) * (-4 * x ^ 4 + 12 * x ^ 3 - 12 * x ^ 2 + 4 * x) +
            ((N : ℝ) ^ 2 * x ^ N) * (6 * x ^ 4 - 6 * x ^ 3 - 6 * x ^ 2 + 6 * x) +
          ((N : ℝ) ^ 1 * x ^ N) * (-4 * x ^ 4 - 12 * x ^ 3 + 12 * x ^ 2 + 4 * x) +
        ((N : ℝ) ^ 0 * x ^ N) * (x ^ 4 + 11 * x ^ 3 + 11 * x ^ 2 + x) :=
    by funext N; unfold Ptel; ring
  rw [this]
  simpa using
    ((((h4.mul_const _).add (h3.mul_const _)).add (h2.mul_const _)).add (h1.mul_const _)).add
      (h0.mul_const _)

/-- `∑_{ℓ ≥ 1} ℓ⁴ x^ℓ = x (1 + 11x + 11x² + x³) / (1 - x)⁵`. -/
lemma hasSum_pow_four_mul_geometric {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun ℓ : ℕ => ((ℓ : ℝ) + 1) ^ 4 * x ^ (ℓ + 1))
      (x * (1 + 11 * x + 11 * x ^ 2 + x ^ 3) / (1 - x) ^ 5) := by
  have h1x : (0 : ℝ) < (1 - x) ^ 5 := pow_pos (by linarith) 5
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun ℓ => by positivity) _).mpr ?_
  have hS :
    ∀ N : ℕ,
      ∑ ℓ ∈ range N, ((ℓ : ℝ) + 1) ^ 4 * x ^ (ℓ + 1) =
        (x * (1 + 11 * x + 11 * x ^ 2 + x ^ 3) - x ^ (N + 1) * Ptel N x) / (1 - x) ^ 5 :=
    by intro N; rw [← telescope, mul_div_cancel_left₀ _ h1x.ne']
  simp_rw [hS]
  have :=
    ((tendsto_const_nhds (x := x * (1 + 11 * x + 11 * x ^ 2 + x ^ 3))).sub
          (tendsto_pow_mul_Ptel hx0 hx1)).div_const
      ((1 - x) ^ 5)
  rw [sub_zero] at this
  exact this

/-! ### `F(y) = 1 / (e^{2πy} - 1)` and its derivatives -/

/-- `q(y) = e^{2πy}`. -/
@[expose] noncomputable def qe (y : ℝ) : ℝ :=
  Real.exp (2 * Real.pi * y)

lemma qe_pos (y : ℝ) : 0 < qe y :=
  Real.exp_pos _

lemma qe_gt_one {y : ℝ} (hy : 0 < y) : 1 < qe y := by
  unfold qe; rw [← Real.exp_zero];
  exact Real.exp_lt_exp.mpr (by positivity)

lemma hasDerivAt_qe (y : ℝ) : HasDerivAt qe (2 * Real.pi * qe y) y := by
  have h := ((hasDerivAt_id (𝕜 := ℝ) y).const_mul (2 * Real.pi)).exp
  simp only [id, mul_one] at h
  unfold qe
  refine
    HasDerivAt.congr_deriv
      (HasDerivAt.congr_of_eventuallyEq h (Filter.Eventually.of_forall fun _ => rfl)) ?_
  ring

/-- `F(y) = 1 / (e^{2πy} - 1)` and its first four derivatives. -/
@[expose] noncomputable def F0 (y : ℝ) : ℝ :=
  1 / (qe y - 1)

/-- Expression for the first derivative of `F0` on the positive half-line. -/
@[expose] noncomputable def F1 (y : ℝ) : ℝ :=
  -(2 * Real.pi) * qe y / (qe y - 1) ^ 2

/-- Expression for the second derivative of `F0` on the positive half-line. -/
@[expose] noncomputable def F2 (y : ℝ) : ℝ :=
  (2 * Real.pi) ^ 2 * qe y * (qe y + 1) / (qe y - 1) ^ 3

/-- Expression for the third derivative of `F0` on the positive half-line. -/
@[expose] noncomputable def F3 (y : ℝ) : ℝ :=
  -(2 * Real.pi) ^ 3 * qe y * (qe y ^ 2 + 4 * qe y + 1) / (qe y - 1) ^ 4

/-- Expression for the fourth derivative of `F0` on the positive half-line. -/
@[expose] noncomputable def F4 (y : ℝ) : ℝ :=
  (2 * Real.pi) ^ 4 * qe y * (qe y ^ 3 + 11 * qe y ^ 2 + 11 * qe y + 1) / (qe y - 1) ^ 5

lemma hasDerivAt_F0 {y : ℝ} (hy : 0 < y) : HasDerivAt F0 (F1 y) y := by
  have hq : qe y - 1 ≠ 0 := by have := qe_gt_one hy; linarith
  have := ((hasDerivAt_qe y).sub_const 1).inv hq
  unfold F0 F1
  simp only [one_div]
  refine
    HasDerivAt.congr_deriv
      (HasDerivAt.congr_of_eventuallyEq this (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
  field_simp

lemma hasDerivAt_F1 {y : ℝ} (hy : 0 < y) : HasDerivAt F1 (F2 y) y := by
  have hq : qe y - 1 ≠ 0 := by have := qe_gt_one hy; linarith
  have hd :=
    ((hasDerivAt_qe y).const_mul (-(2 * Real.pi))).div (((hasDerivAt_qe y).sub_const 1).pow 2)
      (pow_ne_zero 2 hq)
  unfold F1 F2
  refine
    HasDerivAt.congr_deriv
      (HasDerivAt.congr_of_eventuallyEq hd (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply]
  field_simp
  ring

lemma hasDerivAt_F2 {y : ℝ} (hy : 0 < y) : HasDerivAt F2 (F3 y) y := by
  have hq : qe y - 1 ≠ 0 := by have := qe_gt_one hy; linarith
  have hd :=
    (((hasDerivAt_qe y).const_mul ((2 * Real.pi) ^ 2)).mul ((hasDerivAt_qe y).add_const 1)).div
      (((hasDerivAt_qe y).sub_const 1).pow 3) (pow_ne_zero 3 hq)
  unfold F2 F3
  refine
    HasDerivAt.congr_deriv
      (HasDerivAt.congr_of_eventuallyEq hd (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply]
  field_simp
  ring

lemma hasDerivAt_F3 {y : ℝ} (hy : 0 < y) : HasDerivAt F3 (F4 y) y := by
  have hq : qe y - 1 ≠ 0 := by have := qe_gt_one hy; linarith
  have hd :=
    (((hasDerivAt_qe y).const_mul (-(2 * Real.pi) ^ 3)).mul
          ((((hasDerivAt_qe y).pow 2).add ((hasDerivAt_qe y).const_mul 4)).add_const 1)).div
      (((hasDerivAt_qe y).sub_const 1).pow 4) (pow_ne_zero 4 hq)
  unfold F3 F4
  refine
    HasDerivAt.congr_deriv
      (HasDerivAt.congr_of_eventuallyEq hd (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply]
  field_simp
  ring

/-- The series `wS` in closed form: `wS(y) = q (q³ + 11q² + 11q + 1) / (q - 1)⁵`. -/
lemma wS_eq {y : ℝ} (hy : 0 < y) :
    wS y = qe y * (qe y ^ 3 + 11 * qe y ^ 2 + 11 * qe y + 1) / (qe y - 1) ^ 5 := by
  set x : ℝ := Real.exp (-(2 * Real.pi * y)) with hx
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x < 1 := by
    rw [hx, ← Real.exp_zero];
    exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  have hterm :
    ∀ ℓ : ℕ,
      ((ℓ : ℝ) + 1) ^ 4 * Real.exp (-(2 * Real.pi * ((ℓ : ℝ) + 1) * y)) =
        ((ℓ : ℝ) + 1) ^ 4 * x ^ (ℓ + 1) := by
    intro ℓ
    rw [hx, ← Real.exp_nat_mul]
    congr 2
    push_cast; ring
  unfold wS
  simp_rw [hterm]
  rw [(hasSum_pow_four_mul_geometric hx0 hx1).tsum_eq]
  have hq : qe y = 1 / x := by rw [hx, qe, one_div, ← Real.exp_neg, neg_neg]
  rw [hq]
  have hxne : x ≠ 0 := (Real.exp_pos _).ne'
  have h1x : 1 - x ≠ 0 := by linarith
  field_simp
  try ring

/-- `w(y) = y⁵ F₄(y) / 12` for `y > 0`. -/
lemma w_eq_F4 {y : ℝ} (hy : 0 < y) : w y = y ^ 5 * F4 y / 12 := by
  unfold w F4
  rw [wS_eq hy]
  ring

/-! ### `g(y) = y⁵ / (12 (y² + a²))` and its derivatives -/

/-- Rational factor paired with `F4` in the Hermite integral formula. -/
@[expose] noncomputable def g0 (a y : ℝ) : ℝ :=
  y ^ 5 / (12 * (y ^ 2 + a ^ 2))

/-- First derivative of the rational factor `g0 a`, for positive `a`. -/
@[expose] noncomputable def g1 (a y : ℝ) : ℝ :=
  y ^ 4 * (5 * a ^ 2 + 3 * y ^ 2) / (12 * (y ^ 2 + a ^ 2) ^ 2)

/-- Second derivative of the rational factor `g0 a`, for positive `a`. -/
@[expose] noncomputable def g2 (a y : ℝ) : ℝ :=
  y ^ 3 * (10 * a ^ 4 + 9 * a ^ 2 * y ^ 2 + 3 * y ^ 4) / (6 * (y ^ 2 + a ^ 2) ^ 3)

/-- Third derivative of the rational factor `g0 a`, for positive `a`. -/
@[expose] noncomputable def g3 (a y : ℝ) : ℝ :=
  y ^ 2 * (10 * a ^ 6 + 5 * a ^ 4 * y ^ 2 + 4 * a ^ 2 * y ^ 4 + y ^ 6) / (2 * (y ^ 2 + a ^ 2) ^ 4)

/-- Fourth derivative of the rational factor `g0 a`, for positive `a`. -/
@[expose] noncomputable def g4 (a y : ℝ) : ℝ :=
  2 * a ^ 4 * y * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4) / (y ^ 2 + a ^ 2) ^ 5

lemma hasDerivAt_g0 {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (g0 a) (g1 a y) y := by
  have hne : 12 * (y ^ 2 + a ^ 2) ≠ 0 := by positivity
  have hd := (hasDerivAt_pow 5 y).div (((hasDerivAt_pow 2 y).add_const (a ^ 2)).const_mul 12) hne
  unfold g0 g1
  refine
    HasDerivAt.congr_deriv
      (HasDerivAt.congr_of_eventuallyEq hd (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
  field_simp
  ring

lemma hasDerivAt_g1 {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (g1 a) (g2 a y) y := by
  have hne : 12 * (y ^ 2 + a ^ 2) ^ 2 ≠ 0 := by positivity
  have hd :=
    ((hasDerivAt_pow 4 y).mul (((hasDerivAt_pow 2 y).const_mul 3).const_add (5 * a ^ 2))).div
      ((((hasDerivAt_pow 2 y).add_const (a ^ 2)).pow 2).const_mul 12) hne
  unfold g1 g2
  refine
    HasDerivAt.congr_deriv
      (HasDerivAt.congr_of_eventuallyEq hd (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply]
  field_simp
  ring

lemma hasDerivAt_g2 {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (g2 a) (g3 a y) y := by
  have hne : 6 * (y ^ 2 + a ^ 2) ^ 3 ≠ 0 := by positivity
  have hd :=
    ((hasDerivAt_pow 3 y).mul
          ((((hasDerivAt_pow 2 y).const_mul (9 * a ^ 2)).const_add (10 * a ^ 4)).add
            ((hasDerivAt_pow 4 y).const_mul 3))).div
      ((((hasDerivAt_pow 2 y).add_const (a ^ 2)).pow 3).const_mul 6) hne
  unfold g2 g3
  refine
    HasDerivAt.congr_deriv
      (HasDerivAt.congr_of_eventuallyEq hd (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply]
  field_simp
  ring

lemma hasDerivAt_g3 {a : ℝ} (ha : 0 < a) (y : ℝ) : HasDerivAt (g3 a) (g4 a y) y := by
  have hne : 2 * (y ^ 2 + a ^ 2) ^ 4 ≠ 0 := by positivity
  have hd :=
    ((hasDerivAt_pow 2 y).mul
          (((((hasDerivAt_pow 2 y).const_mul (5 * a ^ 4)).const_add (10 * a ^ 6)).add
                ((hasDerivAt_pow 4 y).const_mul (4 * a ^ 2))).add
            (hasDerivAt_pow 6 y))).div
      ((((hasDerivAt_pow 2 y).add_const (a ^ 2)).pow 4).const_mul 2) hne
  unfold g3 g4
  refine
    HasDerivAt.congr_deriv
      (HasDerivAt.congr_of_eventuallyEq hd (Filter.Eventually.of_forall fun _ => rfl)) ?_
  try simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply]
  field_simp
  ring

end Zeta5Irrational

namespace Zeta5Irrational

open MeasureTheory Set

/-! ### Bounds, integrability and the first integral `∫₀^∞ g₄ = 1/2` -/

lemma abs_g4_le {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 ≤ y) :
    |g4 a y| ≤ 10 * a ^ 3 / (y ^ 2 + a ^ 2) ^ 2 := by
  unfold g4
  have hden : 0 < y ^ 2 + a ^ 2 := by positivity
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (y ^ 2 + a ^ 2) ^ 5),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 :
    |2 * a ^ 4 * y * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4)| ≤
      2 * a ^ 4 * y * (10 * (y ^ 2 + a ^ 2) ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * a ^ 4 * y)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_le];
    constructor <;>
      nlinarith [sq_nonneg (a ^ 2 - y ^ 2), sq_nonneg y, sq_nonneg a,
        mul_nonneg (sq_nonneg a) (sq_nonneg y)]
  have h2 : y ≤ (y ^ 2 + a ^ 2) / (2 * a) := by
    rw [le_div_iff₀ (by positivity)];
    nlinarith [sq_nonneg (y - a)]
  calc
    |2 * a ^ 4 * y * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4)| * (y ^ 2 + a ^ 2) ^ 2 ≤
        2 * a ^ 4 * y * (10 * (y ^ 2 + a ^ 2) ^ 2) * (y ^ 2 + a ^ 2) ^ 2 :=
      by gcongr
    _ ≤
        2 * a ^ 4 * ((y ^ 2 + a ^ 2) / (2 * a)) * (10 * (y ^ 2 + a ^ 2) ^ 2) *
          (y ^ 2 + a ^ 2) ^ 2 :=
      by gcongr
    _ = 10 * a ^ 3 * (y ^ 2 + a ^ 2) ^ 5 := by field_simp

lemma inv_sq_add_le {a : ℝ} (ha : 0 < a) (y : ℝ) :
    1 / (y ^ 2 + a ^ 2) ≤ (1 + 1 / a ^ 2) * (1 / (1 + y ^ 2)) := by
  rw [div_le_iff₀ (by positivity)]
  have :
    (1 + 1 / a ^ 2) * (1 / (1 + y ^ 2)) * (y ^ 2 + a ^ 2) =
      (y ^ 2 + a ^ 2 + y ^ 2 / a ^ 2 + 1) / (1 + y ^ 2) :=
    by field_simp; ring
  rw [this, le_div_iff₀ (by positivity)]
  have : 0 ≤ y ^ 2 / a ^ 2 := by positivity
  nlinarith

/-- `g₄ · h` is integrable on `(0, ∞)` whenever `h` is measurable and bounded by `1/(y²+a²)`
-type control: we only need the three cases below. -/
lemma integrableOn_g4 {a : ℝ} (ha : 0 < a) : IntegrableOn (g4 a) (Ioi 0) := by
  have hg :
    IntegrableOn (fun y : ℝ => (10 * a ^ 3 / a ^ 2 * (1 + 1 / a ^ 2)) * (1 + y ^ 2)⁻¹) (Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul _).integrableOn
  have hcont : Continuous (g4 a) := by
    unfold g4
    exact
      (by fun_prop :
            Continuous fun y : ℝ => 2 * a ^ 4 * y * (5 * a ^ 4 - 10 * a ^ 2 * y ^ 2 + y ^ 4)).div
        (by fun_prop) (fun y => by positivity)
  refine hg.mono' hcont.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
  have hy : 0 < y := hy
  rw [Real.norm_eq_abs]
  calc
    |g4 a y| ≤ 10 * a ^ 3 / (y ^ 2 + a ^ 2) ^ 2 := abs_g4_le ha hy.le
    _ ≤ 10 * a ^ 3 / (a ^ 2 * (y ^ 2 + a ^ 2)) := by
      gcongr
      nlinarith [sq_nonneg y]
    _ = 10 * a ^ 3 / a ^ 2 * (1 / (y ^ 2 + a ^ 2)) := by field_simp
    _ ≤ 10 * a ^ 3 / a ^ 2 * ((1 + 1 / a ^ 2) * (1 / (1 + y ^ 2))) := by
      gcongr;
      exact inv_sq_add_le ha y
    _ = _ := by ring

lemma tendsto_g3_atTop {a : ℝ} (ha : 0 < a) : Tendsto (g3 a) atTop (𝓝 (1 / 2)) := by
  have hφ :
    Tendsto
      (fun u : ℝ =>
        (10 * a ^ 6 * u ^ 6 + 5 * a ^ 4 * u ^ 4 + 4 * a ^ 2 * u ^ 2 + 1) /
          (2 * (1 + a ^ 2 * u ^ 2) ^ 4))
      (𝓝 0) (𝓝 (1 / 2)) := by
    have :
      ContinuousAt
        (fun u : ℝ =>
          (10 * a ^ 6 * u ^ 6 + 5 * a ^ 4 * u ^ 4 + 4 * a ^ 2 * u ^ 2 + 1) /
            (2 * (1 + a ^ 2 * u ^ 2) ^ 4))
        0 :=
      by refine ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
    have h0 := this.tendsto
    simpa using h0
  have := hφ.comp tendsto_inv_atTop_zero
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  simp only [Function.comp, g3]
  field_simp

/-- `∫₀^∞ g₄(y) dy = 1/2`. -/
lemma integral_g4 {a : ℝ} (ha : 0 < a) : ∫ y in Ioi 0, g4 a y = 1 / 2 := by
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (f := g3 a) (f' := g4 a)
      (fun y _ => hasDerivAt_g3 ha y) (integrableOn_g4 ha) (tendsto_g3_atTop ha)
  rw [h]; simp [g3]

end Zeta5Irrational

namespace Zeta5Irrational

open Complex in
/-- The Mittag-Leffler expansion of `F(y) = 1/(e^{2πy} - 1)`:
`F(y) = -1/2 + 1/(2πy) + (1/π) ∑_{n ≥ 1} y/(y² + n²)`, from Mathlib's `cot_series_rep`. -/
lemma F0_series {y : ℝ} (hy : 0 < y) :
    F0 y =
      -1 / 2 + 1 / (2 * Real.pi * y) +
        (1 / Real.pi) * ∑' n : ℕ, y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) := by
  have hx : (I * (y : ℂ)) ∈ integerComplement := by
    rw [integerComplement_eq]
    rintro ⟨n, hn⟩
    have h := congrArg Complex.im hn
    simp at h
    linarith
  have h :=
    cot_series_rep
      hx
        -- the left-hand side
  have hs : Real.sinh (Real.pi * y) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have hL :
    (Real.pi : ℂ) * cot (Real.pi * (I * y)) =
      -I * ((Real.pi * (Real.cosh (Real.pi * y) / Real.sinh (Real.pi * y)) : ℝ) : ℂ) := by
    rw [cot_eq_cos_div_sin,
      show (Real.pi : ℂ) * (I * y) = ((Real.pi * y : ℝ) : ℂ) * I by push_cast; ring, cos_mul_I,
      sin_mul_I, ← ofReal_cosh, ← ofReal_sinh]
    have hs' : (Real.sinh (Real.pi * y) : ℂ) ≠ 0 := by exact_mod_cast hs
    push_cast
    field_simp
    ring_nf
    simp [I_sq]
      -- the right-hand side
  have hR :
    (1 / (I * (y : ℂ)) + ∑' n : ℕ+, (1 / (I * y - n) + 1 / (I * y + n))) =
      -I * ((1 / y + ∑' n : ℕ, 2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
    have hterm :
      ∀ n : ℕ+,
        (1 / (I * (y : ℂ) - n) + 1 / (I * y + n)) =
          -I * ((2 * y / (y ^ 2 + ((n : ℕ) : ℝ) ^ 2) : ℝ) : ℂ) := by
      intro n
      have h1 : I * (y : ℂ) - n ≠ 0 := by
        intro h; have := congrArg Complex.im h; simp at this;
        linarith
      have h2 : I * (y : ℂ) + n ≠ 0 := by
        intro h; have := congrArg Complex.im h; simp at this;
        linarith
      have h3 : ((y : ℂ) ^ 2 + ((n : ℕ) : ℂ) ^ 2) ≠ 0 := by
        have : (0 : ℝ) < y ^ 2 + ((n : ℕ) : ℝ) ^ 2 := by positivity
        exact_mod_cast this.ne'
      push_cast
      rw [div_add_div _ _ h1 h2, div_eq_iff (mul_ne_zero h1 h2)]
      have hIy : (I * (y : ℂ) - n) * (I * y + n) = -((y : ℂ) ^ 2 + ((n : ℕ) : ℂ) ^ 2) := by
        ring_nf; rw [I_sq]; ring
      rw [hIy]
      field_simp
      ring
    simp_rw [hterm]
    rw [tsum_mul_left,
      tsum_pnat_eq_tsum_succ (f := fun m : ℕ => ((2 * y / (y ^ 2 + (m : ℝ) ^ 2) : ℝ) : ℂ))]
    push_cast
    rw [one_div, mul_inv, Complex.inv_I]
    ring
  rw [hL, hR] at h
  have hI : (-I : ℂ) ≠ 0 := by simp
  have h' := mul_left_cancel₀ hI h
  have hreal :
    Real.pi * (Real.cosh (Real.pi * y) / Real.sinh (Real.pi * y)) =
      1 / y + ∑' n : ℕ, 2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) := by
    exact_mod_cast
      h'
        -- `cosh/sinh = 1 + 2 F₀`
  have hcoth : Real.cosh (Real.pi * y) / Real.sinh (Real.pi * y) = 1 + 2 * F0 y := by
    rw [Real.cosh_eq, Real.sinh_eq, F0, qe]
    have hq : Real.exp (2 * Real.pi * y) = Real.exp (Real.pi * y) ^ 2 := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hq1 : Real.exp (2 * Real.pi * y) - 1 ≠ 0 := by
      have := qe_gt_one hy; unfold qe at this;
      linarith
    have he : Real.exp (-(Real.pi * y)) = 1 / Real.exp (Real.pi * y) := by
      rw [Real.exp_neg, one_div]
    rw [he]
    have hpos : Real.exp (Real.pi * y) ≠ 0 := (Real.exp_pos _).ne'
    rw [hq] at hq1 ⊢
    field_simp
    ring
  rw [hcoth] at hreal
  have hsum :
    ∑' n : ℕ, 2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) =
      2 * ∑' n : ℕ, y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) :=
    by rw [← tsum_mul_left]; congr 1; funext n; ring
  rw [hsum] at hreal
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  set S := ∑' n : ℕ, y / (y ^ 2 + ((n : ℝ) + 1) ^ 2) with hS
  have h2 : F0 y = (1 / y + 2 * S) / (2 * Real.pi) - 1 / 2 := by
    field_simp at hreal ⊢
    linear_combination hreal
  rw [h2]
  field_simp
  ring

end Zeta5Irrational
