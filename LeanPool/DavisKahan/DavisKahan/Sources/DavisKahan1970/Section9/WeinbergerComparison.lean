/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.NumericalBounds

/-!
# Davis--Kahan 1970, Section 9: Weinberger comparison

This file formalizes the Lehmann/arrowhead lower-root half of the historical
comparison, together with the algebraic conversion from a *supplied*
Weinberger sine-square estimate to the tangent-square bounds printed in (9.8).
It does not derive the Weinberger angle estimate from independent scalar
eigenvalue lower bounds: for the second vector in a cluster that implication is
false without the coupled variational information retained by Weinberger's
argument.  See `WeinbergerAngle.lean` for the executable boundary and the
counterexample that fixes it.

The exact comparison roots are certified directly below.  The source's
pre-(9.8) asymptotic display is not accepted on faith: the theorem
`printed_weinberger_low_shift_inequality_reversed` proves that its leading
strict inequality is actually reversed at the lower root throughout the
printed parameter range.  The source assertion must therefore be treated as a
formal refutation obligation rather than as an omitted proof.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section9

/-- The symmetric three-by-three arrowhead data used in the comparison with
Weinberger and Lehmann. -/
structure ArrowheadThreeByThree where
  diagonal₀ : ℝ
  diagonal₁ : ℝ
  tail : ℝ
  coupling₀ : ℝ
  coupling₁ : ℝ

namespace ArrowheadThreeByThree

/-- Characteristic polynomial of the arrowhead matrix, evaluated at `lam`. -/
def charAt (M : ArrowheadThreeByThree) (lam : ℝ) : ℝ :=
  (M.diagonal₀ - lam) * (M.diagonal₁ - lam) * (M.tail - lam)
    - M.coupling₀ ^ 2 * (M.diagonal₁ - lam)
    - M.coupling₁ ^ 2 * (M.diagonal₀ - lam)

end ArrowheadThreeByThree

/-- The exact comparison matrix from Section 9. -/
noncomputable def weinbergerComparisonMatrix (ε : ℝ) : ArrowheadThreeByThree where
  diagonal₀ := ritzLow ε
  diagonal₁ := ritzHigh ε
  tail := 500
  coupling₀ := ε * (Real.sqrt 30 / 30)
  coupling₁ := ε * (Real.sqrt 30 / 30)

/-- Entries of the Weinberger comparison matrix. -/
lemma weinbergerComparisonMatrix_charAt (ε lam : ℝ) :
    (weinbergerComparisonMatrix ε).charAt lam =
      (ritzLow ε - lam) * (ritzHigh ε - lam) * (500 - lam)
        - (ε ^ 2 / 30) * (ritzHigh ε - lam)
        - (ε ^ 2 / 30) * (ritzLow ε - lam) := by
  have hs : Real.sqrt (30 : ℝ) ^ 2 = 30 := Real.sq_sqrt (by norm_num)
  unfold weinbergerComparisonMatrix ArrowheadThreeByThree.charAt
  dsimp
  -- the two sides differ only by `(ε * (√30 / 30)) ^ 2` versus `ε ^ 2 / 30`,
  -- multiplied against each of the two shifted diagonal entries
  linear_combination
    (-(ε ^ 2) / 900 * (ritzHigh ε - lam + (ritzLow ε - lam))) * hs

/-- A certified pair of lower roots for the comparison matrix.  This is the
precise boundary replacing the informal fourth-order expansion in the source
discussion. -/
structure WeinbergerLowerRootCertificate (ε : ℝ) where
  lower₀ : ℝ
  lower₁ : ℝ
  ordered : lower₀ ≤ lower₁
  lower₀_is_root : (weinbergerComparisonMatrix ε).charAt lower₀ = 0
  lower₁_is_root : (weinbergerComparisonMatrix ε).charAt lower₁ = 0
  lower₀_le_ritz : lower₀ ≤ ritzLow ε
  lower₁_le_ritz : lower₁ ≤ ritzHigh ε
  lower₁_lt_tail : lower₁ < 500

/-- Weinberger's sine-square estimate algebraically implies the corresponding
tangent-square estimate. -/
theorem tangent_sq_le_of_weinberger_sine_sq
    {s alphaCheck alphaHat gap : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hcheck : alphaCheck ≤ alphaHat) (hhat : alphaHat < gap)
    (hweinberger : s ^ 2 ≤
      (alphaHat - alphaCheck) / (gap - alphaCheck)) :
    s ^ 2 / (1 - s ^ 2) ≤
      (alphaHat - alphaCheck) / (gap - alphaHat) := by
  have hgapCheck : 0 < gap - alphaCheck := by linarith
  have hgapHat : 0 < gap - alphaHat := by linarith
  have hsden : 0 < 1 - s ^ 2 := by nlinarith [sq_nonneg s]
  have hcross : s ^ 2 * (gap - alphaCheck) ≤ alphaHat - alphaCheck :=
    (le_div_iff₀ hgapCheck).mp hweinberger
  apply (div_le_div_iff₀ hsden hgapHat).2
  nlinarith

/-- Exact normalized envelope for the first historical comparison bound. -/
noncomputable def weinbergerLowerTangentExactBound (ε : ℝ) : ℝ :=
  ((Real.sqrt 15 / 15) / 500 * ε) /
    (1 - (ritzLowCoefficient / 500) * ε)

/-- Exact normalized envelope for the second historical comparison bound. -/
noncomputable def weinbergerUpperTangentExactBound (ε : ℝ) : ℝ :=
  tangentThetaExactBound ε

private theorem historical_ratio_bound
    {ε c C : ℝ} (hε : 0 < ε)
    (hc : c ≤ C) (hC : C * ε < 1) :
    (((Real.sqrt 15 / 15) / 500) * ε) / (1 - c * ε) <
      ((1291 : ℝ) / 2500000 * ε) / (1 - C * ε) := by
  have hs15 : Real.sqrt 15 < (3873 : ℝ) / 1000 := by
    nlinarith [Real.sqrt_nonneg (15 : ℝ),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)]
  have ha : (Real.sqrt 15 / 15) / 500 < (1291 : ℝ) / 2500000 := by
    nlinarith
  have hdC : 0 < 1 - C * ε := by linarith
  have hdc : 0 < 1 - c * ε := by nlinarith
  have hfirst :
      (((Real.sqrt 15 / 15) / 500) * ε) / (1 - c * ε) <
        ((1291 : ℝ) / 2500000 * ε) / (1 - c * ε) := by
    apply div_lt_div_of_pos_right _ hdc
    exact mul_lt_mul_of_pos_right ha hε
  have hden : 1 - C * ε ≤ 1 - c * ε := by nlinarith
  have hnum0 : 0 ≤ (1291 : ℝ) / 2500000 * ε := by positivity
  have hsecond :
      ((1291 : ℝ) / 2500000 * ε) / (1 - c * ε) ≤
        ((1291 : ℝ) / 2500000 * ε) / (1 - C * ε) := by
    apply (div_le_div_iff₀ hdc hdC).2
    exact mul_le_mul_of_nonneg_left hden hnum0
  exact hfirst.trans_le hsecond

/-- First line of equation (9.8), conditional on the exact comparison bound. -/
theorem equation_9_8_lower
    (ε tanPhi₁ : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    (h : tanPhi₁ ≤ weinbergerLowerTangentExactBound ε) :
    tanPhi₁ <
      ((1291 : ℝ) / 2500000 * ε) /
        (1 - (4227 : ℝ) / 10000000 * ε) := by
  apply h.trans_lt
  unfold weinbergerLowerTangentExactBound
  apply historical_ratio_bound hε
  · nlinarith [ritzLowCoefficient_lt_printed]
  · nlinarith

/-- Second line of equation (9.8), conditional on the exact comparison bound. -/
theorem equation_9_8_upper
    (ε tanPhi₂ : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    (h : tanPhi₂ ≤ weinbergerUpperTangentExactBound ε) :
    tanPhi₂ <
      ((1291 : ℝ) / 2500000 * ε) /
        (1 - (7887 : ℝ) / 5000000 * ε) := by
  apply h.trans_lt
  unfold weinbergerUpperTangentExactBound
  exact tangentThetaExactBound_lt_printed ε hε hε100

/-! ## The certified low roots exist

The file's own interface note says that certified roots of the exact
characteristic polynomial are "the correct future interface" replacing the
paper's informal fourth-order expansion.  Here they are constructed, by the
intermediate value theorem applied at three explicit points:

* `charAt (ritzLow ε) = -(ε²/30)(ritzHigh ε - ritzLow ε) < 0`;
* `charAt (ritzHigh ε) = +(ε²/30)(ritzHigh ε - ritzLow ε) > 0`;
* `charAt (ritzLow ε - ε²/7500) ≥ 0`.

The third point is what makes the comparison quantitative: the low root sits
within `ε²/7500` of the lower Ritz value, and that is exactly the margin the
first line of (9.8) needs. -/

private lemma sqrt_three_gt : (17 : ℝ) / 10 < Real.sqrt 3 := by
  nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private lemma ritzLowCoefficient_pos : 0 < ritzLowCoefficient := by
  unfold ritzLowCoefficient
  nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
    sqrt_three_gt]

private lemma continuous_charAt (ε : ℝ) :
    Continuous fun lam => (weinbergerComparisonMatrix ε).charAt lam := by
  have h : (fun lam => (weinbergerComparisonMatrix ε).charAt lam)
      = fun lam => (ritzLow ε - lam) * (ritzHigh ε - lam) * (500 - lam)
        - (ε ^ 2 / 30) * (ritzHigh ε - lam) - (ε ^ 2 / 30) * (ritzLow ε - lam) := by
    funext lam
    exact weinbergerComparisonMatrix_charAt ε lam
  rw [h]
  fun_prop

/-- The Weinberger comparison polynomial is negative at the lower Ritz value. -/
lemma charAt_ritzLow (ε : ℝ) :
    (weinbergerComparisonMatrix ε).charAt (ritzLow ε)
      = -((ε ^ 2 / 30) * (ritzHigh ε - ritzLow ε)) := by
  rw [weinbergerComparisonMatrix_charAt]
  ring

/-- ... and positive at the upper one. -/
lemma charAt_ritzHigh (ε : ℝ) :
    (weinbergerComparisonMatrix ε).charAt (ritzHigh ε)
      = (ε ^ 2 / 30) * (ritzHigh ε - ritzLow ε) := by
  rw [weinbergerComparisonMatrix_charAt]
  ring

/-- **The certified low roots of the exact comparison matrix exist**, and the
lower one is within `ε²/7500` of the lower Ritz value.

Constructed by the intermediate value theorem at three explicit points; no
asymptotic expansion is used or needed.  The quantitative margin is what the
first line of (9.8) consumes. -/
theorem exists_weinbergerLowerRootCertificate (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    ∃ C : WeinbergerLowerRootCertificate ε,
      ritzLow ε - ε ^ 2 / 7500 ≤ C.lower₀ ∧
        ritzHigh ε - ε ^ 2 / 7500 ≤ C.lower₁ := by
  classical
  set a : ℝ := ritzLow ε with ha
  set b : ℝ := ritzHigh ε with hb
  set t : ℝ := ε ^ 2 / 7500 with ht
  have hc0 : 0 < ritzLowCoefficient := ritzLowCoefficient_pos
  have hc1 : ritzLowCoefficient < (4227 : ℝ) / 20000 := ritzLowCoefficient_lt_printed
  have hapos : 0 < a := by rw [ha, ritzLow]; positivity
  have halt : a < 25 := by
    rw [ha, ritzLow]
    nlinarith
  have hgap : ε * (Real.sqrt 3 / 3) = b - a := (ritzHigh_sub_ritzLow ε).symm
  have hgappos : ε * (17 / 30 : ℝ) ≤ b - a := by
    rw [← hgap]
    nlinarith [sqrt_three_gt]
  have hab : a < b := by nlinarith
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have hc1pos : 0 < ritzHighCoefficient := by
    unfold ritzHighCoefficient
    positivity
  have hblt : b < 100 := by
    rw [hb, ritzHigh]
    nlinarith [ritzHighCoefficient_lt_printed]
  have htpos : 0 < t := by rw [ht]; positivity
  -- the three sign evaluations
  have hva : (weinbergerComparisonMatrix ε).charAt a ≤ 0 := by
    rw [ha, charAt_ritzLow]
    nlinarith
  have hvb : 0 ≤ (weinbergerComparisonMatrix ε).charAt b := by
    rw [hb, charAt_ritzHigh]
    nlinarith
  have hkey : 500 * t ≤ 150 * (b - a) := by
    rw [ht]
    nlinarith
  have hvat : 0 ≤ (weinbergerComparisonMatrix ε).charAt (a - t) := by
    rw [weinbergerComparisonMatrix_charAt, ← ha, ← hb]
    have hk : ε ^ 2 / 30 = 250 * t := by rw [ht]; ring
    have hgoal : (a - (a - t)) * (b - (a - t)) * (500 - (a - t))
          - ε ^ 2 / 30 * (b - (a - t)) - ε ^ 2 / 30 * (a - (a - t))
        = t * (b - a + t) * (500 - a + t) - 250 * t * (b - a) - 500 * t * t := by
      rw [hk]; ring
    rw [hgoal]
    have hA : t * (b - a) * 400 ≤ t * (b - a + t) * (500 - a + t) := by
      refine mul_le_mul ?_ (by linarith) (by norm_num) (by positivity)
      nlinarith
    have hB : 500 * t * t ≤ 150 * t * (b - a) := by nlinarith
    nlinarith [hA, hB]
  -- the two roots
  obtain ⟨r₀, hr₀mem, hr₀⟩ :=
    intermediate_value_Icc' (by linarith : a - t ≤ a)
      ((continuous_charAt ε).continuousOn) (Set.mem_Icc.2 ⟨hva, hvat⟩)
  have htsmall : t ≤ b - a := by
    rw [ht]
    nlinarith
  have hvbt : (weinbergerComparisonMatrix ε).charAt (b - t) ≤ 0 := by
    rw [weinbergerComparisonMatrix_charAt, ← ha, ← hb]
    have hk : ε ^ 2 / 30 = 250 * t := by rw [ht]; ring
    have hgoal : (a - (b - t)) * (b - (b - t)) * (500 - (b - t))
          - ε ^ 2 / 30 * (b - (b - t)) - ε ^ 2 / 30 * (a - (b - t))
        = 250 * t * (b - a) - t * (b - a - t) * (500 - b + t) - 2 * (250 * t) * t := by
      rw [hk]; ring
    rw [hgoal]
    have hA : t * (b - a - t) * 400 ≤ t * (b - a - t) * (500 - b + t) := by
      refine mul_le_mul_of_nonneg_left (by linarith) ?_
      have : (0 : ℝ) ≤ b - a - t := by linarith
      positivity
    nlinarith [hA, htpos, hkey]
  obtain ⟨r₁, hr₁mem, hr₁⟩ :=
    intermediate_value_Icc (by linarith : b - t ≤ b)
      ((continuous_charAt ε).continuousOn) (Set.mem_Icc.2 ⟨hvbt, hvb⟩)
  rw [Set.mem_Icc] at hr₀mem hr₁mem
  have hbtail : b < 500 := by linarith
  exact
    ⟨{ lower₀ := r₀
       lower₁ := r₁
       ordered := by linarith [hr₀mem.2, hr₁mem.1]
       lower₀_is_root := hr₀
       lower₁_is_root := hr₁
       lower₀_le_ritz := hr₀mem.2
       lower₁_le_ritz := hr₁mem.2
       lower₁_lt_tail := by linarith [hr₁mem.2] },
     hr₀mem.1, hr₁mem.1⟩

/-- **The certified low roots of the exact comparison matrix.** -/
noncomputable def weinbergerLowerRoots (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    WeinbergerLowerRootCertificate ε :=
  (exists_weinbergerLowerRootCertificate ε hε hε100).choose

/-- **The certified low root is within `ε²/7500` of the lower Ritz value.**  This
is the quantitative content the paper's informal fourth-order expansion supplied. -/
theorem ritzLow_sub_weinbergerLowerRoots_le (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    ritzLow ε - (weinbergerLowerRoots ε hε hε100).lower₀ ≤ ε ^ 2 / 7500 := by
  have h := (exists_weinbergerLowerRootCertificate ε hε hε100).choose_spec.1
  have hrfl : (weinbergerLowerRoots ε hε hε100).lower₀
      = (exists_weinbergerLowerRootCertificate ε hε hε100).choose.lower₀ := rfl
  rw [hrfl]
  linarith

/-- **The printed pre-(9.8) strict comparison has the wrong direction at the
lower arrowhead root.**

Davis--Kahan print, for both `k = 1,2`,

`(ε²/30) / (500 - α̂_k) > α̂_k - alphaCheck_k`.

For the lower certified root of the exact three-by-three comparison matrix the
characteristic equation gives the opposite strict inequality.  This is not a
numerical-rounding issue: it holds for every `0 < ε < 100`.

Indeed, writing `a = α̂₁`, `b = α̂₂`, `r = alphaCheck₁`, `d = a-r`,
`e = b-r`, and `A = 500-a`, the root equation is

`d e (A+d) = (ε²/30) (e+d)`.

The certified root satisfies `d > 0`, while `e < A` on the source range.
Therefore

`d A (e+d) - d e (A+d) = d² (A-e) > 0`,

so `(ε²/30) < d A`.  Dividing by `A > 0` proves the result.

This theorem is source-fidelity evidence: the formalization should preserve and
refute the printed comparison rather than silently repair its direction. -/
theorem printed_weinberger_low_shift_inequality_reversed
    (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    (ε ^ 2 / 30) / (500 - ritzLow ε) <
      ritzLow ε - (weinbergerLowerRoots ε hε hε100).lower₀ := by
  set C := weinbergerLowerRoots ε hε hε100
  set a := ritzLow ε
  set b := ritzHigh ε
  set r := C.lower₀
  set d := a - r
  set e := b - r
  set A := 500 - a
  set q := ε ^ 2 / 30

  have hc0 : 0 < ritzLowCoefficient := ritzLowCoefficient_pos
  have hapos : 0 < a := by
    rw [show a = ritzLow ε from rfl, ritzLow]
    positivity
  have halt : a < 25 := by
    rw [show a = ritzLow ε from rfl, ritzLow]
    nlinarith [ritzLowCoefficient_lt_printed]
  have hblt : b < 100 := by
    rw [show b = ritzHigh ε from rfl, ritzHigh]
    nlinarith [ritzHighCoefficient_lt_printed]
  have hab : a < b := by
    rw [show a = ritzLow ε from rfl, show b = ritzHigh ε from rfl]
    have hgap := ritzHigh_sub_ritzLow ε
    have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hA : 0 < A := by
    dsimp [A]
    linarith
  have hrle : r ≤ a := by
    dsimp [r, a, C]
    exact (weinbergerLowerRoots ε hε hε100).lower₀_le_ritz
  have he : 0 < e := by
    dsimp [e]
    linarith

  have hroot := (weinbergerLowerRoots ε hε hε100).lower₀_is_root
  rw [weinbergerComparisonMatrix_charAt] at hroot
  have hroot' : d * e * (A + d) - q * e - q * d = 0 := by
    dsimp [d, e, A, q, a, b, r, C] at ⊢
    (convert hroot using 1; ring)

  have hd : 0 < d := by
    have hd0 : 0 ≤ d := by
      dsimp [d]
      linarith
    rcases hd0.eq_or_lt with hd0eq | hdpos
    · have hzero : -(q * e) = 0 := by
        rw [← hd0eq] at hroot'
        simpa using hroot'
      have hqe : 0 < q * e := mul_pos hq he
      linarith
    · exact hdpos

  have hclose : d ≤ ε ^ 2 / 7500 := by
    dsimp [d, a, r, C]
    exact ritzLow_sub_weinbergerLowerRoots_le ε hε hε100
  have hsquare : ε ^ 2 < 10000 := by
    have hsum : 0 < 100 + ε := by linarith
    have hprod := mul_pos (sub_pos.mpr hε100) hsum
    nlinarith
  have hcloseSmall : d < 4 / 3 := by
    nlinarith
  have heA : e < A := by
    dsimp [e, A, d] at hcloseSmall ⊢
    linarith

  have heqd : q * (e + d) = d * e * (A + d) := by
    nlinarith [hroot']
  have hpositiveRemainder : 0 < d ^ 2 * (A - e) := by positivity
  have hfactorIdentity :
      (d * A - q) * (e + d) = d ^ 2 * (A - e) := by
    calc
      (d * A - q) * (e + d)
          = d * A * (e + d) - q * (e + d) := by ring
      _ = d * A * (e + d) - d * e * (A + d) := by rw [heqd]
      _ = d ^ 2 * (A - e) := by ring
  have hfactorProduct : 0 < (d * A - q) * (e + d) := by
    rw [hfactorIdentity]
    exact hpositiveRemainder
  have hsumPos : 0 < e + d := by positivity
  have hfactorPos : 0 < d * A - q := by
    rcases (mul_pos_iff.mp hfactorProduct) with hpos | hneg
    · exact hpos.1
    · linarith [hneg.2, hsumPos]
  have hq_lt : q < d * A := by linarith

  apply (div_lt_iff₀ hA).2
  simpa [d, A, q, a, r, C] using hq_lt

/-- **The first line of equation (9.8), from the certified root.**

Given Weinberger's sine-square estimate at the certified low root, the tangent
obeys the exact envelope `weinbergerLowerTangentExactBound`.  Composing with
`equation_9_8_lower` produces the printed decimal.

The conversion from sine-square to tangent-square is
`tangent_sq_le_of_weinberger_sine_sq`; what is new here is that the root the
estimate is stated against is a certified root of the exact characteristic
polynomial, close enough to the Ritz value to reach the printed constant. -/
theorem weinberger_tangent_le_lowerExactBound (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    {s tanPhi : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (htan : tanPhi ^ 2 ≤ s ^ 2 / (1 - s ^ 2))
    (hweinberger : s ^ 2 ≤
      (ritzLow ε - (weinbergerLowerRoots ε hε hε100).lower₀) /
        (500 - (weinbergerLowerRoots ε hε hε100).lower₀)) :
    tanPhi ≤ weinbergerLowerTangentExactBound ε := by
  set C := weinbergerLowerRoots ε hε hε100 with hC
  have hc0 : 0 < ritzLowCoefficient := ritzLowCoefficient_pos
  have hc1 : ritzLowCoefficient < (4227 : ℝ) / 20000 := ritzLowCoefficient_lt_printed
  have hapos : 0 < ritzLow ε := by rw [ritzLow]; positivity
  have halt : ritzLow ε < 25 := by rw [ritzLow]; nlinarith
  have hclose : ritzLow ε - C.lower₀ ≤ ε ^ 2 / 7500 :=
    ritzLow_sub_weinbergerLowerRoots_le ε hε hε100
  have hroot_le : C.lower₀ ≤ ritzLow ε := C.lower₀_le_ritz
  have hden : (0 : ℝ) < 500 - ritzLow ε := by linarith
  have hden0 : (0 : ℝ) < 500 - C.lower₀ := by linarith
  -- the tangent square, through the algebraic conversion
  have hconv : s ^ 2 / (1 - s ^ 2)
      ≤ (ritzLow ε - C.lower₀) / (500 - ritzLow ε) := by
    refine tangent_sq_le_of_weinberger_sine_sq hs0 hs1 hroot_le ?_ hweinberger
    linarith
  -- and the envelope, squared
  have hW : weinbergerLowerTangentExactBound ε
      = (ε * (Real.sqrt 15 / 15)) / (500 - ritzLow ε) := by
    unfold weinbergerLowerTangentExactBound
    rw [show ritzLow ε = ε * ritzLowCoefficient from rfl] at hden ⊢
    rw [div_eq_div_iff (by nlinarith) (by linarith)]
    ring
  have hWpos : 0 ≤ weinbergerLowerTangentExactBound ε := by
    rw [hW]
    positivity
  have h15 : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have hWsq : (weinbergerLowerTangentExactBound ε) ^ 2
      = (ε ^ 2 / 15) / (500 - ritzLow ε) ^ 2 := by
    rw [hW, div_pow, mul_pow]
    rw [div_pow, h15]
    ring
  have hchain : tanPhi ^ 2 ≤ (weinbergerLowerTangentExactBound ε) ^ 2 := by
    rw [hWsq]
    refine le_trans htan (le_trans hconv ?_)
    rw [div_le_div_iff₀ hden (by positivity)]
    calc (ritzLow ε - C.lower₀) * (500 - ritzLow ε) ^ 2
        ≤ (ε ^ 2 / 7500) * (500 - ritzLow ε) ^ 2 :=
          mul_le_mul_of_nonneg_right hclose (sq_nonneg _)
      _ ≤ ε ^ 2 / 15 * (500 - ritzLow ε) := by
          nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ε) hden.le) hapos.le]
  nlinarith [hchain, hWpos, sq_nonneg (tanPhi - weinbergerLowerTangentExactBound ε)]

/-- **The certified middle root is within `ε²/7500` of the upper Ritz value.** -/
theorem ritzHigh_sub_weinbergerLowerRoots_le (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    ritzHigh ε - (weinbergerLowerRoots ε hε hε100).lower₁ ≤ ε ^ 2 / 7500 := by
  have h := (exists_weinbergerLowerRootCertificate ε hε hε100).choose_spec.2
  have hrfl : (weinbergerLowerRoots ε hε hε100).lower₁
      = (exists_weinbergerLowerRootCertificate ε hε hε100).choose.lower₁ := rfl
  rw [hrfl]
  linarith

/-- **The second line of equation (9.8), from the certified root.**

The mirror of `weinberger_tangent_le_lowerExactBound` at the upper Ritz value and
the middle certified root.  Composing with `equation_9_8_upper` gives the printed
decimal. -/
theorem weinberger_tangent_le_upperExactBound (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    {s tanPhi : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (htan : tanPhi ^ 2 ≤ s ^ 2 / (1 - s ^ 2))
    (hweinberger : s ^ 2 ≤
      (ritzHigh ε - (weinbergerLowerRoots ε hε hε100).lower₁) /
        (500 - (weinbergerLowerRoots ε hε hε100).lower₁)) :
    tanPhi ≤ weinbergerUpperTangentExactBound ε := by
  set C := weinbergerLowerRoots ε hε hε100 with hC
  have hc1pos : 0 < ritzHighCoefficient := by
    unfold ritzHighCoefficient
    positivity
  have hapos : 0 < ritzHigh ε := by rw [ritzHigh]; positivity
  have halt : ritzHigh ε < 100 := by
    rw [ritzHigh]
    nlinarith [ritzHighCoefficient_lt_printed]
  have hclose : ritzHigh ε - C.lower₁ ≤ ε ^ 2 / 7500 :=
    ritzHigh_sub_weinbergerLowerRoots_le ε hε hε100
  have hroot_le : C.lower₁ ≤ ritzHigh ε := C.lower₁_le_ritz
  have hden : (0 : ℝ) < 500 - ritzHigh ε := by linarith
  have hconv : s ^ 2 / (1 - s ^ 2)
      ≤ (ritzHigh ε - C.lower₁) / (500 - ritzHigh ε) := by
    refine tangent_sq_le_of_weinberger_sine_sq hs0 hs1 hroot_le ?_ hweinberger
    linarith
  have hW : weinbergerUpperTangentExactBound ε
      = (ε * (Real.sqrt 15 / 15)) / (500 - ritzHigh ε) := by
    unfold weinbergerUpperTangentExactBound tangentThetaExactBound
    rw [show ritzHigh ε = ε * ritzHighCoefficient from rfl] at hden ⊢
    rw [div_eq_div_iff (by nlinarith) (by linarith)]
    ring
  have hWpos : 0 ≤ weinbergerUpperTangentExactBound ε := by
    rw [hW]
    positivity
  have h15 : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  have hWsq : (weinbergerUpperTangentExactBound ε) ^ 2
      = (ε ^ 2 / 15) / (500 - ritzHigh ε) ^ 2 := by
    rw [hW, div_pow, mul_pow, div_pow, h15]
    ring
  have hchain : tanPhi ^ 2 ≤ (weinbergerUpperTangentExactBound ε) ^ 2 := by
    rw [hWsq]
    refine le_trans htan (le_trans hconv ?_)
    rw [div_le_div_iff₀ hden (by positivity)]
    calc (ritzHigh ε - C.lower₁) * (500 - ritzHigh ε) ^ 2
        ≤ (ε ^ 2 / 7500) * (500 - ritzHigh ε) ^ 2 :=
          mul_le_mul_of_nonneg_right hclose (sq_nonneg _)
      _ ≤ ε ^ 2 / 15 * (500 - ritzHigh ε) := by
          nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ε) hden.le) hapos.le]
  nlinarith [hchain, hWpos, sq_nonneg (tanPhi - weinbergerUpperTangentExactBound ε)]

/-- **Equation (9.8), first line, as printed**, from a Weinberger sine estimate at
the certified low root. -/
theorem equation_9_8_lower_of_weinberger (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    {s tanPhi : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (htan : tanPhi ^ 2 ≤ s ^ 2 / (1 - s ^ 2))
    (hweinberger : s ^ 2 ≤
      (ritzLow ε - (weinbergerLowerRoots ε hε hε100).lower₀) /
        (500 - (weinbergerLowerRoots ε hε hε100).lower₀)) :
    tanPhi < ((1291 : ℝ) / 2500000 * ε) / (1 - (4227 : ℝ) / 10000000 * ε) :=
  equation_9_8_lower ε tanPhi hε hε100
    (weinberger_tangent_le_lowerExactBound ε hε hε100 hs0 hs1 htan hweinberger)

/-- **Equation (9.8), second line, as printed**, from a Weinberger sine estimate at
the certified middle root. -/
theorem equation_9_8_upper_of_weinberger (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    {s tanPhi : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (htan : tanPhi ^ 2 ≤ s ^ 2 / (1 - s ^ 2))
    (hweinberger : s ^ 2 ≤
      (ritzHigh ε - (weinbergerLowerRoots ε hε hε100).lower₁) /
        (500 - (weinbergerLowerRoots ε hε hε100).lower₁)) :
    tanPhi < ((1291 : ℝ) / 2500000 * ε) / (1 - (7887 : ℝ) / 5000000 * ε) :=
  equation_9_8_upper ε tanPhi hε hε100
    (weinberger_tangent_le_upperExactBound ε hε hε100 hs0 hs1 htan hweinberger)

end Section9
end DavisKahan1970
end TauCeti
