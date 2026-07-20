/-
Copyright (c) 2026 Daniel Smania. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Smania
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import LeanPool.Burkholder.Majorants.Definitions

/-!
# Burkholder majorant for `1 < p < 2`

Constructs and verifies the Burkholder majorant in the regime `1 < p < 2`,
including the explicit derivatives, concavity, and tangent estimates.
-/

noncomputable section

namespace Majorants

namespace  MajorantPL2

/-!
# Burkholder majorant candidate

This file builds and studies the piecewise candidate `uCandidate`.

The proof architecture is organized as follows.

1. **Definitions.**  We define the Burkholder parameters, the two local formulas
   `uA1` and `vLeTwo`, their first partial derivatives, the first quadrant
   auxiliary function `auxFunction1`, and finally the four-quadrant function
   `uCandidate`.
2. **Continuity and boundary compatibility.**  We prove that the local formulas,
   their first partials, and the glued functions agree continuously across the
   sector boundaries.
3. **Differentiability and local concavity.**  Inside each smooth sector we
   identify first derivatives and prove the relevant second derivatives are
   non-positive.
4. **Tangent inequalities.**  Local concavity gives tangent inequalities on
   single sectors.  The remaining work is geometric: split horizontal/vertical
   segments at sector boundaries and glue the local tangent estimates while
   comparing derivatives at the break points.

Most of the long private lemmas near the end are not new analytic facts; they are
bookkeeping private lemmas that move a segment through the sector decomposition of
`uCandidate`.
-/

/-! ## 1. Basic parameters and local formulas -/





private lemma pStar_eq_q_of_one_lt_of_lt_two (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    pStar p = q p := by
  unfold pStar
  apply max_eq_right
  unfold q
  have hp_ne_one : p ≠ 1 := by linarith
  simp only [hp_ne_one, ↓reduceIte, ge_iff_le]
  have hp_pos : 0 < p := by linarith
  have hden_pos : 0 < p - 1 := by linarith
  rw [le_div_iff₀ hden_pos]
  nlinarith

private lemma pStar_eq_self_of_two_le (p : ℝ) (hp : 2 ≤ p) : pStar p = p := by
  unfold pStar
  apply max_eq_left
  unfold q
  by_cases h : p = 1
  · simp [h]
  simp only [h, ↓reduceIte]
  have hden_pos : 0 < p - 1 := by linarith
  rw [div_le_iff₀ hden_pos]
  nlinarith






/-- The same expression specialized to the `1< p < 2` regime. -/
private def coeffLeTwo (p : ℝ) : ℝ :=
  Real.rpow ((p - 1)⁻¹) p

private def vLeTwo (p x y : ℝ) : ℝ :=
  Real.rpow (|((x + y) / 2)|) p
    - coeffLeTwo p * Real.rpow (|((x - y) / 2)|) p





private def A2 (p x y : ℝ) : Prop :=
  0 < x ∧ (a p) * x < y ∧ y < x

/-- Closed version of the upper sector. -/
private def closureA2 (p x y : ℝ) : Prop :=
  0 ≤ x ∧ (a p) * x ≤ y ∧ y ≤ x

/-- Lower first-quadrant sector. In the regime `1 < p < 2`,
the affine formula `uA1` is used on this sector. -/
private def A1 (p x y : ℝ) : Prop :=
  0 < x ∧ -x < y ∧ y < (a p) * x

/-- Closed version of the lower sector. -/
private def closureA1 (p x y : ℝ) : Prop :=
  0 ≤ x ∧ -x ≤ y ∧ y ≤ (a p) * x


/-- Local majorant formula on `A1`; outside `x > 0` it is set to zero. -/
private def uA1 (p x y : ℝ) : ℝ :=
  if x > 0 then
     alpha p * Real.rpow x (p-1) * (x - (pStar p) * (x - y) /2)
     else 0




private def DxuA1 (p x y : ℝ) : ℝ :=
  if x > 0 then
    alpha p * (p / 2) * Real.rpow x (p - 2) *
      (((p - 2) / (p - 1)) * x + y)
  else 0



private def DyuA1 (p x _y : ℝ) : ℝ :=
  if x > 0 then
     alpha p * Real.rpow x (p - 1) * (pStar p / 2)
     else 0



private def DxvLeTwo (p x y : ℝ) : ℝ :=
  if x > 0 then
     Real.rpow (|((x + y) / 2)|) (p - 1) * (p / 2)
     - coeffLeTwo p * Real.rpow (|((x - y) / 2)|) (p - 1) * (p / 2)
  else 0

private def DyvLeTwo (p x y : ℝ) : ℝ :=
  if x > 0 then
     Real.rpow (|((x + y) / 2)|) (p - 1) * (p / 2)
     + coeffLeTwo p * Real.rpow (|((x - y) / 2)|) (p - 1) * (p / 2)
  else 0

/-- Closed `A1` as a subset of `ℝ²`. -/
private def closureA1Set (p : ℝ) : Set (ℝ × ℝ) :=
  {z | closureA1 p z.1 z.2}

/-- Closed `A2` as a subset of `ℝ²`. -/
private def closureA2Set (p : ℝ) : Set (ℝ × ℝ) :=
  {z | closureA2 p z.1 z.2}

private def DxuA1Fun (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => DxuA1 p z.1 z.2

private def DyuA1Fun (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => DyuA1 p z.1 z.2

private def DxuA1Formula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z =>
    alpha p * (p / 2) * Real.rpow z.1 (p - 2) *
      (((p - 2) / (p - 1)) * z.1 + z.2)

private def DyuA1Formula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => alpha p * Real.rpow z.1 (p - 1) * (pStar p / 2)

private def DxvLeTwoFun (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => DxvLeTwo p z.1 z.2

private def DyvLeTwoFun (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => DyvLeTwo p z.1 z.2

private def DxvLeTwoFormula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z =>
    Real.rpow (|((z.1 + z.2) / 2)|) (p - 1) * (p / 2) -
      coeffLeTwo p * Real.rpow (|((z.1 - z.2) / 2)|) (p - 1) * (p / 2)

private def DyvLeTwoFormula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z =>
    Real.rpow (|((z.1 + z.2) / 2)|) (p - 1) * (p / 2) +
      coeffLeTwo p * Real.rpow (|((z.1 - z.2) / 2)|) (p - 1) * (p / 2)

open Topology

/-! ## 2. Continuity of the local first partials -/



private def auxFunction1 (p x y : ℝ) : ℝ :=
    by
    classical
    exact
      if  closureA1 p x y then
         uA1 p x y
      else if closureA2 p x y then
          vLeTwo p x y
        else 0

private def DxauxFunction1 (p x y : ℝ) : ℝ :=
    by
    classical
    exact
      if closureA1 p x y then
        DxuA1 p x y
      else if closureA2 p x y then
        DxvLeTwo p x y
      else 0

private def DyauxFunction1 (p x y : ℝ) : ℝ :=
    by
    classical
    exact
      if closureA1 p x y then
        DyuA1 p x y
      else if closureA2 p x y then
        DyvLeTwo p x y
      else 0

/-! ## 3. Quadrants and the global candidate -/

/-
`auxFunction1` lives in the first quadrant cone.  The global candidate is built
by reflecting this auxiliary function into the other three cones.  The order of
the `if` branches is important on shared boundaries; later boundary private lemmas prove
that the chosen formulas agree where they need to.
-/

private def QuarterPlane (x y : ℝ) : Prop := 0 ≤ x ∧ y ≤ x ∧ -x ≤ y

private def QuarterPlaneOpen (x y : ℝ) : Prop := 0 < x ∧ y < x ∧ -x < y

private def QuarterPlane2 (x y : ℝ) : Prop := x ≤ 0 ∧ y ≤ -x ∧ x ≤ y

private def QuarterPlane2Open (x y : ℝ) : Prop := x < 0 ∧ y < -x ∧ x < y

private def QuarterPlane3 (x y : ℝ) : Prop := y ≥  0 ∧ -y ≤ x ∧ x ≤ y

private def QuarterPlane3Open (x y : ℝ) : Prop := 0 < y ∧ -y < x ∧ x < y

private def QuarterPlane4 (x y : ℝ) : Prop := y ≤ 0 ∧ y ≤ x ∧ x ≤ -y

private def QuarterPlane4Open (x y : ℝ) : Prop := y < 0 ∧ y < x ∧ x < -y



private def uCandidate (p x y : ℝ) : ℝ :=
  by
    classical
    exact
      if QuarterPlane  x y then
        auxFunction1  p x y
      else  if QuarterPlane2 x y then
        auxFunction1  p (-x) (-y)
      else if QuarterPlane3 x y then
        auxFunction1  p y x
      else if QuarterPlane4 x y then
        auxFunction1  p (-y) (-x)
      else 0

private def DxuCandidate (p x y : ℝ) : ℝ :=
  by
    classical
    exact
      if QuarterPlane x y then
        DxauxFunction1 p x y
      else if QuarterPlane2 x y then
        -DxauxFunction1 p (-x) (-y)
      else if QuarterPlane3 x y then
        DyauxFunction1 p y x
      else if QuarterPlane4 x y then
        -DyauxFunction1 p (-y) (-x)
      else 0

private def DyuCandidate (p x y : ℝ) : ℝ :=
  by
    classical
    exact
      if QuarterPlane x y then
        DyauxFunction1 p x y
      else if QuarterPlane2 x y then
        -DyauxFunction1 p (-x) (-y)
      else if QuarterPlane3 x y then
        DxauxFunction1 p y x
      else if QuarterPlane4 x y then
        -DxauxFunction1 p (-y) (-x)
      else 0


/-! ## 4. Boundary compatibility and continuity of the glued functions -/



/-! 13. Majorant existence statement -/

/-
This final theorem packages the candidate with the axis-supported tangent
inequality, pointwise majorization, and negativity on the opposing-sign region.
-/

private lemma v_eq_vLeTwo_of_one_lt_of_lt_two
    (p x y : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    v p x y = vLeTwo p x y := by
  have hp_ne_one : p ≠ 1 := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hq : q p = p / (p - 1) := by
    simp [q, hp_ne_one]
  have hcoeff_abs : |pStar p - 1| = (p - 1)⁻¹ := by
    rw [hpStar, hq]
    have hcalc : p / (p - 1) - 1 = (p - 1)⁻¹ := by
      field_simp [hpden_pos.ne']
      ring
    rw [hcalc]
    exact abs_of_pos (inv_pos.mpr hpden_pos)
  simp [v, vLeTwo, coeffLeTwo, hcoeff_abs]

private lemma one_le_coeffLeTwo_of_one_lt_of_lt_two
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    1 ≤ coeffLeTwo p := by
  have hp_nonneg : 0 ≤ p := by linarith
  have hbase : 1 ≤ (p - 1)⁻¹ := by
    have hp1_pos : 0 < p - 1 := by linarith
    rw [show (p - 1)⁻¹ = 1 / (p - 1) by rw [one_div]]
    rw [le_div_iff₀ hp1_pos]
    linarith
  simpa [coeffLeTwo, Real.one_rpow] using
    Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hbase hp_nonneg

private lemma coeffLeTwo_nonneg_of_one_lt_of_lt_two
    (p : ℝ) (_hp1 : 1 < p) (_hp2 : p < 2) :
    0 ≤ coeffLeTwo p := by
  unfold coeffLeTwo
  exact Real.rpow_nonneg (inv_nonneg.mpr (by linarith : 0 ≤ p - 1)) p

private lemma pStar_pos_of_one_lt_of_lt_two
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    0 < pStar p := by
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  rw [hpStar]
  simp only [q, hp_ne_one, ↓reduceIte, gt_iff_lt]
  exact div_pos hp_pos hpden_pos

private lemma a_nonneg_of_one_lt_of_lt_two
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    0 ≤ a p := by
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  rw [a, hpStar]
  simp [q, hp_ne_one]
  field_simp [hpden_pos.ne']
  linarith

private lemma one_le_half_pStar_of_one_lt_of_lt_two
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    1 ≤ pStar p / 2 := by
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  rw [hpStar]
  simp only [q, hp_ne_one, ↓reduceIte, ge_iff_le]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  rw [le_div_iff₀ hpden_pos]
  ring_nf
  linarith

private lemma alpha_nonneg_of_one_lt_of_lt_two
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    0 ≤ alpha p := by
  have hpStar_eq : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  have hps_pos : 0 < pStar p := by
    rw [hpStar_eq]
    simp only [q, hp_ne_one, ↓reduceIte]
    exact div_pos hp_pos hpden_pos
  have hpsm_pos : 0 < pStar p - 1 := by
    rw [hpStar_eq]
    simp [q, hp_ne_one]
    field_simp [hpden_pos.ne']
    nlinarith
  unfold alpha
  exact mul_nonneg hp_pos.le (Real.rpow_nonneg (div_nonneg hps_pos.le hpsm_pos.le) _)

private lemma vLeTwo_le_zero_of_mul_nonpos_leTwo
    (p x y : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hxy : x * y ≤ 0) :
    vLeTwo p x y ≤ 0 := by
  have hp_nonneg : 0 ≤ p := by linarith
  have hsq : ((x + y) / 2) ^ 2 ≤ ((x - y) / 2) ^ 2 := by
    nlinarith
  have habs : |(x + y) / 2| ≤ |(x - y) / 2| := sq_le_sq.mp hsq
  have hpow :
      Real.rpow (|(x + y) / 2|) p ≤ Real.rpow (|(x - y) / 2|) p :=
    Real.rpow_le_rpow (abs_nonneg _) habs hp_nonneg
  have hcoef : 1 ≤ coeffLeTwo p :=
    one_le_coeffLeTwo_of_one_lt_of_lt_two p hp1 hp2
  have hdiff_nonneg : 0 ≤ Real.rpow (|(x - y) / 2|) p :=
    Real.rpow_nonneg (abs_nonneg _) _
  have hmul :
      Real.rpow (|(x - y) / 2|) p ≤
        coeffLeTwo p * Real.rpow (|(x - y) / 2|) p := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hcoef hdiff_nonneg
  exact sub_nonpos.mpr (hpow.trans hmul)

private lemma uA1_le_zero_of_y_nonpos_leTwo
    (p x y : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hx : 0 ≤ x) (hy : y ≤ 0) :
    uA1 p x y ≤ 0 := by
  rcases hx.eq_or_lt with rfl | hxpos
  · simp [uA1]
  · have hx_nonneg : 0 ≤ x := le_of_lt hxpos
    have halpha : 0 ≤ alpha p :=
      alpha_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have hrpow : 0 ≤ x ^ (p - 1) := Real.rpow_nonneg hx_nonneg _
    have hhalf : 1 ≤ pStar p / 2 :=
      one_le_half_pStar_of_one_lt_of_lt_two p hp1 hp2
    have hhalf_nonneg : 0 ≤ pStar p / 2 := le_trans zero_le_one hhalf
    have hxy_le : x ≤ x - y := by linarith
    have hx_le_halfx : x ≤ (pStar p / 2) * x := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hhalf hx_nonneg
    have hhalf_mono :
        (pStar p / 2) * x ≤ (pStar p / 2) * (x - y) :=
      mul_le_mul_of_nonneg_left hxy_le hhalf_nonneg
    have hbracket : x - pStar p * (x - y) / 2 ≤ 0 := by
      have hmain : x ≤ (pStar p / 2) * (x - y) :=
        hx_le_halfx.trans hhalf_mono
      have hrewrite : (pStar p / 2) * (x - y) = pStar p * (x - y) / 2 := by ring
      linarith
    have hprod_nonneg : 0 ≤ alpha p * x ^ (p - 1) :=
      mul_nonneg halpha hrpow
    simp only [uA1, gt_iff_lt, hxpos, ↓reduceIte, Real.rpow_eq_pow, ge_iff_le]
    exact mul_nonpos_of_nonneg_of_nonpos hprod_nonneg hbracket

private lemma mem_some_QuarterPlane_leTwo (x y : ℝ) :
    QuarterPlane x y ∨ QuarterPlane2 x y ∨ QuarterPlane3 x y ∨ QuarterPlane4 x y := by
  by_cases hxy : |x| ≤ |y|
  · by_cases hy : 0 ≤ y
    · have habs : |x| ≤ y := by simpa [abs_of_nonneg hy] using hxy
      rcases abs_le.mp habs with ⟨h1, h2⟩
      exact Or.inr (Or.inr (Or.inl ⟨hy, h1, h2⟩))
    · have hy' : y < 0 := lt_of_not_ge hy
      have habs : |x| ≤ -y := by simpa [abs_of_neg hy'] using hxy
      rcases abs_le.mp habs with ⟨h1, h2⟩
      have h1' : y ≤ x := by simpa using h1
      exact Or.inr (Or.inr (Or.inr ⟨le_of_lt hy', h1', h2⟩))
  · have hyx : |y| ≤ |x| := le_of_lt (not_le.mp hxy)
    by_cases hx : 0 ≤ x
    · have habs : |y| ≤ x := by simpa [abs_of_nonneg hx] using hyx
      rcases abs_le.mp habs with ⟨h1, h2⟩
      exact Or.inl ⟨hx, h2, h1⟩
    · have hx' : x < 0 := lt_of_not_ge hx
      have habs : |y| ≤ -x := by simpa [abs_of_neg hx'] using hyx
      rcases abs_le.mp habs with ⟨h1, h2⟩
      have h1' : x ≤ y := by simpa using h1
      exact Or.inr (Or.inl ⟨le_of_lt hx', h2, h1'⟩)

private lemma uCandidate_eq_Q1_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane x y) :
    uCandidate p x y = auxFunction1 p x y := by
  simp [uCandidate, hQ]

private lemma uCandidate_eq_Q2_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane2 x y) :
    uCandidate p x y = auxFunction1 p (-x) (-y) := by
  by_cases hQ1 : QuarterPlane x y
  · obtain ⟨hx0, hyx, _⟩ := hQ1
    obtain ⟨hx1, _, hxy⟩ := hQ
    have hx : x = 0 := le_antisymm hx1 hx0
    have hy : y = 0 := by
      have hy_le : y ≤ 0 := by simpa [hx] using hyx
      have hy_ge : 0 ≤ y := by simpa [hx] using hxy
      exact le_antisymm hy_le hy_ge
    subst x
    subst y
    simp [uCandidate, auxFunction1, QuarterPlane, closureA1, uA1]
  · simp [uCandidate, hQ1, hQ]

private lemma uCandidate_eq_Q3_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane3 x y) :
    uCandidate p x y = auxFunction1 p y x := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := uCandidate_eq_Q1_leTwo p (hQ := hQ1)
    obtain ⟨_, hyx, _⟩ := hQ1
    obtain ⟨_, _, hxy⟩ := hQ
    have hxy' : x = y := le_antisymm hxy hyx
    calc
      uCandidate p x y = auxFunction1 p x y := hbranch
      _ = auxFunction1 p y x := by rw [hxy']
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := uCandidate_eq_Q2_leTwo p (hQ := hQ2)
      obtain ⟨_, hynegx, _⟩ := hQ2
      obtain ⟨_, hnegyx, _⟩ := hQ
      have hx : x = -y := le_antisymm (by linarith [hynegx]) hnegyx
      calc
        uCandidate p x y = auxFunction1 p (-x) (-y) := hbranch
        _ = auxFunction1 p y x := by rw [hx]; simp
    · simp [uCandidate, hQ1, hQ2, hQ]

private lemma uCandidate_eq_Q4_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane4 x y) :
    uCandidate p x y = auxFunction1 p (-y) (-x) := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := uCandidate_eq_Q1_leTwo p (hQ := hQ1)
    obtain ⟨_, _, hnegxy⟩ := hQ1
    obtain ⟨_, _, hxnegy⟩ := hQ
    have hy : y = -x := by linarith
    calc
      uCandidate p x y = auxFunction1 p x y := hbranch
      _ = auxFunction1 p (-y) (-x) := by rw [hy]; simp
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := uCandidate_eq_Q2_leTwo p (hQ := hQ2)
      obtain ⟨_, _, hxy⟩ := hQ2
      obtain ⟨_, hyx, _⟩ := hQ
      have hxy' : x = y := le_antisymm hxy hyx
      calc
        uCandidate p x y = auxFunction1 p (-x) (-y) := hbranch
        _ = auxFunction1 p (-y) (-x) := by rw [hxy']
    · by_cases hQ3 : QuarterPlane3 x y
      · have hbranch := uCandidate_eq_Q3_leTwo p (hQ := hQ3)
        obtain ⟨hy0, hnegyx, _⟩ := hQ3
        obtain ⟨hy1, _, hxnegy⟩ := hQ
        have hy : y = 0 := le_antisymm hy1 hy0
        have hx : x = 0 := by
          have hx_le : x ≤ 0 := by simpa [hy] using hxnegy
          have hx_ge : 0 ≤ x := by simpa [hy] using hnegyx
          exact le_antisymm hx_le hx_ge
        calc
          uCandidate p x y = auxFunction1 p y x := hbranch
          _ = auxFunction1 p (-y) (-x) := by rw [hx, hy]; simp
      · simp [uCandidate, hQ1, hQ2, hQ3, hQ]

private lemma uCandidate_swap_leTwo
    (p : ℝ) (x y : ℝ) :
    uCandidate p x y = uCandidate p y x := by
  rcases mem_some_QuarterPlane_leTwo x y with hQ1 | hrest
  · have hswap : QuarterPlane3 y x := ⟨hQ1.1, hQ1.2.2, hQ1.2.1⟩
    rw [uCandidate_eq_Q1_leTwo p hQ1, uCandidate_eq_Q3_leTwo p hswap]
  rcases hrest with hQ2 | hrest
  · have hswap : QuarterPlane4 y x := ⟨hQ2.1, hQ2.2.2, hQ2.2.1⟩
    rw [uCandidate_eq_Q2_leTwo p hQ2, uCandidate_eq_Q4_leTwo p hswap]
  rcases hrest with hQ3 | hQ4
  · have hswap : QuarterPlane y x := ⟨hQ3.1, hQ3.2.2, hQ3.2.1⟩
    rw [uCandidate_eq_Q3_leTwo p hQ3, uCandidate_eq_Q1_leTwo p hswap]
  · have hswap : QuarterPlane2 y x := ⟨hQ4.1, hQ4.2.2, hQ4.2.1⟩
    rw [uCandidate_eq_Q4_leTwo p hQ4, uCandidate_eq_Q2_leTwo p hswap]

private lemma axis_tangent_inequality_of_coordinate_tangents_leTwo
    (u ux uy : ℝ → ℝ → ℝ)
    (hx_tangent : ∀ x y h, u (x + h) y ≤ u x y + ux x y * h)
    (hy_tangent : ∀ x y k, u x (y + k) ≤ u x y + uy x y * k)
    (x y h k : ℝ) (hk : h * k = 0) :
    u (x + h) (y + k) ≤ u x y + ux x y * h + uy x y * k := by
  rcases mul_eq_zero.mp hk with hh | hk'
  · subst h
    simpa [add_assoc] using hy_tangent x y k
  · subst k
    simpa [add_assoc] using hx_tangent x y h

private lemma DxuCandidate_eq_Q1_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane x y) :
    DxuCandidate p x y = DxauxFunction1 p x y := by
  simp [DxuCandidate, hQ]

private lemma DyuCandidate_eq_Q1_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane x y) :
    DyuCandidate p x y = DyauxFunction1 p x y := by
  simp [DyuCandidate, hQ]

private lemma DxuCandidate_eq_Q2_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane2 x y) :
    DxuCandidate p x y = -DxauxFunction1 p (-x) (-y) := by
  by_cases hQ1 : QuarterPlane x y
  · obtain ⟨hx0, hyx, _⟩ := hQ1
    obtain ⟨hx1, _, hxy⟩ := hQ
    have hx : x = 0 := le_antisymm hx1 hx0
    have hy : y = 0 := by
      have hy_le : y ≤ 0 := by simpa [hx] using hyx
      have hy_ge : 0 ≤ y := by simpa [hx] using hxy
      exact le_antisymm hy_le hy_ge
    subst x
    subst y
    simp [DxuCandidate, DxauxFunction1, QuarterPlane, closureA1, DxuA1]
  · simp [DxuCandidate, hQ1, hQ]

private lemma DyuCandidate_eq_Q2_leTwo
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane2 x y) :
    DyuCandidate p x y = -DyauxFunction1 p (-x) (-y) := by
  by_cases hQ1 : QuarterPlane x y
  · obtain ⟨hx0, hyx, _⟩ := hQ1
    obtain ⟨hx1, _, hxy⟩ := hQ
    have hx : x = 0 := le_antisymm hx1 hx0
    have hy : y = 0 := by
      have hy_le : y ≤ 0 := by simpa [hx] using hyx
      have hy_ge : 0 ≤ y := by simpa [hx] using hxy
      exact le_antisymm hy_le hy_ge
    subst x
    subst y
    simp [DyuCandidate, DyauxFunction1, QuarterPlane, closureA1, DyuA1]
  · simp [DyuCandidate, hQ1, hQ]

private lemma auxFunction1_le_zero_of_QuarterPlane_mul_nonpos_leTwo
    (p x y : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hQ : QuarterPlane x y) (hxy : x * y ≤ 0) :
    auxFunction1 p x y ≤ 0 := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hy_nonpos : y ≤ 0 := by
    by_contra hy_not
    have hy_pos : 0 < y := lt_of_not_ge hy_not
    have hx_pos : 0 < x := lt_of_lt_of_le hy_pos hQ.2.1
    have hprod_pos : 0 < x * y := mul_pos hx_pos hy_pos
    linarith
  have hA1 : closureA1 p x y := by
    refine ⟨hQ.1, hQ.2.2, ?_⟩
    exact le_trans hy_nonpos (mul_nonneg ha_nonneg hQ.1)
  rw [auxFunction1]
  simp only [hA1, ↓reduceIte, ge_iff_le]
  exact uA1_le_zero_of_y_nonpos_leTwo p x y hp1 hp2 hQ.1 hy_nonpos

private lemma uCandidate_le_zero_of_mul_nonpos_leTwo
    (p x y : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hxy : x * y ≤ 0) :
    uCandidate p x y ≤ 0 := by
  rcases mem_some_QuarterPlane_leTwo x y with hQ1 | hrest
  · rw [uCandidate_eq_Q1_leTwo p hQ1]
    exact auxFunction1_le_zero_of_QuarterPlane_mul_nonpos_leTwo p x y hp1 hp2 hQ1 hxy
  rcases hrest with hQ2 | hrest
  · have hQ : QuarterPlane (-x) (-y) :=
      ⟨by linarith [hQ2.1], by linarith [hQ2.2.2], by linarith [hQ2.2.1]⟩
    have hxy' : (-x) * (-y) ≤ 0 := by nlinarith
    rw [uCandidate_eq_Q2_leTwo p hQ2]
    exact auxFunction1_le_zero_of_QuarterPlane_mul_nonpos_leTwo p (-x) (-y) hp1 hp2 hQ hxy'
  rcases hrest with hQ3 | hQ4
  · have hQ : QuarterPlane y x := ⟨hQ3.1, hQ3.2.2, hQ3.2.1⟩
    have hxy' : y * x ≤ 0 := by nlinarith
    rw [uCandidate_eq_Q3_leTwo p hQ3]
    exact auxFunction1_le_zero_of_QuarterPlane_mul_nonpos_leTwo p y x hp1 hp2 hQ hxy'
  · have hQ : QuarterPlane (-y) (-x) :=
      ⟨by linarith [hQ4.1], by linarith [hQ4.2.1], by linarith [hQ4.2.2]⟩
    have hxy' : (-y) * (-x) ≤ 0 := by nlinarith
    rw [uCandidate_eq_Q4_leTwo p hQ4]
    exact auxFunction1_le_zero_of_QuarterPlane_mul_nonpos_leTwo p (-y) (-x) hp1 hp2 hQ hxy'

private lemma uCandidate_le_zero_of_xy_zero_leTwo
    (p x y : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hxy : x * y = 0) :
    uCandidate p x y ≤ 0 :=
  uCandidate_le_zero_of_mul_nonpos_leTwo p x y hp1 hp2 (le_of_eq hxy)

private lemma a_eq_leTwo (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    a p = (2 - p) / p := by
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  rw [a, hpStar]
  simp [q, hp_ne_one]
  field_simp [hp_pos.ne', hpden_pos.ne']
  ring

private lemma alpha_eq_leTwo (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    alpha p = p * p ^ (1 - p) := by
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  rw [alpha, hpStar]
  simp [q, hp_ne_one]
  have hbase : (p / (p - 1)) / (p / (p - 1) - 1) = p := by
    field_simp [hp_pos.ne', hpden_pos.ne']
    ring
  simp [hbase]

private lemma a_lt_one_of_one_lt_of_lt_two
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    a p < 1 := by
  rw [a_eq_leTwo p hp1 hp2]
  have hp_pos : 0 < p := by linarith
  rw [div_lt_iff₀ hp_pos]
  linarith

private lemma DxauxFunction1_eq_DyauxFunction1_on_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x : ℝ)
    (hx : 0 ≤ x) :
    DxauxFunction1 p x x = DyauxFunction1 p x x := by
  rcases hx.lt_or_eq with hxpos | hxeq
  · have hlt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    have hax : a p * x ≤ x :=
      (mul_le_mul_of_nonneg_right hlt.le hx).trans_eq (one_mul x)
    have hcl2 : closureA2 p x x := ⟨hx, hax, le_rfl⟩
    have hnot1 : ¬ closureA1 p x x := by
      intro h
      have hax_lt : a p * x < x := by
        simpa using mul_lt_mul_of_pos_right hlt hxpos
      exact not_le_of_gt hax_lt h.2.2
    have hp1_ne : p - 1 ≠ 0 := by linarith
    simp [DxauxFunction1, DyauxFunction1, hnot1, hcl2, DxvLeTwo, DyvLeTwo,
      hxpos, Real.zero_rpow hp1_ne]
  · subst x
    simp [DxauxFunction1, DyauxFunction1, closureA1, DxuA1, DyuA1]

private lemma DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x : ℝ)
    (hx : 0 ≤ x) :
    DxauxFunction1 p x (-x) = -DyauxFunction1 p x (-x) := by
  rcases hx.lt_or_eq with hxpos | hxeq
  · have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have hcl1 : closureA1 p x (-x) := by
      refine ⟨hx, le_rfl, ?_⟩
      exact le_trans (neg_nonpos.mpr hx) (mul_nonneg ha_nonneg hx)
    have hpStar : pStar p = q p :=
      pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
    have hp_ne_one : p ≠ 1 := by linarith
    have hpden_ne : p - 1 ≠ 0 := by linarith
    have hpow : x ^ (p - 1) = x ^ (p - 2) * x := by
      calc
        x ^ (p - 1) = x ^ ((p - 2) + (1 : ℝ)) := by ring_nf
        _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hxpos]
        _ = x ^ (p - 2) * x := by rw [Real.rpow_one]
    simp only [DxauxFunction1, hcl1, ↓reduceIte, DxuA1, gt_iff_lt, hxpos, Real.rpow_eq_pow,
      DyauxFunction1, DyuA1, hpStar, q, hp_ne_one]
    rw [hpow]
    field_simp [hpden_ne]
    ring
  · subst x
    simp [DxauxFunction1, DyauxFunction1, closureA1, DxuA1, DyuA1]

private lemma DxuCandidate_eq_Q3_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (hQ : QuarterPlane3 x y) :
    DxuCandidate p x y = DyauxFunction1 p y x := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := DxuCandidate_eq_Q1_leTwo p (hQ := hQ1)
    obtain ⟨_, hyx, _⟩ := hQ1
    obtain ⟨hy0, _, hxy⟩ := hQ
    have hxy' : x = y := le_antisymm hxy hyx
    subst x
    calc
      DxuCandidate p y y = DxauxFunction1 p y y := hbranch
      _ = DyauxFunction1 p y y :=
        DxauxFunction1_eq_DyauxFunction1_on_diag_leTwo p hp1 hp2 y hy0
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := DxuCandidate_eq_Q2_leTwo p (hQ := hQ2)
      obtain ⟨_, hynegx, _⟩ := hQ2
      obtain ⟨hy0, hnegyx, _⟩ := hQ
      have hx : x = -y := le_antisymm (by linarith [hynegx]) hnegyx
      subst x
      have hrel :=
        DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo p hp1 hp2 y hy0
      have h' : -DxauxFunction1 p y (-y) = DyauxFunction1 p y (-y) := by
        linarith
      calc
        DxuCandidate p (-y) y = -DxauxFunction1 p (-(-y)) (-y) := hbranch
        _ = -DxauxFunction1 p y (-y) := by simp
        _ = DyauxFunction1 p y (-y) := h'
    · simp [DxuCandidate, hQ1, hQ2, hQ]

private lemma DxuCandidate_eq_Q4_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (hQ : QuarterPlane4 x y) :
    DxuCandidate p x y = -DyauxFunction1 p (-y) (-x) := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := DxuCandidate_eq_Q1_leTwo p (hQ := hQ1)
    obtain ⟨hx0, _, hnegxy⟩ := hQ1
    obtain ⟨_, _, hxnegy⟩ := hQ
    have hy : y = -x := by linarith
    subst y
    calc
      DxuCandidate p x (-x) = DxauxFunction1 p x (-x) := hbranch
      _ = -DyauxFunction1 p x (-x) :=
        DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo p hp1 hp2 x hx0
      _ = -DyauxFunction1 p (-(-x)) (-x) := by simp
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := DxuCandidate_eq_Q2_leTwo p (hQ := hQ2)
      obtain ⟨hx0, _, hxy⟩ := hQ2
      obtain ⟨_, hyx, _⟩ := hQ
      have hxy' : x = y := le_antisymm hxy hyx
      subst x
      have hnonneg : 0 ≤ -y := by linarith
      have hdiag :=
        DxauxFunction1_eq_DyauxFunction1_on_diag_leTwo p hp1 hp2 (-y) hnonneg
      calc
        DxuCandidate p y y = -DxauxFunction1 p (-y) (-y) := hbranch
        _ = -DyauxFunction1 p (-y) (-y) := by rw [hdiag]
    · by_cases hQ3 : QuarterPlane3 x y
      · have hbranch := DxuCandidate_eq_Q3_leTwo p hp1 hp2 (hQ := hQ3)
        obtain ⟨hy0, hnegyx, _⟩ := hQ3
        obtain ⟨hy1, _, hxnegy⟩ := hQ
        have hy : y = 0 := le_antisymm hy1 hy0
        have hx : x = 0 := by
          have hx_le : x ≤ 0 := by simpa [hy] using hxnegy
          have hx_ge : 0 ≤ x := by simpa [hy] using hnegyx
          exact le_antisymm hx_le hx_ge
        subst x
        subst y
        simpa [DyauxFunction1, closureA1, DyuA1] using hbranch
      · simp [DxuCandidate, hQ1, hQ2, hQ3, hQ]

private lemma DyuCandidate_eq_Q3_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (hQ : QuarterPlane3 x y) :
    DyuCandidate p x y = DxauxFunction1 p y x := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := DyuCandidate_eq_Q1_leTwo p (hQ := hQ1)
    obtain ⟨_, hyx, _⟩ := hQ1
    obtain ⟨hy0, _, hxy⟩ := hQ
    have hxy' : x = y := le_antisymm hxy hyx
    subst x
    calc
      DyuCandidate p y y = DyauxFunction1 p y y := hbranch
      _ = DxauxFunction1 p y y :=
        (DxauxFunction1_eq_DyauxFunction1_on_diag_leTwo p hp1 hp2 y hy0).symm
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := DyuCandidate_eq_Q2_leTwo p (hQ := hQ2)
      obtain ⟨_, hynegx, _⟩ := hQ2
      obtain ⟨hy0, hnegyx, _⟩ := hQ
      have hx : x = -y := le_antisymm (by linarith [hynegx]) hnegyx
      subst x
      have hrel :=
        DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo p hp1 hp2 y hy0
      calc
        DyuCandidate p (-y) y = -DyauxFunction1 p (-(-y)) (-y) := hbranch
        _ = -DyauxFunction1 p y (-y) := by simp
        _ = DxauxFunction1 p y (-y) := hrel.symm
    · simp [DyuCandidate, hQ1, hQ2, hQ]

private lemma DyuCandidate_eq_Q4_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (hQ : QuarterPlane4 x y) :
    DyuCandidate p x y = -DxauxFunction1 p (-y) (-x) := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := DyuCandidate_eq_Q1_leTwo p (hQ := hQ1)
    obtain ⟨hx0, _, hnegxy⟩ := hQ1
    obtain ⟨_, _, hxnegy⟩ := hQ
    have hy : y = -x := by linarith
    subst y
    have hrel :=
      DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo p hp1 hp2 x hx0
    have h' : DyauxFunction1 p x (-x) = -DxauxFunction1 p x (-x) := by
      linarith
    calc
      DyuCandidate p x (-x) = DyauxFunction1 p x (-x) := hbranch
      _ = -DxauxFunction1 p x (-x) := h'
      _ = -DxauxFunction1 p (-(-x)) (-x) := by simp
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := DyuCandidate_eq_Q2_leTwo p (hQ := hQ2)
      obtain ⟨hx0, _, hxy⟩ := hQ2
      obtain ⟨_, hyx, _⟩ := hQ
      have hxy' : x = y := le_antisymm hxy hyx
      subst x
      have hnonneg : 0 ≤ -y := by linarith
      have hdiag :=
        DxauxFunction1_eq_DyauxFunction1_on_diag_leTwo p hp1 hp2 (-y) hnonneg
      calc
        DyuCandidate p y y = -DyauxFunction1 p (-y) (-y) := hbranch
        _ = -DxauxFunction1 p (-y) (-y) := by rw [hdiag]
    · by_cases hQ3 : QuarterPlane3 x y
      · have hbranch := DyuCandidate_eq_Q3_leTwo p hp1 hp2 (hQ := hQ3)
        obtain ⟨hy0, hnegyx, _⟩ := hQ3
        obtain ⟨hy1, _, hxnegy⟩ := hQ
        have hy : y = 0 := le_antisymm hy1 hy0
        have hx : x = 0 := by
          have hx_le : x ≤ 0 := by simpa [hy] using hxnegy
          have hx_ge : 0 ≤ x := by simpa [hy] using hnegyx
          exact le_antisymm hx_le hx_ge
        subst x
        subst y
        simpa [DxauxFunction1, closureA1, DxuA1] using hbranch
      · simp [DyuCandidate, hQ1, hQ2, hQ3, hQ]

private lemma DyuCandidate_eq_DxuCandidate_swap_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) :
    DyuCandidate p x y = DxuCandidate p y x := by
  rcases mem_some_QuarterPlane_leTwo x y with hQ1 | hrest
  · have hswap : QuarterPlane3 y x := ⟨hQ1.1, hQ1.2.2, hQ1.2.1⟩
    rw [DyuCandidate_eq_Q1_leTwo p hQ1,
      DxuCandidate_eq_Q3_leTwo p hp1 hp2 hswap]
  rcases hrest with hQ2 | hrest
  · have hswap : QuarterPlane4 y x := ⟨hQ2.1, hQ2.2.2, hQ2.2.1⟩
    rw [DyuCandidate_eq_Q2_leTwo p hQ2,
      DxuCandidate_eq_Q4_leTwo p hp1 hp2 hswap]
  rcases hrest with hQ3 | hQ4
  · have hswap : QuarterPlane y x := ⟨hQ3.1, hQ3.2.2, hQ3.2.1⟩
    rw [DyuCandidate_eq_Q3_leTwo p hp1 hp2 hQ3,
      DxuCandidate_eq_Q1_leTwo p hswap]
  · have hswap : QuarterPlane2 y x := ⟨hQ4.1, hQ4.2.2, hQ4.2.1⟩
    rw [DyuCandidate_eq_Q4_leTwo p hp1 hp2 hQ4,
      DxuCandidate_eq_Q2_leTwo p hswap]

private lemma uA1_eq_zero_on_boundary_leTwo
    (p x : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hx : 0 < x) :
    uA1 p x ((a p) * x) = 0 := by
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  unfold uA1
  rw [if_pos hx]
  have hfactor : x - pStar p * (x - a p * x) / 2 = 0 := by
    rw [hpStar, a_eq_leTwo p hp1 hp2]
    simp [q, hp_ne_one]
    field_simp [hp_pos.ne', hpden_pos.ne']
    ring
  rw [hfactor, mul_zero]

private lemma vLeTwo_eq_zero_on_boundary_leTwo
    (p x : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hx : 0 < x) :
    vLeTwo p x ((a p) * x) = 0 := by
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  have hpden_nonneg : 0 ≤ p - 1 := le_of_lt hpden_pos
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  rw [a_eq_leTwo p hp1 hp2]
  simp only [vLeTwo, coeffLeTwo]
  have hsum : (x + (2 - p) / p * x) / 2 = x / p := by
    field_simp [hp_pos.ne']
    ring
  have hdiff : (x - (2 - p) / p * x) / 2 = ((p - 1) / p) * x := by
    field_simp [hp_pos.ne']
    ring
  rw [hsum, hdiff, abs_of_pos (div_pos hx hp_pos),
    abs_of_pos (mul_pos (div_pos hpden_pos hp_pos) hx)]
  have hmul :
      (((p - 1) / p) * x) ^ p = ((p - 1) / p) ^ p * x ^ p := by
    rw [Real.mul_rpow (div_nonneg hpden_nonneg hp_pos.le) hx_nonneg]
  change (x / p) ^ p - (p - 1)⁻¹ ^ p * ((((p - 1) / p) * x) ^ p) = 0
  rw [hmul]
  have hdiv : (x / p) ^ p = x ^ p / p ^ p := by
    rw [Real.div_rpow hx_nonneg hp_pos.le]
  rw [hdiv]
  have hcoef :
      (p - 1)⁻¹ ^ p * (((p - 1) / p) ^ p * x ^ p) = x ^ p / p ^ p := by
    rw [Real.div_rpow hpden_nonneg hp_pos.le]
    have hinv_mul : (p - 1)⁻¹ ^ p * ((p - 1) ^ p * (p ^ p)⁻¹ * x ^ p)
        = x ^ p * (p ^ p)⁻¹ := by
      have hcancel : (p - 1)⁻¹ ^ p * (p - 1) ^ p = 1 := by
        rw [← Real.mul_rpow (inv_nonneg.mpr hpden_nonneg) hpden_nonneg]
        simp [hpden_pos.ne']
      calc
        (p - 1)⁻¹ ^ p * ((p - 1) ^ p * (p ^ p)⁻¹ * x ^ p)
            = ((p - 1)⁻¹ ^ p * (p - 1) ^ p) * (p ^ p)⁻¹ * x ^ p := by ring
        _ = x ^ p * (p ^ p)⁻¹ := by
          rw [hcancel]
          ring
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hinv_mul
  rw [hcoef]
  ring

private lemma uA1_eq_vLeTwo_on_inter_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ)
    (h1 : closureA1 p x y) (h2 : closureA2 p x y) :
    uA1 p x y = vLeTwo p x y := by
  obtain ⟨hx, _hneg, hy_ax⟩ := h1
  obtain ⟨_, hax_y, _hyx⟩ := h2
  have heq : y = a p * x := le_antisymm hy_ax hax_y
  rcases hx.lt_or_eq with hxpos | hxeq
  · rw [heq]
    exact (uA1_eq_zero_on_boundary_leTwo p x hp1 hp2 hxpos).trans
      (vLeTwo_eq_zero_on_boundary_leTwo p x hp1 hp2 hxpos).symm
  · have hx0 : x = 0 := hxeq.symm
    subst x
    have hy0 : y = 0 := by linarith
    subst y
    simp [uA1, vLeTwo, Real.zero_rpow (by linarith : p ≠ 0)]

private lemma auxFunction1_eq_vLeTwo_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ)
    (h2 : closureA2 p x y) :
    auxFunction1 p x y = vLeTwo p x y := by
  simp only [auxFunction1]
  by_cases h1 : closureA1 p x y
  · simp only [h1, ite_true]
    exact uA1_eq_vLeTwo_on_inter_leTwo p hp1 hp2 x y h1 h2
  · simp only [h1, ite_false, h2, ite_true]

private lemma DxuA1_eq_DxvLeTwo_on_A1A2_boundary_leTwo
    (p x : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hx : 0 < x) :
    DxuA1 p x ((a p) * x) = DxvLeTwo p x ((a p) * x) := by
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  have hpden_nonneg : 0 ≤ p - 1 := hpden_pos.le
  have hx_nonneg : 0 ≤ x := hx.le
  simp only [DxuA1, gt_iff_lt, hx, ↓reduceIte, alpha_eq_leTwo p hp1 hp2, Real.rpow_eq_pow,
    a_eq_leTwo p hp1 hp2, DxvLeTwo]
  have hsum : (x + (2 - p) / p * x) / 2 = x / p := by
    field_simp [hp_pos.ne']
    ring
  have hdiff : (x - (2 - p) / p * x) / 2 = ((p - 1) / p) * x := by
    field_simp [hp_pos.ne']
    ring
  rw [hsum, hdiff, abs_of_pos (div_pos hx hp_pos),
    abs_of_pos (mul_pos (div_pos hpden_pos hp_pos) hx)]
  have hmul_diff :
      (((p - 1) / p) * x) ^ (p - 1) =
        ((p - 1) / p) ^ (p - 1) * x ^ (p - 1) := by
    rw [Real.mul_rpow (div_nonneg hpden_nonneg hp_pos.le) hx_nonneg]
  have hdiv_x : (x / p) ^ (p - 1) = x ^ (p - 1) / p ^ (p - 1) := by
    rw [Real.div_rpow hx_nonneg hp_pos.le]
  have hdiv_coeff :
      ((p - 1) / p) ^ (p - 1) =
        (p - 1) ^ (p - 1) / p ^ (p - 1) := by
    rw [Real.div_rpow hpden_nonneg hp_pos.le]
  rw [hmul_diff, hdiv_x, hdiv_coeff]
  have hbr :
      (p - 2) / (p - 1) * x + (2 - p) / p * x =
        ((p - 2) / (p * (p - 1))) * x := by
    field_simp [hp_pos.ne', hpden_pos.ne']
    ring
  rw [hbr]
  have hxpow : x ^ (p - 2) * x = x ^ (p - 1) := by
    calc
      x ^ (p - 2) * x = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((p - 2) + 1) := by rw [← Real.rpow_add hx]
      _ = x ^ (p - 1) := by ring_nf
  have hxpow' :
      x ^ (p - 2) * (((p - 2) / (p * (p - 1))) * x) =
        ((p - 2) / (p * (p - 1))) * x ^ (p - 1) := by
    calc
      x ^ (p - 2) * (((p - 2) / (p * (p - 1))) * x)
          = ((p - 2) / (p * (p - 1))) * (x ^ (p - 2) * x) := by ring
      _ = ((p - 2) / (p * (p - 1))) * x ^ (p - 1) := by rw [hxpow]
  rw [show
    p * p ^ (1 - p) * (p / 2) * x ^ (p - 2) *
        (((p - 2) / (p * (p - 1))) * x) =
      p * p ^ (1 - p) * (p / 2) *
        (x ^ (p - 2) * (((p - 2) / (p * (p - 1))) * x)) by ring]
  rw [hxpow']
  have hcancel :
      Real.rpow ((p - 1)⁻¹) p *
          ((p - 1) ^ (p - 1) / p ^ (p - 1) * x ^ (p - 1)) =
        ((p - 1)⁻¹ / p ^ (p - 1)) * x ^ (p - 1) := by
    have hpow : (p - 1)⁻¹ ^ p * (p - 1) ^ (p - 1) = (p - 1)⁻¹ := by
      have hcancel0 :
          (p - 1)⁻¹ ^ (p - 1) * (p - 1) ^ (p - 1) = 1 := by
        rw [← Real.mul_rpow (inv_nonneg.mpr hpden_nonneg) hpden_nonneg]
        simp [hpden_pos.ne']
      have hsplit :
          (p - 1)⁻¹ ^ p =
            (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ := by
        calc
          (p - 1)⁻¹ ^ p = (p - 1)⁻¹ ^ ((p - 1) + 1) := by
            congr 1
            ring
          _ = (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ ^ (1 : ℝ) := by
            rw [Real.rpow_add (inv_pos.mpr hpden_pos)]
          _ = (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ := by
            rw [Real.rpow_one]
      rw [hsplit]
      calc
        ((p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹) * (p - 1) ^ (p - 1)
            = ((p - 1)⁻¹ ^ (p - 1) * (p - 1) ^ (p - 1)) * (p - 1)⁻¹ := by ring
        _ = (p - 1)⁻¹ := by
          rw [hcancel0]
          ring
    rw [div_eq_mul_inv]
    calc
      (p - 1)⁻¹ ^ p * ((p - 1) ^ (p - 1) * (p ^ (p - 1))⁻¹ * x ^ (p - 1))
          = ((p - 1)⁻¹ ^ p * (p - 1) ^ (p - 1)) * (p ^ (p - 1))⁻¹ *
              x ^ (p - 1) := by ring
      _ = (p - 1)⁻¹ * (p ^ (p - 1))⁻¹ * x ^ (p - 1) := by rw [hpow]
  rw [coeffLeTwo]
  rw [hcancel]
  have hp_pow_cancel : p ^ (1 - p) * p ^ (-1 + p) = 1 := by
    calc
      p ^ (1 - p) * p ^ (-1 + p) = p ^ ((1 - p) + (-1 + p)) := by
        rw [← Real.rpow_add hp_pos]
      _ = p ^ (0 : ℝ) := by ring_nf
      _ = 1 := by rw [Real.rpow_zero]
  have hp_pow_cancel' : p ^ (1 - p) * p ^ (p - 1) = 1 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hp_pow_cancel
  field_simp [hp_pos.ne', hpden_pos.ne']
  rw [show p ^ (1 - p) * (p - 2) * p ^ (p - 1) =
      (p - 2) * (p ^ (1 - p) * p ^ (p - 1)) by ring]
  rw [hp_pow_cancel']
  ring

private lemma DyuA1_eq_DyvLeTwo_on_A1A2_boundary_leTwo
    (p x : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hx : 0 < x) :
    DyuA1 p x ((a p) * x) = DyvLeTwo p x ((a p) * x) := by
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  have hpden_nonneg : 0 ≤ p - 1 := hpden_pos.le
  have hx_nonneg : 0 ≤ x := hx.le
  have hpStar : pStar p = q p := pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  simp only [DyuA1, gt_iff_lt, hx, ↓reduceIte, alpha_eq_leTwo p hp1 hp2, Real.rpow_eq_pow,
    hpStar, q, hp_ne_one, DyvLeTwo, a_eq_leTwo p hp1 hp2]
  have hsum : (x + (2 - p) / p * x) / 2 = x / p := by
    field_simp [hp_pos.ne']
    ring
  have hdiff : (x - (2 - p) / p * x) / 2 = ((p - 1) / p) * x := by
    field_simp [hp_pos.ne']
    ring
  rw [hsum, hdiff, abs_of_pos (div_pos hx hp_pos),
    abs_of_pos (mul_pos (div_pos hpden_pos hp_pos) hx)]
  have hmul_diff :
      (((p - 1) / p) * x) ^ (p - 1) =
        ((p - 1) / p) ^ (p - 1) * x ^ (p - 1) := by
    rw [Real.mul_rpow (div_nonneg hpden_nonneg hp_pos.le) hx_nonneg]
  have hdiv_x : (x / p) ^ (p - 1) = x ^ (p - 1) / p ^ (p - 1) := by
    rw [Real.div_rpow hx_nonneg hp_pos.le]
  have hdiv_coeff :
      ((p - 1) / p) ^ (p - 1) =
        (p - 1) ^ (p - 1) / p ^ (p - 1) := by
    rw [Real.div_rpow hpden_nonneg hp_pos.le]
  rw [hmul_diff, hdiv_x, hdiv_coeff]
  have hcancel :
      Real.rpow ((p - 1)⁻¹) p *
          ((p - 1) ^ (p - 1) / p ^ (p - 1) * x ^ (p - 1)) =
        ((p - 1)⁻¹ / p ^ (p - 1)) * x ^ (p - 1) := by
    have hpow : (p - 1)⁻¹ ^ p * (p - 1) ^ (p - 1) = (p - 1)⁻¹ := by
      have hcancel0 :
          (p - 1)⁻¹ ^ (p - 1) * (p - 1) ^ (p - 1) = 1 := by
        rw [← Real.mul_rpow (inv_nonneg.mpr hpden_nonneg) hpden_nonneg]
        simp [hpden_pos.ne']
      have hsplit :
          (p - 1)⁻¹ ^ p =
            (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ := by
        calc
          (p - 1)⁻¹ ^ p = (p - 1)⁻¹ ^ ((p - 1) + 1) := by
            congr 1
            ring
          _ = (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ ^ (1 : ℝ) := by
            rw [Real.rpow_add (inv_pos.mpr hpden_pos)]
          _ = (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ := by
            rw [Real.rpow_one]
      rw [hsplit]
      calc
        ((p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹) * (p - 1) ^ (p - 1)
            = ((p - 1)⁻¹ ^ (p - 1) * (p - 1) ^ (p - 1)) * (p - 1)⁻¹ := by ring
        _ = (p - 1)⁻¹ := by
          rw [hcancel0]
          ring
    rw [div_eq_mul_inv]
    calc
      (p - 1)⁻¹ ^ p * ((p - 1) ^ (p - 1) * (p ^ (p - 1))⁻¹ * x ^ (p - 1))
          = ((p - 1)⁻¹ ^ p * (p - 1) ^ (p - 1)) * (p ^ (p - 1))⁻¹ *
              x ^ (p - 1) := by ring
      _ = (p - 1)⁻¹ * (p ^ (p - 1))⁻¹ * x ^ (p - 1) := by rw [hpow]
  rw [coeffLeTwo]
  rw [hcancel]
  have hp_pow_cancel : p ^ (1 - p) * p ^ (-1 + p) = 1 := by
    calc
      p ^ (1 - p) * p ^ (-1 + p) = p ^ ((1 - p) + (-1 + p)) := by
        rw [← Real.rpow_add hp_pos]
      _ = p ^ (0 : ℝ) := by ring_nf
      _ = 1 := by rw [Real.rpow_zero]
  have hp_pow_cancel' : p ^ (1 - p) * p ^ (p - 1) = 1 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hp_pow_cancel
  field_simp [hp_pos.ne', hpden_pos.ne']
  rw [show p * p ^ (1 - p) * p ^ (p - 1) =
      p * (p ^ (1 - p) * p ^ (p - 1)) by ring]
  rw [hp_pow_cancel']
  ring

private lemma DxuA1_eq_DxvLeTwo_on_inter_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ)
    (h1 : closureA1 p x y) (h2 : closureA2 p x y) :
    DxuA1 p x y = DxvLeTwo p x y := by
  obtain ⟨hx, _hneg, hy_ax⟩ := h1
  obtain ⟨_, hax_y, _hyx⟩ := h2
  have heq : y = a p * x := le_antisymm hy_ax hax_y
  rcases hx.lt_or_eq with hxpos | hxeq
  · rw [heq]
    exact DxuA1_eq_DxvLeTwo_on_A1A2_boundary_leTwo p x hp1 hp2 hxpos
  · have hx0 : x = 0 := hxeq.symm
    subst x
    have hy0 : y = 0 := by linarith
    subst y
    simp [DxuA1, DxvLeTwo]

private lemma DyuA1_eq_DyvLeTwo_on_inter_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ)
    (h1 : closureA1 p x y) (h2 : closureA2 p x y) :
    DyuA1 p x y = DyvLeTwo p x y := by
  obtain ⟨hx, _hneg, hy_ax⟩ := h1
  obtain ⟨_, hax_y, _hyx⟩ := h2
  have heq : y = a p * x := le_antisymm hy_ax hax_y
  rcases hx.lt_or_eq with hxpos | hxeq
  · rw [heq]
    exact DyuA1_eq_DyvLeTwo_on_A1A2_boundary_leTwo p x hp1 hp2 hxpos
  · have hx0 : x = 0 := hxeq.symm
    subst x
    have hy0 : y = 0 := by linarith
    subst y
    simp [DyuA1, DyvLeTwo]

private lemma auxFunction1_Dx_eq_DxvLeTwo_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) (h2 : closureA2 p x y) :
    DxauxFunction1 p x y = DxvLeTwo p x y := by
  simp only [DxauxFunction1]
  by_cases h1 : closureA1 p x y
  · simp only [h1, ite_true]
    exact DxuA1_eq_DxvLeTwo_on_inter_leTwo p hp1 hp2 x y h1 h2
  · simp only [h1, ite_false, h2, ite_true]

private lemma auxFunction1_Dy_eq_DyvLeTwo_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) (h2 : closureA2 p x y) :
    DyauxFunction1 p x y = DyvLeTwo p x y := by
  simp only [DyauxFunction1]
  by_cases h1 : closureA1 p x y
  · simp only [h1, ite_true]
    exact DyuA1_eq_DyvLeTwo_on_inter_leTwo p hp1 hp2 x y h1 h2
  · simp only [h1, ite_false, h2, ite_true]

private lemma horizontal_boundary_closureA1_closureA2_leTwo
    (p y : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hy : 0 < y) :
    closureA1 p (y / a p) y ∧ closureA2 p (y / a p) y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hboundary : a p * (y / a p) = y := by
    field_simp [ha_pos.ne']
  have hx_pos : 0 < y / a p := div_pos hy ha_pos
  have hyx : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hneg : -(y / a p) < y := by
    linarith [hx_pos, hy]
  constructor
  · exact ⟨hx_pos.le, le_of_lt hneg, hboundary.ge⟩
  · exact ⟨hx_pos.le, hboundary.le, hyx.le⟩

private lemma vLeTwo_neg_neg_leTwo (p x y : ℝ) :
    vLeTwo p (-x) (-y) = vLeTwo p x y := by
  have hsum : ((-x + -y) / 2 : ℝ) = -((x + y) / 2) := by ring
  have hdiff : ((-x + y) / 2 : ℝ) = -((x - y) / 2) := by ring
  simp [vLeTwo, hsum, hdiff]

private lemma vLeTwo_swap_leTwo (p x y : ℝ) :
    vLeTwo p y x = vLeTwo p x y := by
  have hsum : ((y + x) / 2 : ℝ) = (x + y) / 2 := by ring
  have hdiff : ((y - x) / 2 : ℝ) = -((x - y) / 2) := by ring
  simp [vLeTwo, hsum, hdiff]

private lemma vLeTwo_le_auxFunction1_on_QuarterPlane_of_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hA1 : ∀ ⦃x y : ℝ⦄, closureA1 p x y → vLeTwo p x y ≤ uA1 p x y)
    {x y : ℝ} (hQ : QuarterPlane x y) :
    vLeTwo p x y ≤ auxFunction1 p x y := by
  by_cases h1 : closureA1 p x y
  · exact (hA1 h1).trans_eq (by simp [auxFunction1, h1])
  · have h2 : closureA2 p x y := by
      rcases hQ with ⟨hx, hyx, hnegx_y⟩
      have hy_ge_ax : a p * x ≤ y := by
        by_contra hy_not
        exact h1 ⟨hx, hnegx_y, le_of_not_ge hy_not⟩
      exact ⟨hx, hy_ge_ax, hyx⟩
    exact le_of_eq (auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 x y h2).symm

private lemma vLeTwo_le_uCandidate_of_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (hA1 : ∀ ⦃x y : ℝ⦄, closureA1 p x y → vLeTwo p x y ≤ uA1 p x y)
    (x y : ℝ) :
    vLeTwo p x y ≤ uCandidate p x y := by
  rcases mem_some_QuarterPlane_leTwo x y with hQ1 | hrest
  · rw [uCandidate_eq_Q1_leTwo p hQ1]
    exact vLeTwo_le_auxFunction1_on_QuarterPlane_of_A1_leTwo p hp1 hp2 hA1 hQ1
  rcases hrest with hQ2 | hrest
  · have hQ : QuarterPlane (-x) (-y) :=
      ⟨by linarith [hQ2.1], by linarith [hQ2.2.2], by linarith [hQ2.2.1]⟩
    rw [uCandidate_eq_Q2_leTwo p hQ2, ← vLeTwo_neg_neg_leTwo p x y]
    exact vLeTwo_le_auxFunction1_on_QuarterPlane_of_A1_leTwo p hp1 hp2 hA1 hQ
  rcases hrest with hQ3 | hQ4
  · have hQ : QuarterPlane y x := ⟨hQ3.1, hQ3.2.2, hQ3.2.1⟩
    rw [uCandidate_eq_Q3_leTwo p hQ3, ← vLeTwo_swap_leTwo p x y]
    exact vLeTwo_le_auxFunction1_on_QuarterPlane_of_A1_leTwo p hp1 hp2 hA1 hQ
  · have hQ : QuarterPlane (-y) (-x) :=
      ⟨by linarith [hQ4.1], by linarith [hQ4.2.1], by linarith [hQ4.2.2]⟩
    have hv : vLeTwo p (-y) (-x) = vLeTwo p x y := by
      rw [vLeTwo_neg_neg_leTwo p y x, vLeTwo_swap_leTwo p y x]
    rw [uCandidate_eq_Q4_leTwo p hQ4, ← hv]
    exact vLeTwo_le_auxFunction1_on_QuarterPlane_of_A1_leTwo p hp1 hp2 hA1 hQ

private lemma scalar_deriv_sum_lower_leTwo
    (p t : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (ht_lower : (p - 1) / p ≤ t) (ht_upper : t ≤ 1) :
    alpha p * pStar p / p ≤
      (1 - t) ^ (p - 1) + coeffLeTwo p * t ^ (p - 1) := by
  let lam : ℝ := p * (1 - t)
  let mu : ℝ := p * t - (p - 1)
  have hp_pos : 0 < p := by linarith
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hpden_pos : 0 < p - 1 := by linarith
  have hp_ne : p ≠ 0 := by linarith
  have hpden_nonneg : 0 ≤ p - 1 := le_of_lt hpden_pos
  have hp_ne_one : p ≠ 1 := by linarith
  have hr_nonneg : 0 ≤ p - 1 := by linarith
  have hr_le_one : p - 1 ≤ 1 := by linarith
  have hlam_nonneg : 0 ≤ lam := by
    dsimp [lam]
    exact mul_nonneg hp_nonneg (sub_nonneg.mpr ht_upper)
  have hmu_nonneg : 0 ≤ mu := by
    dsimp [mu]
    rw [sub_nonneg]
    have h := (div_le_iff₀ hp_pos).mp ht_lower
    simpa [mul_comm] using h
  have hsum : lam + mu = 1 := by
    dsimp [lam, mu]
    ring
  have hpow_conc := Real.concaveOn_rpow hr_nonneg hr_le_one
  have hfirst :
      lam * (1 / p) ^ (p - 1) + mu * (0 : ℝ) ^ (p - 1) ≤
        (1 - t) ^ (p - 1) := by
    have hmem₁ : (1 / p : ℝ) ∈ Set.Ici 0 := by
      exact div_nonneg zero_le_one hp_nonneg
    have hmem₀ : (0 : ℝ) ∈ Set.Ici 0 := by simp
    have h :=
      hpow_conc.2 hmem₁ hmem₀ hlam_nonneg hmu_nonneg hsum
    have hcombo :
        lam • (1 / p : ℝ) + mu • (0 : ℝ) = 1 - t := by
      dsimp [lam, mu]
      field_simp [hp_ne]
      ring
    have hcombo' : lam * p⁻¹ = 1 - t := by
      dsimp [lam]
      field_simp [hp_ne]
    simpa [smul_eq_mul, one_div, hcombo'] using h
  have hsecond :
      lam * ((p - 1) / p) ^ (p - 1) + mu ≤
        t ^ (p - 1) := by
    have hmem₁ : ((p - 1) / p : ℝ) ∈ Set.Ici 0 := by
      exact div_nonneg hpden_nonneg hp_nonneg
    have hmem₂ : (1 : ℝ) ∈ Set.Ici 0 := by simp
    have h :=
      hpow_conc.2 hmem₁ hmem₂ hlam_nonneg hmu_nonneg hsum
    have hcombo :
        lam • ((p - 1) / p : ℝ) + mu • (1 : ℝ) = t := by
      dsimp [lam, mu]
      field_simp [hp_ne]
      ring
    have hcombo' : lam * ((p - 1) / p) + mu = t := by
      dsimp [lam, mu]
      field_simp [hp_ne]
      ring
    simpa [smul_eq_mul, one_div, hcombo'] using h
  have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
  have hB :
      alpha p * pStar p / p =
        (1 / p) ^ (p - 1) + coeffLeTwo p * ((p - 1) / p) ^ (p - 1) := by
    have hpStar : pStar p = q p :=
      pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
    have halpha : alpha p = p * p ^ (1 - p) :=
      alpha_eq_leTwo p hp1 hp2
    have hp_inv_pow :
        (p ^ (p - 1))⁻¹ = p ^ (1 - p) := by
      rw [show 1 - p = -(p - 1) by ring]
      rw [Real.rpow_neg hp_nonneg]
    have hone_div_pow :
        (1 / p) ^ (p - 1) = p ^ (1 - p) := by
      rw [one_div, Real.inv_rpow hp_nonneg]
      exact hp_inv_pow
    have hcoeff_piece :
        coeffLeTwo p * ((p - 1) / p) ^ (p - 1) =
          (p - 1)⁻¹ * p ^ (1 - p) := by
      rw [coeffLeTwo, Real.div_rpow hpden_nonneg hp_nonneg]
      rw [div_eq_mul_inv, hp_inv_pow]
      change (p - 1)⁻¹ ^ p * ((p - 1) ^ (p - 1) * p ^ (1 - p)) =
          (p - 1)⁻¹ * p ^ (1 - p)
      have hcancel :
          (p - 1)⁻¹ ^ (p - 1) * (p - 1) ^ (p - 1) = 1 := by
        rw [← Real.mul_rpow (inv_nonneg.mpr hpden_nonneg) hpden_nonneg]
        simp [hpden_pos.ne']
      have hsplit :
          (p - 1)⁻¹ ^ p =
            (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ := by
        calc
          (p - 1)⁻¹ ^ p = (p - 1)⁻¹ ^ ((p - 1) + 1) := by
              congr 1
              ring
          _ = (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ ^ (1 : ℝ) := by
              rw [Real.rpow_add (inv_pos.mpr hpden_pos)]
          _ = (p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹ := by
              rw [Real.rpow_one]
      rw [hsplit]
      calc
        ((p - 1)⁻¹ ^ (p - 1) * (p - 1)⁻¹) *
            ((p - 1) ^ (p - 1) * p ^ (1 - p))
            = ((p - 1)⁻¹ ^ (p - 1) * (p - 1) ^ (p - 1)) *
                ((p - 1)⁻¹ * p ^ (1 - p)) := by ring
        _ = (p - 1)⁻¹ * p ^ (1 - p) := by
          rw [hcancel]
          ring
    rw [halpha, hpStar, q]
    simp only [hp_ne_one, ↓reduceIte, one_div]
    rw [show p⁻¹ ^ (p - 1) = p ^ (1 - p) by
      simpa [one_div] using hone_div_pow, hcoeff_piece]
    field_simp [hp_ne, hpden_pos.ne']
    ring
  have hend :
      (1 / p) ^ (p - 1) + coeffLeTwo p * ((p - 1) / p) ^ (p - 1)
        ≤ coeffLeTwo p := by
    rw [← hB]
    have htwo_sub_nonneg : 0 ≤ 2 - p := by linarith
    have hweights : (p - 1) + (2 - p) = 1 := by ring
    have hamgm :
        (p - 1) ^ (p - 1) * p ^ (2 - p) ≤ 1 := by
      have h := Real.geom_mean_le_arith_mean2_weighted
        hpden_nonneg htwo_sub_nonneg hpden_nonneg hp_nonneg hweights
      calc
        (p - 1) ^ (p - 1) * p ^ (2 - p)
            ≤ (p - 1) * (p - 1) + (2 - p) * p := h
        _ = 1 := by ring
    have hdenpow_pos : 0 < (p - 1) ^ (p - 1) :=
      Real.rpow_pos_of_pos hpden_pos _
    have hp_pow_le_inv :
        p ^ (2 - p) ≤ ((p - 1) ^ (p - 1))⁻¹ := by
      rw [show ((p - 1) ^ (p - 1))⁻¹ = 1 / ((p - 1) ^ (p - 1)) by
        rw [one_div]]
      rw [le_div_iff₀ hdenpow_pos]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hamgm
    have hinv_eq :
        ((p - 1) ^ (p - 1))⁻¹ = (p - 1) ^ (1 - p) := by
      rw [← Real.rpow_neg hpden_nonneg]
      congr 1
      ring
    have hp_pow :
        p ^ (2 - p) ≤ (p - 1) ^ (1 - p) := by
      rwa [hinv_eq] at hp_pow_le_inv
    have hleft_eq :
        alpha p * pStar p / p = p ^ (2 - p) / (p - 1) := by
      have hpStar : pStar p = q p :=
        pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
      rw [alpha_eq_leTwo p hp1 hp2, hpStar, q]
      simp only [hp_ne_one, ↓reduceIte]
      have hpow_shift : p * p ^ (1 - p) = p ^ (2 - p) := by
        calc
          p * p ^ (1 - p) = p ^ (1 : ℝ) * p ^ (1 - p) := by
              rw [Real.rpow_one]
          _ = p ^ ((1 : ℝ) + (1 - p)) := by
              rw [Real.rpow_add hp_pos]
          _ = p ^ (2 - p) := by ring
      rw [← hpow_shift]
      field_simp [hp_ne, hpden_pos.ne']
    have hcoeff_eq :
        coeffLeTwo p = (p - 1) ^ (-p) := by
      rw [coeffLeTwo]
      exact (Real.rpow_neg_eq_inv_rpow (p - 1) p).symm
    have hdiv_eq :
        (p - 1) ^ (1 - p) / (p - 1) = (p - 1) ^ (-p) := by
      rw [div_eq_mul_inv]
      rw [show (p - 1)⁻¹ = (p - 1) ^ (-1 : ℝ) by
        rw [Real.rpow_neg_one]]
      rw [← Real.rpow_add hpden_pos]
      congr 1
      ring
    calc
      alpha p * pStar p / p = p ^ (2 - p) / (p - 1) := hleft_eq
      _ ≤ (p - 1) ^ (1 - p) / (p - 1) :=
          div_le_div_of_nonneg_right hp_pow hpden_pos.le
      _ = (p - 1) ^ (-p) := hdiv_eq
      _ = coeffLeTwo p := hcoeff_eq.symm
  have hmul_second :
      coeffLeTwo p *
        (lam * ((p - 1) / p) ^ (p - 1) + mu)
        ≤ coeffLeTwo p * t ^ (p - 1) := by
    exact mul_le_mul_of_nonneg_left hsecond
      (coeffLeTwo_nonneg_of_one_lt_of_lt_two p hp1 hp2)
  calc
    alpha p * pStar p / p
        = lam * (alpha p * pStar p / p) + mu * (alpha p * pStar p / p) := by
            rw [← add_mul, hsum, one_mul]
    _ ≤ lam *
          ((1 / p) ^ (p - 1) + coeffLeTwo p * ((p - 1) / p) ^ (p - 1)) +
        mu * coeffLeTwo p := by
          rw [hB]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hend hmu_nonneg)
    _ = (lam * (1 / p) ^ (p - 1) + mu * (0 : ℝ) ^ (p - 1)) +
        coeffLeTwo p *
          (lam * ((p - 1) / p) ^ (p - 1) + mu) := by
          rw [hzero]
          ring
    _ ≤ (1 - t) ^ (p - 1) + coeffLeTwo p * t ^ (p - 1) := by
          exact add_le_add hfirst hmul_second

private lemma burkholder_scalar_gap_antitone_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    AntitoneOn
      (fun t : ℝ =>
        (1 - t) ^ p - coeffLeTwo p * t ^ p -
          alpha p * (1 - pStar p * t))
      (Set.Icc ((p - 1) / p) 1) := by
  let F : ℝ → ℝ := fun t =>
    (1 - t) ^ p - coeffLeTwo p * t ^ p -
      alpha p * (1 - pStar p * t)
  let F' : ℝ → ℝ := fun t =>
    p * (alpha p * pStar p / p -
      ((1 - t) ^ (p - 1) + coeffLeTwo p * t ^ (p - 1)))
  have hp_pos : 0 < p := by linarith
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hpden_pos : 0 < p - 1 := by linarith
  have hp_ne : p ≠ 0 := by linarith
  have hcont : ContinuousOn F (Set.Icc ((p - 1) / p) 1) := by
    dsimp [F]
    apply ContinuousOn.sub
    · apply ContinuousOn.sub
      · exact ((continuousOn_const.sub continuousOn_id).rpow_const
          (by intro t ht; exact Or.inr (by linarith : 0 ≤ p)))
      · exact continuousOn_const.mul
          (continuousOn_id.rpow_const
            (by intro t ht; exact Or.inr (by linarith : 0 ≤ p)))
    · exact continuousOn_const.mul
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
  have hderiv :
      ∀ t ∈ interior (Set.Icc ((p - 1) / p) 1),
        HasDerivWithinAt F (F' t) (interior (Set.Icc ((p - 1) / p) 1)) t := by
    intro t ht
    have htI : t ∈ Set.Ioo ((p - 1) / p) 1 := by
      simpa [interior_Icc] using ht
    have ht_pos : 0 < t := by
      have hbase : 0 < (p - 1) / p := div_pos hpden_pos hp_pos
      exact lt_trans hbase htI.1
    have h1t_pos : 0 < 1 - t := sub_pos.mpr htI.2
    have hone_sub :
        HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have hpow1 :
        HasDerivAt (fun s : ℝ => (1 - s) ^ p)
          (p * (1 - t) ^ (p - 1) * (-1)) t := by
      have hbase :
          HasDerivAt (fun u : ℝ => u ^ p)
            (p * (1 - t) ^ (p - 1)) (1 - t) :=
        Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt h1t_pos))
      exact hbase.comp t hone_sub
    have hpow2 :
        HasDerivAt (fun s : ℝ => s ^ p)
          (p * t ^ (p - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht_pos))
    have hlin :
        HasDerivAt (fun s : ℝ => alpha p * (1 - pStar p * s))
          (alpha p * (-pStar p)) t := by
      have hbase :
          HasDerivAt (fun s : ℝ => 1 - pStar p * s) (-pStar p) t := by
        simpa using ((hasDerivAt_id t).const_mul (pStar p)).const_sub (1 : ℝ)
      exact hbase.const_mul (alpha p)
    have hmain :
        HasDerivAt F
          ((p * (1 - t) ^ (p - 1) * (-1)) -
            coeffLeTwo p * (p * t ^ (p - 1)) -
            alpha p * (-pStar p)) t := by
      dsimp [F]
      exact (hpow1.sub (hpow2.const_mul (coeffLeTwo p))).sub hlin
    refine (hmain.congr_deriv ?_).hasDerivWithinAt
    dsimp [F']
    field_simp [hp_ne]
    ring
  have hderiv_nonpos :
      ∀ t ∈ interior (Set.Icc ((p - 1) / p) 1), F' t ≤ 0 := by
    intro t ht
    have htI : t ∈ Set.Ioo ((p - 1) / p) 1 := by
      simpa [interior_Icc] using ht
    have hsum := scalar_deriv_sum_lower_leTwo p t hp1 hp2
      (le_of_lt htI.1) (le_of_lt htI.2)
    dsimp [F']
    have hbracket :
        alpha p * pStar p / p -
          ((1 - t) ^ (p - 1) + coeffLeTwo p * t ^ (p - 1)) ≤ 0 := by
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos hp_nonneg hbracket
  simpa [F] using
    antitoneOn_of_hasDerivWithinAt_nonpos
      (convex_Icc ((p - 1) / p) 1) hcont hderiv hderiv_nonpos

private lemma burkholder_scalar_A1_leTwo
    (p t : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (ht_lower : (p - 1) / p ≤ t) (ht_upper : t ≤ 1) :
    (1 - t) ^ p - coeffLeTwo p * t ^ p ≤
      alpha p * (1 - pStar p * t) := by
  let H : ℝ → ℝ := fun s =>
    (1 - s) ^ p - coeffLeTwo p * s ^ p -
      alpha p * (1 - pStar p * s)
  have hanti : AntitoneOn H (Set.Icc ((p - 1) / p) 1) := by
    simpa [H] using burkholder_scalar_gap_antitone_leTwo p hp1 hp2
  have ht_mem : t ∈ Set.Icc ((p - 1) / p) 1 := ⟨ht_lower, ht_upper⟩
  have hb_mem : ((p - 1) / p) ∈ Set.Icc ((p - 1) / p) 1 := by
    constructor
    · rfl
    · have hp_pos : 0 < p := by linarith
      rw [div_le_iff₀ hp_pos]
      linarith
  have hle : H t ≤ H ((p - 1) / p) :=
    hanti hb_mem ht_mem ht_lower
  have hb : H ((p - 1) / p) = 0 := by
    have hp_pos : 0 < p := by linarith
    have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
    have hpden_pos : 0 < p - 1 := by linarith
    have hpden_nonneg : 0 ≤ p - 1 := le_of_lt hpden_pos
    have hp_ne : p ≠ 0 := by linarith
    have hp_ne_one : p ≠ 1 := by linarith
    have h1 :
        1 - (p - 1) / p = 1 / p := by
      field_simp [hp_ne]
      ring
    have hps :
        pStar p * ((p - 1) / p) = 1 := by
      rw [pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2]
      simp [q, hp_ne_one]
      field_simp [hp_ne, hpden_pos.ne']
    have hfirst : (1 / p) ^ p = (p ^ p)⁻¹ := by
      rw [one_div, Real.inv_rpow hp_nonneg]
    have hsecond :
        coeffLeTwo p * ((p - 1) / p) ^ p = (p ^ p)⁻¹ := by
      rw [coeffLeTwo, Real.div_rpow hpden_nonneg hp_nonneg]
      have hcancel : (p - 1)⁻¹ ^ p * (p - 1) ^ p = 1 := by
        rw [← Real.mul_rpow (inv_nonneg.mpr hpden_nonneg) hpden_nonneg]
        simp [hpden_pos.ne']
      calc
        (p - 1)⁻¹ ^ p * ((p - 1) ^ p / p ^ p)
            = ((p - 1)⁻¹ ^ p * (p - 1) ^ p) * (p ^ p)⁻¹ := by
                ring
        _ = (p ^ p)⁻¹ := by rw [hcancel]; ring
    dsimp [H]
    rw [h1, hfirst, hsecond, hps]
    ring
  have hH_nonpos : H t ≤ 0 := by
    rwa [hb] at hle
  dsimp [H] at hH_nonpos
  linarith

private lemma vLeTwo_le_uA1_on_closureA1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hA1 : closureA1 p x y) :
    vLeTwo p x y ≤ uA1 p x y := by
  rcases hA1 with ⟨hx_nonneg, hlow, hyup⟩
  rcases hx_nonneg.eq_or_lt with rfl | hxpos
  · have hy0 : y = 0 := by linarith
    subst y
    simp [vLeTwo, uA1, Real.zero_rpow (by linarith : p ≠ 0)]
  · have hx_nonneg' : 0 ≤ x := le_of_lt hxpos
    have hp_pos : 0 < p := by linarith
    have hp_ne : p ≠ 0 := by linarith
    have hpden_pos : 0 < p - 1 := by linarith
    have hpStar : pStar p = q p := pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
    have hp_ne_one : p ≠ 1 := by linarith
    have ha_eq : a p = (2 - p) / p := a_eq_leTwo p hp1 hp2
    let t : ℝ := (x - y) / (2 * x)
    have ht_upper : t ≤ 1 := by
      dsimp [t]
      have hxy : x - y ≤ 2 * x := by linarith
      have hden_pos : 0 < 2 * x := mul_pos (by norm_num) hxpos
      have h := div_le_div_of_nonneg_right hxy hden_pos.le
      calc
        (x - y) / (2 * x) ≤ (2 * x) / (2 * x) := h
        _ = 1 := by field_simp [hxpos.ne']
    have ht_lower : (p - 1) / p ≤ t := by
      dsimp [t]
      rw [ha_eq] at hyup
      have hxy : 2 * x * ((p - 1) / p) ≤ x - y := by
        have htmp : x - (2 - p) / p * x = 2 * x * ((p - 1) / p) := by
          field_simp [hp_ne]
          ring
        linarith
      have hden_pos : 0 < 2 * x := mul_pos (by norm_num) hxpos
      rw [le_div_iff₀ hden_pos]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hxy
    have ht_nonneg : 0 ≤ t := by
      have hbase : 0 ≤ (p - 1) / p := div_nonneg (le_of_lt hpden_pos) hp_pos.le
      exact hbase.trans ht_lower
    have h1mt_nonneg : 0 ≤ 1 - t := by linarith
    have hsum_norm : (x + y) / 2 = x * (1 - t) := by
      dsimp [t]
      field_simp [hxpos.ne']
      ring
    have hdiff_norm : (x - y) / 2 = x * t := by
      dsimp [t]
      field_simp [hxpos.ne']
    have hlinear_norm :
        x - pStar p * (x - y) / 2 = x * (1 - pStar p * t) := by
      dsimp [t]
      field_simp [hxpos.ne']
    have hv_norm :
        vLeTwo p x y =
          x ^ p * ((1 - t) ^ p - coeffLeTwo p * t ^ p) := by
      have hsum_nonneg : 0 ≤ (x + y) / 2 := by
        rw [hsum_norm]
        exact mul_nonneg hx_nonneg' h1mt_nonneg
      have hdiff_nonneg : 0 ≤ (x - y) / 2 := by
        rw [hdiff_norm]
        exact mul_nonneg hx_nonneg' ht_nonneg
      calc
        vLeTwo p x y =
            ((x + y) / 2) ^ p - coeffLeTwo p * ((x - y) / 2) ^ p := by
              simp [vLeTwo, abs_of_nonneg hsum_nonneg, abs_of_nonneg hdiff_nonneg]
        _ = (x * (1 - t)) ^ p - coeffLeTwo p * (x * t) ^ p := by
              rw [hsum_norm, hdiff_norm]
        _ = x ^ p * (1 - t) ^ p - coeffLeTwo p * (x ^ p * t ^ p) := by
              rw [Real.mul_rpow hx_nonneg' h1mt_nonneg,
                Real.mul_rpow hx_nonneg' ht_nonneg]
        _ = x ^ p * ((1 - t) ^ p - coeffLeTwo p * t ^ p) := by ring
    have hu_norm :
        uA1 p x y = x ^ p * (alpha p * (1 - pStar p * t)) := by
      have hxpow : x ^ (p - 1) * x = x ^ p := by
        have h := Real.rpow_one_add' hx_nonneg'
          (by linarith : (1 : ℝ) + (p - 1) ≠ 0)
        have h' : x ^ p = x * x ^ (p - 1) := by
          simpa [show (1 : ℝ) + (p - 1) = p by ring] using h
        rw [h']
        ring
      calc
        uA1 p x y =
            alpha p * x ^ (p - 1) * (x - pStar p * (x - y) / 2) := by
              simp [uA1, hxpos]
        _ = alpha p * x ^ (p - 1) * (x * (1 - pStar p * t)) := by
              rw [hlinear_norm]
        _ = x ^ p * (alpha p * (1 - pStar p * t)) := by
              rw [← hxpow]
              ring
    have hscalar := burkholder_scalar_A1_leTwo p t hp1 hp2 ht_lower ht_upper
    have hxpow_nonneg : 0 ≤ x ^ p := Real.rpow_nonneg hx_nonneg' p
    calc
      vLeTwo p x y =
          x ^ p * ((1 - t) ^ p - coeffLeTwo p * t ^ p) := hv_norm
      _ ≤ x ^ p * (alpha p * (1 - pStar p * t)) :=
          mul_le_mul_of_nonneg_left hscalar hxpow_nonneg
      _ = uA1 p x y := hu_norm.symm

private lemma vLeTwo_le_uCandidate_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) :
    vLeTwo p x y ≤ uCandidate p x y :=
  vLeTwo_le_uCandidate_of_A1_leTwo p hp1 hp2
    (fun {_x _y} hA1 => vLeTwo_le_uA1_on_closureA1_leTwo p hp1 hp2 hA1) x y

private lemma uCandidate_neg_neg_of_y_neg_leTwo
    (p : ℝ) {x y : ℝ} (hy_neg : y < 0) :
    uCandidate p x y = uCandidate p (-x) (-y) := by
  by_cases hx_left : x ≤ y
  · have hQ2 : QuarterPlane2 x y := ⟨by linarith, by linarith, hx_left⟩
    have hQ_ref : QuarterPlane (-x) (-y) :=
      ⟨by linarith, by linarith, by linarith⟩
    have hnotQ : ¬ QuarterPlane x y := by
      intro hq
      linarith [hq.1]
    simp [uCandidate, hnotQ, hQ2, hQ_ref]
  · have hyx : y < x := lt_of_not_ge hx_left
    by_cases hx_mid : x < -y
    · have hQ4 : QuarterPlane4 x y := ⟨hy_neg.le, hyx.le, hx_mid.le⟩
      have hQ3_ref : QuarterPlane3 (-x) (-y) :=
        ⟨by linarith, by linarith, by linarith⟩
      have hnotQ : ¬ QuarterPlane x y := by
        intro hq
        linarith [hq.2.2]
      have hnotQ2 : ¬ QuarterPlane2 x y := by
        intro hq
        linarith [hq.2.2]
      have hnotQ3 : ¬ QuarterPlane3 x y := by
        intro hq
        linarith [hq.1]
      have hnotQ_ref : ¬ QuarterPlane (-x) (-y) := by
        intro hq
        linarith [hq.2.1]
      have hnotQ2_ref : ¬ QuarterPlane2 (-x) (-y) := by
        intro hq
        have hle : -y ≤ x := by simpa using hq.2.1
        linarith
      simp [uCandidate, hnotQ, hnotQ2, hnotQ3, hQ4, hnotQ_ref, hnotQ2_ref, hQ3_ref]
    · have hx_right : -y ≤ x := le_of_not_gt hx_mid
      have hQ : QuarterPlane x y := ⟨by linarith, by linarith, by linarith⟩
      have hQ2_ref : QuarterPlane2 (-x) (-y) :=
        ⟨by linarith, by linarith, by linarith⟩
      have hnotQ_ref : ¬ QuarterPlane (-x) (-y) := by
        intro hq
        linarith [hq.1]
      simp [uCandidate, hQ, hnotQ_ref, hQ2_ref]

private lemma DxuCandidate_neg_neg_of_y_neg_leTwo
    (p : ℝ) {x y : ℝ} (hy_neg : y < 0) :
    DxuCandidate p x y = -DxuCandidate p (-x) (-y) := by
  by_cases hx_left : x ≤ y
  · have hQ2 : QuarterPlane2 x y := ⟨by linarith, by linarith, hx_left⟩
    have hQ_ref : QuarterPlane (-x) (-y) :=
      ⟨by linarith, by linarith, by linarith⟩
    have hnotQ : ¬ QuarterPlane x y := by
      intro hq
      linarith [hq.1]
    simp [DxuCandidate, hnotQ, hQ2, hQ_ref]
  · have hyx : y < x := lt_of_not_ge hx_left
    by_cases hx_mid : x < -y
    · have hQ4 : QuarterPlane4 x y := ⟨hy_neg.le, hyx.le, hx_mid.le⟩
      have hQ3_ref : QuarterPlane3 (-x) (-y) :=
        ⟨by linarith, by linarith, by linarith⟩
      have hnotQ : ¬ QuarterPlane x y := by
        intro hq
        linarith [hq.2.2]
      have hnotQ2 : ¬ QuarterPlane2 x y := by
        intro hq
        linarith [hq.2.2]
      have hnotQ3 : ¬ QuarterPlane3 x y := by
        intro hq
        linarith [hq.1]
      have hnotQ_ref : ¬ QuarterPlane (-x) (-y) := by
        intro hq
        linarith [hq.2.1]
      have hnotQ2_ref : ¬ QuarterPlane2 (-x) (-y) := by
        intro hq
        have hle : -y ≤ x := by simpa using hq.2.1
        linarith
      simp [DxuCandidate, hnotQ, hnotQ2, hnotQ3, hQ4, hnotQ_ref, hnotQ2_ref, hQ3_ref]
    · have hx_right : -y ≤ x := le_of_not_gt hx_mid
      have hQ : QuarterPlane x y := ⟨by linarith, by linarith, by linarith⟩
      have hQ2_ref : QuarterPlane2 (-x) (-y) :=
        ⟨by linarith, by linarith, by linarith⟩
      have hnotQ_ref : ¬ QuarterPlane (-x) (-y) := by
        intro hq
        linarith [hq.1]
      simp [DxuCandidate, hQ, hnotQ_ref, hQ2_ref]

private lemma uCandidate_tangent_x_increment_of_y_neg_leTwo_of_pos
    (p : ℝ)
    (hpos_tangent :
      ∀ {x y h : ℝ}, 0 < y →
        uCandidate p (x + h) y ≤
          uCandidate p x y + DxuCandidate p x y * h)
    {x y h : ℝ} (hy_neg : y < 0) :
    uCandidate p (x + h) y ≤
      uCandidate p x y + DxuCandidate p x y * h := by
  have hpos : 0 < -y := by linarith
  have hmain := hpos_tangent (x := -x) (y := -y) (h := -h) hpos
  have hstart := uCandidate_neg_neg_of_y_neg_leTwo (p := p) (x := x) (y := y) hy_neg
  have hend := uCandidate_neg_neg_of_y_neg_leTwo (p := p) (x := x + h) (y := y) hy_neg
  have hdx := DxuCandidate_neg_neg_of_y_neg_leTwo (p := p) (x := x) (y := y) hy_neg
  calc
    uCandidate p (x + h) y = uCandidate p (-(x + h)) (-y) := hend
    _ = uCandidate p ((-x) + (-h)) (-y) := by ring
    _ ≤ uCandidate p (-x) (-y) + DxuCandidate p (-x) (-y) * (-h) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * h := by
      rw [← hstart, hdx]
      ring

private lemma concaveOn_Icc_tangent_inequality_of_hasDerivAt_leTwo
    {f : ℝ → ℝ} {a b x z f' : ℝ}
    (hf : ConcaveOn ℝ (Set.Icc a b) f)
    (hx : x ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b)
    (hderiv : HasDerivAt f f' x) :
    f z ≤ f x + f' * (z - x) := by
  rcases lt_trichotomy z x with hlt | heq | hgt
  · have hslope : f' ≤ slope f z x :=
      hf.le_slope_of_hasDerivAt hz hx hlt hderiv
    have hslope' : f' ≤ (f x - f z) / (x - z) := by
      simpa [slope_def_field] using hslope
    have hden_pos : 0 < x - z := by linarith
    have hmul := mul_le_mul_of_nonneg_right hslope' hden_pos.le
    field_simp [hden_pos.ne'] at hmul
    linarith
  · subst z
    simp
  · have hslope : slope f x z ≤ f' :=
      hf.slope_le_of_hasDerivAt hx hz hgt hderiv
    have hslope' : (f z - f x) / (z - x) ≤ f' := by
      simpa [slope_def_field] using hslope
    have hden_pos : 0 < z - x := by linarith
    have hmul := mul_le_mul_of_nonneg_right hslope' hden_pos.le
    field_simp [hden_pos.ne'] at hmul
    linarith

private lemma tangent_inequality_on_Icc_of_hasDerivWithinAt2_nonpos_leTwo
    {f f₁ f₂ : ℝ → ℝ} {a b x z f' : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hf₁ : ∀ t ∈ interior (Set.Icc a b),
      HasDerivWithinAt f (f₁ t) (interior (Set.Icc a b)) t)
    (hf₂ : ∀ t ∈ interior (Set.Icc a b),
      HasDerivWithinAt f₁ (f₂ t) (interior (Set.Icc a b)) t)
    (hf₂_nonpos : ∀ t ∈ interior (Set.Icc a b), f₂ t ≤ 0)
    (hx : x ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b)
    (hderiv : HasDerivAt f f' x) :
    f z ≤ f x + f' * (z - x) := by
  exact concaveOn_Icc_tangent_inequality_of_hasDerivAt_leTwo
    (concaveOn_of_hasDerivWithinAt2_nonpos
      (convex_Icc a b) hcont hf₁ hf₂ hf₂_nonpos)
    hx hz hderiv

private lemma hasDerivAt_uA1_x_of_pos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => uA1 p t y) (DxuA1 p x y) x := by
  have hpStar : pStar p = q p := pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hpden_ne : p - 1 ≠ 0 := by linarith
  let g : ℝ → ℝ := fun t =>
    alpha p * ((1 - pStar p / 2) * t ^ p + (pStar p * y / 2) * t ^ (p - 1))
  have hEq : (fun t => uA1 p t y) =ᶠ[nhds x] g := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have ht0 : 0 < t := by simpa [Set.mem_Ioi] using ht
    have hpow : t ^ p = t ^ (p - 1) * t := by
      calc
        t ^ p = t ^ ((p - 1) + (1 : ℝ)) := by ring_nf
        _ = t ^ (p - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_add ht0]
        _ = t ^ (p - 1) * t := by rw [Real.rpow_one]
    simp only [uA1, gt_iff_lt, ht0, ↓reduceIte, Real.rpow_eq_pow, g]
    rw [hpow]
    ring
  have hxne : x ≠ 0 := by linarith
  have hxne1 : x ≠ 0 ∨ 1 ≤ p := Or.inl hxne
  have hxne2 : x ≠ 0 ∨ 1 ≤ p - 1 := Or.inl hxne
  have hd1 :
      HasDerivAt (fun t : ℝ => t ^ p) (p * x ^ (p - 1)) x := by
    simpa using
      (Real.hasDerivAt_rpow_const hxne1 :
        HasDerivAt (fun t : ℝ => t ^ p) (p * x ^ (p - 1)) x)
  have hd2 :
      HasDerivAt (fun t : ℝ => t ^ (p - 1)) ((p - 1) * x ^ (p - 2)) x := by
    have h := (Real.hasDerivAt_rpow_const hxne2 :
      HasDerivAt (fun t : ℝ => t ^ (p - 1))
        ((p - 1) * x ^ ((p - 1) - 1)) x)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      show p + (-1 + -1) = p + -2 by ring] using h
  have hd :
      HasDerivAt g
        (alpha p *
          ((1 - pStar p / 2) * (p * x ^ (p - 1)) +
            (pStar p * y / 2) * ((p - 1) * x ^ (p - 2)))) x := by
    dsimp [g]
    have hsum :=
      ((hd1.const_mul (1 - pStar p / 2)).add
        (hd2.const_mul (pStar p * y / 2))).const_mul (alpha p)
    simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hsum
  have hpow : x ^ (p - 1) = x ^ (p - 2) * x := by
    calc
      x ^ (p - 1) = x ^ ((p - 2) + (1 : ℝ)) := by ring_nf
      _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hx]
      _ = x ^ (p - 2) * x := by rw [Real.rpow_one]
  have hg :
      HasDerivAt g
        (alpha p * (p / 2) * x ^ (p - 2) *
          (((p - 2) / (p - 1)) * x + y)) x := by
    refine hd.congr_deriv ?_
    rw [hpow, hpStar]
    simp [q, hp_ne_one]
    field_simp [hpden_ne]
    ring
  refine (hg.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DxuA1, hx]

private lemma deriv_DxuA1Fun_x_nonpos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ)
    (hx : 0 < x) (hxy : 0 ≤ x + y) :
    deriv (fun t => DxuA1Fun p (t, y)) x ≤ 0 := by
  have hpden_ne : p - 1 ≠ 0 := by linarith
  have hEq :
      (fun t => DxuA1Fun p (t, y)) =ᶠ[nhds x]
        fun t => alpha p * (p / 2) * t ^ (p - 2) *
          (((p - 2) / (p - 1)) * t + y) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have htpos : 0 < t := by simpa using ht
    simp [DxuA1Fun, DxuA1, htpos]
  have hxne : x ≠ 0 := by linarith
  have hxne_pow : x ≠ 0 ∨ 1 ≤ p - 2 := Or.inl hxne
  have hpow :
      HasDerivAt (fun t : ℝ => t ^ (p - 2)) ((p - 2) * x ^ (p - 3)) x := by
    have h := (Real.hasDerivAt_rpow_const hxne_pow :
      HasDerivAt (fun t : ℝ => t ^ (p - 2))
        ((p - 2) * x ^ ((p - 2) - 1)) x)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      show p + (-1 + -2) = p + -3 by ring] using h
  have hlin :
      HasDerivAt (fun t : ℝ => ((p - 2) / (p - 1)) * t + y)
        ((p - 2) / (p - 1)) x := by
    simpa using
      ((hasDerivAt_id x).const_mul ((p - 2) / (p - 1))).const_add y
  have hd :
      HasDerivAt
        (fun t : ℝ => alpha p * (p / 2) * t ^ (p - 2) *
          (((p - 2) / (p - 1)) * t + y))
        (alpha p * (p / 2) *
          (((p - 2) * x ^ (p - 3)) *
              (((p - 2) / (p - 1)) * x + y) +
            x ^ (p - 2) * ((p - 2) / (p - 1)))) x := by
    have hmul := hpow.mul hlin
    simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using
      hmul.const_mul (alpha p * (p / 2))
  have hshift : x ^ (p - 2) = x ^ (p - 3) * x := by
    calc
      x ^ (p - 2) = x ^ ((p - 3) + (1 : ℝ)) := by ring_nf
      _ = x ^ (p - 3) * x ^ (1 : ℝ) := by rw [Real.rpow_add hx]
      _ = x ^ (p - 3) * x := by rw [Real.rpow_one]
  have hderiv :
      deriv
        (fun t : ℝ => alpha p * (p / 2) * t ^ (p - 2) *
          (((p - 2) / (p - 1)) * t + y)) x
        = alpha p * (p / 2) * (p - 2) * x ^ (p - 3) * (x + y) := by
    rw [hd.deriv]
    rw [hshift]
    field_simp [hpden_ne]
    ring
  rw [hEq.deriv_eq, hderiv]
  have ha : 0 ≤ alpha p := alpha_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hp_nonneg : 0 ≤ p / 2 := by linarith
  have hp2_nonpos : p - 2 ≤ 0 := by linarith
  have hpow_nonneg : 0 ≤ x ^ (p - 3) := Real.rpow_nonneg hx.le _
  have hmain :
      (alpha p * (p / 2) * x ^ (p - 3)) * ((p - 2) * (x + y)) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg ha hp_nonneg) hpow_nonneg)
      (mul_nonpos_of_nonpos_of_nonneg hp2_nonpos hxy)
  rw [show alpha p * (p / 2) * (p - 2) * x ^ (p - 3) * (x + y) =
      (alpha p * (p / 2) * x ^ (p - 3)) * ((p - 2) * (x + y)) by ring]
  exact hmain

private lemma differentiableAt_DxuA1Fun_x_of_pos_leTwo
    (p x y : ℝ) (hx : 0 < x) :
    DifferentiableAt ℝ (fun t => DxuA1Fun p (t, y)) x := by
  have hEq :
      (fun t => DxuA1Fun p (t, y)) =ᶠ[nhds x]
        fun t => alpha p * (p / 2) * t ^ (p - 2) *
          (((p - 2) / (p - 1)) * t + y) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have htpos : 0 < t := by simpa using ht
    simp [DxuA1Fun, DxuA1, htpos]
  have hpow :
      DifferentiableAt ℝ (fun t : ℝ => t ^ (p - 2)) x := by
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).differentiableAt
  have hlin :
      DifferentiableAt ℝ (fun t : ℝ => ((p - 2) / (p - 1)) * t + y) x := by
    exact ((differentiableAt_id.const_mul ((p - 2) / (p - 1))).add
      (differentiableAt_const y))
  have hformula :
      DifferentiableAt ℝ
        (fun t : ℝ => alpha p * (p / 2) * t ^ (p - 2) *
          (((p - 2) / (p - 1)) * t + y)) x := by
    exact ((hpow.const_mul (alpha p * (p / 2))).mul hlin)
  exact hformula.congr_of_eventuallyEq hEq

private lemma uA1_tangent_x_on_Icc_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {lo hi x z y : ℝ}
    (hIcc_pos : ∀ t ∈ Set.Icc lo hi, 0 < t)
    (hIcc_sum : ∀ t ∈ interior (Set.Icc lo hi), 0 ≤ t + y)
    (hx : x ∈ Set.Icc lo hi) (hz : z ∈ Set.Icc lo hi) :
    uA1 p z y ≤ uA1 p x y + DxuA1 p x y * (z - x) := by
  apply tangent_inequality_on_Icc_of_hasDerivWithinAt2_nonpos_leTwo
      (f := fun t => uA1 p t y)
      (f₁ := fun t => DxuA1Fun p (t, y))
      (f₂ := fun t => deriv (fun s => DxuA1Fun p (s, y)) t)
      (f' := DxuA1 p x y)
  · have hEq :
        ∀ t ∈ Set.Icc lo hi,
          uA1 p t y =
            alpha p * ((1 - pStar p / 2) * t ^ p +
              (pStar p * y / 2) * t ^ (p - 1)) := by
      intro t ht
      have htpos := hIcc_pos t ht
      have hpow : t ^ p = t ^ (p - 1) * t := by
        calc
          t ^ p = t ^ ((p - 1) + (1 : ℝ)) := by ring_nf
          _ = t ^ (p - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_add htpos]
          _ = t ^ (p - 1) * t := by rw [Real.rpow_one]
      simp only [uA1, gt_iff_lt, htpos, ↓reduceIte, Real.rpow_eq_pow]
      rw [hpow]
      ring
    refine ContinuousOn.congr ?_ hEq
    apply continuousOn_const.mul
    apply ContinuousOn.add
    · exact continuousOn_const.mul
        (continuousOn_id.rpow_const (by intro t ht; exact Or.inl (ne_of_gt (hIcc_pos t ht))))
    · exact continuousOn_const.mul
        (continuousOn_id.rpow_const (by intro t ht; exact Or.inl (ne_of_gt (hIcc_pos t ht))))
  · intro t ht
    exact (hasDerivAt_uA1_x_of_pos_leTwo p hp1 hp2 t y (hIcc_pos t
      (interior_subset ht))).hasDerivWithinAt
  · intro t ht
    exact (differentiableAt_DxuA1Fun_x_of_pos_leTwo p t y (hIcc_pos t
      (interior_subset ht))).hasDerivAt.hasDerivWithinAt
  · intro t ht
    exact deriv_DxuA1Fun_x_nonpos_leTwo p hp1 hp2 t y
      (hIcc_pos t (interior_subset ht)) (hIcc_sum t ht)
  · exact hx
  · exact hz
  · exact hasDerivAt_uA1_x_of_pos_leTwo p hp1 hp2 x y (hIcc_pos x hx)

private lemma vLeTwo_A2_second_bracket_nonpos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2)
    (x y : ℝ) (hA2 : A2 p x y) :
    ((x + y) / 2) ^ (p - 2) -
      coeffLeTwo p * ((x - y) / 2) ^ (p - 2) ≤ 0 := by
  rcases hA2 with ⟨hx, hay, hyx⟩
  have hp_pos : 0 < p := by linarith
  have hpden_pos : 0 < p - 1 := by linarith
  have hpden_nonneg : 0 ≤ p - 1 := le_of_lt hpden_pos
  have hpden_le_one : p - 1 ≤ 1 := by linarith
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) hp_pos
  have hy_pos : 0 < y := lt_trans (mul_pos ha_pos hx) hay
  have hsum_pos : 0 < (x + y) / 2 := by linarith
  have hdiff_pos : 0 < (x - y) / 2 := by linarith
  have ha_eq : a p = (2 - p) / p := a_eq_leTwo p hp1 hp2
  have hC_le :
      ((x - y) / 2) / (p - 1) ≤ (x + y) / 2 := by
    have hmain : (2 - p) * x ≤ p * y := by
      have hmul := mul_le_mul_of_nonneg_left (le_of_lt hay) hp_pos.le
      rw [ha_eq] at hmul
      field_simp [hp_pos.ne'] at hmul
      linarith
    rw [div_le_iff₀ hpden_pos]
    nlinarith
  have hC_pos : 0 < ((x - y) / 2) / (p - 1) :=
    div_pos hdiff_pos hpden_pos
  have hexp_neg : p - 2 < 0 := by linarith
  have hpow_le :
      ((x + y) / 2) ^ (p - 2) ≤
        (((x - y) / 2) / (p - 1)) ^ (p - 2) := by
    exact (Real.rpow_le_rpow_iff_of_neg hsum_pos hC_pos hexp_neg).2 hC_le
  have hsplit :
      (((x - y) / 2) / (p - 1)) ^ (p - 2) =
        ((x - y) / 2) ^ (p - 2) * (p - 1) ^ (2 - p) := by
    rw [div_eq_mul_inv]
    rw [Real.mul_rpow hdiff_pos.le (inv_nonneg.mpr hpden_nonneg)]
    rw [Real.inv_rpow hpden_nonneg]
    rw [← Real.rpow_neg hpden_nonneg]
    congr 2
    ring
  have hcoeff_pow :
      (p - 1) ^ (2 - p) ≤ coeffLeTwo p := by
    have hpow :
        (p - 1) ^ (2 - p) ≤ (p - 1) ^ (-p) := by
      exact Real.rpow_le_rpow_of_exponent_ge hpden_pos hpden_le_one (by linarith)
    have hcoeff : coeffLeTwo p = (p - 1) ^ (-p) := by
      rw [coeffLeTwo]
      exact (Real.rpow_neg_eq_inv_rpow (p - 1) p).symm
    simpa [hcoeff] using hpow
  have hright :
      (((x - y) / 2) / (p - 1)) ^ (p - 2) ≤
        coeffLeTwo p * ((x - y) / 2) ^ (p - 2) := by
    rw [hsplit]
    have hB_nonneg : 0 ≤ ((x - y) / 2) ^ (p - 2) :=
      Real.rpow_nonneg hdiff_pos.le _
    nlinarith [mul_le_mul_of_nonneg_left hcoeff_pow hB_nonneg]
  linarith

private lemma deriv_DxvLeTwo_x_nonpos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ)
    (hA2 : A2 p x y) :
    deriv (fun t => DxvLeTwo p t y) x ≤ 0 := by
  rcases hA2 with ⟨hx, hay, hyx⟩
  have hp_pos : 0 < p := by linarith
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) hp_pos
  have hy_pos : 0 < y := lt_trans (mul_pos ha_pos hx) hay
  have hsum : 0 < (x + y) / 2 := by linarith
  have hdiff : 0 < (x - y) / 2 := by linarith
  have hEq :
      (fun t => DxvLeTwo p t y) =ᶠ[nhds x]
        fun t =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) -
            coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2) := by
    have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
      exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hsum))
    have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
      exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hdiff))
    filter_upwards [Ioi_mem_nhds hx, hsum_nhds, hdiff_nhds] with t ht htsum htdiff
    have htpos : 0 < t := by simpa using ht
    simp [DxvLeTwo, htpos, abs_of_pos htsum, abs_of_pos htdiff]
  have hbase_sum :
      HasDerivAt (fun t : ℝ => (t + y) / 2) (1 / 2) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).add_const y).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun t : ℝ => (t - y) / 2) (1 / 2) x := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).add_const (-y)).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun t : ℝ => ((t + y) / 2) ^ (p - 1))
        ((p - 1) * (((x + y) / 2) ^ (p - 2)) * (1 / 2)) x := by
    have hrpow :
        HasDerivAt (fun u : ℝ => u ^ (p - 1))
          ((p - 1) * (((x + y) / 2) ^ (p - 2))) ((x + y) / 2) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        show p + (-1 + -1) = p + -2 by ring] using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hsum)) :
          HasDerivAt (fun u : ℝ => u ^ (p - 1))
            ((p - 1) * ((x + y) / 2) ^ ((p - 1) - 1)) ((x + y) / 2))
    have hcomp := hrpow.comp x hbase_sum
    simp only [Function.comp_def] at hcomp
    convert hcomp using 2
  have hpow_diff :
      HasDerivAt (fun t : ℝ => ((t - y) / 2) ^ (p - 1))
        ((p - 1) * (((x - y) / 2) ^ (p - 2)) * (1 / 2)) x := by
    have hrpow :
        HasDerivAt (fun u : ℝ => u ^ (p - 1))
          ((p - 1) * (((x - y) / 2) ^ (p - 2))) ((x - y) / 2) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        show p + (-1 + -1) = p + -2 by ring] using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hdiff)) :
          HasDerivAt (fun u : ℝ => u ^ (p - 1))
            ((p - 1) * ((x - y) / 2) ^ ((p - 1) - 1)) ((x - y) / 2))
    have hcomp := hrpow.comp x hbase_diff
    simp only [Function.comp_def] at hcomp
    convert hcomp using 2
  have hd :
      HasDerivAt
        (fun t : ℝ =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) -
            coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2))
        ((p * (p - 1) / 4) *
          (((x + y) / 2) ^ (p - 2) -
            coeffLeTwo p * ((x - y) / 2) ^ (p - 2))) x := by
    have htmp :
        HasDerivAt
          (fun t : ℝ =>
            ((t + y) / 2) ^ (p - 1) * (p / 2) -
              coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2))
          (((p - 1) * (((x + y) / 2) ^ (p - 2)) * (1 / 2)) * (p / 2) -
            coeffLeTwo p *
              (((p - 1) * (((x - y) / 2) ^ (p - 2)) * (1 / 2))) *
                (p / 2)) x := by
      exact (hpow_sum.mul_const (p / 2)).sub
        ((hpow_diff.const_mul (coeffLeTwo p)).mul_const (p / 2))
    refine htmp.congr_deriv ?_
    ring
  rw [hEq.deriv_eq, hd.deriv]
  have hcoef : 0 ≤ p * (p - 1) / 4 := by
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hbr := vLeTwo_A2_second_bracket_nonpos_leTwo p hp1 hp2 x y ⟨hx, hay, hyx⟩
  exact mul_nonpos_of_nonneg_of_nonpos hcoef hbr

private lemma hasDerivAt_vLeTwo_x_of_pos_leTwo (p : ℝ) (x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    HasDerivAt (fun t => vLeTwo p t y) (DxvLeTwo p x y) x := by
  let g : ℝ → ℝ := fun t =>
    ((t + y) / 2) ^ p - coeffLeTwo p * (((t - y) / 2) ^ p)
  have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq : (fun t => vLeTwo p t y) =ᶠ[nhds x] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with t ht_sum ht_diff
    simp [vLeTwo, g, abs_of_pos ht_sum, abs_of_pos ht_diff]
  have hbase_sum :
      HasDerivAt (fun t : ℝ => (t + y) / 2) (1 / 2) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).add_const y).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun t : ℝ => (t - y) / 2) (1 / 2) x := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).add_const (-y)).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun t : ℝ => ((t + y) / 2) ^ p)
        (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2)) x := by
    have hrpow :
        HasDerivAt (fun s : ℝ => s ^ p) (p * (((x + y) / 2) ^ (p - 1))) ((x + y) / 2) := by
      simpa using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hsum)) :
          HasDerivAt (fun s : ℝ => s ^ p) (p * ((x + y) / 2) ^ (p - 1)) ((x + y) / 2))
    have hcomp := hrpow.comp x hbase_sum
    simp only [Function.comp_def] at hcomp
    convert hcomp using 2
  have hpow_diff :
      HasDerivAt (fun t : ℝ => ((t - y) / 2) ^ p)
        (p * (((x - y) / 2) ^ (p - 1)) * (1 / 2)) x := by
    have hrpow :
        HasDerivAt (fun s : ℝ => s ^ p) (p * (((x - y) / 2) ^ (p - 1))) ((x - y) / 2) := by
      simpa using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hdiff)) :
          HasDerivAt (fun s : ℝ => s ^ p) (p * ((x - y) / 2) ^ (p - 1)) ((x - y) / 2))
    have hcomp := hrpow.comp x hbase_diff
    simp only [Function.comp_def] at hcomp
    convert hcomp using 2
  have hd :
      HasDerivAt g
        (((x + y) / 2) ^ (p - 1) * (p / 2) -
          coeffLeTwo p * (((x - y) / 2) ^ (p - 1)) * (p / 2)) x := by
    have htmp :
        HasDerivAt g
          (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
            coeffLeTwo p * (p * (((x - y) / 2) ^ (p - 1)) * (1 / 2))) x := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul (coeffLeTwo p))
    refine htmp.congr_deriv ?_
    ring
  have hx : 0 < x := by linarith
  refine (hd.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DxvLeTwo, hx, abs_of_pos hsum, abs_of_pos hdiff]

private lemma continuous_vLeTwo_leTwo (p : ℝ) (hp1 : 1 < p) :
    Continuous (fun z : ℝ × ℝ => vLeTwo p z.1 z.2) := by
  have hp_nonneg : (0 : ℝ) ≤ p := by linarith
  simp only [vLeTwo]
  apply Continuous.sub
  · apply Continuous.rpow_const _ (fun _ => Or.inr hp_nonneg)
    exact ((continuous_fst.add continuous_snd).div_const 2).abs
  · apply Continuous.mul continuous_const
    apply Continuous.rpow_const _ (fun _ => Or.inr hp_nonneg)
    exact ((continuous_fst.sub continuous_snd).div_const 2).abs

private lemma differentiableAt_DxvLeTwo_x_of_pos_leTwo (p x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    DifferentiableAt ℝ (fun t => DxvLeTwo p t y) x := by
  have hx : 0 < x := by linarith
  have hEq :
      (fun t => DxvLeTwo p t y) =ᶠ[nhds x]
        fun t =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) -
            coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2) := by
    have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
      exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hsum))
    have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
      exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hdiff))
    filter_upwards [Ioi_mem_nhds hx, hsum_nhds, hdiff_nhds] with t ht htsum htdiff
    have htpos : 0 < t := by simpa using ht
    simp [DxvLeTwo, htpos, abs_of_pos htsum, abs_of_pos htdiff]
  have hsum_diff :
      DifferentiableAt ℝ (fun t : ℝ => ((t + y) / 2) ^ (p - 1)) x := by
    have hbase : DifferentiableAt ℝ (fun t : ℝ => (t + y) / 2) x := by
      simp only [add_div]
      exact (differentiableAt_id.div_const 2).add (differentiableAt_const _)
    exact hbase.rpow_const (Or.inl (ne_of_gt hsum))
  have hdiff_diff :
      DifferentiableAt ℝ (fun t : ℝ => ((t - y) / 2) ^ (p - 1)) x := by
    have hbase : DifferentiableAt ℝ (fun t : ℝ => (t - y) / 2) x := by
      simp only [sub_div]
      exact (differentiableAt_id.div_const 2).sub (differentiableAt_const _)
    exact hbase.rpow_const (Or.inl (ne_of_gt hdiff))
  have hformula :
      DifferentiableAt ℝ
        (fun t : ℝ =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) -
            coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2)) x := by
    exact (hsum_diff.mul_const (p / 2)).sub
      ((hdiff_diff.const_mul (coeffLeTwo p)).mul_const (p / 2))
  exact hformula.congr_of_eventuallyEq hEq

private lemma vLeTwo_tangent_x_on_Icc_of_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {lo hi x z y : ℝ}
    (hA2_int : ∀ t ∈ interior (Set.Icc lo hi), A2 p t y)
    (hx : x ∈ Set.Icc lo hi) (hz : z ∈ Set.Icc lo hi)
    (hderiv : HasDerivAt (fun t => vLeTwo p t y) (DxvLeTwo p x y) x) :
    vLeTwo p z y ≤ vLeTwo p x y + DxvLeTwo p x y * (z - x) := by
  have hcont : ContinuousOn (fun t => vLeTwo p t y) (Set.Icc lo hi) := by
    have hpair : Continuous (fun t : ℝ => (t, y)) := by continuity
    have hcomp := ((continuous_vLeTwo_leTwo p hp1).comp hpair).continuousOn
      (s := Set.Icc lo hi)
    simpa [Function.comp_def] using hcomp
  apply tangent_inequality_on_Icc_of_hasDerivWithinAt2_nonpos_leTwo
      (f := fun t => vLeTwo p t y)
      (f₁ := fun t => DxvLeTwo p t y)
      (f₂ := fun t => deriv (fun s => DxvLeTwo p s y) t)
      (f' := DxvLeTwo p x y)
  · exact hcont
  · intro t ht
    have hA2 := hA2_int t ht
    rcases hA2 with ⟨htpos, hlo, hup⟩
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have hy_pos : 0 < y := lt_trans (mul_pos ha_pos htpos) hlo
    have hsum : 0 < (t + y) / 2 := by linarith
    have hdiff : 0 < (t - y) / 2 := by linarith
    exact (hasDerivAt_vLeTwo_x_of_pos_leTwo p t y hsum hdiff).hasDerivWithinAt
  · intro t ht
    have hA2 := hA2_int t ht
    rcases hA2 with ⟨htpos, hlo, hup⟩
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have hy_pos : 0 < y := lt_trans (mul_pos ha_pos htpos) hlo
    have hsum : 0 < (t + y) / 2 := by linarith
    have hdiff : 0 < (t - y) / 2 := by linarith
    exact (differentiableAt_DxvLeTwo_x_of_pos_leTwo p t y hsum hdiff).hasDerivAt.hasDerivWithinAt
  · intro t ht
    exact deriv_DxvLeTwo_x_nonpos_leTwo p hp1 hp2 t y (hA2_int t ht)
  · exact hx
  · exact hz
  · exact hderiv

private lemma DxauxFunction1_A2_boundary_le_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hyx : y < x) (hax : a p * x < y) :
    DxauxFunction1 p (y / a p) y ≤ DxauxFunction1 p x y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hxc : x < c := by
    have hmul : a p * x < a p * c := by simpa [hac] using hax
    nlinarith [hmul, ha_pos]
  have hx_pos : 0 < x := lt_trans hy_pos hyx
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hcl_x : closureA2 p x y := ⟨hx_pos.le, le_of_lt hax, hyx.le⟩
  have hanti :
      AntitoneOn (fun t : ℝ => DxvLeTwo p t y) (Set.Icc x c) := by
    have hcont : ContinuousOn (fun t : ℝ => DxvLeTwo p t y) (Set.Icc x c) := by
      let g : ℝ → ℝ := fun t =>
        ((t + y) / 2) ^ (p - 1) * (p / 2) -
          coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2)
      have hg : ContinuousOn g (Set.Icc x c) := by
        dsimp [g]
        apply ContinuousOn.sub
        · exact ((continuousOn_id.add continuousOn_const).div_const 2).rpow_const
            (fun t ht => Or.inl (ne_of_gt (by
              change 0 < (t + y) / 2
              linarith [hx_pos, ht.1, hy_pos]))) |>.mul
            continuousOn_const
        · exact (continuousOn_const.mul
            (((continuousOn_id.sub continuousOn_const).div_const 2).rpow_const
              (fun t ht => Or.inl (ne_of_gt (by
                change 0 < (t - y) / 2
                linarith [hyx, ht.1]))))).mul
            continuousOn_const
      refine ContinuousOn.congr hg ?_
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hx_pos ht.1
      have hsum : 0 < (t + y) / 2 := by linarith [ht_pos, hy_pos]
      have hdiff : 0 < (t - y) / 2 := by linarith [hyx, ht.1]
      simp [g, DxvLeTwo, ht_pos, abs_of_pos hsum, abs_of_pos hdiff]
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc x c)
      (f := fun t : ℝ => DxvLeTwo p t y)
      (f' := fun t : ℝ => deriv (fun s => DxvLeTwo p s y) t)
      (convex_Icc x c) hcont ?_ ?_
    · intro t ht
      have htIoo : t ∈ Set.Ioo x c := by
        simpa [interior_Icc] using ht
      have hsum : 0 < (t + y) / 2 := by linarith [hx_pos, htIoo.1, hy_pos]
      have hdiff : 0 < (t - y) / 2 := by linarith [hyx, htIoo.1]
      exact (differentiableAt_DxvLeTwo_x_of_pos_leTwo p t y hsum hdiff).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htIoo : t ∈ Set.Ioo x c := by
        simpa [interior_Icc] using ht
      have h_at : a p * t < y := by
        have hmul : a p * t < a p * c := mul_lt_mul_of_pos_left htIoo.2 ha_pos
        simpa [hac] using hmul
      exact deriv_DxvLeTwo_x_nonpos_leTwo p hp1 hp2 t y
        ⟨lt_trans hx_pos htIoo.1, h_at, lt_trans hyx htIoo.1⟩
  have hx_mem : x ∈ Set.Icc x c := ⟨le_rfl, hxc.le⟩
  have hc_mem : c ∈ Set.Icc x c := ⟨hxc.le, le_rfl⟩
  have hle : DxvLeTwo p c y ≤ DxvLeTwo p x y :=
    hanti hx_mem hc_mem hxc.le
  simpa [c, auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 x y hcl_x,
    auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 (y / a p) y hboundary.2] using hle

private lemma DxauxFunction1_A1_le_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hyx : y < x) (hay : y < a p * x) :
    DxauxFunction1 p x y ≤ DxauxFunction1 p (y / a p) y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hcx : c < x := by
    have hmul : a p * c < a p * x := by simpa [hac] using hay
    nlinarith [hmul, ha_pos]
  have hx_pos : 0 < x := lt_trans hy_pos hyx
  have hc_pos : 0 < c := div_pos hy_pos ha_pos
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hcl_x : closureA1 p x y := ⟨hx_pos.le, by linarith [hx_pos, hy_pos], le_of_lt hay⟩
  have hanti :
      AntitoneOn (fun t : ℝ => DxuA1Fun p (t, y)) (Set.Icc c x) := by
    have hcont : ContinuousOn (fun t : ℝ => DxuA1Fun p (t, y)) (Set.Icc c x) := by
      let g : ℝ → ℝ := fun t =>
        alpha p * (p / 2) * t ^ (p - 2) *
          (((p - 2) / (p - 1)) * t + y)
      have hg : ContinuousOn g (Set.Icc c x) := by
        dsimp [g]
        exact ((continuousOn_const.mul continuousOn_const).mul
          (continuousOn_id.rpow_const
            (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hc_pos ht.1))))).mul
          ((continuousOn_const.mul continuousOn_id).add continuousOn_const)
      refine ContinuousOn.congr hg ?_
      intro t ht
      have htpos : 0 < t := lt_of_lt_of_le hc_pos ht.1
      simp [g, DxuA1Fun, DxuA1, htpos]
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc c x)
      (f := fun t : ℝ => DxuA1Fun p (t, y))
      (f' := fun t : ℝ => deriv (fun s => DxuA1Fun p (s, y)) t)
      (convex_Icc c x) hcont ?_ ?_
    · intro t ht
      have htIoo : t ∈ Set.Ioo c x := by
        simpa [interior_Icc] using ht
      exact (differentiableAt_DxuA1Fun_x_of_pos_leTwo p t y
        (lt_trans hc_pos htIoo.1)).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htIoo : t ∈ Set.Ioo c x := by
        simpa [interior_Icc] using ht
      exact deriv_DxuA1Fun_x_nonpos_leTwo p hp1 hp2 t y
        (lt_trans hc_pos htIoo.1) (by linarith [hy_pos, lt_trans hc_pos htIoo.1])
  have hc_mem : c ∈ Set.Icc c x := ⟨le_rfl, hcx.le⟩
  have hx_mem : x ∈ Set.Icc c x := ⟨hcx.le, le_rfl⟩
  have hle : DxuA1Fun p (x, y) ≤ DxuA1Fun p (c, y) :=
    hanti hc_mem hx_mem hcx.le
  simpa [c, DxauxFunction1, hcl_x, hboundary.1, DxuA1Fun] using hle

private lemma hasDerivAt_vLeTwo_y_of_pos_leTwo (p : ℝ) (x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    HasDerivAt (fun s => vLeTwo p x s) (DyvLeTwo p x y) y := by
  let g : ℝ → ℝ := fun s =>
    ((x + s) / 2) ^ p - coeffLeTwo p * (((x - s) / 2) ^ p)
  have hsum_nhds : {s : ℝ | 0 < (x + s) / 2} ∈ nhds y := by
    exact ((((continuous_const.add continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {s : ℝ | 0 < (x - s) / 2} ∈ nhds y := by
    exact ((((continuous_const.sub continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq : (fun s => vLeTwo p x s) =ᶠ[nhds y] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with s hs_sum hs_diff
    simp [vLeTwo, g, abs_of_pos hs_sum, abs_of_pos hs_diff]
  have hbase_sum :
      HasDerivAt (fun s : ℝ => (x + s) / 2) (1 / 2) y := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id y).const_add x).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun s : ℝ => (x - s) / 2) (-(1 / 2)) y := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((((hasDerivAt_id y).neg).const_add x).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun s : ℝ => ((x + s) / 2) ^ p)
        (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2)) y := by
    have hrpow :
        HasDerivAt (fun t : ℝ => t ^ p) (p * (((x + y) / 2) ^ (p - 1))) ((x + y) / 2) := by
      simpa using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hsum)) :
          HasDerivAt (fun t : ℝ => t ^ p) (p * ((x + y) / 2) ^ (p - 1)) ((x + y) / 2))
    have hcomp := hrpow.comp y hbase_sum
    simp only [Function.comp_def] at hcomp
    convert hcomp using 2
  have hpow_diff :
      HasDerivAt (fun s : ℝ => ((x - s) / 2) ^ p)
        (p * (((x - y) / 2) ^ (p - 1)) * (-(1 / 2))) y := by
    have hrpow :
        HasDerivAt (fun t : ℝ => t ^ p) (p * (((x - y) / 2) ^ (p - 1))) ((x - y) / 2) := by
      simpa using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hdiff)) :
          HasDerivAt (fun t : ℝ => t ^ p) (p * ((x - y) / 2) ^ (p - 1)) ((x - y) / 2))
    have hcomp := hrpow.comp y hbase_diff
    simp only [Function.comp_def] at hcomp
    convert hcomp using 2
  have hd :
      HasDerivAt g
        (((x + y) / 2) ^ (p - 1) * (p / 2) +
          coeffLeTwo p * (((x - y) / 2) ^ (p - 1)) * (p / 2)) y := by
    have htmp :
        HasDerivAt g
          (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
            coeffLeTwo p * (p * (((x - y) / 2) ^ (p - 1)) * (-(1 / 2)))) y := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul (coeffLeTwo p))
    refine htmp.congr_deriv ?_
    ring
  have hx : 0 < x := by linarith
  refine (hd.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DyvLeTwo, hx, abs_of_pos hsum, abs_of_pos hdiff]

private lemma differentiableAt_DyvLeTwo_y_of_pos_leTwo (p x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    DifferentiableAt ℝ (fun s => DyvLeTwo p x s) y := by
  have hx : 0 < x := by linarith
  have hEq :
      (fun s => DyvLeTwo p x s) =ᶠ[nhds y]
        fun s =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) +
            coeffLeTwo p * ((x - s) / 2) ^ (p - 1) * (p / 2) := by
    have hsum_nhds : {s : ℝ | 0 < (x + s) / 2} ∈ nhds y := by
      exact ((((continuous_const.add continuous_id').div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hsum))
    have hdiff_nhds : {s : ℝ | 0 < (x - s) / 2} ∈ nhds y := by
      exact ((((continuous_const.sub continuous_id').div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hdiff))
    filter_upwards [hsum_nhds, hdiff_nhds] with s hssum hsdiff
    simp [DyvLeTwo, hx, abs_of_pos hssum, abs_of_pos hsdiff]
  have hsum_diff :
      DifferentiableAt ℝ (fun s : ℝ => ((x + s) / 2) ^ (p - 1)) y := by
    have hbase : DifferentiableAt ℝ (fun s : ℝ => (x + s) / 2) y := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((differentiableAt_id.const_add x).const_mul (1 / 2 : ℝ)))
    exact hbase.rpow_const (Or.inl (ne_of_gt hsum))
  have hdiff_diff :
      DifferentiableAt ℝ (fun s : ℝ => ((x - s) / 2) ^ (p - 1)) y := by
    have hbase : DifferentiableAt ℝ (fun s : ℝ => (x - s) / 2) y := by
      simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((differentiableAt_const x).sub differentiableAt_id).const_mul (1 / 2 : ℝ))
    exact hbase.rpow_const (Or.inl (ne_of_gt hdiff))
  have hformula :
      DifferentiableAt ℝ
        (fun s : ℝ =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) +
            coeffLeTwo p * ((x - s) / 2) ^ (p - 1) * (p / 2)) y := by
    exact (hsum_diff.mul_const (p / 2)).add
      ((hdiff_diff.const_mul (coeffLeTwo p)).mul_const (p / 2))
  exact hformula.congr_of_eventuallyEq hEq

private lemma deriv_DyvLeTwo_y_nonpos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ)
    (hA2 : A2 p x y) :
    deriv (fun s => DyvLeTwo p x s) y ≤ 0 := by
  rcases hA2 with ⟨hx, hay, hyx⟩
  have hsum : 0 < (x + y) / 2 := by
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have hy_pos : 0 < y := lt_trans (mul_pos ha_pos hx) hay
    linarith
  have hdiff : 0 < (x - y) / 2 := by linarith
  have hEq :
      (fun s => DyvLeTwo p x s) =ᶠ[nhds y]
        fun s =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) +
            coeffLeTwo p * ((x - s) / 2) ^ (p - 1) * (p / 2) := by
    have hsum_nhds : {s : ℝ | 0 < (x + s) / 2} ∈ nhds y := by
      exact ((((continuous_const.add continuous_id').div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hsum))
    have hdiff_nhds : {s : ℝ | 0 < (x - s) / 2} ∈ nhds y := by
      exact ((((continuous_const.sub continuous_id').div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hdiff))
    filter_upwards [hsum_nhds, hdiff_nhds] with s hssum hsdiff
    simp [DyvLeTwo, hx, abs_of_pos hssum, abs_of_pos hsdiff]
  have hbase_sum :
      HasDerivAt (fun s : ℝ => (x + s) / 2) (1 / 2) y := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id y).const_add x).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun s : ℝ => (x - s) / 2) (-(1 / 2)) y := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((((hasDerivAt_id y).neg).const_add x).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun s : ℝ => ((x + s) / 2) ^ (p - 1))
        ((p - 1) * (((x + y) / 2) ^ (p - 2)) * (1 / 2)) y := by
    have hrpow :
        HasDerivAt (fun u : ℝ => u ^ (p - 1))
          ((p - 1) * (((x + y) / 2) ^ (p - 2))) ((x + y) / 2) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        show p + (-1 + -1) = p + -2 by ring] using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hsum)) :
          HasDerivAt (fun u : ℝ => u ^ (p - 1))
            ((p - 1) * ((x + y) / 2) ^ ((p - 1) - 1)) ((x + y) / 2))
    have hcomp := hrpow.comp y hbase_sum
    simp only [Function.comp_def] at hcomp
    convert hcomp using 2
  have hpow_diff :
      HasDerivAt (fun s : ℝ => ((x - s) / 2) ^ (p - 1))
        ((p - 1) * (((x - y) / 2) ^ (p - 2)) * (-(1 / 2))) y := by
    have hrpow :
        HasDerivAt (fun u : ℝ => u ^ (p - 1))
          ((p - 1) * (((x - y) / 2) ^ (p - 2))) ((x - y) / 2) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        show p + (-1 + -1) = p + -2 by ring] using
        (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hdiff)) :
          HasDerivAt (fun u : ℝ => u ^ (p - 1))
            ((p - 1) * ((x - y) / 2) ^ ((p - 1) - 1)) ((x - y) / 2))
    have hcomp := hrpow.comp y hbase_diff
    simp only [Function.comp_def] at hcomp
    convert hcomp using 2
  have hd :
      HasDerivAt
        (fun s : ℝ =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) +
            coeffLeTwo p * ((x - s) / 2) ^ (p - 1) * (p / 2))
        ((p * (p - 1) / 4) *
          (((x + y) / 2) ^ (p - 2) -
            coeffLeTwo p * ((x - y) / 2) ^ (p - 2))) y := by
    have htmp :
        HasDerivAt
          (fun s : ℝ =>
            ((x + s) / 2) ^ (p - 1) * (p / 2) +
              coeffLeTwo p * ((x - s) / 2) ^ (p - 1) * (p / 2))
          (((p - 1) * (((x + y) / 2) ^ (p - 2)) * (1 / 2)) * (p / 2) +
            coeffLeTwo p *
              (((p - 1) * (((x - y) / 2) ^ (p - 2)) * (-(1 / 2)))) *
                (p / 2)) y := by
      exact (hpow_sum.mul_const (p / 2)).add
        ((hpow_diff.const_mul (coeffLeTwo p)).mul_const (p / 2))
    refine htmp.congr_deriv ?_
    ring
  rw [hEq.deriv_eq, hd.deriv]
  have hcoef : 0 ≤ p * (p - 1) / 4 := by
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hbr := vLeTwo_A2_second_bracket_nonpos_leTwo p hp1 hp2 x y ⟨hx, hay, hyx⟩
  exact mul_nonpos_of_nonneg_of_nonpos hcoef hbr

private lemma vLeTwo_tangent_y_on_Icc_of_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {lo hi y z x : ℝ}
    (hA2_int : ∀ t ∈ interior (Set.Icc lo hi), A2 p x t)
    (hy : y ∈ Set.Icc lo hi) (hz : z ∈ Set.Icc lo hi)
    (hderiv : HasDerivAt (fun t => vLeTwo p x t) (DyvLeTwo p x y) y) :
    vLeTwo p x z ≤ vLeTwo p x y + DyvLeTwo p x y * (z - y) := by
  have hcont : ContinuousOn (fun t => vLeTwo p x t) (Set.Icc lo hi) := by
    have hpair : Continuous (fun t : ℝ => (x, t)) := by continuity
    have hcomp := ((continuous_vLeTwo_leTwo p hp1).comp hpair).continuousOn
      (s := Set.Icc lo hi)
    simpa [Function.comp_def] using hcomp
  apply tangent_inequality_on_Icc_of_hasDerivWithinAt2_nonpos_leTwo
      (f := fun t => vLeTwo p x t)
      (f₁ := fun t => DyvLeTwo p x t)
      (f₂ := fun t => deriv (fun s => DyvLeTwo p x s) t)
      (f' := DyvLeTwo p x y)
  · exact hcont
  · intro t ht
    rcases hA2_int t ht with ⟨hx, hat, htx⟩
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have ht_pos : 0 < t := lt_trans (mul_pos ha_pos hx) hat
    have hsum : 0 < (x + t) / 2 := by linarith
    have hdiff : 0 < (x - t) / 2 := by linarith
    exact (hasDerivAt_vLeTwo_y_of_pos_leTwo p x t hsum hdiff).hasDerivWithinAt
  · intro t ht
    rcases hA2_int t ht with ⟨hx, hat, htx⟩
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have ht_pos : 0 < t := lt_trans (mul_pos ha_pos hx) hat
    have hsum : 0 < (x + t) / 2 := by linarith
    have hdiff : 0 < (x - t) / 2 := by linarith
    exact (differentiableAt_DyvLeTwo_y_of_pos_leTwo p x t hsum hdiff).hasDerivAt.hasDerivWithinAt
  · intro t ht
    exact deriv_DyvLeTwo_y_nonpos_leTwo p hp1 hp2 x t (hA2_int t ht)
  · exact hy
  · exact hz
  · exact hderiv

private lemma uA1_affine_y_tangent_leTwo
    (p x y z : ℝ) (hx : 0 < x) :
    uA1 p x z = uA1 p x y + DyuA1 p x y * (z - y) := by
  simp [uA1, DyuA1, hx]
  ring

private lemma uCandidate_tangent_x_on_Q3_A1_segment_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y)
    (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hx_lower, by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    have hax_lt_y : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact le_of_lt (lt_trans hx_upper hax_lt_y)⟩
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, le_of_lt hz_lower, by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    have hax_lt_y : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact le_of_lt (lt_trans hz_upper hax_lt_y)⟩
  have hclx : closureA1 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hclz : closureA1 p y z := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt hz_upper⟩
  have hux : uCandidate p x y = uA1 p y x := by
    rw [uCandidate_eq_Q3_leTwo p hQx]
    simp [auxFunction1, hclx]
  have huz : uCandidate p z y = uA1 p y z := by
    rw [uCandidate_eq_Q3_leTwo p hQz]
    simp [auxFunction1, hclz]
  have hdx : DxuCandidate p x y = DyuA1 p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    simp [DyauxFunction1, hclx]
  apply le_of_eq
  calc
    uCandidate p z y = uA1 p y z := huz
    _ = uA1 p y x + DyuA1 p y x * (z - x) :=
        uA1_affine_y_tangent_leTwo p y x z hy_pos
    _ = uCandidate p x y + DxuCandidate p x y * (z - x) := by
        rw [hux, hdx]

private lemma uCandidate_tangent_x_on_Q3_A2_segment_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y)
    (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hx_upper⟩
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hz_upper⟩
  have hclx : closureA2 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hclz : closureA2 p y z := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt hz_upper⟩
  have hux : uCandidate p x y = vLeTwo p y x := by
    rw [uCandidate_eq_Q3_leTwo p hQx, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y x hclx]
  have huz : uCandidate p z y = vLeTwo p y z := by
    rw [uCandidate_eq_Q3_leTwo p hQz, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y z hclz]
  have hdx : DxuCandidate p x y = DyvLeTwo p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    have hnot : ¬ closureA1 p y x := by
      intro h
      exact not_le_of_gt hx_lower h.2.2
    simp [DyauxFunction1, hnot, hclx]
  have hderiv :
      HasDerivAt (fun t => vLeTwo p y t) (DyvLeTwo p y x) x := by
    have hsum : 0 < (y + x) / 2 := by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith
    have hdiff : 0 < (y - x) / 2 := by linarith
    exact hasDerivAt_vLeTwo_y_of_pos_leTwo p y x hsum hdiff
  have hmain :
      vLeTwo p y z ≤ vLeTwo p y x + DyvLeTwo p y x * (z - x) := by
    apply vLeTwo_tangent_y_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := min x z) (hi := max x z) (x := y)
        (y := x) (z := z)
    · intro t ht
      have htI : t ∈ Set.Icc (min x z) (max x z) := interior_subset ht
      have hlow : a p * y < min x z := lt_min hx_lower hz_lower
      have hhi : max x z < y := max_lt hx_upper hz_upper
      exact ⟨hy_pos, lt_of_lt_of_le hlow htI.1, lt_of_le_of_lt htI.2 hhi⟩
    · exact ⟨min_le_left x z, le_max_left x z⟩
    · exact ⟨min_le_right x z, le_max_right x z⟩
    · exact hderiv
  calc
    uCandidate p z y = vLeTwo p y z := huz
    _ ≤ vLeTwo p y x + DyvLeTwo p y x * (z - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (z - x) := by
      rw [hux, hdx]

private lemma tangent_glue_two_forward_leTwo_local
    (f d : ℝ → ℝ) {x m z : ℝ}
    (_hxm : x ≤ m) (hmz : m ≤ z)
    (hxm_tangent : f m ≤ f x + d x * (m - x))
    (hmz_tangent : f z ≤ f m + d m * (z - m))
    (hd_antitone : d m ≤ d x) :
    f z ≤ f x + d x * (z - x) := by
  have hnonneg : 0 ≤ z - m := by linarith
  have hmul : d m * (z - m) ≤ d x * (z - m) :=
    mul_le_mul_of_nonneg_right hd_antitone hnonneg
  calc
    f z ≤ f m + d m * (z - m) := hmz_tangent
    _ ≤ (f x + d x * (m - x)) + d m * (z - m) := by linarith
    _ ≤ (f x + d x * (m - x)) + d x * (z - m) := by linarith
    _ = f x + d x * (z - x) := by ring

private lemma tangent_glue_two_backward_leTwo_local
    (f d : ℝ → ℝ) {x m z : ℝ}
    (hzm : z ≤ m) (_hmx : m ≤ x)
    (hxm_tangent : f m ≤ f x + d x * (m - x))
    (hmz_tangent : f z ≤ f m + d m * (z - m))
    (hd_antitone : d x ≤ d m) :
    f z ≤ f x + d x * (z - x) := by
  have hnonpos : z - m ≤ 0 := by linarith
  have hmul : d m * (z - m) ≤ d x * (z - m) :=
    mul_le_mul_of_nonpos_right hd_antitone hnonpos
  calc
    f z ≤ f m + d m * (z - m) := hmz_tangent
    _ ≤ (f x + d x * (m - x)) + d m * (z - m) := by linarith
    _ ≤ (f x + d x * (m - x)) + d x * (z - m) := by linarith
    _ = f x + d x * (z - x) := by ring

private lemma uCandidate_tangent_x_Q3_A1_to_A2_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    uCandidate p (a p * y) y ≤
      uCandidate p x y + DxuCandidate p x y * (a p * y - x) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hx_lower, by
    have haxy_lt_y : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact le_of_lt (lt_trans hx_upper haxy_lt_y)⟩
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, by
      have haxy_le_y : a p * y ≤ y := by
        simpa using mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      exact haxy_le_y⟩
  have hclx : closureA1 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hux : uCandidate p x y = uA1 p y x := by
    rw [uCandidate_eq_Q3_leTwo p hQx]
    simp [auxFunction1, hclx]
  have huc : uCandidate p (a p * y) y = uA1 p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc]
    simp [auxFunction1, hclc]
  have hdx : DxuCandidate p x y = DyuA1 p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    simp [DyauxFunction1, hclx]
  apply le_of_eq
  calc
    uCandidate p (a p * y) y = uA1 p y (a p * y) := huc
    _ = uA1 p y x + DyuA1 p y x * (a p * y - x) :=
      uA1_affine_y_tangent_leTwo p y x (a p * y) hy_pos
    _ = uCandidate p x y + DxuCandidate p x y * (a p * y - x) := by
      rw [hux, hdx]

private lemma uCandidate_tangent_x_Q3_A2_boundary_to_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (z - a p * y) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_nonneg : 0 ≤ a p := ha_pos.le
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_pos : 0 < a p * y := mul_pos ha_pos hy_pos
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by linarith, le_of_lt hc_lt_y⟩
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, by linarith [hc_pos, hz_lower], le_of_lt hz_upper⟩
  have hclc1 : closureA1 p y (a p * y) := ⟨hy_pos.le, by linarith [hc_pos], le_rfl⟩
  have hclc2 : closureA2 p y (a p * y) := ⟨hy_pos.le, le_rfl, le_of_lt hc_lt_y⟩
  have hclz : closureA2 p y z := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt hz_upper⟩
  have huc : uCandidate p (a p * y) y = vLeTwo p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc]
    rw [auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y (a p * y) hclc2]
  have huz : uCandidate p z y = vLeTwo p y z := by
    rw [uCandidate_eq_Q3_leTwo p hQz]
    rw [auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y z hclz]
  have hdc : DxuCandidate p (a p * y) y = DyvLeTwo p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    have hdyu : DyauxFunction1 p y (a p * y) = DyuA1 p y (a p * y) := by
      simp [DyauxFunction1, hclc1]
    have hglue := DyuA1_eq_DyvLeTwo_on_A1A2_boundary_leTwo
      p y hp1 hp2 hy_pos
    simpa [hdyu] using hglue
  have hderiv : HasDerivAt (fun t => vLeTwo p y t) (DyvLeTwo p y (a p * y)) (a p * y) := by
    have hsum : 0 < (y + a p * y) / 2 := by linarith [hy_pos, hc_pos]
    have hdiff : 0 < (y - a p * y) / 2 := by linarith [hc_lt_y]
    exact hasDerivAt_vLeTwo_y_of_pos_leTwo p y (a p * y) hsum hdiff
  have hmain :
      vLeTwo p y z ≤
        vLeTwo p y (a p * y) + DyvLeTwo p y (a p * y) * (z - a p * y) := by
    apply vLeTwo_tangent_y_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := a p * y) (hi := z) (x := y) (y := a p * y) (z := z)
    · intro t ht
      have htI : t ∈ Set.Ioo (a p * y) z := by
        simpa [interior_Icc] using ht
      exact ⟨hy_pos, htI.1, lt_trans htI.2 hz_upper⟩
    · exact ⟨le_rfl, le_of_lt hz_lower⟩
    · exact ⟨le_of_lt hz_lower, le_rfl⟩
    · exact hderiv
  calc
    uCandidate p z y = vLeTwo p y z := huz
    _ ≤ vLeTwo p y (a p * y) + DyvLeTwo p y (a p * y) * (z - a p * y) := hmain
    _ = uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (z - a p * y) := by
      rw [huc, hdc]

private lemma uCandidate_tangent_x_cross_Q3_A1_to_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y)
    (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q3_A1_to_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd : DxuCandidate p (a p * y) y ≤ DxuCandidate p x y := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hx_lower, by
      have hc_lt_y : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt (lt_trans hx_upper hc_lt_y)⟩
    have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith, by
        have hle : a p * y ≤ y := by
          simpa using mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
        exact hle⟩
    have hclx : closureA1 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
    have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith, le_rfl⟩
    have hdx : DxuCandidate p x y = DyuA1 p y x := by
      rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
      simp [DyauxFunction1, hclx]
    have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
      rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
      simp [DyauxFunction1, hclc]
    rw [hdx, hdc]
    simp [DyuA1, hy_pos]
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hx_upper) (le_of_lt hz_lower) hxc hcz hd

private lemma uCandidate_tangent_x_on_Q1_A2_segment_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p)
    (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hQx : QuarterPlane x y := ⟨by linarith, le_of_lt hx_lower, by linarith⟩
  have hQz : QuarterPlane z y := ⟨by linarith, le_of_lt hz_lower, by linarith⟩
  have hax : a p * x < y := by
    have hmul := mul_lt_mul_of_pos_left hx_upper ha_pos
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have haz : a p * z < y := by
    have hmul := mul_lt_mul_of_pos_left hz_upper ha_pos
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hclx : closureA2 p x y := ⟨by linarith, by linarith, le_of_lt hx_lower⟩
  have hclz : closureA2 p z y := ⟨by linarith, by linarith, le_of_lt hz_lower⟩
  have hnotx : ¬ closureA1 p x y := by
    intro h
    exact not_le_of_gt hax h.2.2
  have hux : uCandidate p x y = vLeTwo p x y := by
    rw [uCandidate_eq_Q1_leTwo p hQx]
    simp [auxFunction1, hnotx, hclx]
  have huz : uCandidate p z y = vLeTwo p z y := by
    have hnotz : ¬ closureA1 p z y := by
      intro h
      exact not_le_of_gt haz h.2.2
    rw [uCandidate_eq_Q1_leTwo p hQz]
    simp [auxFunction1, hnotz, hclz]
  have hdx : DxuCandidate p x y = DxvLeTwo p x y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQx]
    simp [DxauxFunction1, hnotx, hclx]
  have hderiv :
      HasDerivAt (fun t => vLeTwo p t y) (DxvLeTwo p x y) x := by
    have hsum : 0 < (x + y) / 2 := by linarith
    have hdiff : 0 < (x - y) / 2 := by linarith
    exact hasDerivAt_vLeTwo_x_of_pos_leTwo p x y hsum hdiff
  have hmain :
      vLeTwo p z y ≤ vLeTwo p x y + DxvLeTwo p x y * (z - x) := by
    apply vLeTwo_tangent_x_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := min x z) (hi := max x z) (y := y)
        (x := x) (z := z)
    · intro t ht
      have htI : t ∈ Set.Icc (min x z) (max x z) := interior_subset ht
      have hlow : y < min x z := lt_min hx_lower hz_lower
      have hhi : max x z < y / a p := max_lt hx_upper hz_upper
      have hyt : y < t := lt_of_lt_of_le hlow htI.1
      have ht_pos : 0 < t := lt_trans hy_pos hyt
      have hat : a p * t < y := by
        have ht_div : t < y / a p := lt_of_le_of_lt htI.2 hhi
        have hmul := mul_lt_mul_of_pos_left ht_div ha_pos
        field_simp [ha_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      exact ⟨ht_pos, hat, hyt⟩
    · exact ⟨min_le_left x z, le_max_left x z⟩
    · exact ⟨min_le_right x z, le_max_right x z⟩
    · exact hderiv
  calc
    uCandidate p z y = vLeTwo p z y := huz
    _ ≤ vLeTwo p x y + DxvLeTwo p x y * (z - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (z - x) := by
      rw [hux, hdx]

private lemma DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    DyvLeTwo p y y ≤ DyvLeTwo p y x := by
  have hx_pos : 0 < x := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hanti :
      AntitoneOn (fun t : ℝ => DyvLeTwo p y t) (Set.Icc x y) := by
    have hcont : ContinuousOn (fun t : ℝ => DyvLeTwo p y t) (Set.Icc x y) := by
      let g : ℝ → ℝ := fun t =>
        ((y + t) / 2) ^ (p - 1) * (p / 2) +
          coeffLeTwo p * ((y - t) / 2) ^ (p - 1) * (p / 2)
      have hg : ContinuousOn g (Set.Icc x y) := by
        dsimp [g]
        apply ContinuousOn.add
        · exact (((continuousOn_const.add continuousOn_id).div_const 2).rpow_const
            (fun t ht => Or.inl (ne_of_gt (by
              change 0 < (y + t) / 2
              linarith [hy_pos, hx_pos, ht.1])))).mul continuousOn_const
        · exact (continuousOn_const.mul
            (((continuousOn_const.sub continuousOn_id).div_const 2).rpow_const
              (fun t ht => Or.inr (by linarith)))).mul continuousOn_const
      refine ContinuousOn.congr hg ?_
      intro t ht
      have ht_upper : t ≤ y := ht.2
      have hsum : 0 < (y + t) / 2 := by linarith [hy_pos, hx_pos, ht.1]
      have hdiff_nonneg : 0 ≤ (y - t) / 2 := by linarith [ht.2]
      by_cases hdiff : 0 < (y - t) / 2
      · have htpos : 0 < y := hy_pos
        simp [g, DyvLeTwo, htpos, abs_of_pos hsum, abs_of_pos hdiff]
      · have hdiff_zero : (y - t) / 2 = 0 := le_antisymm (le_of_not_gt hdiff) hdiff_nonneg
        have ht_eq : t = y := by linarith
        subst t
        have hp_ne : p - 1 ≠ 0 := by linarith
        simp [g, DyvLeTwo, hy_pos, abs_of_pos hy_pos, Real.zero_rpow hp_ne]
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc x y)
      (f := fun t : ℝ => DyvLeTwo p y t)
      (f' := fun t : ℝ => deriv (fun s => DyvLeTwo p y s) t)
      (convex_Icc x y) hcont ?_ ?_
    · intro t ht
      have htI : t ∈ Set.Ioo x y := by
        simpa [interior_Icc] using ht
      have hsum : 0 < (y + t) / 2 := by linarith [hy_pos, hx_pos, htI.1]
      have hdiff : 0 < (y - t) / 2 := by linarith [htI.2]
      exact (differentiableAt_DyvLeTwo_y_of_pos_leTwo p y t hsum hdiff).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htI : t ∈ Set.Ioo x y := by
        simpa [interior_Icc] using ht
      exact deriv_DyvLeTwo_y_nonpos_leTwo p hp1 hp2 y t
        ⟨hy_pos, lt_trans hx_lower htI.1, htI.2⟩
  exact hanti ⟨le_rfl, hx_upper.le⟩ ⟨hx_upper.le, le_rfl⟩ hx_upper.le

private lemma DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_closed_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y ≤ x) (hx_upper : x < y) :
    DyvLeTwo p y y ≤ DyvLeTwo p y x := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hx_pos : 0 < x := lt_of_lt_of_le (mul_pos ha_pos hy_pos) hx_lower
  have hanti :
      AntitoneOn (fun t : ℝ => DyvLeTwo p y t) (Set.Icc x y) := by
    have hcont : ContinuousOn (fun t : ℝ => DyvLeTwo p y t) (Set.Icc x y) := by
      let g : ℝ → ℝ := fun t =>
        ((y + t) / 2) ^ (p - 1) * (p / 2) +
          coeffLeTwo p * ((y - t) / 2) ^ (p - 1) * (p / 2)
      have hg : ContinuousOn g (Set.Icc x y) := by
        dsimp [g]
        apply ContinuousOn.add
        · exact (((continuousOn_const.add continuousOn_id).div_const 2).rpow_const
            (fun t ht => Or.inl (ne_of_gt (by
              change 0 < (y + t) / 2
              linarith [hy_pos, hx_pos, ht.1])))).mul continuousOn_const
        · exact (continuousOn_const.mul
            (((continuousOn_const.sub continuousOn_id).div_const 2).rpow_const
              (fun t ht => Or.inr (by linarith)))).mul continuousOn_const
      refine ContinuousOn.congr hg ?_
      intro t ht
      have hsum : 0 < (y + t) / 2 := by linarith [hy_pos, hx_pos, ht.1]
      have hdiff_nonneg : 0 ≤ (y - t) / 2 := by linarith [ht.2]
      by_cases hdiff : 0 < (y - t) / 2
      · simp [g, DyvLeTwo, hy_pos, abs_of_pos hsum, abs_of_pos hdiff]
      · have hdiff_zero : (y - t) / 2 = 0 := le_antisymm (le_of_not_gt hdiff) hdiff_nonneg
        have ht_eq : t = y := by linarith
        subst t
        have hp_ne : p - 1 ≠ 0 := by linarith
        simp [g, DyvLeTwo, hy_pos, abs_of_pos hy_pos, Real.zero_rpow hp_ne]
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc x y)
      (f := fun t : ℝ => DyvLeTwo p y t)
      (f' := fun t : ℝ => deriv (fun s => DyvLeTwo p y s) t)
      (convex_Icc x y) hcont ?_ ?_
    · intro t ht
      have htI : t ∈ Set.Ioo x y := by
        simpa [interior_Icc] using ht
      have hsum : 0 < (y + t) / 2 := by linarith [hy_pos, hx_pos, htI.1]
      have hdiff : 0 < (y - t) / 2 := by linarith [htI.2]
      exact (differentiableAt_DyvLeTwo_y_of_pos_leTwo p y t hsum hdiff).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htI : t ∈ Set.Ioo x y := by
        simpa [interior_Icc] using ht
      exact deriv_DyvLeTwo_y_nonpos_leTwo p hp1 hp2 y t
        ⟨hy_pos, lt_of_le_of_lt hx_lower htI.1, htI.2⟩
  exact hanti ⟨le_rfl, hx_upper.le⟩ ⟨hx_upper.le, le_rfl⟩ hx_upper.le

private lemma uCandidate_tangent_x_Q3_A2_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    uCandidate p y y ≤
      uCandidate p x y + DxuCandidate p x y * (y - x) := by
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hx_upper⟩
  have hQy : QuarterPlane3 y y := ⟨hy_pos.le, by linarith, le_rfl⟩
  have hclx : closureA2 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hcly : closureA2 p y y := by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    exact ⟨hy_pos.le, (mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le).trans_eq (one_mul y), le_rfl⟩
  have hux : uCandidate p x y = vLeTwo p y x := by
    rw [uCandidate_eq_Q3_leTwo p hQx, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y x hclx]
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q3_leTwo p hQy, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y y hcly]
  have hdx : DxuCandidate p x y = DyvLeTwo p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    have hnot : ¬ closureA1 p y x := by
      intro h
      exact not_le_of_gt hx_lower h.2.2
    simp [DyauxFunction1, hnot, hclx]
  have hderiv : HasDerivAt (fun t => vLeTwo p y t) (DyvLeTwo p y x) x := by
    have hsum : 0 < (y + x) / 2 := by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith
    have hdiff : 0 < (y - x) / 2 := by linarith
    exact hasDerivAt_vLeTwo_y_of_pos_leTwo p y x hsum hdiff
  have hmain :
      vLeTwo p y y ≤ vLeTwo p y x + DyvLeTwo p y x * (y - x) := by
    apply vLeTwo_tangent_y_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := x) (hi := y) (x := y) (y := x) (z := y)
    · intro t ht
      have htI : t ∈ Set.Ioo x y := by
        simpa [interior_Icc] using ht
      exact ⟨hy_pos, lt_trans hx_lower htI.1, htI.2⟩
    · exact ⟨le_rfl, le_of_lt hx_upper⟩
    · exact ⟨le_of_lt hx_upper, le_rfl⟩
    · exact hderiv
  calc
    uCandidate p y y = vLeTwo p y y := huy
    _ ≤ vLeTwo p y x + DyvLeTwo p y x * (y - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (y - x) := by
      rw [hux, hdx]

private lemma uCandidate_tangent_x_Q3_A2_boundary_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p y y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (y - a p * y) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_pos : 0 < a p * y := mul_pos ha_pos hy_pos
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by linarith, le_of_lt hc_lt_y⟩
  have hQy : QuarterPlane3 y y := ⟨hy_pos.le, by linarith, le_rfl⟩
  have hclc1 : closureA1 p y (a p * y) := ⟨hy_pos.le, by linarith [hc_pos], le_rfl⟩
  have hclc2 : closureA2 p y (a p * y) := ⟨hy_pos.le, le_rfl, le_of_lt hc_lt_y⟩
  have hcly : closureA2 p y y := by
    exact ⟨hy_pos.le, by
      have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      simpa using h, le_rfl⟩
  have huc : uCandidate p (a p * y) y = vLeTwo p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc]
    rw [auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y (a p * y) hclc2]
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q3_leTwo p hQy, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y y hcly]
  have hdc : DxuCandidate p (a p * y) y = DyvLeTwo p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    have hdyu : DyauxFunction1 p y (a p * y) = DyuA1 p y (a p * y) := by
      simp [DyauxFunction1, hclc1]
    have hglue := DyuA1_eq_DyvLeTwo_on_A1A2_boundary_leTwo
      p y hp1 hp2 hy_pos
    simpa [hdyu] using hglue
  have hderiv : HasDerivAt (fun t => vLeTwo p y t) (DyvLeTwo p y (a p * y)) (a p * y) := by
    have hsum : 0 < (y + a p * y) / 2 := by linarith [hy_pos, hc_pos]
    have hdiff : 0 < (y - a p * y) / 2 := by linarith [hc_lt_y]
    exact hasDerivAt_vLeTwo_y_of_pos_leTwo p y (a p * y) hsum hdiff
  have hmain :
      vLeTwo p y y ≤
        vLeTwo p y (a p * y) + DyvLeTwo p y (a p * y) * (y - a p * y) := by
    apply vLeTwo_tangent_y_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := a p * y) (hi := y) (x := y) (y := a p * y) (z := y)
    · intro t ht
      have htI : t ∈ Set.Ioo (a p * y) y := by
        simpa [interior_Icc] using ht
      exact ⟨hy_pos, htI.1, htI.2⟩
    · exact ⟨le_rfl, le_of_lt hc_lt_y⟩
    · exact ⟨le_of_lt hc_lt_y, le_rfl⟩
    · exact hderiv
  calc
    uCandidate p y y = vLeTwo p y y := huy
    _ ≤ vLeTwo p y (a p * y) + DyvLeTwo p y (a p * y) * (y - a p * y) := hmain
    _ = uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (y - a p * y) := by
      rw [huc, hdc]

private lemma hasDerivAt_vLeTwo_x_on_diag_pos_leTwo (p : ℝ) (hp1 : 1 < p)
    (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t => vLeTwo p t y) (DxvLeTwo p y y) y := by
  let g : ℝ → ℝ := fun t =>
    |((t + y) / 2)| ^ p - coeffLeTwo p * |((t - y) / 2)| ^ p
  have hEq : (fun t => vLeTwo p t y) = g := by
    ext t
    simp [vLeTwo, g]
  have hbase_sum :
      HasDerivAt (fun t : ℝ => (t + y) / 2) (1 / 2) y := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id y).add_const y).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun t : ℝ => (t - y) / 2) (1 / 2) y := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id y).add_const (-y)).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun t : ℝ => |((t + y) / 2)| ^ p)
        (p * (y ^ (p - 2) * y) * (1 / 2)) y := by
    have h :
        HasDerivAt (fun s : ℝ => |s| ^ p)
          (p * |(y + y) / 2| ^ (p - 2) * ((y + y) / 2)) ((y + y) / 2) :=
      hasDerivAt_abs_rpow ((y + y) / 2) hp1
    have hcomp := h.comp y hbase_sum
    refine hcomp.congr_deriv ?_
    simp [abs_of_pos hy]
    ring
  have hpow_diff :
      HasDerivAt (fun t : ℝ => |((t - y) / 2)| ^ p) 0 y := by
    have h :
        HasDerivAt (fun s : ℝ => |s| ^ p)
          (p * |(y - y) / 2| ^ (p - 2) * ((y - y) / 2)) ((y - y) / 2) :=
      hasDerivAt_abs_rpow ((y - y) / 2) hp1
    have hcomp := h.comp y hbase_diff
    simp only [Function.comp_def] at hcomp
    refine hcomp.congr_deriv ?_
    simp
  have hd :
      HasDerivAt g (p * (y ^ (p - 2) * y) * (1 / 2) - coeffLeTwo p * 0) y := by
    dsimp [g]
    exact hpow_sum.sub (hpow_diff.const_mul (coeffLeTwo p))
  rw [hEq]
  refine hd.congr_deriv ?_
  have hpow : y ^ (p - 2) * y = y ^ (p - 1) := by
    calc
      y ^ (p - 2) * y = y ^ (p - 2) * y ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = y ^ ((p - 2) + 1) := by rw [← Real.rpow_add hy]
      _ = y ^ (p - 1) := by ring_nf
  have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
  simp only [one_div, mul_zero, sub_zero, DxvLeTwo, gt_iff_lt, hy, ↓reduceIte, add_self_div_two,
    abs_of_pos hy, Real.rpow_eq_pow, sub_self, zero_div, abs_zero, hzero, zero_mul]
  rw [hpow]
  ring

private lemma uCandidate_tangent_x_diag_to_Q1_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p y y + DxuCandidate p y y * (z - y) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hQz : QuarterPlane z y := ⟨by linarith, le_of_lt hz_lower, by linarith⟩
  have hcly : closureA2 p y y := by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    exact ⟨hy_pos.le, by
      have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      simpa using h, le_rfl⟩
  have hclz : closureA2 p z y := by
    have haz : a p * z < y := by
      have hmul := mul_lt_mul_of_pos_left hz_upper ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact ⟨by linarith, le_of_lt haz, le_of_lt hz_lower⟩
  have hnotz : ¬ closureA1 p z y := by
    intro h
    have haz : a p * z < y := by
      have hmul := mul_lt_mul_of_pos_left hz_upper ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact not_le_of_gt haz h.2.2
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q1_leTwo p hQy, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y y hcly]
  have huz : uCandidate p z y = vLeTwo p z y := by
    rw [uCandidate_eq_Q1_leTwo p hQz]
    simp [auxFunction1, hnotz, hclz]
  have hdy : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQy]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y y hcly
  have hderiv : HasDerivAt (fun t => vLeTwo p t y) (DxvLeTwo p y y) y :=
    hasDerivAt_vLeTwo_x_on_diag_pos_leTwo p hp1 y hy_pos
  have hmain :
      vLeTwo p z y ≤ vLeTwo p y y + DxvLeTwo p y y * (z - y) := by
    apply vLeTwo_tangent_x_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y) (hi := z) (y := y) (x := y) (z := z)
    · intro t ht
      have htI : t ∈ Set.Ioo y z := by
        simpa [interior_Icc] using ht
      have ht_pos : 0 < t := by linarith [hy_pos, htI.1]
      have hat : a p * t < y := by
        have hmul : a p * t < a p * (y / a p) := by
          exact mul_lt_mul_of_pos_left (lt_trans htI.2 hz_upper) ha_pos
        have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
        simpa [hac] using hmul
      exact ⟨ht_pos, hat, htI.1⟩
    · exact ⟨le_rfl, le_of_lt hz_lower⟩
    · exact ⟨le_of_lt hz_lower, le_rfl⟩
    · exact hderiv
  calc
    uCandidate p z y = vLeTwo p z y := huz
    _ ≤ vLeTwo p y y + DxvLeTwo p y y * (z - y) := hmain
    _ = uCandidate p y y + DxuCandidate p y y * (z - y) := by
      rw [huy, hdy]

private lemma uCandidate_tangent_x_cross_Q3_A2_to_Q1_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y)
    (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have h_xy := uCandidate_tangent_x_Q3_A2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have h_yz := uCandidate_tangent_x_diag_to_Q1_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd : DxuCandidate p y y ≤ DxuCandidate p x y := by
    have hQx : QuarterPlane3 x y := ⟨hy_pos.le, by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith, le_of_lt hx_upper⟩
    have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
    have hcly : closureA2 p y y := by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      exact ⟨hy_pos.le, by
        have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
        simpa using h, le_rfl⟩
    have hclx : closureA2 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
    have hdx : DxuCandidate p x y = DyvLeTwo p y x := by
      rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
      have hnot : ¬ closureA1 p y x := by
        intro h
        exact not_le_of_gt hx_lower h.2.2
      simp [DyauxFunction1, hnot, hclx]
    have hdy : DxuCandidate p y y = DxvLeTwo p y y := by
      rw [DxuCandidate_eq_Q1_leTwo p hQy]
      exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y y hcly
    have hdiag : DxvLeTwo p y y = DyvLeTwo p y y := by
      have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
      simp [DxvLeTwo, DyvLeTwo, hy_pos, abs_of_pos hy_pos, hzero]
    have hmono := DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower hx_upper
    rw [hdy, hdx, hdiag]
    exact hmono
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hx_upper) (le_of_lt hz_lower) h_xy h_yz hd

private lemma uCandidate_tangent_x_on_Q1_A1_segment_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x)
    (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hy_div_pos : 0 < y / a p := div_pos hy_pos ha_pos
  have hQx : QuarterPlane x y := ⟨by linarith, by
    have hlt : y < y / a p := by
      rw [div_eq_mul_inv]
      have hinv : 1 < (a p)⁻¹ := by
        rw [one_lt_inv₀ ha_pos]
        exact ha_lt
      nlinarith
    exact le_of_lt (lt_trans hlt hx_lower), by linarith⟩
  have hQz : QuarterPlane z y := ⟨by linarith, by
    have hlt : y < y / a p := by
      rw [div_eq_mul_inv]
      have hinv : 1 < (a p)⁻¹ := by
        rw [one_lt_inv₀ ha_pos]
        exact ha_lt
      nlinarith
    exact le_of_lt (lt_trans hlt hz_lower), by linarith⟩
  have hayx : y < a p * x := by
    have hmul := mul_lt_mul_of_pos_left hx_lower ha_pos
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hayz : y < a p * z := by
    have hmul := mul_lt_mul_of_pos_left hz_lower ha_pos
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hclx : closureA1 p x y := ⟨hQx.1, hQx.2.2, le_of_lt hayx⟩
  have hclz : closureA1 p z y := ⟨hQz.1, hQz.2.2, le_of_lt hayz⟩
  have hux : uCandidate p x y = uA1 p x y := by
    rw [uCandidate_eq_Q1_leTwo p hQx]
    simp [auxFunction1, hclx]
  have huz : uCandidate p z y = uA1 p z y := by
    rw [uCandidate_eq_Q1_leTwo p hQz]
    simp [auxFunction1, hclz]
  have hdx : DxuCandidate p x y = DxuA1 p x y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQx]
    simp [DxauxFunction1, hclx]
  have hderiv : HasDerivAt (fun t => uA1 p t y) (DxuA1 p x y) x :=
    hasDerivAt_uA1_x_of_pos_leTwo p hp1 hp2 x y (by linarith)
  have hmain : uA1 p z y ≤ uA1 p x y + DxuA1 p x y * (z - x) := by
    apply uA1_tangent_x_on_Icc_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := min x z) (hi := max x z) (x := x) (z := z) (y := y)
    · intro t ht
      have hlow : y / a p < min x z := lt_min hx_lower hz_lower
      exact lt_of_lt_of_le (lt_trans hy_div_pos hlow) ht.1
    · intro t ht
      have htI : t ∈ Set.Icc (min x z) (max x z) := interior_subset ht
      have hlow : y / a p < min x z := lt_min hx_lower hz_lower
      have hyt_div : y / a p < t := lt_of_lt_of_le hlow htI.1
      have ht_pos : 0 < t := lt_trans hy_div_pos hyt_div
      linarith
    · exact ⟨min_le_left x z, le_max_left x z⟩
    · exact ⟨min_le_right x z, le_max_right x z⟩
  calc
    uCandidate p z y = uA1 p z y := huz
    _ ≤ uA1 p x y + DxuA1 p x y * (z - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (z - x) := by
      rw [hux, hdx]

private lemma tangent_glue_two_forward_leTwo
    (f d : ℝ → ℝ) {x m z : ℝ}
    (_hxm : x ≤ m) (hmz : m ≤ z)
    (hxm_tangent : f m ≤ f x + d x * (m - x))
    (hmz_tangent : f z ≤ f m + d m * (z - m))
    (hd_antitone : d m ≤ d x) :
    f z ≤ f x + d x * (z - x) := by
  have hnonneg : 0 ≤ z - m := by linarith
  have hmul : d m * (z - m) ≤ d x * (z - m) :=
    mul_le_mul_of_nonneg_right hd_antitone hnonneg
  calc
    f z ≤ f m + d m * (z - m) := hmz_tangent
    _ ≤ (f x + d x * (m - x)) + d m * (z - m) := by linarith
    _ ≤ (f x + d x * (m - x)) + d x * (z - m) := by linarith
    _ = f x + d x * (z - x) := by ring

private lemma uCandidate_tangent_x_Q1_A2_to_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p) :
    uCandidate p (y / a p) y ≤
      uCandidate p x y + DxuCandidate p x y * (y / a p - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hQx : QuarterPlane x y := ⟨by linarith, le_of_lt hx_lower, by linarith⟩
  have hQb : QuarterPlane (y / a p) y := by
    have hlt : y < y / a p := by
      rw [div_eq_mul_inv]
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hinv : 1 < (a p)⁻¹ := by
        rw [one_lt_inv₀ ha_pos]
        exact ha_lt
      nlinarith
    exact ⟨(div_pos hy_pos ha_pos).le, le_of_lt hlt, by linarith⟩
  have hclx : closureA2 p x y := by
    have hax : a p * x < y := by
      have hmul := mul_lt_mul_of_pos_left hx_upper ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact ⟨by linarith, le_of_lt hax, le_of_lt hx_lower⟩
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hnotx : ¬ closureA1 p x y := by
    intro h
    have hax : a p * x < y := by
      have hmul := mul_lt_mul_of_pos_left hx_upper ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact not_le_of_gt hax h.2.2
  have hux : uCandidate p x y = vLeTwo p x y := by
    rw [uCandidate_eq_Q1_leTwo p hQx]
    simp [auxFunction1, hnotx, hclx]
  have hub : uCandidate p (y / a p) y = vLeTwo p (y / a p) y := by
    rw [uCandidate_eq_Q1_leTwo p hQb, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 _ _ hboundary.2]
  have hdx : DxuCandidate p x y = DxvLeTwo p x y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQx]
    simp [DxauxFunction1, hnotx, hclx]
  have hderiv : HasDerivAt (fun t => vLeTwo p t y) (DxvLeTwo p x y) x := by
    have hsum : 0 < (x + y) / 2 := by linarith
    have hdiff : 0 < (x - y) / 2 := by linarith
    exact hasDerivAt_vLeTwo_x_of_pos_leTwo p x y hsum hdiff
  have hmain :
      vLeTwo p (y / a p) y ≤
        vLeTwo p x y + DxvLeTwo p x y * (y / a p - x) := by
    apply vLeTwo_tangent_x_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := x) (hi := y / a p) (x := x) (z := y / a p) (y := y)
    · intro t ht
      have htI : t ∈ Set.Ioo x (y / a p) := by
        simpa [interior_Icc] using ht
      have ht_pos : 0 < t := by linarith [hy_pos, hx_lower, htI.1]
      have hat : a p * t < y := by
        have hmul : a p * t < a p * (y / a p) :=
          mul_lt_mul_of_pos_left htI.2 ha_pos
        have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
        simpa [hac] using hmul
      exact ⟨ht_pos, hat, lt_trans hx_lower htI.1⟩
    · exact ⟨le_rfl, le_of_lt hx_upper⟩
    · exact ⟨le_of_lt hx_upper, le_rfl⟩
    · exact hderiv
  calc
    uCandidate p (y / a p) y = vLeTwo p (y / a p) y := hub
    _ ≤ vLeTwo p x y + DxvLeTwo p x y * (y / a p - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (y / a p - x) := by
      rw [hux, hdx]

private lemma uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (z - y / a p) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hb_pos : 0 < y / a p := div_pos hy_pos ha_pos
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hQb : QuarterPlane (y / a p) y :=
    ⟨hb_pos.le, le_of_lt hy_lt_b, by linarith⟩
  have hQz : QuarterPlane z y :=
    ⟨by linarith, le_of_lt (lt_trans hy_lt_b hz_lower), by linarith⟩
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hclz : closureA1 p z y := by
    have hayz : y < a p * z := by
      have hmul := mul_lt_mul_of_pos_left hz_lower ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact ⟨hQz.1, hQz.2.2, le_of_lt hayz⟩
  have hub : uCandidate p (y / a p) y = uA1 p (y / a p) y := by
    rw [uCandidate_eq_Q1_leTwo p hQb]
    simp [auxFunction1, hboundary.1]
  have huz : uCandidate p z y = uA1 p z y := by
    rw [uCandidate_eq_Q1_leTwo p hQz]
    simp [auxFunction1, hclz]
  have hdb : DxuCandidate p (y / a p) y = DxuA1 p (y / a p) y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQb]
    simp [DxauxFunction1, hboundary.1]
  have hmain :
      uA1 p z y ≤
        uA1 p (y / a p) y + DxuA1 p (y / a p) y * (z - y / a p) := by
    apply uA1_tangent_x_on_Icc_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y / a p) (hi := z) (x := y / a p) (z := z) (y := y)
    · intro t ht
      exact lt_of_lt_of_le hb_pos ht.1
    · intro t ht
      have htI : t ∈ Set.Ioo (y / a p) z := by
        simpa [interior_Icc] using ht
      linarith [hy_pos, hb_pos, htI.1]
    · exact ⟨le_rfl, le_of_lt hz_lower⟩
    · exact ⟨le_of_lt hz_lower, le_rfl⟩
  calc
    uCandidate p z y = uA1 p z y := huz
    _ ≤ uA1 p (y / a p) y + DxuA1 p (y / a p) y * (z - y / a p) := hmain
    _ = uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (z - y / a p) := by
      rw [hub, hdb]

private lemma uCandidate_tangent_x_cross_Q1_A2_to_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p)
    (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have h_xb := uCandidate_tangent_x_Q1_A2_to_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have h_bz := uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower
  have hd : DxuCandidate p (y / a p) y ≤ DxuCandidate p x y := by
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have hQx : QuarterPlane x y := ⟨by linarith, le_of_lt hx_lower, by linarith⟩
    have hQb : QuarterPlane (y / a p) y := by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hy_lt_b : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact ⟨(div_pos hy_pos ha_pos).le, le_of_lt hy_lt_b, by linarith⟩
    have hax : a p * x < y := by
      have hmul := mul_lt_mul_of_pos_left hx_upper ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have hdx := DxauxFunction1_A2_boundary_le_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower hax
    have hcx : DxuCandidate p x y = DxauxFunction1 p x y := by
      rw [DxuCandidate_eq_Q1_leTwo p hQx]
    have hcb : DxuCandidate p (y / a p) y = DxauxFunction1 p (y / a p) y := by
      rw [DxuCandidate_eq_Q1_leTwo p hQb]
    rwa [hcx, hcb]
  exact tangent_glue_two_forward_leTwo
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hx_upper) (le_of_lt hz_lower) h_xb h_bz hd

private lemma uCandidate_tangent_x_forward_on_Q1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hyx : y < x) (hxz : x ≤ z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  let b : ℝ := y / a p
  by_cases hxb : x < b
  · rcases lt_trichotomy z b with hzb | hzb | hbz
    · exact uCandidate_tangent_x_on_Q1_A2_segment_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
        hy_pos hyx hxb (lt_of_lt_of_le hyx hxz) hzb
    · subst z
      simpa [b] using
        uCandidate_tangent_x_Q1_A2_to_boundary_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
          hy_pos hyx hxb
    · exact uCandidate_tangent_x_cross_Q1_A2_to_A1_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
        hy_pos hyx hxb hbz
  · have hbx : b ≤ x := le_of_not_gt hxb
    rcases hbx.lt_or_eq with hbx_lt | hbx_eq
    · have hbz : b < z := lt_of_lt_of_le hbx_lt hxz
      exact uCandidate_tangent_x_on_Q1_A1_segment_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
        hy_pos (by simpa [b] using hbx_lt) (by simpa [b] using hbz)
    · subst x
      rcases hxz.lt_or_eq with hxz_lt | rfl
      · exact uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
          hy_pos (by simpa [b] using hxz_lt)
      · simp

private lemma uCandidate_tangent_x_on_Q2_A1_segment_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane2 x y := ⟨by linarith, by linarith, by linarith⟩
  have hQz : QuarterPlane2 z y := ⟨by linarith, by linarith, by linarith⟩
  have hclx : closureA1 p (-x) (-y) := by
    refine ⟨by linarith, by linarith, ?_⟩
    have hmul : a p * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha_nonneg (by linarith)
    linarith
  have hclz : closureA1 p (-z) (-y) := by
    refine ⟨by linarith, by linarith, ?_⟩
    have hmul : a p * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha_nonneg (by linarith)
    linarith
  have hux : uCandidate p x y = uA1 p (-x) (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQx]
    simp [auxFunction1, hclx]
  have huz : uCandidate p z y = uA1 p (-z) (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQz]
    simp [auxFunction1, hclz]
  have hdx : DxuCandidate p x y = -DxuA1 p (-x) (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQx]
    simp [DxauxFunction1, hclx]
  have hmain :
      uA1 p (-z) (-y) ≤
        uA1 p (-x) (-y) + DxuA1 p (-x) (-y) * ((-z) - (-x)) := by
    apply uA1_tangent_x_on_Icc_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := min (-x) (-z)) (hi := max (-x) (-z))
        (x := -x) (z := -z) (y := -y)
    · intro t ht
      have hlow : y < min (-x) (-z) := lt_min (by linarith) (by linarith)
      exact lt_trans hy_pos (lt_of_lt_of_le hlow ht.1)
    · intro t ht
      have htI : t ∈ Set.Icc (min (-x) (-z)) (max (-x) (-z)) := interior_subset ht
      have hlow : y < min (-x) (-z) := lt_min (by linarith) (by linarith)
      have hyt : y < t := lt_of_lt_of_le hlow htI.1
      linarith
    · exact ⟨min_le_left (-x) (-z), le_max_left (-x) (-z)⟩
    · exact ⟨min_le_right (-x) (-z), le_max_right (-x) (-z)⟩
  calc
    uCandidate p z y = uA1 p (-z) (-y) := huz
    _ ≤ uA1 p (-x) (-y) + DxuA1 p (-x) (-y) * ((-z) - (-x)) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (z - x) := by
      rw [hux, hdx]
      ring

private lemma uCandidate_tangent_x_Q2_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    uCandidate p (-y) y ≤
      uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane2 x y := ⟨by linarith, by linarith, by linarith⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hclx : closureA1 p (-x) (-y) := by
    refine ⟨by linarith, by linarith, ?_⟩
    have hmul : a p * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha_nonneg (by linarith)
    linarith
  have hcla : closureA1 p y (-y) := by
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hux : uCandidate p x y = uA1 p (-x) (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQx]
    simp [auxFunction1, hclx]
  have hua : uCandidate p (-y) y = uA1 p y (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQa]
    simp [auxFunction1, hcla]
  have hdx : DxuCandidate p x y = -DxuA1 p (-x) (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQx]
    simp [DxauxFunction1, hclx]
  have hmain :
      uA1 p y (-y) ≤
        uA1 p (-x) (-y) + DxuA1 p (-x) (-y) * (y - (-x)) := by
    apply uA1_tangent_x_on_Icc_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y) (hi := -x) (x := -x) (z := y) (y := -y)
    · intro t ht
      exact lt_of_lt_of_le hy_pos ht.1
    · intro t ht
      have htI : t ∈ Set.Ioo y (-x) := by
        simpa [interior_Icc] using ht
      linarith [htI.1]
    · exact ⟨le_of_lt (by linarith), le_rfl⟩
    · exact ⟨le_rfl, le_of_lt (by linarith)⟩
  calc
    uCandidate p (-y) y = uA1 p y (-y) := hua
    _ ≤ uA1 p (-x) (-y) + DxuA1 p (-x) (-y) * (y - (-x)) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
      rw [hux, hdx]
      ring

private lemma uCandidate_tangent_x_antidiag_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, le_of_lt hz_lower, by
    have hc_lt_y : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact le_of_lt (lt_trans hz_upper hc_lt_y)⟩
  have hcla : closureA1 p y (-y) := by
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hclz : closureA1 p y z := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt hz_upper⟩
  have hua : uCandidate p (-y) y = uA1 p y (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQa]
    simp [auxFunction1, hcla]
  have huz : uCandidate p z y = uA1 p y z := by
    rw [uCandidate_eq_Q3_leTwo p hQz]
    simp [auxFunction1, hclz]
  have hda : DxuCandidate p (-y) y = DyuA1 p y (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQa]
    have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo
      p hp1 hp2 y hy_pos.le
    have hdy : DyauxFunction1 p y (-y) = DyuA1 p y (-y) := by
      simp [DyauxFunction1, hcla]
    simp only [neg_neg]
    rw [hrel, hdy]
    ring
  apply le_of_eq
  calc
    uCandidate p z y = uA1 p y z := huz
    _ = uA1 p y (-y) + DyuA1 p y (-y) * (z - (-y)) :=
      uA1_affine_y_tangent_leTwo p y (-y) z hy_pos
    _ = uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
      rw [hua, hda]

private lemma uCandidate_tangent_x_antidiag_to_Q3_A1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (a p * y) y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (a p * y - (-y)) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, by
      have hc_le_y : a p * y ≤ y := by
        simpa using mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      exact hc_le_y⟩
  have hcla : closureA1 p y (-y) := by
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hua : uCandidate p (-y) y = uA1 p y (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQa]
    simp [auxFunction1, hcla]
  have huc : uCandidate p (a p * y) y = uA1 p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc]
    simp [auxFunction1, hclc]
  have hda : DxuCandidate p (-y) y = DyuA1 p y (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQa]
    have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo
      p hp1 hp2 y hy_pos.le
    have hdy : DyauxFunction1 p y (-y) = DyuA1 p y (-y) := by
      simp [DyauxFunction1, hcla]
    simp only [neg_neg]
    rw [hrel, hdy]
    ring
  apply le_of_eq
  calc
    uCandidate p (a p * y) y = uA1 p y (a p * y) := huc
    _ = uA1 p y (-y) + DyuA1 p y (-y) * (a p * y - (-y)) :=
      uA1_affine_y_tangent_leTwo p y (-y) (a p * y) hy_pos
    _ = uCandidate p (-y) y + DxuCandidate p (-y) y * (a p * y - (-y)) := by
      rw [hua, hda]

private lemma DxuCandidate_antidiag_le_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    DxuCandidate p (-y) y ≤ DxuCandidate p x y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane2 x y := ⟨by linarith, by linarith, by linarith⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hclx : closureA1 p (-x) (-y) := by
    refine ⟨by linarith, by linarith, ?_⟩
    have hmul : a p * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha_nonneg (by linarith)
    linarith
  have hcla : closureA1 p y (-y) := by
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hdx : DxuCandidate p x y = -DxuA1 p (-x) (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQx]
    simp [DxauxFunction1, hclx]
  have hda : DxuCandidate p (-y) y = -DxuA1 p y (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQa]
    simp [DxauxFunction1, hcla]
  have hmono : DxuA1 p (-x) (-y) ≤ DxuA1 p y (-y) := by
    have hanti :
        AntitoneOn (fun t : ℝ => DxuA1Fun p (t, -y)) (Set.Icc y (-x)) := by
      have hcont : ContinuousOn (fun t : ℝ => DxuA1Fun p (t, -y)) (Set.Icc y (-x)) := by
        let g : ℝ → ℝ := fun t =>
          alpha p * (p / 2) * t ^ (p - 2) *
            (((p - 2) / (p - 1)) * t + (-y))
        have hg : ContinuousOn g (Set.Icc y (-x)) := by
          dsimp [g]
          exact ((continuousOn_const.mul continuousOn_const).mul
            (continuousOn_id.rpow_const
              (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hy_pos ht.1))))).mul
            ((continuousOn_const.mul continuousOn_id).add continuousOn_const)
        refine ContinuousOn.congr hg ?_
        intro t ht
        have htpos : 0 < t := lt_of_lt_of_le hy_pos ht.1
        simp [g, DxuA1Fun, DxuA1, htpos]
      refine antitoneOn_of_hasDerivWithinAt_nonpos
        (D := Set.Icc y (-x))
        (f := fun t : ℝ => DxuA1Fun p (t, -y))
        (f' := fun t : ℝ => deriv (fun s => DxuA1Fun p (s, -y)) t)
        (convex_Icc y (-x)) hcont ?_ ?_
      · intro t ht
        have htI : t ∈ Set.Ioo y (-x) := by
          simpa [interior_Icc] using ht
        exact (differentiableAt_DxuA1Fun_x_of_pos_leTwo p t (-y)
          (lt_trans hy_pos htI.1)).hasDerivAt.hasDerivWithinAt
      · intro t ht
        have htI : t ∈ Set.Ioo y (-x) := by
          simpa [interior_Icc] using ht
        exact deriv_DxuA1Fun_x_nonpos_leTwo p hp1 hp2 t (-y)
          (lt_trans hy_pos htI.1) (by linarith [htI.1])
    have hy_mem : y ∈ Set.Icc y (-x) := ⟨le_rfl, le_of_lt (by linarith)⟩
    have hx_mem : -x ∈ Set.Icc y (-x) := ⟨le_of_lt (by linarith), le_rfl⟩
    have hle := hanti hy_mem hx_mem (le_of_lt (by linarith))
    simpa [DxuA1Fun] using hle
  rw [hda, hdx]
  linarith

private lemma uCandidate_tangent_x_cross_Q2_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y)
    (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxa := uCandidate_tangent_x_Q2_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  have haz := uCandidate_tangent_x_antidiag_to_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_antidiag_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hx_left) (le_of_lt hz_lower) hxa haz hd

private lemma uCandidate_tangent_x_Q2_to_Q3_A1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    uCandidate p (a p * y) y ≤
      uCandidate p x y + DxuCandidate p x y * (a p * y - x) := by
  have hxa := uCandidate_tangent_x_Q2_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  have hac := uCandidate_tangent_x_antidiag_to_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_antidiag_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hx_left) (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith) hxa hac hd

private lemma DxuCandidate_Q3_A1_boundary_le_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    DxuCandidate p (a p * y) y ≤ DxuCandidate p x y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, by
      have hc_le_y : a p * y ≤ y := by
        simpa using mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      exact hc_le_y⟩
  have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    simp [DyauxFunction1, hclc]
  have hda : DxuCandidate p (-y) y = DyuA1 p y (-y) := by
    have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
    have hcla : closureA1 p y (-y) := by
      refine ⟨hy_pos.le, le_rfl, ?_⟩
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith
    rw [DxuCandidate_eq_Q2_leTwo p hQa]
    have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo
      p hp1 hp2 y hy_pos.le
    have hdy : DyauxFunction1 p y (-y) = DyuA1 p y (-y) := by
      simp [DyauxFunction1, hcla]
    simp only [neg_neg]
    rw [hrel, hdy]
    ring
  have heq : DxuCandidate p (a p * y) y = DxuCandidate p (-y) y := by
    rw [hdc, hda]
    simp [DyuA1, hy_pos]
  rw [heq]
  exact DxuCandidate_antidiag_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left

private lemma DxuCandidate_Q3_A1_boundary_eq_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DxuCandidate p (a p * y) y = DxuCandidate p (-y) y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, by
      have hc_le_y : a p * y ≤ y := by
        simpa using mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      exact hc_le_y⟩
  have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    simp [DyauxFunction1, hclc]
  have hda : DxuCandidate p (-y) y = DyuA1 p y (-y) := by
    have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
    have hcla : closureA1 p y (-y) := by
      refine ⟨hy_pos.le, le_rfl, ?_⟩
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith
    rw [DxuCandidate_eq_Q2_leTwo p hQa]
    have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo
      p hp1 hp2 y hy_pos.le
    have hdy : DyauxFunction1 p y (-y) = DyuA1 p y (-y) := by
      simp [DyauxFunction1, hcla]
    simp only [neg_neg]
    rw [hrel, hdy]
    ring
  rw [hdc, hda]
  simp [DyuA1, hy_pos]

private lemma DxuCandidate_Q3_A1_boundary_le_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DxuCandidate p (a p * y) y ≤ DxuCandidate p (-y) y := by
  rw [DxuCandidate_Q3_A1_boundary_eq_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos]

private lemma uCandidate_tangent_x_antidiag_to_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
  have hac := uCandidate_tangent_x_antidiag_to_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q3_A1_boundary_le_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith) (le_of_lt hz_lower) hac hcz hd

private lemma uCandidate_tangent_x_antidiag_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p y y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (y - (-y)) := by
  have hac := uCandidate_tangent_x_antidiag_to_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hcy := uCandidate_tangent_x_Q3_A2_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q3_A1_boundary_le_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith) (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt) hac hcy hd

private lemma uCandidate_tangent_x_cross_Q2_to_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y)
    (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q2_to_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q3_A1_boundary_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith) (le_of_lt hz_lower) hxc hcz hd

private lemma uCandidate_tangent_x_Q2_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    uCandidate p y y ≤
      uCandidate p x y + DxuCandidate p x y * (y - x) := by
  have hxc := uCandidate_tangent_x_Q2_to_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  have hcy := uCandidate_tangent_x_Q3_A2_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q3_A1_boundary_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith) (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt) hxc hcy hd

private lemma DxuCandidate_diag_le_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    DxuCandidate p y y ≤ DxuCandidate p x y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hdiag_a2 :
      DxuCandidate p y y ≤ DxuCandidate p (a p * y) y := by
    have hQd : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
    have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith, le_of_lt hc_lt_y⟩
    have hcld : closureA2 p y y := by
      refine ⟨hy_pos.le, ?_, le_rfl⟩
      have hle : a p * y ≤ y := le_of_lt hc_lt_y
      exact hle
    have hclc : closureA2 p y (a p * y) := ⟨hy_pos.le, le_rfl, le_of_lt hc_lt_y⟩
    have hnotd : ¬ closureA1 p y y := by
      intro h
      exact not_le_of_gt hc_lt_y h.2.2
    have hdd : DxuCandidate p y y = DxvLeTwo p y y := by
      rw [DxuCandidate_eq_Q1_leTwo p hQd]
      simp [DxauxFunction1, hnotd, hcld]
    have hclc1 : closureA1 p y (a p * y) := ⟨hy_pos.le, by
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith, le_rfl⟩
    have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
      rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
      simp [DyauxFunction1, hclc1]
    have hglue : DyuA1 p y (a p * y) = DyvLeTwo p y (a p * y) :=
      DyuA1_eq_DyvLeTwo_on_A1A2_boundary_leTwo p y hp1 hp2 hy_pos
    have hrel := DxauxFunction1_eq_DyauxFunction1_on_diag_leTwo
      p hp1 hp2 y hy_pos.le
    have hdy : DyauxFunction1 p y y = DyvLeTwo p y y := by
      simp [DyauxFunction1, hnotd, hcld]
    have hdx : DxvLeTwo p y y = DyvLeTwo p y y := by
      have hdx' : DxauxFunction1 p y y = DxvLeTwo p y y := by
        simp [DxauxFunction1, hnotd, hcld]
      rw [← hdx', hrel, hdy]
    have hmono := DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_closed_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := a p * y) (y := y)
      hy_pos le_rfl hc_lt_y
    calc
      DxuCandidate p y y = DxvLeTwo p y y := hdd
      _ = DyvLeTwo p y y := hdx
      _ ≤ DyvLeTwo p y (a p * y) := hmono
      _ = DyuA1 p y (a p * y) := hglue.symm
      _ = DxuCandidate p (a p * y) y := hdc.symm
  exact le_trans hdiag_a2
    (DxuCandidate_Q3_A1_boundary_le_Q2_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_left)

private lemma uCandidate_tangent_x_cross_Q2_to_Q1_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y)
    (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxy := uCandidate_tangent_x_Q2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  have hyz := uCandidate_tangent_x_diag_to_Q1_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_diag_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by linarith) (le_of_lt hz_lower) hxy hyz hd

private lemma DxuCandidate_Q1_boundary_le_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DxuCandidate p (y / a p) y ≤ DxuCandidate p y y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  let b : ℝ := y / a p
  have hb_pos : 0 < b := by
    dsimp [b]
    exact div_pos hy_pos ha_pos
  have hab : a p * b = y := by
    dsimp [b]
    field_simp [ha_pos.ne']
  have hy_lt_b : y < b := by
    dsimp [b]
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hQd : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hQb : QuarterPlane b y := ⟨hb_pos.le, le_of_lt hy_lt_b, by linarith⟩
  have hcld : closureA2 p y y := by
    refine ⟨hy_pos.le, ?_, le_rfl⟩
    have hle : a p * y ≤ y := by
      exact (mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le).trans_eq (one_mul y)
    exact hle
  have hnotd : ¬ closureA1 p y y := by
    intro h
    have hlt : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact not_le_of_gt hlt h.2.2
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hdd : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQd]
    simp [DxauxFunction1, hnotd, hcld]
  have hb1 : closureA1 p b y := by
    simpa [b] using hboundary.1
  have hdb : DxuCandidate p b y = DxuA1 p b y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQb]
    simp [DxauxFunction1, hb1]
  have hglue : DxuA1 p b y = DxvLeTwo p b y := by
    dsimp [b]
    simpa [hab] using DxuA1_eq_DxvLeTwo_on_A1A2_boundary_leTwo
      p b hp1 hp2 hb_pos
  have hanti :
      AntitoneOn (fun t : ℝ => DxvLeTwo p t y) (Set.Icc y b) := by
    have hcont : ContinuousOn (fun t : ℝ => DxvLeTwo p t y) (Set.Icc y b) := by
      let g : ℝ → ℝ := fun t =>
        ((t + y) / 2) ^ (p - 1) * (p / 2) -
          coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2)
      have hg : ContinuousOn g (Set.Icc y b) := by
        dsimp [g]
        apply ContinuousOn.sub
        · exact (((continuousOn_id.add continuousOn_const).div_const 2).rpow_const
            (fun t ht => Or.inl (ne_of_gt (by
              change 0 < (t + y) / 2
              linarith [hy_pos, ht.1])))).mul continuousOn_const
        · exact (continuousOn_const.mul
            (((continuousOn_id.sub continuousOn_const).div_const 2).rpow_const
              (fun _ _ => Or.inr (by linarith)))).mul continuousOn_const
      refine ContinuousOn.congr hg ?_
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hy_pos ht.1
      have hsum : 0 < (t + y) / 2 := by linarith [ht_pos, hy_pos]
      have hdiff_nonneg : 0 ≤ (t - y) / 2 := by linarith [ht.1]
      by_cases hdiff : 0 < (t - y) / 2
      · simp [g, DxvLeTwo, ht_pos, abs_of_pos hsum, abs_of_pos hdiff]
      · have hdiff_zero : (t - y) / 2 = 0 :=
          le_antisymm (le_of_not_gt hdiff) hdiff_nonneg
        have ht_eq : t = y := by linarith
        subst t
        have hp_ne : p - 1 ≠ 0 := by linarith
        simp [g, DxvLeTwo, hy_pos, abs_of_pos hy_pos, Real.zero_rpow hp_ne]
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc y b)
      (f := fun t : ℝ => DxvLeTwo p t y)
      (f' := fun t : ℝ => deriv (fun s => DxvLeTwo p s y) t)
      (convex_Icc y b) hcont ?_ ?_
    · intro t ht
      have htI : t ∈ Set.Ioo y b := by
        simpa [interior_Icc] using ht
      have hsum : 0 < (t + y) / 2 := by linarith [hy_pos, htI.1]
      have hdiff : 0 < (t - y) / 2 := by linarith [htI.1]
      exact (differentiableAt_DxvLeTwo_x_of_pos_leTwo p t y hsum hdiff).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htI : t ∈ Set.Ioo y b := by
        simpa [interior_Icc] using ht
      have h_at : a p * t < y := by
        have hmul : a p * t < a p * b := mul_lt_mul_of_pos_left htI.2 ha_pos
        simpa [hab] using hmul
      exact deriv_DxvLeTwo_x_nonpos_leTwo p hp1 hp2 t y
        ⟨lt_trans hy_pos htI.1, h_at, htI.1⟩
  have hle : DxvLeTwo p b y ≤ DxvLeTwo p y y :=
    hanti ⟨le_rfl, hy_lt_b.le⟩ ⟨hy_lt_b.le, le_rfl⟩ hy_lt_b.le
  calc
    DxuCandidate p (y / a p) y = DxuCandidate p b y := by rfl
    _ = DxuA1 p b y := hdb
    _ = DxvLeTwo p b y := hglue
    _ ≤ DxvLeTwo p y y := hle
    _ = DxuCandidate p y y := hdd.symm

private lemma DxuCandidate_Q1_boundary_le_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    DxuCandidate p (y / a p) y ≤ DxuCandidate p x y :=
  le_trans
    (DxuCandidate_Q1_boundary_le_diag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
    (DxuCandidate_diag_le_Q2_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_left)

private lemma uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (y / a p) y ≤
      uCandidate p y y + DxuCandidate p y y * (y / a p - y) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hQb : QuarterPlane (y / a p) y :=
    ⟨(div_pos hy_pos ha_pos).le, le_of_lt hy_lt_b, by linarith⟩
  have hcl_y : closureA2 p y y := by
    refine ⟨hy_pos.le, ?_, le_rfl⟩
    exact (mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le).trans_eq (one_mul y)
  have hnot_y : ¬ closureA1 p y y := by
    intro h
    have hlt : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact not_le_of_gt hlt h.2.2
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q1_leTwo p hQy]
    simp [auxFunction1, hnot_y, hcl_y]
  have hub : uCandidate p (y / a p) y = vLeTwo p (y / a p) y := by
    rw [uCandidate_eq_Q1_leTwo p hQb,
      auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 (y / a p) y hboundary.2]
  have hdy : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQy]
    simp [DxauxFunction1, hnot_y, hcl_y]
  have hderiv := hasDerivAt_vLeTwo_x_on_diag_pos_leTwo p hp1 y hy_pos
  have hmain :
      vLeTwo p (y / a p) y ≤
        vLeTwo p y y + DxvLeTwo p y y * (y / a p - y) := by
    apply vLeTwo_tangent_x_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y) (hi := y / a p) (x := y) (z := y / a p) (y := y)
    · intro t ht
      have htI : t ∈ Set.Ioo y (y / a p) := by
        simpa [interior_Icc] using ht
      have hat : a p * t < y := by
        have hmul : a p * t < a p * (y / a p) :=
          mul_lt_mul_of_pos_left htI.2 ha_pos
        have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
        simpa [hac] using hmul
      exact ⟨lt_trans hy_pos htI.1, hat, htI.1⟩
    · exact ⟨le_rfl, le_of_lt hy_lt_b⟩
    · exact ⟨le_of_lt hy_lt_b, le_rfl⟩
    · exact hderiv
  calc
    uCandidate p (y / a p) y = vLeTwo p (y / a p) y := hub
    _ ≤ vLeTwo p y y + DxvLeTwo p y y * (y / a p - y) := hmain
    _ = uCandidate p y y + DxuCandidate p y y * (y / a p - y) := by
      rw [huy, hdy]

private lemma uCandidate_tangent_x_Q2_to_Q1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    uCandidate p (y / a p) y ≤
      uCandidate p x y + DxuCandidate p x y * (y / a p - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hxy := uCandidate_tangent_x_Q2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  have hyb := uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_diag_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by linarith) (le_of_lt hy_lt_b) hxy hyb hd

private lemma uCandidate_tangent_x_cross_Q2_to_Q1_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y)
    (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxb := uCandidate_tangent_x_Q2_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  have hbz := uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower
  have hd := DxuCandidate_Q1_boundary_le_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_left
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hy_lt_b : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      linarith)
    (le_of_lt hz_lower) hxb hbz hd

private lemma DxuCandidate_Q3_A1_boundary_le_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    DxuCandidate p (a p * y) y ≤ DxuCandidate p x y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hx_lower, by
    have hc_lt_y : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact le_of_lt (lt_trans hx_upper hc_lt_y)⟩
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, by
      have hle : a p * y ≤ y := by
        simpa using mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      exact hle⟩
  have hclx : closureA1 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hdx : DxuCandidate p x y = DyuA1 p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    simp [DyauxFunction1, hclx]
  have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    simp [DyauxFunction1, hclc]
  rw [hdx, hdc]
  simp [DyuA1, hy_pos]

private lemma DxuCandidate_diag_le_Q3_A1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DxuCandidate p y y ≤ DxuCandidate p (a p * y) y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hQd : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hc_lt_y⟩
  have hcld : closureA2 p y y := ⟨hy_pos.le, le_of_lt hc_lt_y, le_rfl⟩
  have hnotd : ¬ closureA1 p y y := by
    intro h
    exact not_le_of_gt hc_lt_y h.2.2
  have hclc1 : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hdd : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQd]
    simp [DxauxFunction1, hnotd, hcld]
  have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    simp [DyauxFunction1, hclc1]
  have hglue : DyuA1 p y (a p * y) = DyvLeTwo p y (a p * y) :=
    DyuA1_eq_DyvLeTwo_on_A1A2_boundary_leTwo p y hp1 hp2 hy_pos
  have hrel := DxauxFunction1_eq_DyauxFunction1_on_diag_leTwo
    p hp1 hp2 y hy_pos.le
  have hdy : DyauxFunction1 p y y = DyvLeTwo p y y := by
    simp [DyauxFunction1, hnotd, hcld]
  have hdx : DxvLeTwo p y y = DyvLeTwo p y y := by
    have hdx' : DxauxFunction1 p y y = DxvLeTwo p y y := by
      simp [DxauxFunction1, hnotd, hcld]
    rw [← hdx', hrel, hdy]
  have hmono := DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_closed_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := a p * y) (y := y)
    hy_pos le_rfl hc_lt_y
  calc
    DxuCandidate p y y = DxvLeTwo p y y := hdd
    _ = DyvLeTwo p y y := hdx
    _ ≤ DyvLeTwo p y (a p * y) := hmono
    _ = DyuA1 p y (a p * y) := hglue.symm
    _ = DxuCandidate p (a p * y) y := hdc.symm

private lemma DxuCandidate_diag_le_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DxuCandidate p y y ≤ DxuCandidate p (-y) y := by
  calc
    DxuCandidate p y y ≤ DxuCandidate p (a p * y) y :=
      DxuCandidate_diag_le_Q3_A1_boundary_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
    _ = DxuCandidate p (-y) y :=
      DxuCandidate_Q3_A1_boundary_eq_antidiag_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos

private lemma DxuCandidate_diag_le_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    DxuCandidate p y y ≤ DxuCandidate p x y :=
  le_trans
    (DxuCandidate_diag_le_Q3_A1_boundary_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
    (DxuCandidate_Q3_A1_boundary_le_Q3_A1_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower hx_upper)

private lemma DxuCandidate_Q1_boundary_le_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    DxuCandidate p (y / a p) y ≤ DxuCandidate p x y :=
  le_trans
    (DxuCandidate_Q1_boundary_le_diag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
    (DxuCandidate_diag_le_Q3_A1_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower hx_upper)

private lemma DxuCandidate_Q1_boundary_le_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DxuCandidate p (y / a p) y ≤ DxuCandidate p (-y) y :=
  le_trans
    (DxuCandidate_Q1_boundary_le_diag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
    (DxuCandidate_diag_le_antidiag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)

private lemma DxuCandidate_diag_le_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    DxuCandidate p y y ≤ DxuCandidate p x y := by
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hx_upper⟩
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hcly : closureA2 p y y := by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    exact ⟨hy_pos.le, by
      have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      simpa using h, le_rfl⟩
  have hclx : closureA2 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hdx : DxuCandidate p x y = DyvLeTwo p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    have hnot : ¬ closureA1 p y x := by
      intro h
      exact not_le_of_gt hx_lower h.2.2
    simp [DyauxFunction1, hnot, hclx]
  have hdy : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQy]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y y hcly
  have hdiag : DxvLeTwo p y y = DyvLeTwo p y y := by
    have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
    simp [DxvLeTwo, DyvLeTwo, hy_pos, abs_of_pos hy_pos, hzero]
  have hmono := DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  rw [hdy, hdx, hdiag]
  exact hmono

private lemma DxuCandidate_Q1_boundary_le_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    DxuCandidate p (y / a p) y ≤ DxuCandidate p x y :=
  le_trans
    (DxuCandidate_Q1_boundary_le_diag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
    (DxuCandidate_diag_le_Q3_A2_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower hx_upper)

private lemma uCandidate_tangent_x_antidiag_to_Q1_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
  have hxy := uCandidate_tangent_x_antidiag_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hyz := uCandidate_tangent_x_diag_to_Q1_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_diag_le_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by linarith) (le_of_lt hz_lower) hxy hyz hd

private lemma uCandidate_tangent_x_antidiag_to_Q1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (y / a p) y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (y / a p - (-y)) := by
  have hxy := uCandidate_tangent_x_antidiag_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hyb := uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_diag_le_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by linarith) (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_of_lt hlt) hxy hyb hd

private lemma uCandidate_tangent_x_antidiag_to_Q1_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
  have hxb := uCandidate_tangent_x_antidiag_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hbz := uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower
  have hd := DxuCandidate_Q1_boundary_le_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      linarith)
    (le_of_lt hz_lower) hxb hbz hd

private lemma uCandidate_tangent_x_Q3_A1_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    uCandidate p y y ≤
      uCandidate p x y + DxuCandidate p x y * (y - x) := by
  have hxc := uCandidate_tangent_x_Q3_A1_to_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hcy := uCandidate_tangent_x_Q3_A2_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q3_A1_boundary_le_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hx_upper) (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt) hxc hcy hd

private lemma uCandidate_tangent_x_Q3_A1_to_Q1_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y)
    (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxy := uCandidate_tangent_x_Q3_A1_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hyz := uCandidate_tangent_x_diag_to_Q1_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_diag_le_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      linarith) (le_of_lt hz_lower) hxy hyz hd

private lemma uCandidate_tangent_x_Q3_A1_to_Q1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    uCandidate p (y / a p) y ≤
      uCandidate p x y + DxuCandidate p x y * (y / a p - x) := by
  have hxy := uCandidate_tangent_x_Q3_A1_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hyb := uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_diag_le_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      linarith) (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_of_lt hlt) hxy hyb hd

private lemma uCandidate_tangent_x_Q3_A1_to_Q1_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y)
    (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxb := uCandidate_tangent_x_Q3_A1_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hbz := uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower
  have hd := DxuCandidate_Q1_boundary_le_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y / a p := by
        have hay : a p * y < y := by
          simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
        have hyb : y < y / a p := by
          rw [div_eq_mul_inv]
          have hinv : 1 < (a p)⁻¹ := by
            rw [one_lt_inv₀ ha_pos]
            exact ha_lt
          nlinarith
        linarith
      linarith)
    (le_of_lt hz_lower) hxb hbz hd

private lemma uCandidate_tangent_x_Q3_A2_to_Q1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    uCandidate p (y / a p) y ≤
      uCandidate p x y + DxuCandidate p x y * (y / a p - x) := by
  have hxy := uCandidate_tangent_x_Q3_A2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hyb := uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_diag_le_Q3_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hx_upper) (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_of_lt hlt) hxy hyb hd

private lemma uCandidate_tangent_x_Q3_A2_to_Q1_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y)
    (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxb := uCandidate_tangent_x_Q3_A2_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hbz := uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower
  have hd := DxuCandidate_Q1_boundary_le_Q3_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      linarith)
    (le_of_lt hz_lower) hxb hbz hd

private lemma uCandidate_tangent_x_Q3_A2_boundary_to_Q1_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (z - a p * y) := by
  have hcy := uCandidate_tangent_x_Q3_A2_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hyz := uCandidate_tangent_x_diag_to_Q1_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_diag_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    (le_of_lt hz_lower) hcy hyz hd

private lemma uCandidate_tangent_x_Q3_A2_boundary_to_Q1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (y / a p) y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (y / a p - a p * y) := by
  have hcy := uCandidate_tangent_x_Q3_A2_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hyb := uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_diag_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_of_lt hlt) hcy hyb hd

private lemma uCandidate_tangent_x_Q3_A2_boundary_to_Q1_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : y / a p < z) :
    uCandidate p z y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (z - a p * y) := by
  have hcb := uCandidate_tangent_x_Q3_A2_boundary_to_Q1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hbz := uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower
  have hd : DxuCandidate p (y / a p) y ≤ DxuCandidate p (a p * y) y := by
    exact le_trans
      (DxuCandidate_Q1_boundary_le_diag_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
      (DxuCandidate_diag_le_Q3_A1_boundary_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
  exact tangent_glue_two_forward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt1 : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      have hlt2 : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      linarith)
    (le_of_lt hz_lower) hcb hbz hd

private lemma uCandidate_tangent_x_forward_of_y_pos_right_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hxz : x < z) (hx_left : ¬ x < -y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hxa_le : -y ≤ x := le_of_not_gt hx_left
  rcases hxa_le.lt_or_eq with hxa | hxa_eq
  · by_cases hx_c : x < a p * y
    · by_cases hz_c : z < a p * y
      · exact uCandidate_tangent_x_on_Q3_A1_segment_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
          hy_pos hxa hx_c (lt_trans hxa hxz) hz_c
      · have hcz_le : a p * y ≤ z := le_of_not_gt hz_c
        rcases hcz_le.lt_or_eq with hcz | hcz_eq
        · by_cases hz_y : z < y
          · exact uCandidate_tangent_x_cross_Q3_A1_to_A2_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
              hy_pos hxa hx_c hcz hz_y
          · have hyz_le : y ≤ z := le_of_not_gt hz_y
            rcases hyz_le.lt_or_eq with hyz | hyz_eq
            · by_cases hz_b : z < y / a p
              · exact uCandidate_tangent_x_Q3_A1_to_Q1_A2_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                  hy_pos hxa hx_c hyz hz_b
              · have hbz_le : y / a p ≤ z := le_of_not_gt hz_b
                rcases hbz_le.lt_or_eq with hbz | hbz_eq
                · exact uCandidate_tangent_x_Q3_A1_to_Q1_A1_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hxa hx_c hbz
                · subst z
                  exact uCandidate_tangent_x_Q3_A1_to_Q1_boundary_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                    hy_pos hxa hx_c
            · subst z
              exact uCandidate_tangent_x_Q3_A1_to_diag_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                hy_pos hxa hx_c
        · subst z
          exact uCandidate_tangent_x_Q3_A1_to_A2_boundary_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
            hy_pos hxa hx_c
    · have hcx_le : a p * y ≤ x := le_of_not_gt hx_c
      rcases hcx_le.lt_or_eq with hcx | hcx_eq
      · by_cases hx_y : x < y
        · by_cases hz_y : z < y
          · exact uCandidate_tangent_x_on_Q3_A2_segment_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
              hy_pos hcx hx_y (lt_trans hcx hxz) hz_y
          · have hyz_le : y ≤ z := le_of_not_gt hz_y
            rcases hyz_le.lt_or_eq with hyz | hyz_eq
            · by_cases hz_b : z < y / a p
              · exact uCandidate_tangent_x_cross_Q3_A2_to_Q1_A2_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                  hy_pos hcx hx_y hyz hz_b
              · have hbz_le : y / a p ≤ z := le_of_not_gt hz_b
                rcases hbz_le.lt_or_eq with hbz | hbz_eq
                · exact uCandidate_tangent_x_Q3_A2_to_Q1_A1_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hcx hx_y hbz
                · subst z
                  exact uCandidate_tangent_x_Q3_A2_to_Q1_boundary_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                    hy_pos hcx hx_y
            · subst z
              exact uCandidate_tangent_x_Q3_A2_to_diag_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                hy_pos hcx hx_y
        · have hyx_le : y ≤ x := le_of_not_gt hx_y
          rcases hyx_le.lt_or_eq with hyx | hyx_eq
          · exact uCandidate_tangent_x_forward_on_Q1_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
              hy_pos hyx (le_of_lt hxz)
          · subst x
            by_cases hz_b : z < y / a p
            · exact uCandidate_tangent_x_diag_to_Q1_A2_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                hy_pos (by simpa using hxz) hz_b
            · have hbz_le : y / a p ≤ z := le_of_not_gt hz_b
              rcases hbz_le.lt_or_eq with hbz | hbz_eq
              · have hyb := uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
                have hbz' := uCandidate_tangent_x_Q1_boundary_to_A1_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                  hy_pos hbz
                have hd := DxuCandidate_Q1_boundary_le_diag_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
                exact tangent_glue_two_forward_leTwo_local
                  (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
                  (le_of_lt hy_lt_b) (le_of_lt hbz) hyb hbz' hd
              · subst z
                exact uCandidate_tangent_x_diag_to_Q1_boundary_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
      · subst x
        by_cases hz_y : z < y
        · exact uCandidate_tangent_x_Q3_A2_boundary_to_A2_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
            hy_pos (by simpa using hxz) hz_y
        · have hyz_le : y ≤ z := le_of_not_gt hz_y
          rcases hyz_le.lt_or_eq with hyz | hyz_eq
          · by_cases hz_b : z < y / a p
            · exact uCandidate_tangent_x_Q3_A2_boundary_to_Q1_A2_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                hy_pos hyz hz_b
            · have hbz_le : y / a p ≤ z := le_of_not_gt hz_b
              rcases hbz_le.lt_or_eq with hbz | hbz_eq
              · exact uCandidate_tangent_x_Q3_A2_boundary_to_Q1_A1_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                  hy_pos hbz
              · subst z
                exact uCandidate_tangent_x_Q3_A2_boundary_to_Q1_boundary_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
          · subst z
            exact uCandidate_tangent_x_Q3_A2_boundary_to_diag_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  · subst x
    by_cases hz_c : z < a p * y
    · exact uCandidate_tangent_x_antidiag_to_Q3_A1_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
        hy_pos (by simpa using hxz) hz_c
    · have hcz_le : a p * y ≤ z := le_of_not_gt hz_c
      rcases hcz_le.lt_or_eq with hcz | hcz_eq
      · by_cases hz_y : z < y
        · exact uCandidate_tangent_x_antidiag_to_Q3_A2_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
            hy_pos hcz hz_y
        · have hyz_le : y ≤ z := le_of_not_gt hz_y
          rcases hyz_le.lt_or_eq with hyz | hyz_eq
          · by_cases hz_b : z < y / a p
            · exact uCandidate_tangent_x_antidiag_to_Q1_A2_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                hy_pos hyz hz_b
            · have hbz_le : y / a p ≤ z := le_of_not_gt hz_b
              rcases hbz_le.lt_or_eq with hbz | hbz_eq
              · exact uCandidate_tangent_x_antidiag_to_Q1_A1_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                  hy_pos hbz
              · subst z
                exact uCandidate_tangent_x_antidiag_to_Q1_boundary_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
          · subst z
            exact uCandidate_tangent_x_antidiag_to_diag_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
      · subst z
        exact uCandidate_tangent_x_antidiag_to_Q3_A1_boundary_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos

private lemma uCandidate_tangent_x_forward_of_y_pos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hxz : x < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  by_cases hx_left : x < -y
  · by_cases hz_left : z < -y
    · exact uCandidate_tangent_x_on_Q2_A1_segment_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
        hy_pos hx_left hz_left
    · have hza_le : -y ≤ z := le_of_not_gt hz_left
      rcases hza_le.lt_or_eq with hza | hza_eq
      · by_cases hz_c : z < a p * y
        · exact uCandidate_tangent_x_cross_Q2_to_Q3_A1_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
            hy_pos hx_left hza hz_c
        · have hcz_le : a p * y ≤ z := le_of_not_gt hz_c
          rcases hcz_le.lt_or_eq with hcz | hcz_eq
          · by_cases hz_y : z < y
            · exact uCandidate_tangent_x_cross_Q2_to_Q3_A2_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                hy_pos hx_left hcz hz_y
            · have hyz_le : y ≤ z := le_of_not_gt hz_y
              rcases hyz_le.lt_or_eq with hyz | hyz_eq
              · by_cases hz_b : z < y / a p
                · exact uCandidate_tangent_x_cross_Q2_to_Q1_A2_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hx_left hyz hz_b
                · have hbz_le : y / a p ≤ z := le_of_not_gt hz_b
                  rcases hbz_le.lt_or_eq with hbz | hbz_eq
                  · exact uCandidate_tangent_x_cross_Q2_to_Q1_A1_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                      hy_pos hx_left hbz
                  · subst z
                    exact uCandidate_tangent_x_Q2_to_Q1_boundary_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                      hy_pos hx_left
              · subst z
                exact uCandidate_tangent_x_Q2_to_diag_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                  hy_pos hx_left
          · subst z
            exact uCandidate_tangent_x_Q2_to_Q3_A1_boundary_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
              hy_pos hx_left
      · subst z
        exact uCandidate_tangent_x_Q2_to_antidiag_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
          hy_pos hx_left
  · exact uCandidate_tangent_x_forward_of_y_pos_right_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
      hy_pos hxz hx_left

private lemma uCandidate_tangent_x_forward_of_y_pos_le_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hxz : x ≤ z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  rcases hxz.lt_or_eq with hxz_lt | rfl
  · exact uCandidate_tangent_x_forward_of_y_pos_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
      hy_pos hxz_lt
  · simp

private lemma uCandidate_tangent_x_Q1_A1_to_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x) :
    uCandidate p (y / a p) y ≤
      uCandidate p x y + DxuCandidate p x y * (y / a p - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hb_pos : 0 < y / a p := div_pos hy_pos ha_pos
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hQx : QuarterPlane x y :=
    ⟨by linarith, le_of_lt (lt_trans hy_lt_b hx_lower), by linarith⟩
  have hQb : QuarterPlane (y / a p) y :=
    ⟨hb_pos.le, le_of_lt hy_lt_b, by linarith⟩
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hclx : closureA1 p x y := by
    have hay : y < a p * x := by
      have hmul := mul_lt_mul_of_pos_left hx_lower ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact ⟨by linarith, by linarith, le_of_lt hay⟩
  have hux : uCandidate p x y = uA1 p x y := by
    rw [uCandidate_eq_Q1_leTwo p hQx]
    simp [auxFunction1, hclx]
  have hub : uCandidate p (y / a p) y = uA1 p (y / a p) y := by
    rw [uCandidate_eq_Q1_leTwo p hQb]
    simp [auxFunction1, hboundary.1]
  have hdx : DxuCandidate p x y = DxuA1 p x y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQx]
    simp [DxauxFunction1, hclx]
  have hmain :
      uA1 p (y / a p) y ≤
        uA1 p x y + DxuA1 p x y * (y / a p - x) := by
    apply uA1_tangent_x_on_Icc_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y / a p) (hi := x) (x := x) (z := y / a p) (y := y)
    · intro t ht
      exact lt_of_lt_of_le hb_pos ht.1
    · intro t ht
      have htI : t ∈ Set.Ioo (y / a p) x := by
        simpa [interior_Icc] using ht
      linarith [hy_pos, hb_pos, htI.1]
    · exact ⟨le_of_lt hx_lower, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt hx_lower⟩
  calc
    uCandidate p (y / a p) y = uA1 p (y / a p) y := hub
    _ ≤ uA1 p x y + DxuA1 p x y * (y / a p - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (y / a p - x) := by
      rw [hux, hdx]

private lemma uCandidate_tangent_x_Q1_A2_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p) :
    uCandidate p y y ≤
      uCandidate p x y + DxuCandidate p x y * (y - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hQx : QuarterPlane x y := ⟨by linarith, le_of_lt hx_lower, by linarith⟩
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hax : a p * x < y := by
    have hmul := mul_lt_mul_of_pos_left hx_upper ha_pos
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hclx : closureA2 p x y := ⟨by linarith, le_of_lt hax, le_of_lt hx_lower⟩
  have hcly : closureA2 p y y := by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    exact ⟨hy_pos.le, by
      have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      simpa using h, le_rfl⟩
  have hnotx : ¬ closureA1 p x y := by
    intro h
    exact not_le_of_gt hax h.2.2
  have hux : uCandidate p x y = vLeTwo p x y := by
    rw [uCandidate_eq_Q1_leTwo p hQx]
    simp [auxFunction1, hnotx, hclx]
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q1_leTwo p hQy, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y y hcly]
  have hdx : DxuCandidate p x y = DxvLeTwo p x y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQx]
    simp [DxauxFunction1, hnotx, hclx]
  have hderiv : HasDerivAt (fun t => vLeTwo p t y) (DxvLeTwo p x y) x := by
    have hsum : 0 < (x + y) / 2 := by linarith
    have hdiff : 0 < (x - y) / 2 := by linarith
    exact hasDerivAt_vLeTwo_x_of_pos_leTwo p x y hsum hdiff
  have hmain :
      vLeTwo p y y ≤ vLeTwo p x y + DxvLeTwo p x y * (y - x) := by
    apply vLeTwo_tangent_x_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y) (hi := x) (x := x) (z := y) (y := y)
    · intro t ht
      have htI : t ∈ Set.Ioo y x := by
        simpa [interior_Icc] using ht
      have ht_pos : 0 < t := by linarith [hy_pos, htI.1]
      have hat : a p * t < y := by
        have ht_div : t < y / a p := lt_trans htI.2 hx_upper
        have hmul := mul_lt_mul_of_pos_left ht_div ha_pos
        field_simp [ha_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      exact ⟨ht_pos, hat, htI.1⟩
    · exact ⟨le_of_lt hx_lower, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt hx_lower⟩
    · exact hderiv
  calc
    uCandidate p y y = vLeTwo p y y := huy
    _ ≤ vLeTwo p x y + DxvLeTwo p x y * (y - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (y - x) := by
      rw [hux, hdx]

private lemma uCandidate_tangent_x_Q1_boundary_to_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (z - y / a p) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hb_pos : 0 < y / a p := div_pos hy_pos ha_pos
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hQb : QuarterPlane (y / a p) y :=
    ⟨hb_pos.le, le_of_lt hy_lt_b, by linarith⟩
  have hQz : QuarterPlane z y := ⟨by linarith, le_of_lt hz_lower, by linarith⟩
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hclz : closureA2 p z y := by
    have haz : a p * z < y := by
      have hmul := mul_lt_mul_of_pos_left hz_upper ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact ⟨by linarith, le_of_lt haz, le_of_lt hz_lower⟩
  have hnotz : ¬ closureA1 p z y := by
    intro h
    have haz : a p * z < y := by
      have hmul := mul_lt_mul_of_pos_left hz_upper ha_pos
      field_simp [ha_pos.ne'] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact not_le_of_gt haz h.2.2
  have hub : uCandidate p (y / a p) y = vLeTwo p (y / a p) y := by
    rw [uCandidate_eq_Q1_leTwo p hQb,
      auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 (y / a p) y hboundary.2]
  have huz : uCandidate p z y = vLeTwo p z y := by
    rw [uCandidate_eq_Q1_leTwo p hQz]
    simp [auxFunction1, hnotz, hclz]
  have hdb : DxuCandidate p (y / a p) y = DxvLeTwo p (y / a p) y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQb]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 (y / a p) y hboundary.2
  have hderiv : HasDerivAt (fun t => vLeTwo p t y)
      (DxvLeTwo p (y / a p) y) (y / a p) := by
    have hsum : 0 < (y / a p + y) / 2 := by linarith [hb_pos, hy_pos]
    have hdiff : 0 < (y / a p - y) / 2 := by linarith [hy_lt_b]
    exact hasDerivAt_vLeTwo_x_of_pos_leTwo p (y / a p) y hsum hdiff
  have hmain :
      vLeTwo p z y ≤
        vLeTwo p (y / a p) y + DxvLeTwo p (y / a p) y * (z - y / a p) := by
    apply vLeTwo_tangent_x_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := z) (hi := y / a p) (x := y / a p) (z := z) (y := y)
    · intro t ht
      have htI : t ∈ Set.Ioo z (y / a p) := by
        simpa [interior_Icc] using ht
      have ht_pos : 0 < t := by linarith [hy_pos, hz_lower, htI.1]
      have hat : a p * t < y := by
        have hmul : a p * t < a p * (y / a p) :=
          mul_lt_mul_of_pos_left htI.2 ha_pos
        have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
        simpa [hac] using hmul
      exact ⟨ht_pos, hat, lt_trans hz_lower htI.1⟩
    · exact ⟨le_of_lt hz_upper, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt hz_upper⟩
    · exact hderiv
  calc
    uCandidate p z y = vLeTwo p z y := huz
    _ ≤ vLeTwo p (y / a p) y + DxvLeTwo p (y / a p) y * (z - y / a p) := hmain
    _ = uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (z - y / a p) := by
      rw [hub, hdb]

private lemma uCandidate_tangent_x_Q1_A1_to_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x)
    (hz_lower : y < z) (hz_upper : z < y / a p) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxb := uCandidate_tangent_x_Q1_A1_to_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  have hbz := uCandidate_tangent_x_Q1_boundary_to_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd : DxuCandidate p x y ≤ DxuCandidate p (y / a p) y := by
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    have hQx : QuarterPlane x y := by
      have hy_lt_b : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact ⟨by linarith, le_of_lt (lt_trans hy_lt_b hx_lower), by linarith⟩
    have hclx : closureA1 p x y := by
      have hay : y < a p * x := by
        have hmul := mul_lt_mul_of_pos_left hx_lower ha_pos
        field_simp [ha_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      exact ⟨by linarith, by linarith, le_of_lt hay⟩
    have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
    have hdx : DxuCandidate p x y = DxauxFunction1 p x y := by
      rw [DxuCandidate_eq_Q1_leTwo p hQx]
    have hdb : DxuCandidate p (y / a p) y = DxauxFunction1 p (y / a p) y := by
      have hQb : QuarterPlane (y / a p) y := by
        have hb_pos : 0 < y / a p := div_pos hy_pos ha_pos
        have hy_lt_b : y < y / a p := by
          rw [div_eq_mul_inv]
          have hinv : 1 < (a p)⁻¹ := by
            rw [one_lt_inv₀ ha_pos]
            exact ha_lt
          nlinarith
        exact ⟨hb_pos.le, le_of_lt hy_lt_b, by linarith⟩
      rw [DxuCandidate_eq_Q1_leTwo p hQb]
    have hle := DxauxFunction1_A1_le_boundary_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos (by
        have hy_lt_b : y < y / a p := by
          rw [div_eq_mul_inv]
          have hinv : 1 < (a p)⁻¹ := by
            rw [one_lt_inv₀ ha_pos]
            exact ha_lt
          nlinarith
        linarith) (by
        have hmul := mul_lt_mul_of_pos_left hx_lower ha_pos
        field_simp [ha_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    rwa [hdx, hdb]
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (le_of_lt hx_lower) hxb hbz hd

private lemma uCandidate_tangent_x_Q1_boundary_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p y y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (y - y / a p) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hb_pos : 0 < y / a p := div_pos hy_pos ha_pos
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hQb : QuarterPlane (y / a p) y :=
    ⟨hb_pos.le, le_of_lt hy_lt_b, by linarith⟩
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hboundary := horizontal_boundary_closureA1_closureA2_leTwo p y hp1 hp2 hy_pos
  have hcly : closureA2 p y y := by
    exact ⟨hy_pos.le, by
      have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      simpa using h, le_rfl⟩
  have hub : uCandidate p (y / a p) y = vLeTwo p (y / a p) y := by
    rw [uCandidate_eq_Q1_leTwo p hQb,
      auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 (y / a p) y hboundary.2]
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q1_leTwo p hQy, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y y hcly]
  have hdb : DxuCandidate p (y / a p) y = DxvLeTwo p (y / a p) y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQb]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 (y / a p) y hboundary.2
  have hderiv : HasDerivAt (fun t => vLeTwo p t y)
      (DxvLeTwo p (y / a p) y) (y / a p) := by
    have hsum : 0 < (y / a p + y) / 2 := by linarith [hb_pos, hy_pos]
    have hdiff : 0 < (y / a p - y) / 2 := by linarith [hy_lt_b]
    exact hasDerivAt_vLeTwo_x_of_pos_leTwo p (y / a p) y hsum hdiff
  have hmain :
      vLeTwo p y y ≤
        vLeTwo p (y / a p) y + DxvLeTwo p (y / a p) y * (y - y / a p) := by
    apply vLeTwo_tangent_x_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y) (hi := y / a p) (x := y / a p) (z := y) (y := y)
    · intro t ht
      have htI : t ∈ Set.Ioo y (y / a p) := by
        simpa [interior_Icc] using ht
      have ht_pos : 0 < t := by linarith [hy_pos, htI.1]
      have hat : a p * t < y := by
        have hmul : a p * t < a p * (y / a p) :=
          mul_lt_mul_of_pos_left htI.2 ha_pos
        have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
        simpa [hac] using hmul
      exact ⟨ht_pos, hat, htI.1⟩
    · exact ⟨le_of_lt hy_lt_b, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt hy_lt_b⟩
    · exact hderiv
  calc
    uCandidate p y y = vLeTwo p y y := huy
    _ ≤ vLeTwo p (y / a p) y + DxvLeTwo p (y / a p) y * (y - y / a p) := hmain
    _ = uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (y - y / a p) := by
      rw [hub, hdb]

private lemma uCandidate_tangent_x_Q1_A1_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x) :
    uCandidate p y y ≤
      uCandidate p x y + DxuCandidate p x y * (y - x) := by
  have hxb := uCandidate_tangent_x_Q1_A1_to_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  have hby := uCandidate_tangent_x_Q1_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd : DxuCandidate p x y ≤ DxuCandidate p (y / a p) y := by
    have ha_pos : 0 < a p := by
      rw [a_eq_leTwo p hp1 hp2]
      exact div_pos (by linarith) (by linarith)
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    have hQx : QuarterPlane x y := by
      have hy_lt_b : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact ⟨by linarith, le_of_lt (lt_trans hy_lt_b hx_lower), by linarith⟩
    have hQb : QuarterPlane (y / a p) y := by
      have hb_pos : 0 < y / a p := div_pos hy_pos ha_pos
      have hy_lt_b : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact ⟨hb_pos.le, le_of_lt hy_lt_b, by linarith⟩
    have hdx : DxuCandidate p x y = DxauxFunction1 p x y := by
      rw [DxuCandidate_eq_Q1_leTwo p hQx]
    have hdb : DxuCandidate p (y / a p) y = DxauxFunction1 p (y / a p) y := by
      rw [DxuCandidate_eq_Q1_leTwo p hQb]
    have hle := DxauxFunction1_A1_le_boundary_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos (by
        have hy_lt_b : y < y / a p := by
          rw [div_eq_mul_inv]
          have hinv : 1 < (a p)⁻¹ := by
            rw [one_lt_inv₀ ha_pos]
            exact ha_lt
          nlinarith
        linarith) (by
        have hmul := mul_lt_mul_of_pos_left hx_lower ha_pos
        field_simp [ha_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    rwa [hdx, hdb]
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_of_lt hlt)
    (le_of_lt hx_lower) hxb hby hd

private lemma uCandidate_tangent_x_diag_to_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p y y + DxuCandidate p y y * (z - y) := by
  have hzy := uCandidate_tangent_x_Q3_A2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := z) (y := y)
    hy_pos hz_lower hz_upper
  -- Same A2 concavity segment, but based at the diagonal endpoint.
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, by
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hz_upper⟩
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hclz : closureA2 p y z := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt hz_upper⟩
  have hcly : closureA2 p y y := by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    exact ⟨hy_pos.le, by
      have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      simpa using h, le_rfl⟩
  have huz : uCandidate p z y = vLeTwo p y z := by
    rw [uCandidate_eq_Q3_leTwo p hQz, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y z hclz]
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q1_leTwo p hQy, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y y hcly]
  have hdy : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQy]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y y hcly
  have hdiag : DxvLeTwo p y y = DyvLeTwo p y y := by
    have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
    simp [DxvLeTwo, DyvLeTwo, hy_pos, abs_of_pos hy_pos, hzero]
  have hderiv : HasDerivAt (fun t => vLeTwo p y t) (DyvLeTwo p y y) y := by
    have hsum : 0 < (y + y) / 2 := by linarith
    have hdiff_nonneg : 0 ≤ (y - y) / 2 := by norm_num
    -- use the x-derivative diagonal private lemma and symmetry of formulas at the diagonal
    have hxder := hasDerivAt_vLeTwo_x_on_diag_pos_leTwo p hp1 y hy_pos
    -- direct y-derivative at the cusp follows from the abs-rpow derivative
    -- as in the x lemma.
    let g : ℝ → ℝ := fun t =>
      |((y + t) / 2)| ^ p - coeffLeTwo p * |((y - t) / 2)| ^ p
    have hEq : (fun t => vLeTwo p y t) = g := by
      ext t
      simp [vLeTwo, g]
    have hbase_sum :
        HasDerivAt (fun t : ℝ => (y + t) / 2) (1 / 2) y := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id y).const_add y).const_mul (1 / 2 : ℝ))
    have hbase_diff :
        HasDerivAt (fun t : ℝ => (y - t) / 2) (-(1 / 2)) y := by
      simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        ((((hasDerivAt_id y).neg).const_add y).const_mul (1 / 2 : ℝ))
    have hpow_sum :
        HasDerivAt (fun t : ℝ => |((y + t) / 2)| ^ p)
          (p * (y ^ (p - 2) * y) * (1 / 2)) y := by
      have h :
          HasDerivAt (fun s : ℝ => |s| ^ p)
            (p * |(y + y) / 2| ^ (p - 2) * ((y + y) / 2)) ((y + y) / 2) :=
        hasDerivAt_abs_rpow ((y + y) / 2) hp1
      have hcomp := h.comp y hbase_sum
      refine hcomp.congr_deriv ?_
      simp [abs_of_pos hy_pos]
      ring
    have hpow_diff :
        HasDerivAt (fun t : ℝ => |((y - t) / 2)| ^ p) 0 y := by
      have h :
          HasDerivAt (fun s : ℝ => |s| ^ p)
            (p * |(y - y) / 2| ^ (p - 2) * ((y - y) / 2)) ((y - y) / 2) :=
        hasDerivAt_abs_rpow ((y - y) / 2) hp1
      have hcomp := h.comp y hbase_diff
      simp only [Function.comp_def] at hcomp
      refine hcomp.congr_deriv ?_
      simp
    have hd :
        HasDerivAt g (p * (y ^ (p - 2) * y) * (1 / 2) - coeffLeTwo p * 0) y := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul (coeffLeTwo p))
    rw [hEq]
    refine hd.congr_deriv ?_
    have hpow : y ^ (p - 2) * y = y ^ (p - 1) := by
      calc
        y ^ (p - 2) * y = y ^ (p - 2) * y ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = y ^ ((p - 2) + 1) := by rw [← Real.rpow_add hy_pos]
        _ = y ^ (p - 1) := by ring_nf
    have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
    simp only [one_div, mul_zero, sub_zero, DyvLeTwo, gt_iff_lt, hy_pos, ↓reduceIte,
      add_self_div_two, abs_of_pos hy_pos, Real.rpow_eq_pow, sub_self, zero_div, abs_zero, hzero,
      zero_mul, add_zero]
    rw [hpow]
    ring
  have hmain :
      vLeTwo p y z ≤ vLeTwo p y y + DyvLeTwo p y y * (z - y) := by
    apply vLeTwo_tangent_y_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := z) (hi := y) (x := y) (y := y) (z := z)
    · intro t ht
      have htI : t ∈ Set.Ioo z y := by
        simpa [interior_Icc] using ht
      exact ⟨hy_pos, lt_trans hz_lower htI.1, htI.2⟩
    · exact ⟨le_of_lt hz_upper, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt hz_upper⟩
    · exact hderiv
  calc
    uCandidate p z y = vLeTwo p y z := huz
    _ ≤ vLeTwo p y y + DyvLeTwo p y y * (z - y) := hmain
    _ = uCandidate p y y + DxuCandidate p y y * (z - y) := by
      rw [huy, hdy, hdiag]

private lemma uCandidate_tangent_x_Q3_A1_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    uCandidate p (-y) y ≤
      uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hx_lower, by
    have hc_lt_y : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact le_of_lt (lt_trans hx_upper hc_lt_y)⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hclx : closureA1 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hcla : closureA1 p y (-y) := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hux : uCandidate p x y = uA1 p y x := by
    rw [uCandidate_eq_Q3_leTwo p hQx]
    simp [auxFunction1, hclx]
  have hua : uCandidate p (-y) y = uA1 p y (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQa]
    simp [auxFunction1, hcla]
  have hdx : DxuCandidate p x y = DyuA1 p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    simp [DyauxFunction1, hclx]
  apply le_of_eq
  calc
    uCandidate p (-y) y = uA1 p y (-y) := hua
    _ = uA1 p y x + DyuA1 p y x * ((-y) - x) :=
      uA1_affine_y_tangent_leTwo p y x (-y) hy_pos
    _ = uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
      rw [hux, hdx]

private lemma uCandidate_tangent_x_antidiag_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hQz : QuarterPlane2 z y := ⟨by linarith, by linarith, by linarith⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hclz : closureA1 p (-z) (-y) := by
    refine ⟨by linarith, by linarith, ?_⟩
    have hmul : a p * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha_nonneg (by linarith)
    linarith
  have hcla : closureA1 p y (-y) := by
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have huz : uCandidate p z y = uA1 p (-z) (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQz]
    simp [auxFunction1, hclz]
  have hua : uCandidate p (-y) y = uA1 p y (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQa]
    simp [auxFunction1, hcla]
  have hda : DxuCandidate p (-y) y = -DxuA1 p y (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQa]
    simp [DxauxFunction1, hcla]
  have hmain :
      uA1 p (-z) (-y) ≤
        uA1 p y (-y) + DxuA1 p y (-y) * ((-z) - y) := by
    apply uA1_tangent_x_on_Icc_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := y) (hi := -z) (x := y) (z := -z) (y := -y)
    · intro t ht
      exact lt_of_lt_of_le hy_pos ht.1
    · intro t ht
      have htI : t ∈ Set.Ioo y (-z) := by
        simpa [interior_Icc] using ht
      linarith [hy_pos, htI.1]
    · exact ⟨le_rfl, le_of_lt (by linarith)⟩
    · exact ⟨le_of_lt (by linarith), le_rfl⟩
  calc
    uCandidate p z y = uA1 p (-z) (-y) := huz
    _ ≤ uA1 p y (-y) + DxuA1 p y (-y) * ((-z) - y) := hmain
    _ = uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
      rw [hua, hda]
      ring

private lemma DxuCandidate_Q1_A2_le_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p) :
    DxuCandidate p x y ≤ DxuCandidate p y y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hQx : QuarterPlane x y := ⟨by linarith, le_of_lt hx_lower, by linarith⟩
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hax : a p * x < y := by
    have hmul := mul_lt_mul_of_pos_left hx_upper ha_pos
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hclx : closureA2 p x y := ⟨by linarith, le_of_lt hax, le_of_lt hx_lower⟩
  have hcly : closureA2 p y y := by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    exact ⟨hy_pos.le, by
      have h := mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le
      simpa using h, le_rfl⟩
  have hnotx : ¬ closureA1 p x y := by
    intro h
    exact not_le_of_gt hax h.2.2
  have hdx : DxuCandidate p x y = DxvLeTwo p x y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQx]
    simp [DxauxFunction1, hnotx, hclx]
  have hdy : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQy]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y y hcly
  have hanti :
      AntitoneOn (fun t : ℝ => DxvLeTwo p t y) (Set.Icc y x) := by
    have hcont : ContinuousOn (fun t : ℝ => DxvLeTwo p t y) (Set.Icc y x) := by
      let g : ℝ → ℝ := fun t =>
        ((t + y) / 2) ^ (p - 1) * (p / 2) -
          coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2)
      have hg : ContinuousOn g (Set.Icc y x) := by
        dsimp [g]
        apply ContinuousOn.sub
        · exact (((continuousOn_id.add continuousOn_const).div_const 2).rpow_const
            (fun t ht => Or.inl (ne_of_gt (by
              change 0 < (t + y) / 2
              linarith [hy_pos, ht.1])))).mul continuousOn_const
        · exact (continuousOn_const.mul
            (((continuousOn_id.sub continuousOn_const).div_const 2).rpow_const
              (fun _ _ => Or.inr (by linarith)))).mul continuousOn_const
      refine ContinuousOn.congr hg ?_
      intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hy_pos ht.1
      have hsum : 0 < (t + y) / 2 := by linarith [ht_pos, hy_pos]
      have hdiff_nonneg : 0 ≤ (t - y) / 2 := by linarith [ht.1]
      by_cases hdiff : 0 < (t - y) / 2
      · simp [g, DxvLeTwo, ht_pos, abs_of_pos hsum, abs_of_pos hdiff]
      · have hdiff_zero : (t - y) / 2 = 0 :=
          le_antisymm (le_of_not_gt hdiff) hdiff_nonneg
        have ht_eq : t = y := by linarith
        subst t
        have hp_ne : p - 1 ≠ 0 := by linarith
        simp [g, DxvLeTwo, hy_pos, abs_of_pos hy_pos, Real.zero_rpow hp_ne]
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc y x)
      (f := fun t : ℝ => DxvLeTwo p t y)
      (f' := fun t : ℝ => deriv (fun s => DxvLeTwo p s y) t)
      (convex_Icc y x) hcont ?_ ?_
    · intro t ht
      have htI : t ∈ Set.Ioo y x := by
        simpa [interior_Icc] using ht
      have hsum : 0 < (t + y) / 2 := by linarith [hy_pos, htI.1]
      have hdiff : 0 < (t - y) / 2 := by linarith [htI.1]
      exact (differentiableAt_DxvLeTwo_x_of_pos_leTwo p t y hsum hdiff).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htI : t ∈ Set.Ioo y x := by
        simpa [interior_Icc] using ht
      have h_at : a p * t < y := by
        have ht_div : t < y / a p := lt_trans htI.2 hx_upper
        have hmul := mul_lt_mul_of_pos_left ht_div ha_pos
        field_simp [ha_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      exact deriv_DxvLeTwo_x_nonpos_leTwo p hp1 hp2 t y
        ⟨lt_trans hy_pos htI.1, h_at, htI.1⟩
  have hle := hanti ⟨le_rfl, le_of_lt hx_lower⟩ ⟨le_of_lt hx_lower, le_rfl⟩
    (le_of_lt hx_lower)
  rwa [hdx, hdy]

private lemma DxuCandidate_Q3_A2_le_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    DxuCandidate p x y ≤ DxuCandidate p (a p * y) y := by
  have hdiag := DxuCandidate_diag_le_Q3_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hbd := DxuCandidate_diag_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  -- On the A2 strip the derivative is antitone, so the right endpoint has
  -- smaller derivative than the left boundary.
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, by
    have ha_nonneg : 0 ≤ a p := ha_pos.le
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hx_upper⟩
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_pos.le hy_pos.le
    linarith, by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      exact (mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le).trans_eq (one_mul y)⟩
  have hclx : closureA2 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hclc1 : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_pos.le hy_pos.le
    linarith, le_rfl⟩
  have hdx : DxuCandidate p x y = DyvLeTwo p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    have hnot : ¬ closureA1 p y x := by
      intro h
      exact not_le_of_gt hx_lower h.2.2
    simp [DyauxFunction1, hnot, hclx]
  have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    simp [DyauxFunction1, hclc1]
  have hglue : DyuA1 p y (a p * y) = DyvLeTwo p y (a p * y) :=
    DyuA1_eq_DyvLeTwo_on_A1A2_boundary_leTwo p y hp1 hp2 hy_pos
  have hmono : DyvLeTwo p y x ≤ DyvLeTwo p y (a p * y) := by
    have hanti := DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_closed_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos (le_of_lt hx_lower) hx_upper
    have hanti_c := DyvLeTwo_diag_le_DyvLeTwo_Q3_A2_closed_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := a p * y) (y := y)
      hy_pos le_rfl (by
        have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos)
    -- Direct antitonicity on `[a*y,x]`.
    have hantiOn :
        AntitoneOn (fun t : ℝ => DyvLeTwo p y t) (Set.Icc (a p * y) x) := by
      have hcont : ContinuousOn (fun t : ℝ => DyvLeTwo p y t) (Set.Icc (a p * y) x) := by
        let g : ℝ → ℝ := fun t =>
          ((y + t) / 2) ^ (p - 1) * (p / 2) +
            coeffLeTwo p * ((y - t) / 2) ^ (p - 1) * (p / 2)
        have hg : ContinuousOn g (Set.Icc (a p * y) x) := by
          dsimp [g]
          apply ContinuousOn.add
          · exact (((continuousOn_const.add continuousOn_id).div_const 2).rpow_const
              (fun t ht => Or.inl (ne_of_gt (by
                change 0 < (y + t) / 2
                have hnonneg : 0 ≤ a p * y := mul_nonneg ha_pos.le hy_pos.le
                linarith [hy_pos, hnonneg, ht.1])))).mul continuousOn_const
          · exact (continuousOn_const.mul
              (((continuousOn_const.sub continuousOn_id).div_const 2).rpow_const
                (fun t ht => Or.inl (ne_of_gt (by
                  change 0 < (y - t) / 2
                  linarith [ht.2, hx_upper]))))).mul continuousOn_const
        refine ContinuousOn.congr hg ?_
        intro t ht
        have hsum : 0 < (y + t) / 2 := by
          have hnonneg : 0 ≤ a p * y := mul_nonneg ha_pos.le hy_pos.le
          linarith [hy_pos, hnonneg, ht.1]
        have hdiff : 0 < (y - t) / 2 := by linarith [ht.2, hx_upper]
        simp [g, DyvLeTwo, hy_pos, abs_of_pos hsum, abs_of_pos hdiff]
      refine antitoneOn_of_hasDerivWithinAt_nonpos
        (D := Set.Icc (a p * y) x)
        (f := fun t : ℝ => DyvLeTwo p y t)
        (f' := fun t : ℝ => deriv (fun s => DyvLeTwo p y s) t)
        (convex_Icc (a p * y) x) hcont ?_ ?_
      · intro t ht
        have htI : t ∈ Set.Ioo (a p * y) x := by
          simpa [interior_Icc] using ht
        have hsum : 0 < (y + t) / 2 := by
          have hnonneg : 0 ≤ a p * y := mul_nonneg ha_pos.le hy_pos.le
          linarith [hy_pos, hnonneg, htI.1]
        have hdiff : 0 < (y - t) / 2 := by linarith [htI.2, hx_upper]
        exact (differentiableAt_DyvLeTwo_y_of_pos_leTwo p y t hsum
          hdiff).hasDerivAt.hasDerivWithinAt
      · intro t ht
        have htI : t ∈ Set.Ioo (a p * y) x := by
          simpa [interior_Icc] using ht
        exact deriv_DyvLeTwo_y_nonpos_leTwo p hp1 hp2 y t
          ⟨hy_pos, htI.1, lt_trans htI.2 hx_upper⟩
    exact hantiOn ⟨le_rfl, le_of_lt hx_lower⟩ ⟨le_of_lt hx_lower, le_rfl⟩
      (le_of_lt hx_lower)
  rw [hdx, hdc, hglue]
  exact hmono

private lemma DxuCandidate_Q3_A1_eq_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y) :
    DxuCandidate p x y = DxuCandidate p (-y) y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hx_lower, by
    have hc_lt_y : a p * y < y := by
      simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
    exact le_of_lt (lt_trans hx_upper hc_lt_y)⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hclx : closureA1 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hcla : closureA1 p y (-y) := by
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hdx : DxuCandidate p x y = DyuA1 p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    simp [DyauxFunction1, hclx]
  have hda : DxuCandidate p (-y) y = DyuA1 p y (-y) := by
    rw [DxuCandidate_eq_Q2_leTwo p hQa]
    have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag_leTwo
      p hp1 hp2 y hy_pos.le
    have hdy : DyauxFunction1 p y (-y) = DyuA1 p y (-y) := by
      simp [DyauxFunction1, hcla]
    simp only [neg_neg]
    rw [hrel, hdy]
    ring
  rw [hdx, hda]
  simp [DyuA1, hy_pos]

private lemma uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (a p * y) y ≤
      uCandidate p y y + DxuCandidate p y y * (a p * y - y) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hc_pos : 0 < a p * y := mul_pos ha_pos hy_pos
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by linarith, le_of_lt hc_lt_y⟩
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hclc : closureA2 p y (a p * y) := ⟨hy_pos.le, le_rfl, le_of_lt hc_lt_y⟩
  have hcly : closureA2 p y y := ⟨hy_pos.le, le_of_lt hc_lt_y, le_rfl⟩
  have huc : uCandidate p (a p * y) y = vLeTwo p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc,
      auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y (a p * y) hclc]
  have huy : uCandidate p y y = vLeTwo p y y := by
    rw [uCandidate_eq_Q1_leTwo p hQy,
      auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y y hcly]
  have hdy : DxuCandidate p y y = DxvLeTwo p y y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQy]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y y hcly
  have hdiag : DxvLeTwo p y y = DyvLeTwo p y y := by
    have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
    simp [DxvLeTwo, DyvLeTwo, hy_pos, abs_of_pos hy_pos, hzero]
  have hderiv : HasDerivAt (fun t => vLeTwo p y t) (DyvLeTwo p y y) y := by
    -- same diagonal derivative in the second coordinate as above
    let g : ℝ → ℝ := fun t =>
      |((y + t) / 2)| ^ p - coeffLeTwo p * |((y - t) / 2)| ^ p
    have hEq : (fun t => vLeTwo p y t) = g := by
      ext t
      simp [vLeTwo, g]
    have hbase_sum :
        HasDerivAt (fun t : ℝ => (y + t) / 2) (1 / 2) y := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id y).const_add y).const_mul (1 / 2 : ℝ))
    have hbase_diff :
        HasDerivAt (fun t : ℝ => (y - t) / 2) (-(1 / 2)) y := by
      simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        ((((hasDerivAt_id y).neg).const_add y).const_mul (1 / 2 : ℝ))
    have hpow_sum :
        HasDerivAt (fun t : ℝ => |((y + t) / 2)| ^ p)
          (p * (y ^ (p - 2) * y) * (1 / 2)) y := by
      have h :
          HasDerivAt (fun s : ℝ => |s| ^ p)
            (p * |(y + y) / 2| ^ (p - 2) * ((y + y) / 2)) ((y + y) / 2) :=
        hasDerivAt_abs_rpow ((y + y) / 2) hp1
      have hcomp := h.comp y hbase_sum
      refine hcomp.congr_deriv ?_
      simp [abs_of_pos hy_pos]
      ring
    have hpow_diff :
        HasDerivAt (fun t : ℝ => |((y - t) / 2)| ^ p) 0 y := by
      have h :
          HasDerivAt (fun s : ℝ => |s| ^ p)
            (p * |(y - y) / 2| ^ (p - 2) * ((y - y) / 2)) ((y - y) / 2) :=
        hasDerivAt_abs_rpow ((y - y) / 2) hp1
      have hcomp := h.comp y hbase_diff
      simp only [Function.comp_def] at hcomp
      refine hcomp.congr_deriv ?_
      simp
    have hd :
        HasDerivAt g (p * (y ^ (p - 2) * y) * (1 / 2) - coeffLeTwo p * 0) y := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul (coeffLeTwo p))
    rw [hEq]
    refine hd.congr_deriv ?_
    have hpow : y ^ (p - 2) * y = y ^ (p - 1) := by
      calc
        y ^ (p - 2) * y = y ^ (p - 2) * y ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = y ^ ((p - 2) + 1) := by rw [← Real.rpow_add hy_pos]
        _ = y ^ (p - 1) := by ring_nf
    have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
    simp only [one_div, mul_zero, sub_zero, DyvLeTwo, gt_iff_lt, hy_pos, ↓reduceIte,
      add_self_div_two, abs_of_pos hy_pos, Real.rpow_eq_pow, sub_self, zero_div, abs_zero, hzero,
      zero_mul, add_zero]
    rw [hpow]
    ring
  have hmain :
      vLeTwo p y (a p * y) ≤
        vLeTwo p y y + DyvLeTwo p y y * (a p * y - y) := by
    apply vLeTwo_tangent_y_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := a p * y) (hi := y) (x := y) (y := y) (z := a p * y)
    · intro t ht
      have htI : t ∈ Set.Ioo (a p * y) y := by
        simpa [interior_Icc] using ht
      exact ⟨hy_pos, htI.1, htI.2⟩
    · exact ⟨le_of_lt hc_lt_y, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt hc_lt_y⟩
    · exact hderiv
  calc
    uCandidate p (a p * y) y = vLeTwo p y (a p * y) := huc
    _ ≤ vLeTwo p y y + DyvLeTwo p y y * (a p * y - y) := hmain
    _ = uCandidate p y y + DxuCandidate p y y * (a p * y - y) := by
      rw [huy, hdy, hdiag]

private lemma uCandidate_tangent_x_Q1_A2_to_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p)
    (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxy := uCandidate_tangent_x_Q1_A2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hyz := uCandidate_tangent_x_diag_to_Q3_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q1_A2_le_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (le_of_lt hx_lower) hxy hyz hd

private lemma uCandidate_tangent_x_Q1_A2_to_Q3_A2_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p) :
    uCandidate p (a p * y) y ≤
      uCandidate p x y + DxuCandidate p x y * (a p * y - x) := by
  have hxy := uCandidate_tangent_x_Q1_A2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hyc := uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q1_A2_le_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    (le_of_lt hx_lower) hxy hyc hd

private lemma uCandidate_tangent_x_Q3_A2_to_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    uCandidate p (a p * y) y ≤
      uCandidate p x y + DxuCandidate p x y * (a p * y - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hc_pos : 0 < a p * y := mul_pos ha_pos hy_pos
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, by linarith [hc_pos, hx_lower], le_of_lt hx_upper⟩
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by linarith, le_of_lt hc_lt_y⟩
  have hclx : closureA2 p y x := ⟨hy_pos.le, le_of_lt hx_lower, le_of_lt hx_upper⟩
  have hclc : closureA2 p y (a p * y) := ⟨hy_pos.le, le_rfl, le_of_lt hc_lt_y⟩
  have hux : uCandidate p x y = vLeTwo p y x := by
    rw [uCandidate_eq_Q3_leTwo p hQx, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y x hclx]
  have huc : uCandidate p (a p * y) y = vLeTwo p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc, auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 y (a p * y) hclc]
  have hdx : DxuCandidate p x y = DyvLeTwo p y x := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    have hnot : ¬ closureA1 p y x := by
      intro h
      exact not_le_of_gt hx_lower h.2.2
    simp [DyauxFunction1, hnot, hclx]
  have hderiv : HasDerivAt (fun t => vLeTwo p y t) (DyvLeTwo p y x) x := by
    have hsum : 0 < (y + x) / 2 := by linarith [hy_pos, hc_pos, hx_lower]
    have hdiff : 0 < (y - x) / 2 := by linarith
    exact hasDerivAt_vLeTwo_y_of_pos_leTwo p y x hsum hdiff
  have hmain :
      vLeTwo p y (a p * y) ≤
        vLeTwo p y x + DyvLeTwo p y x * (a p * y - x) := by
    apply vLeTwo_tangent_y_on_Icc_of_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (lo := a p * y) (hi := x) (x := y) (y := x) (z := a p * y)
    · intro t ht
      have htI : t ∈ Set.Ioo (a p * y) x := by
        simpa [interior_Icc] using ht
      exact ⟨hy_pos, htI.1, lt_trans htI.2 hx_upper⟩
    · exact ⟨le_of_lt hx_lower, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt hx_lower⟩
    · exact hderiv
  calc
    uCandidate p (a p * y) y = vLeTwo p y (a p * y) := huc
    _ ≤ vLeTwo p y x + DyvLeTwo p y x * (a p * y - x) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * (a p * y - x) := by
      rw [hux, hdx]

private lemma uCandidate_tangent_x_Q3_A2_boundary_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (z - a p * y) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hc_lt_y⟩
  have hQz : QuarterPlane3 z y :=
    ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt (lt_trans hz_upper hc_lt_y)⟩
  have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hclz : closureA1 p y z := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt hz_upper⟩
  have huc : uCandidate p (a p * y) y = uA1 p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc]
    simp [auxFunction1, hclc]
  have huz : uCandidate p z y = uA1 p y z := by
    rw [uCandidate_eq_Q3_leTwo p hQz]
    simp [auxFunction1, hclz]
  have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    simp [DyauxFunction1, hclc]
  apply le_of_eq
  calc
    uCandidate p z y = uA1 p y z := huz
    _ = uA1 p y (a p * y) + DyuA1 p y (a p * y) * (z - a p * y) :=
      uA1_affine_y_tangent_leTwo p y (a p * y) z hy_pos
    _ = uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (z - a p * y) := by
      rw [huc, hdc]

private lemma uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (-y) y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * ((-y) - a p * y) := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hQc : QuarterPlane3 (a p * y) y := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_of_lt hc_lt_y⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hclc : closureA1 p y (a p * y) := ⟨hy_pos.le, by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith, le_rfl⟩
  have hcla : closureA1 p y (-y) := by
    refine ⟨hy_pos.le, le_rfl, ?_⟩
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have huc : uCandidate p (a p * y) y = uA1 p y (a p * y) := by
    rw [uCandidate_eq_Q3_leTwo p hQc]
    simp [auxFunction1, hclc]
  have hua : uCandidate p (-y) y = uA1 p y (-y) := by
    rw [uCandidate_eq_Q2_leTwo p hQa]
    simp [auxFunction1, hcla]
  have hdc : DxuCandidate p (a p * y) y = DyuA1 p y (a p * y) := by
    rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQc]
    simp [DyauxFunction1, hclc]
  apply le_of_eq
  calc
    uCandidate p (-y) y = uA1 p y (-y) := hua
    _ = uA1 p y (a p * y) + DyuA1 p y (a p * y) * ((-y) - a p * y) :=
      uA1_affine_y_tangent_leTwo p y (a p * y) (-y) hy_pos
    _ = uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * ((-y) - a p * y) := by
      rw [huc, hdc]

private lemma uCandidate_tangent_x_Q3_A2_boundary_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p (a p * y) y +
        DxuCandidate p (a p * y) y * (z - a p * y) := by
  have hca := uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have haz := uCandidate_tangent_x_antidiag_to_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_left
  have hd := DxuCandidate_Q3_A1_boundary_le_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_left) (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    hca haz hd

private lemma uCandidate_tangent_x_Q3_A2_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y)
    (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q3_A2_to_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q3_A2_le_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (le_of_lt hx_lower) hxc hcz hd

private lemma uCandidate_tangent_x_Q3_A2_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y) :
    uCandidate p (-y) y ≤
      uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
  have hxc := uCandidate_tangent_x_Q3_A2_to_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hca := uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q3_A2_le_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (le_of_lt hx_lower) hxc hca hd

private lemma uCandidate_tangent_x_Q3_A2_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y < x) (hx_upper : x < y)
    (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q3_A2_to_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_left
  have hd := DxuCandidate_Q3_A2_le_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (le_of_lt hx_lower) hxc hcz hd

private lemma uCandidate_tangent_x_Q3_A1_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y < x) (hx_upper : x < a p * y)
    (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxa := uCandidate_tangent_x_Q3_A1_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have haz := uCandidate_tangent_x_antidiag_to_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_left
  have hd : DxuCandidate p x y ≤ DxuCandidate p (-y) y := by
    rw [DxuCandidate_Q3_A1_eq_antidiag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower hx_upper]
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_left) (le_of_lt hx_lower) hxa haz hd

private lemma uCandidate_tangent_x_diag_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p y y + DxuCandidate p y y * (z - y) := by
  have hyc := uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_diag_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    hyc hcz hd

private lemma uCandidate_tangent_x_diag_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (-y) y ≤
      uCandidate p y y + DxuCandidate p y y * ((-y) - y) := by
  have hyc := uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hca := uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_diag_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    hyc hca hd

private lemma uCandidate_tangent_x_diag_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p y y + DxuCandidate p y y * (z - y) := by
  have hyc := uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_left
  have hd := DxuCandidate_diag_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    hyc hcz hd

private lemma DxuCandidate_Q1_A2_le_Q3_A1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p) :
    DxuCandidate p x y ≤ DxuCandidate p (a p * y) y :=
  le_trans
    (DxuCandidate_Q1_A2_le_diag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower hx_upper)
    (DxuCandidate_diag_le_Q3_A1_boundary_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)

private lemma DxuCandidate_Q1_A1_le_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x) :
    DxuCandidate p x y ≤ DxuCandidate p y y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  have hQx : QuarterPlane x y :=
    ⟨by linarith, le_of_lt (lt_trans hy_lt_b hx_lower), by linarith⟩
  have hQb : QuarterPlane (y / a p) y :=
    ⟨(div_pos hy_pos ha_pos).le, le_of_lt hy_lt_b, by linarith⟩
  have hdx : DxuCandidate p x y = DxauxFunction1 p x y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQx]
  have hdb : DxuCandidate p (y / a p) y = DxauxFunction1 p (y / a p) y := by
    rw [DxuCandidate_eq_Q1_leTwo p hQb]
  have hxb : DxuCandidate p x y ≤ DxuCandidate p (y / a p) y := by
    have hle := DxauxFunction1_A1_le_boundary_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos (lt_trans hy_lt_b hx_lower) (by
        have hmul := mul_lt_mul_of_pos_left hx_lower ha_pos
        field_simp [ha_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    rwa [hdx, hdb]
  exact le_trans hxb
    (DxuCandidate_Q1_boundary_le_diag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)

private lemma DxuCandidate_Q1_A1_le_Q3_A1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x) :
    DxuCandidate p x y ≤ DxuCandidate p (a p * y) y :=
  le_trans
    (DxuCandidate_Q1_A1_le_diag_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
      hy_pos hx_lower)
    (DxuCandidate_diag_le_Q3_A1_boundary_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)

private lemma uCandidate_tangent_x_Q1_A2_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p)
    (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q1_A2_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q1_A2_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_trans (le_of_lt hlt) (le_of_lt hx_lower))
    hxc hcz hd

private lemma uCandidate_tangent_x_Q1_A2_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p) :
    uCandidate p (-y) y ≤
      uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
  have hxc := uCandidate_tangent_x_Q1_A2_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hca := uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q1_A2_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_trans (le_of_lt hlt) (le_of_lt hx_lower))
    hxc hca hd

private lemma uCandidate_tangent_x_Q1_A2_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y < x) (hx_upper : x < y / a p)
    (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q1_A2_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_left
  have hd := DxuCandidate_Q1_A2_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower hx_upper
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_trans (le_of_lt hlt) (le_of_lt hx_lower))
    hxc hcz hd

private lemma uCandidate_tangent_x_Q1_boundary_to_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (z - y / a p) := by
  have hbd := uCandidate_tangent_x_Q1_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hdz := uCandidate_tangent_x_diag_to_Q3_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q1_boundary_le_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_of_lt hlt)
    hbd hdz hd

private lemma uCandidate_tangent_x_Q1_boundary_to_Q3_A2_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (a p * y) y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (a p * y - y / a p) := by
  have hbd := uCandidate_tangent_x_Q1_boundary_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hdc := uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q1_boundary_le_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_of_lt hlt)
    hbd hdc hd

private lemma uCandidate_tangent_x_Q1_boundary_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (z - y / a p) := by
  have hbc := uCandidate_tangent_x_Q1_boundary_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd : DxuCandidate p (y / a p) y ≤ DxuCandidate p (a p * y) y :=
    le_trans
      (DxuCandidate_Q1_boundary_le_diag_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
      (DxuCandidate_diag_le_Q3_A1_boundary_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt1 : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      have hlt2 : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt1) (le_of_lt hlt2))
    hbc hcz hd

private lemma uCandidate_tangent_x_Q1_boundary_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * (z - y / a p) := by
  have hbc := uCandidate_tangent_x_Q1_boundary_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_left
  have hd : DxuCandidate p (y / a p) y ≤ DxuCandidate p (a p * y) y :=
    le_trans
      (DxuCandidate_Q1_boundary_le_diag_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
      (DxuCandidate_diag_le_Q3_A1_boundary_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt1 : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      have hlt2 : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt1) (le_of_lt hlt2))
    hbc hcz hd

private lemma uCandidate_tangent_x_Q1_boundary_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (-y) y ≤
      uCandidate p (y / a p) y +
        DxuCandidate p (y / a p) y * ((-y) - y / a p) := by
  have hbc := uCandidate_tangent_x_Q1_boundary_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hca := uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd : DxuCandidate p (y / a p) y ≤ DxuCandidate p (a p * y) y :=
    le_trans
      (DxuCandidate_Q1_boundary_le_diag_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
      (DxuCandidate_diag_le_Q3_A1_boundary_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt1 : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      have hlt2 : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt1) (le_of_lt hlt2))
    hbc hca hd

private lemma uCandidate_tangent_x_Q1_A1_to_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x)
    (hz_lower : a p * y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxd := uCandidate_tangent_x_Q1_A1_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  have hdz := uCandidate_tangent_x_diag_to_Q3_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q1_A1_le_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt) (le_of_lt hx_lower))
    hxd hdz hd

private lemma uCandidate_tangent_x_Q1_A1_to_Q3_A2_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x) :
    uCandidate p (a p * y) y ≤
      uCandidate p x y + DxuCandidate p x y * (a p * y - x) := by
  have hxd := uCandidate_tangent_x_Q1_A1_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  have hdc := uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q1_A1_le_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      exact le_of_lt hlt)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt) (le_of_lt hx_lower))
    hxd hdc hd

private lemma uCandidate_tangent_x_Q1_A1_to_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x)
    (hz_lower : -y < z) (hz_upper : z < a p * y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q1_A1_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_lower hz_upper
  have hd := DxuCandidate_Q1_A1_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (le_of_lt hz_upper) (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt1 : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      have hlt2 : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt1) (le_trans (le_of_lt hlt2) (le_of_lt hx_lower)))
    hxc hcz hd

private lemma uCandidate_tangent_x_Q1_A1_to_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxc := uCandidate_tangent_x_Q1_A1_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  have hcz := uCandidate_tangent_x_Q3_A2_boundary_to_Q2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
    hy_pos hz_left
  have hd := DxuCandidate_Q1_A1_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt1 : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      have hlt2 : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt1) (le_trans (le_of_lt hlt2) (le_of_lt hx_lower)))
    hxc hcz hd

private lemma uCandidate_tangent_x_Q1_A1_to_antidiag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p < x) :
    uCandidate p (-y) y ≤
      uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
  have hxc := uCandidate_tangent_x_Q1_A1_to_Q3_A2_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  have hca := uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  have hd := DxuCandidate_Q1_A1_le_Q3_A1_boundary_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
    hy_pos hx_lower
  exact tangent_glue_two_backward_leTwo_local
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith)
    (by
      have ha_pos : 0 < a p := by
        rw [a_eq_leTwo p hp1 hp2]
        exact div_pos (by linarith) (by linarith)
      have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
      have hlt1 : a p * y < y := by
        simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
      have hlt2 : y < y / a p := by
        rw [div_eq_mul_inv]
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans (le_of_lt hlt1) (le_trans (le_of_lt hlt2) (le_of_lt hx_lower)))
    hxc hca hd

private lemma uCandidate_tangent_x_backward_of_y_pos_left_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hzx : z < x) (hx_b : ¬ y / a p < x) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hxb_le : x ≤ y / a p := le_of_not_gt hx_b
  rcases hxb_le.lt_or_eq with hxb_lt | hxb_eq
  · by_cases hx_y : y < x
    · by_cases hz_y : y < z
      · exact uCandidate_tangent_x_on_Q1_A2_segment_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
          hy_pos hx_y hxb_lt hz_y (lt_trans hzx hxb_lt)
      · have hzy_le : z ≤ y := le_of_not_gt hz_y
        rcases hzy_le.lt_or_eq with hzy | hzy_eq
        · by_cases hz_c : a p * y < z
          · exact uCandidate_tangent_x_Q1_A2_to_Q3_A2_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
              hy_pos hx_y hxb_lt hz_c hzy
          · have hzc_le : z ≤ a p * y := le_of_not_gt hz_c
            rcases hzc_le.lt_or_eq with hzc | hzc_eq
            · by_cases hz_a : -y < z
              · exact uCandidate_tangent_x_Q1_A2_to_Q3_A1_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                  hy_pos hx_y hxb_lt hz_a hzc
              · have hza_le : z ≤ -y := le_of_not_gt hz_a
                rcases hza_le.lt_or_eq with hza | hza_eq
                · exact uCandidate_tangent_x_Q1_A2_to_Q2_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hx_y hxb_lt hza
                · subst z
                  exact uCandidate_tangent_x_Q1_A2_to_antidiag_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                    hy_pos hx_y hxb_lt
            · subst z
              exact uCandidate_tangent_x_Q1_A2_to_Q3_A2_boundary_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                hy_pos hx_y hxb_lt
        · subst z
          exact uCandidate_tangent_x_Q1_A2_to_diag_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
            hy_pos hx_y hxb_lt
    · have hxy_le : x ≤ y := le_of_not_gt hx_y
      rcases hxy_le.lt_or_eq with hxy | hxy_eq
      · by_cases hx_c : a p * y < x
        · by_cases hz_c : a p * y < z
          · exact uCandidate_tangent_x_on_Q3_A2_segment_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
              hy_pos hx_c hxy hz_c (lt_trans hzx hxy)
          · have hzc_le : z ≤ a p * y := le_of_not_gt hz_c
            rcases hzc_le.lt_or_eq with hzc | hzc_eq
            · by_cases hz_a : -y < z
              · exact uCandidate_tangent_x_Q3_A2_to_Q3_A1_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                  hy_pos hx_c hxy hz_a hzc
              · have hza_le : z ≤ -y := le_of_not_gt hz_a
                rcases hza_le.lt_or_eq with hza | hza_eq
                · exact uCandidate_tangent_x_Q3_A2_to_Q2_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hx_c hxy hza
                · subst z
                  exact uCandidate_tangent_x_Q3_A2_to_antidiag_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                    hy_pos hx_c hxy
            · subst z
              exact uCandidate_tangent_x_Q3_A2_to_boundary_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                hy_pos hx_c hxy
        · have hxc_le : x ≤ a p * y := le_of_not_gt hx_c
          rcases hxc_le.lt_or_eq with hxc | hxc_eq
          · by_cases hx_a : -y < x
            · by_cases hz_a : -y < z
              · exact uCandidate_tangent_x_on_Q3_A1_segment_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                  hy_pos hx_a hxc hz_a (lt_trans hzx hxc)
              · have hza_le : z ≤ -y := le_of_not_gt hz_a
                rcases hza_le.lt_or_eq with hza | hza_eq
                · exact uCandidate_tangent_x_Q3_A1_to_Q2_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hx_a hxc hza
                · subst z
                  exact uCandidate_tangent_x_Q3_A1_to_antidiag_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                    hy_pos hx_a hxc
            · have hxa_le : x ≤ -y := le_of_not_gt hx_a
              rcases hxa_le.lt_or_eq with hxa | hxa_eq
              · exact uCandidate_tangent_x_on_Q2_A1_segment_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                  hy_pos hxa (lt_trans hzx hxa)
              · subst x
                exact uCandidate_tangent_x_antidiag_to_Q2_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                  hy_pos (by simpa using hzx)
          · subst x
            by_cases hz_a : -y < z
            · exact uCandidate_tangent_x_Q3_A2_boundary_to_Q3_A1_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                hy_pos hz_a (by simpa using hzx)
            · have hza_le : z ≤ -y := le_of_not_gt hz_a
              rcases hza_le.lt_or_eq with hza | hza_eq
              · exact uCandidate_tangent_x_Q3_A2_boundary_to_Q2_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                  hy_pos hza
              · subst z
                exact uCandidate_tangent_x_Q3_A2_boundary_to_antidiag_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
      · subst x
        by_cases hz_c : a p * y < z
        · exact uCandidate_tangent_x_diag_to_Q3_A2_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
            hy_pos hz_c (by simpa using hzx)
        · have hzc_le : z ≤ a p * y := le_of_not_gt hz_c
          rcases hzc_le.lt_or_eq with hzc | hzc_eq
          · by_cases hz_a : -y < z
            · exact uCandidate_tangent_x_diag_to_Q3_A1_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                hy_pos hz_a hzc
            · have hza_le : z ≤ -y := le_of_not_gt hz_a
              rcases hza_le.lt_or_eq with hza | hza_eq
              · exact uCandidate_tangent_x_diag_to_Q2_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                  hy_pos hza
              · subst z
                exact uCandidate_tangent_x_diag_to_antidiag_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
          · subst z
            exact uCandidate_tangent_x_diag_to_Q3_A2_boundary_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
  · subst x
    by_cases hz_y : y < z
    · exact uCandidate_tangent_x_Q1_boundary_to_A2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
        hy_pos hz_y (by simpa using hzx)
    · have hzy_le : z ≤ y := le_of_not_gt hz_y
      rcases hzy_le.lt_or_eq with hzy | hzy_eq
      · by_cases hz_c : a p * y < z
        · exact uCandidate_tangent_x_Q1_boundary_to_Q3_A2_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
            hy_pos hz_c hzy
        · have hzc_le : z ≤ a p * y := le_of_not_gt hz_c
          rcases hzc_le.lt_or_eq with hzc | hzc_eq
          · by_cases hz_a : -y < z
            · exact uCandidate_tangent_x_Q1_boundary_to_Q3_A1_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                hy_pos hz_a hzc
            · have hza_le : z ≤ -y := le_of_not_gt hz_a
              rcases hza_le.lt_or_eq with hza | hza_eq
              · exact uCandidate_tangent_x_Q1_boundary_to_Q2_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                  hy_pos hza
              · subst z
                exact uCandidate_tangent_x_Q1_boundary_to_antidiag_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
          · subst z
            exact uCandidate_tangent_x_Q1_boundary_to_Q3_A2_boundary_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
      · subst z
        exact uCandidate_tangent_x_Q1_boundary_to_diag_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos


private lemma uCandidate_tangent_x_backward_of_y_pos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hzx : z < x) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_nonneg : 0 ≤ a p := ha_pos.le
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hneg_lt_c : -y < a p * y := by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hc_lt_y : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hy_lt_b : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  by_cases hx_b : y / a p < x
  · by_cases hz_b : y / a p < z
    · exact uCandidate_tangent_x_on_Q1_A1_segment_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
        hy_pos hx_b hz_b
    · have hzb_le : z ≤ y / a p := le_of_not_gt hz_b
      rcases hzb_le.lt_or_eq with hzb_lt | hzb_eq
      · by_cases hz_y : y < z
        · exact uCandidate_tangent_x_Q1_A1_to_A2_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
            hy_pos hx_b hz_y hzb_lt
        · have hzy_le : z ≤ y := le_of_not_gt hz_y
          rcases hzy_le.lt_or_eq with hzy | hzy_eq
          · by_cases hz_c : a p * y < z
            · exact uCandidate_tangent_x_Q1_A1_to_Q3_A2_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                hy_pos hx_b hz_c hzy
            · have hzc_le : z ≤ a p * y := le_of_not_gt hz_c
              rcases hzc_le.lt_or_eq with hzc | hzc_eq
              · by_cases hz_a : -y < z
                · exact uCandidate_tangent_x_Q1_A1_to_Q3_A1_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                    hy_pos hx_b hz_a hzc
                · have hza_le : z ≤ -y := le_of_not_gt hz_a
                  rcases hza_le.lt_or_eq with hza | hza_eq
                  · exact uCandidate_tangent_x_Q1_A1_to_Q2_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
                      hy_pos hx_b hza
                  · subst z
                    exact uCandidate_tangent_x_Q1_A1_to_antidiag_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                      hy_pos hx_b
              · subst z
                exact uCandidate_tangent_x_Q1_A1_to_Q3_A2_boundary_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
                  hy_pos hx_b
          · subst z
            exact uCandidate_tangent_x_Q1_A1_to_diag_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
              hy_pos hx_b
      · subst z
        exact uCandidate_tangent_x_Q1_A1_to_boundary_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y)
          hy_pos hx_b
  · exact uCandidate_tangent_x_backward_of_y_pos_left_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
      hy_pos hzx hx_b
private lemma uCandidate_tangent_x_backward_of_y_pos_le_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hzx : z ≤ x) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  rcases hzx.lt_or_eq with hzx_lt | rfl
  · exact uCandidate_tangent_x_backward_of_y_pos_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
      hy_pos hzx_lt
  · simp

private lemma uCandidate_tangent_x_increment_of_y_pos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y h : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (x + h) y ≤
      uCandidate p x y + DxuCandidate p x y * h := by
  rcases le_total 0 h with hh | hh
  · have hxz : x ≤ x + h := by linarith
    have hmain := uCandidate_tangent_x_forward_of_y_pos_le_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := x + h) (y := y)
      hy_pos hxz
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmain
  · have hxz : x + h ≤ x := by linarith
    have hmain := uCandidate_tangent_x_backward_of_y_pos_le_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := x + h) (y := y)
      hy_pos hxz
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmain

private lemma uCandidate_tangent_x_increment_of_y_neg_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y h : ℝ}
    (hy_neg : y < 0) :
    uCandidate p (x + h) y ≤
      uCandidate p x y + DxuCandidate p x y * h := by
  exact uCandidate_tangent_x_increment_of_y_neg_leTwo_of_pos
    p (fun {x y h} hy_pos =>
      uCandidate_tangent_x_increment_of_y_pos_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y) (h := h) hy_pos)
    hy_neg

private lemma rpow_tangent_nonneg_leTwo
    (p : ℝ) (hp1 : 1 < p) {x z : ℝ}
    (hx : 0 < x) (hz : 0 ≤ z) :
    x ^ p + (p * x ^ (p - 1)) * (z - x) ≤ z ^ p := by
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => t ^ p) :=
    convexOn_rpow (by linarith : 1 ≤ p)
  have hderiv :
      HasDerivAt (fun t : ℝ => t ^ p) (p * x ^ (p - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))
  rcases lt_trichotomy x z with hxz | hxz | hzx
  · have hslope :=
      hconv.le_slope_of_hasDerivAt
        (x := x) (y := z) (f' := p * x ^ (p - 1))
        hx.le hz hxz hderiv
    have hslope' :
        p * x ^ (p - 1) ≤ (z ^ p - x ^ p) / (z - x) := by
      simpa [slope_def_field] using hslope
    have hden_pos : 0 < z - x := by linarith
    have hmul := mul_le_mul_of_nonneg_right hslope' hden_pos.le
    field_simp [hden_pos.ne'] at hmul
    linarith
  · subst z
    simp
  · have hslope :=
      hconv.slope_le_of_hasDerivAt
        (x := z) (y := x) (f' := p * x ^ (p - 1))
        hz hx.le hzx hderiv
    have hslope' :
        (x ^ p - z ^ p) / (x - z) ≤ p * x ^ (p - 1) := by
      simpa [slope_def_field] using hslope
    have hden_pos : 0 < x - z := by linarith
    have hmul := mul_le_mul_of_nonneg_right hslope' hden_pos.le
    field_simp [hden_pos.ne'] at hmul
    linarith

private lemma abs_rpow_tangent_leTwo
    (p : ℝ) (hp1 : 1 < p) (x z : ℝ) :
    |x| ^ p +
        (if 0 < x then p * x ^ (p - 1)
         else if x < 0 then -p * (-x) ^ (p - 1)
         else 0) * (z - x) ≤
      |z| ^ p := by
  by_cases hxpos : 0 < x
  · by_cases hzneg : z < 0
    · have hxpow_nonneg : 0 ≤ x ^ p := Real.rpow_nonneg hxpos.le p
      have hxpow1_nonneg : 0 ≤ x ^ (p - 1) := Real.rpow_nonneg hxpos.le (p - 1)
      have hlin :
          x ^ p + (p * x ^ (p - 1)) * (z - x) ≤ 0 := by
        have hz_le : z ≤ 0 := le_of_lt hzneg
        have hp_nonneg : 0 ≤ p := by linarith
        have hterm_nonpos : p * x ^ (p - 1) * z ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg hp_nonneg hxpow1_nonneg) hz_le
        have hshift : x ^ (p - 1) * x = x ^ p := by
          calc
            x ^ (p - 1) * x = x ^ (p - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = x ^ ((p - 1) + 1) := by rw [Real.rpow_add hxpos]
            _ = x ^ p := by ring_nf
        calc
          x ^ p + (p * x ^ (p - 1)) * (z - x)
              = (1 - p) * x ^ p + p * x ^ (p - 1) * z := by
                  rw [← hshift]
                  ring
          _ ≤ 0 := by
            have hfirst : (1 - p) * x ^ p ≤ 0 := by
              exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hxpow_nonneg
            linarith
      have hzpow_nonneg : 0 ≤ |z| ^ p := Real.rpow_nonneg (abs_nonneg z) p
      simpa [hxpos, abs_of_pos hxpos] using hlin.trans hzpow_nonneg
    · have hz_nonneg : 0 ≤ z := le_of_not_gt hzneg
      have ht := rpow_tangent_nonneg_leTwo p hp1 hxpos hz_nonneg
      simpa [hxpos, abs_of_pos hxpos, abs_of_nonneg hz_nonneg] using ht
  · by_cases hxneg : x < 0
    · by_cases hzpos : 0 < z
      · have hxabs_pos : 0 < -x := by linarith
        have hxpow_nonneg : 0 ≤ (-x) ^ p := Real.rpow_nonneg (le_of_lt hxabs_pos) p
        have hxpow1_nonneg : 0 ≤ (-x) ^ (p - 1) :=
          Real.rpow_nonneg (le_of_lt hxabs_pos) (p - 1)
        have hlin :
            (-x) ^ p + (-p * (-x) ^ (p - 1)) * (z - x) ≤ 0 := by
          have hp_nonneg : 0 ≤ p := by linarith
          have hterm_nonpos : -(p * (-x) ^ (p - 1) * z) ≤ 0 := by
            have hz_nonneg : 0 ≤ z := le_of_lt hzpos
            have hnonneg : 0 ≤ p * (-x) ^ (p - 1) * z :=
              mul_nonneg (mul_nonneg hp_nonneg hxpow1_nonneg) hz_nonneg
            linarith
          have hshift : (-x) ^ (p - 1) * (-x) = (-x) ^ p := by
            calc
              (-x) ^ (p - 1) * (-x) = (-x) ^ (p - 1) * (-x) ^ (1 : ℝ) := by
                rw [Real.rpow_one]
              _ = (-x) ^ ((p - 1) + 1) := by rw [Real.rpow_add hxabs_pos]
              _ = (-x) ^ p := by ring_nf
          calc
            (-x) ^ p + (-p * (-x) ^ (p - 1)) * (z - x)
                = (1 - p) * (-x) ^ p - p * (-x) ^ (p - 1) * z := by
                    rw [← hshift]
                    ring
            _ ≤ 0 := by
              have hfirst : (1 - p) * (-x) ^ p ≤ 0 := by
                exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hxpow_nonneg
              linarith
        have hzpow_nonneg : 0 ≤ |z| ^ p := Real.rpow_nonneg (abs_nonneg z) p
        simpa [hxpos, hxneg, abs_of_neg hxneg] using hlin.trans hzpow_nonneg
      · have hz_nonpos : z ≤ 0 := le_of_not_gt hzpos
        have ht := rpow_tangent_nonneg_leTwo p hp1
          (x := -x) (z := -z) (by linarith) (by linarith)
        have hrewrite :
            (-x) ^ p + (p * (-x) ^ (p - 1)) * ((-z) - (-x))
              = (-x) ^ p + (-p * (-x) ^ (p - 1)) * (z - x) := by ring
        rw [hrewrite] at ht
        simpa [hxpos, hxneg, abs_of_neg hxneg, abs_of_nonpos hz_nonpos] using ht
    · have hx0 : x = 0 := le_antisymm (le_of_not_gt hxpos) (le_of_not_gt hxneg)
      subst x
      simp only [abs_zero, lt_irrefl, if_false, zero_mul, sub_zero, add_zero]
      rw [Real.zero_rpow (by linarith : p ≠ 0)]
      exact Real.rpow_nonneg (abs_nonneg z) p

private lemma axisCoeff_nonpos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    alpha p * (1 - pStar p / 2) ≤ 0 := by
  have ha : 0 ≤ alpha p := alpha_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hstar : 1 ≤ pStar p / 2 := one_le_half_pStar_of_one_lt_of_lt_two p hp1 hp2
  exact mul_nonpos_of_nonneg_of_nonpos ha (by linarith)

private lemma uCandidate_axis_eq_abs_rpow_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x : ℝ) :
    uCandidate p x 0 = alpha p * (1 - pStar p / 2) * |x| ^ p := by
  let C : ℝ := alpha p * (1 - pStar p / 2)
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · have hQ2 : QuarterPlane2 x 0 := ⟨le_of_lt hxneg, by linarith, by linarith⟩
    have hxpos' : 0 < -x := by linarith
    have hcl : closureA1 p (-x) 0 := by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      exact ⟨le_of_lt hxpos', by linarith, mul_nonneg ha_nonneg (le_of_lt hxpos')⟩
    have hshift : (-x) ^ (p - 1) * (-x) = (-x) ^ p := by
      calc
        (-x) ^ (p - 1) * (-x) = (-x) ^ (p - 1) * (-x) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = (-x) ^ ((p - 1) + 1) := by rw [Real.rpow_add hxpos']
        _ = (-x) ^ p := by ring_nf
    calc
      uCandidate p x 0 = auxFunction1 p (-x) 0 := by
        simpa using uCandidate_eq_Q2_leTwo p hQ2
      _ = uA1 p (-x) 0 := by simp [auxFunction1, hcl]
      _ = C * |x| ^ p := by
        simp only [uA1, gt_iff_lt, hxpos', ↓reduceIte, Real.rpow_eq_pow, sub_zero, mul_neg,
          abs_of_neg hxneg, C]
        rw [← hshift]
        ring
  · subst x
    have hQ : QuarterPlane 0 0 := by norm_num [QuarterPlane]
    calc
      uCandidate p 0 0 = auxFunction1 p 0 0 := uCandidate_eq_Q1_leTwo p hQ
      _ = 0 := by simp [auxFunction1, closureA1, uA1]
      _ = C * |(0 : ℝ)| ^ p := by
        simp [C, Real.zero_rpow (by linarith : p ≠ 0)]
  · have hQ : QuarterPlane x 0 := ⟨le_of_lt hxpos, by linarith, by linarith⟩
    have hcl : closureA1 p x 0 := by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      exact ⟨le_of_lt hxpos, by linarith, mul_nonneg ha_nonneg (le_of_lt hxpos)⟩
    have hshift : x ^ (p - 1) * x = x ^ p := by
      calc
        x ^ (p - 1) * x = x ^ (p - 1) * x ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = x ^ ((p - 1) + 1) := by rw [Real.rpow_add hxpos]
        _ = x ^ p := by ring_nf
    calc
      uCandidate p x 0 = auxFunction1 p x 0 := uCandidate_eq_Q1_leTwo p hQ
      _ = uA1 p x 0 := by simp [auxFunction1, hcl]
      _ = C * |x| ^ p := by
        simp only [uA1, gt_iff_lt, hxpos, ↓reduceIte, Real.rpow_eq_pow, sub_zero, abs_of_pos hxpos,
          C]
        rw [← hshift]
        ring

private lemma DxuCandidate_axis_eq_abs_deriv_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x : ℝ) :
    DxuCandidate p x 0 =
      alpha p * (1 - pStar p / 2) *
        (if 0 < x then p * x ^ (p - 1)
         else if x < 0 then -p * (-x) ^ (p - 1)
         else 0) := by
  let C : ℝ := alpha p * (1 - pStar p / 2)
  have hpStar : pStar p = q p :=
    pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
  have hp_ne_one : p ≠ 1 := by linarith
  have hpden_ne : p - 1 ≠ 0 := by linarith
  rcases lt_trichotomy x 0 with hxneg | hx0 | hxpos
  · have hQ2 : QuarterPlane2 x 0 := ⟨le_of_lt hxneg, by linarith, by linarith⟩
    have hxpos' : 0 < -x := by linarith
    have hcl : closureA1 p (-x) 0 := by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      exact ⟨le_of_lt hxpos', by linarith, mul_nonneg ha_nonneg (le_of_lt hxpos')⟩
    have hshift : (-x) ^ (p - 1) = (-x) ^ (p - 2) * (-x) := by
      calc
        (-x) ^ (p - 1) = (-x) ^ ((p - 2) + (1 : ℝ)) := by ring_nf
        _ = (-x) ^ (p - 2) * (-x) ^ (1 : ℝ) := by rw [Real.rpow_add hxpos']
        _ = (-x) ^ (p - 2) * (-x) := by rw [Real.rpow_one]
    calc
      DxuCandidate p x 0 = -DxauxFunction1 p (-x) 0 := by
        simpa using DxuCandidate_eq_Q2_leTwo p hQ2
      _ = C * (-p * (-x) ^ (p - 1)) := by
        simp only [DxauxFunction1, hcl, ↓reduceIte, DxuA1, gt_iff_lt, hxpos', Real.rpow_eq_pow,
          mul_neg, add_zero, neg_neg, hpStar, q, hp_ne_one, neg_mul, C]
        rw [hshift]
        field_simp [hpden_ne]
        ring
      _ = C *
          (if 0 < x then p * x ^ (p - 1)
           else if x < 0 then -p * (-x) ^ (p - 1)
           else 0) := by
        simp [hxneg, not_lt_of_gt hxneg]
  · subst x
    have hQ : QuarterPlane 0 0 := by norm_num [QuarterPlane]
    calc
      DxuCandidate p 0 0 = DxauxFunction1 p 0 0 := DxuCandidate_eq_Q1_leTwo p hQ
      _ = 0 := by simp [DxauxFunction1, closureA1, DxuA1]
      _ = C *
          (if 0 < (0 : ℝ) then p * (0 : ℝ) ^ (p - 1)
           else if (0 : ℝ) < 0 then -p * (-(0 : ℝ)) ^ (p - 1)
           else 0) := by simp [C]
  · have hQ : QuarterPlane x 0 := ⟨le_of_lt hxpos, by linarith, by linarith⟩
    have hcl : closureA1 p x 0 := by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
      exact ⟨le_of_lt hxpos, by linarith, mul_nonneg ha_nonneg (le_of_lt hxpos)⟩
    have hshift : x ^ (p - 1) = x ^ (p - 2) * x := by
      calc
        x ^ (p - 1) = x ^ ((p - 2) + (1 : ℝ)) := by ring_nf
        _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hxpos]
        _ = x ^ (p - 2) * x := by rw [Real.rpow_one]
    calc
      DxuCandidate p x 0 = DxauxFunction1 p x 0 := DxuCandidate_eq_Q1_leTwo p hQ
      _ = C * (p * x ^ (p - 1)) := by
        simp only [DxauxFunction1, hcl, ↓reduceIte, DxuA1, gt_iff_lt, hxpos, Real.rpow_eq_pow,
          add_zero, hpStar, q, hp_ne_one, C]
        rw [hshift]
        field_simp [hpden_ne]
        ring
      _ = C *
          (if 0 < x then p * x ^ (p - 1)
           else if x < 0 then -p * (-x) ^ (p - 1)
           else 0) := by
        simp [hxpos]

private lemma uCandidate_tangent_x_increment_of_y_zero_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x h : ℝ} :
    uCandidate p (x + h) 0 ≤
      uCandidate p x 0 + DxuCandidate p x 0 * h := by
  let C : ℝ := alpha p * (1 - pStar p / 2)
  let d : ℝ :=
    if 0 < x then p * x ^ (p - 1)
    else if x < 0 then -p * (-x) ^ (p - 1)
    else 0
  have hC : C ≤ 0 := by
    simpa [C] using axisCoeff_nonpos_leTwo p hp1 hp2
  have htangent :
      |x| ^ p + d * ((x + h) - x) ≤ |x + h| ^ p := by
    simpa [d] using abs_rpow_tangent_leTwo p hp1 x (x + h)
  have hmul :
      C * |x + h| ^ p ≤ C * (|x| ^ p + d * ((x + h) - x)) := by
    exact mul_le_mul_of_nonpos_left htangent hC
  calc
    uCandidate p (x + h) 0 = C * |x + h| ^ p := by
      simpa [C] using uCandidate_axis_eq_abs_rpow_leTwo p hp1 hp2 (x + h)
    _ ≤ C * (|x| ^ p + d * ((x + h) - x)) := hmul
    _ = C * |x| ^ p + (C * d) * h := by ring
    _ = uCandidate p x 0 + DxuCandidate p x 0 * h := by
      rw [uCandidate_axis_eq_abs_rpow_leTwo p hp1 hp2 x,
        DxuCandidate_axis_eq_abs_deriv_leTwo p hp1 hp2 x]

private lemma uCandidate_axis_tangent_horizontal_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y h k : ℝ}
    (hk0 : k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  subst k
  rcases lt_trichotomy y 0 with hy_neg | hy0 | hy_pos
  · have hx := uCandidate_tangent_x_increment_of_y_neg_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y) (h := h) hy_neg
    simpa using hx
  · subst y
    have hx := uCandidate_tangent_x_increment_of_y_zero_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (h := h)
    simpa using hx
  · have hx := uCandidate_tangent_x_increment_of_y_pos_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (y := y) (h := h) hy_pos
    simpa using hx

private lemma uCandidate_axis_tangent_vertical_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y h k : ℝ}
    (hh0 : h = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  subst h
  have hhor := uCandidate_axis_tangent_horizontal_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := y) (y := x) (h := k) (k := 0) rfl
  have hswap_target :
      uCandidate p (x + 0) (y + k) =
        uCandidate p (y + k) (x + 0) := by
    exact uCandidate_swap_leTwo p (x + 0) (y + k)
  have hswap_base : uCandidate p y x = uCandidate p x y :=
    (uCandidate_swap_leTwo p x y).symm
  have hderiv : DxuCandidate p y x = DyuCandidate p x y :=
    (DyuCandidate_eq_DxuCandidate_swap_leTwo p hp1 hp2 x y).symm
  calc
    uCandidate p (x + 0) (y + k) =
        uCandidate p (y + k) (x + 0) := hswap_target
    _ ≤ uCandidate p y x + DxuCandidate p y x * k + DyuCandidate p y x * 0 := hhor
    _ = uCandidate p x y + DxuCandidate p x y * 0 + DyuCandidate p x y * k := by
      rw [hswap_base, hderiv]
      ring

private lemma uCandidate_axis_tangent_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y h k : ℝ}
    (hk : h * k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  rcases mul_eq_zero.mp hk with hh0 | hk0
  · exact uCandidate_axis_tangent_vertical_leTwo p hp1 hp2 hh0
  · exact uCandidate_axis_tangent_horizontal_leTwo p hp1 hp2 hk0

private lemma uCandidate_le_zero_of_mul_neg_LeTwo
    (p x y : ℝ) (hp : 1 < p ∧ p < 2) (hxy : x * y = 0) (hnzero : (x, y) ≠ (0, 0)) :
    uCandidate p x y < 0 := by
  have huA1_axis : ∀ t : ℝ, 0 ≤ t → t ≠ 0 → uA1 p t 0 < 0 := by
    intro t ht htne
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htne)
    have hp_pos : 0 < p := by linarith
    have halpha_pos : 0 < alpha p := by
      rw [alpha_eq_leTwo p hp.1 hp.2]
      exact mul_pos hp_pos (Real.rpow_pos_of_pos hp_pos _)
    have hpow_pos : 0 < t ^ (p - 1) :=
      Real.rpow_pos_of_pos htpos _
    have hprod_pos : 0 < alpha p * t ^ (p - 1) :=
      mul_pos halpha_pos hpow_pos
    have hpStar_half_gt_one : 1 < pStar p / 2 := by
      have hpStar : pStar p = q p :=
        pStar_eq_q_of_one_lt_of_lt_two p hp.1 hp.2
      have hp_ne_one : p ≠ 1 := by linarith
      have hpden_pos : 0 < p - 1 := by linarith
      rw [hpStar]
      simp only [q, hp_ne_one, ↓reduceIte, gt_iff_lt]
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      rw [lt_div_iff₀ hpden_pos]
      linarith
    have hmain : t < pStar p * t / 2 := by
      have hmul := mul_lt_mul_of_pos_right hpStar_half_gt_one htpos
      nlinarith
    have hbracket : t - pStar p * t / 2 < 0 := by
      linarith
    simp only [uA1, gt_iff_lt, htpos, ↓reduceIte, Real.rpow_eq_pow, sub_zero]
    exact mul_neg_of_pos_of_neg hprod_pos hbracket
  have haux_axis : ∀ t : ℝ, 0 ≤ t → t ≠ 0 → auxFunction1 p t 0 < 0 := by
    intro t ht htne
    have h1 : closureA1 p t 0 := by
      refine ⟨ht, by linarith, ?_⟩
      exact mul_nonneg (a_nonneg_of_one_lt_of_lt_two p hp.1 hp.2) ht
    rw [auxFunction1]
    simp only [h1, ↓reduceIte, gt_iff_lt]
    exact huA1_axis t ht htne
  rcases mem_some_QuarterPlane_leTwo x y with hQ1 | hrest
  · rw [uCandidate_eq_Q1_leTwo p hQ1]
    have hy0 : y = 0 := by
      rcases mul_eq_zero.mp hxy with hx0 | hy0
      · have hy_le : y ≤ 0 := by simpa [hx0] using hQ1.2.1
        have hy_ge : 0 ≤ y := by simpa [hx0] using hQ1.2.2
        exact le_antisymm hy_le hy_ge
      · exact hy0
    subst y
    have hxne : x ≠ 0 := by
      intro hx0
      apply hnzero
      ext <;> simp [hx0]
    exact haux_axis x hQ1.1 hxne
  rcases hrest with hQ2 | hrest
  · rw [uCandidate_eq_Q2_leTwo p hQ2]
    have hy0 : y = 0 := by
      rcases mul_eq_zero.mp hxy with hx0 | hy0
      · have hy_le : y ≤ 0 := by simpa [hx0] using hQ2.2.1
        have hy_ge : 0 ≤ y := by simpa [hx0] using hQ2.2.2
        exact le_antisymm hy_le hy_ge
      · exact hy0
    subst y
    have ht : 0 ≤ -x := by linarith [hQ2.1]
    have htne : -x ≠ 0 := by
      intro hx0
      apply hnzero
      ext <;> linarith
    simpa using haux_axis (-x) ht htne
  rcases hrest with hQ3 | hQ4
  · rw [uCandidate_eq_Q3_leTwo p hQ3]
    have hx0 : x = 0 := by
      rcases mul_eq_zero.mp hxy with hx0 | hy0
      · exact hx0
      · have hx_ge : 0 ≤ x := by simpa [hy0] using hQ3.2.1
        have hx_le : x ≤ 0 := by simpa [hy0] using hQ3.2.2
        exact le_antisymm hx_le hx_ge
    subst x
    have hyne : y ≠ 0 := by
      intro hy0
      apply hnzero
      ext <;> simp [hy0]
    exact haux_axis y hQ3.1 hyne
  · rw [uCandidate_eq_Q4_leTwo p hQ4]
    have hx0 : x = 0 := by
      rcases mul_eq_zero.mp hxy with hx0 | hy0
      · exact hx0
      · have hx_ge : 0 ≤ x := by simpa [hy0] using hQ4.2.1
        have hx_le : x ≤ 0 := by simpa [hy0] using hQ4.2.2
        exact le_antisymm hx_le hx_ge
    subst x
    have ht : 0 ≤ -y := by linarith [hQ4.1]
    have htne : -y ≠ 0 := by
      intro hy0
      apply hnzero
      ext <;> linarith
    simpa using haux_axis (-y) ht htne

private lemma hasDerivAt_DyuA1_x_of_pos_leTwo
    (p : ℝ) (_hp1 : 1 < p) (_hp2 : p < 2) (x y : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => DyuA1 p t y)
      (alpha p * ((p - 1) * x ^ (p - 2)) * (pStar p / 2)) x := by
  have hEq :
      (fun t => DyuA1 p t y) =ᶠ[nhds x]
        fun t => alpha p * t ^ (p - 1) * (pStar p / 2) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have htpos : 0 < t := by simpa using ht
    simp [DyuA1, htpos]
  have hxne : x ≠ 0 := by linarith
  have hxne_pow : x ≠ 0 ∨ 1 ≤ p - 1 := Or.inl hxne
  have hpow :
      HasDerivAt (fun t : ℝ => t ^ (p - 1)) ((p - 1) * x ^ (p - 2)) x := by
    have h := (Real.hasDerivAt_rpow_const hxne_pow :
      HasDerivAt (fun t : ℝ => t ^ (p - 1))
        ((p - 1) * x ^ ((p - 1) - 1)) x)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      show p + (-1 + -1) = p + -2 by ring] using h
  have hderiv :
      HasDerivAt (fun t => alpha p * t ^ (p - 1) * (pStar p / 2))
        (alpha p * ((p - 1) * x ^ (p - 2)) * (pStar p / 2)) x := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      ((hpow.const_mul (alpha p)).mul_const (pStar p / 2))
  exact hderiv.congr_of_eventuallyEq hEq

private lemma deriv_DyuA1_x_nonneg_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) (hx : 0 < x) :
    0 ≤ deriv (fun t => DyuA1 p t y) x := by
  have hderiv := hasDerivAt_DyuA1_x_of_pos_leTwo p hp1 hp2 x y hx
  rw [hderiv.deriv]
  have ha : 0 ≤ alpha p := alpha_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hp_sub : 0 ≤ p - 1 := by linarith
  have hpow : 0 ≤ x ^ (p - 2) := Real.rpow_nonneg hx.le _
  have hpStar_nonneg : 0 ≤ pStar p / 2 := by
    have hpStar : pStar p = q p := pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
    have hp_ne_one : p ≠ 1 := by linarith
    have hpden_pos : 0 < p - 1 := by linarith
    rw [hpStar]
    simp only [q, hp_ne_one, ↓reduceIte, ge_iff_le]
    exact div_nonneg (div_nonneg (by linarith) hpden_pos.le) (by norm_num)
  positivity

private lemma hasDerivAt_DyvLeTwo_x_of_pos_leTwo
    (p x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    HasDerivAt (fun t => DyvLeTwo p t y)
      ((p * (p - 1) / 4) *
        (((x + y) / 2) ^ (p - 2) +
          coeffLeTwo p * ((x - y) / 2) ^ (p - 2))) x := by
  have hx : 0 < x := by linarith
  have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq :
      (fun t => DyvLeTwo p t y) =ᶠ[nhds x]
        fun t =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) +
            coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2) := by
    filter_upwards [hsum_nhds, hdiff_nhds] with t htsum htdiff
    have htpos : 0 < t := by linarith
    simp [DyvLeTwo, htpos, abs_of_pos htsum, abs_of_pos htdiff]
  have hbase_sum :
      HasDerivAt (fun t : ℝ => (t + y) / 2) (1 / 2) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).add_const y).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun t : ℝ => (t - y) / 2) (1 / 2) x := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).sub (hasDerivAt_const x y)).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun t : ℝ => ((t + y) / 2) ^ (p - 1))
        ((p - 1) * ((x + y) / 2) ^ (p - 2) * (1 / 2)) x := by
    have hrpow :
        HasDerivAt (fun s : ℝ => s ^ (p - 1))
          ((p - 1) * ((x + y) / 2) ^ (p - 2)) ((x + y) / 2) := by
      have hne : (x + y) / 2 ≠ 0 := ne_of_gt hsum
      have hcond : (x + y) / 2 ≠ 0 ∨ 1 ≤ p - 1 := Or.inl hne
      have h := (Real.hasDerivAt_rpow_const hcond :
        HasDerivAt (fun s : ℝ => s ^ (p - 1))
          ((p - 1) * ((x + y) / 2) ^ ((p - 1) - 1)) ((x + y) / 2))
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        show p + (-1 + -1) = p + -2 by ring] using h
    exact hrpow.comp x hbase_sum
  have hpow_diff :
      HasDerivAt (fun t : ℝ => ((t - y) / 2) ^ (p - 1))
        ((p - 1) * ((x - y) / 2) ^ (p - 2) * (1 / 2)) x := by
    have hrpow :
        HasDerivAt (fun s : ℝ => s ^ (p - 1))
          ((p - 1) * ((x - y) / 2) ^ (p - 2)) ((x - y) / 2) := by
      have hne : (x - y) / 2 ≠ 0 := ne_of_gt hdiff
      have hcond : (x - y) / 2 ≠ 0 ∨ 1 ≤ p - 1 := Or.inl hne
      have h := (Real.hasDerivAt_rpow_const hcond :
        HasDerivAt (fun s : ℝ => s ^ (p - 1))
          ((p - 1) * ((x - y) / 2) ^ ((p - 1) - 1)) ((x - y) / 2))
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        show p + (-1 + -1) = p + -2 by ring] using h
    exact hrpow.comp x hbase_diff
  have hderiv :
      HasDerivAt
        (fun t : ℝ =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) +
            coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2))
        ((p * (p - 1) / 4) *
          (((x + y) / 2) ^ (p - 2) +
            coeffLeTwo p * ((x - y) / 2) ^ (p - 2))) x := by
    have htmp :=
      (hpow_sum.mul_const (p / 2)).add
        ((hpow_diff.const_mul (coeffLeTwo p)).mul_const (p / 2))
    refine htmp.congr_deriv ?_
    ring
  exact hderiv.congr_of_eventuallyEq hEq

private lemma deriv_DyvLeTwo_x_nonneg_leTwo
    (p : ℝ) (hp1 : 1 < p) (x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    0 ≤ deriv (fun t => DyvLeTwo p t y) x := by
  have hderiv := hasDerivAt_DyvLeTwo_x_of_pos_leTwo p x y hsum hdiff
  rw [hderiv.deriv]
  have hpcoef : 0 ≤ p * (p - 1) / 4 := by
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hsum_pow : 0 ≤ ((x + y) / 2) ^ (p - 2) :=
    Real.rpow_nonneg hsum.le _
  have hdiff_pow : 0 ≤ ((x - y) / 2) ^ (p - 2) :=
    Real.rpow_nonneg hdiff.le _
  have hcoeff : 0 ≤ coeffLeTwo p := by
    exact Real.rpow_nonneg (inv_nonneg.mpr (by linarith)) _
  exact mul_nonneg hpcoef (add_nonneg hsum_pow (mul_nonneg hcoeff hdiff_pow))

private lemma DyvLeTwo_mono_x_on_Icc_of_pos_leTwo
    (p : ℝ) (hp1 : 1 < p) {lo hi y : ℝ}
    (hlo_sum : 0 < (lo + y) / 2) (hlo_diff : 0 < (lo - y) / 2) :
    MonotoneOn (fun t : ℝ => DyvLeTwo p t y) (Set.Icc lo hi) := by
  have hlo_pos : 0 < lo := by linarith
  have hcont : ContinuousOn (fun t : ℝ => DyvLeTwo p t y) (Set.Icc lo hi) := by
    let g : ℝ → ℝ := fun t =>
      ((t + y) / 2) ^ (p - 1) * (p / 2) +
        coeffLeTwo p * ((t - y) / 2) ^ (p - 1) * (p / 2)
    have hg : ContinuousOn g (Set.Icc lo hi) := by
      dsimp [g]
      apply ContinuousOn.add
      · exact (((continuousOn_id.add continuousOn_const).div_const 2).rpow_const
          (fun t ht => Or.inl (ne_of_gt (by
            change 0 < (t + y) / 2
            linarith [hlo_sum, ht.1])))).mul continuousOn_const
      · exact (continuousOn_const.mul
          (((continuousOn_id.sub continuousOn_const).div_const 2).rpow_const
            (fun t ht => Or.inl (ne_of_gt (by
              change 0 < (t - y) / 2
              linarith [hlo_diff, ht.1]))))).mul continuousOn_const
    refine ContinuousOn.congr hg ?_
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hlo_pos ht.1
    have hsum : 0 < (t + y) / 2 := by linarith [hlo_sum, ht.1]
    have hdiff : 0 < (t - y) / 2 := by linarith [hlo_diff, ht.1]
    simp [g, DyvLeTwo, htpos, abs_of_pos hsum, abs_of_pos hdiff]
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (D := Set.Icc lo hi)
    (f := fun t : ℝ => DyvLeTwo p t y)
    (f' := fun t : ℝ =>
      (p * (p - 1) / 4) *
        (((t + y) / 2) ^ (p - 2) +
          coeffLeTwo p * ((t - y) / 2) ^ (p - 2)))
    (convex_Icc lo hi) hcont ?_ ?_
  · intro t ht
    have htI : t ∈ Set.Ioo lo hi := by
      simpa [interior_Icc] using ht
    have hsum : 0 < (t + y) / 2 := by linarith [hlo_sum, htI.1]
    have hdiff : 0 < (t - y) / 2 := by linarith [hlo_diff, htI.1]
    exact (hasDerivAt_DyvLeTwo_x_of_pos_leTwo p t y hsum hdiff).hasDerivWithinAt
  · intro t ht
    have htI : t ∈ Set.Ioo lo hi := by
      simpa [interior_Icc] using ht
    have hsum : 0 < (t + y) / 2 := by linarith [hlo_sum, htI.1]
    have hdiff : 0 < (t - y) / 2 := by linarith [hlo_diff, htI.1]
    have hpcoef : 0 ≤ p * (p - 1) / 4 := by
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
    have hsum_pow : 0 ≤ ((t + y) / 2) ^ (p - 2) :=
      Real.rpow_nonneg hsum.le _
    have hdiff_pow : 0 ≤ ((t - y) / 2) ^ (p - 2) :=
      Real.rpow_nonneg hdiff.le _
    have hcoeff : 0 ≤ coeffLeTwo p := by
      exact Real.rpow_nonneg (inv_nonneg.mpr (by linarith)) _
    exact mul_nonneg hpcoef (add_nonneg hsum_pow (mul_nonneg hcoeff hdiff_pow))

private lemma DyuA1_mono_x_on_Icc_pos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {lo hi y : ℝ}
    (hlo : 0 < lo) :
    MonotoneOn (fun t : ℝ => DyuA1 p t y) (Set.Icc lo hi) := by
  have hcont : ContinuousOn (fun t : ℝ => DyuA1 p t y) (Set.Icc lo hi) := by
    let g : ℝ → ℝ := fun t => alpha p * t ^ (p - 1) * (pStar p / 2)
    have hg : ContinuousOn g (Set.Icc lo hi) := by
      dsimp [g]
      exact ((continuousOn_const.mul
        (continuousOn_id.rpow_const
          (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hlo ht.1))))).mul
        continuousOn_const)
    refine ContinuousOn.congr hg ?_
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hlo ht.1
    simp [g, DyuA1, htpos]
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (D := Set.Icc lo hi)
    (f := fun t : ℝ => DyuA1 p t y)
    (f' := fun t : ℝ => alpha p * ((p - 1) * t ^ (p - 2)) * (pStar p / 2))
    (convex_Icc lo hi) hcont ?_ ?_
  · intro t ht
    have htI : t ∈ Set.Ioo lo hi := by
      simpa [interior_Icc] using ht
    exact (hasDerivAt_DyuA1_x_of_pos_leTwo p hp1 hp2 t y
      (lt_trans hlo htI.1)).hasDerivWithinAt
  · intro t ht
    have htI : t ∈ Set.Ioo lo hi := by
      simpa [interior_Icc] using ht
    have htpos : 0 < t := lt_trans hlo htI.1
    have ha : 0 ≤ alpha p := alpha_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have hp_sub : 0 ≤ p - 1 := by linarith
    have hpow : 0 ≤ t ^ (p - 2) := Real.rpow_nonneg htpos.le _
    have hpStar_nonneg : 0 ≤ pStar p / 2 := by
      have hpStar : pStar p = q p := pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
      have hp_ne_one : p ≠ 1 := by linarith
      have hpden_pos : 0 < p - 1 := by linarith
      rw [hpStar]
      simp only [q, hp_ne_one, ↓reduceIte, ge_iff_le]
      exact div_nonneg (div_nonneg (by linarith) hpden_pos.le) (by norm_num)
    positivity

private lemma DyuA1_mono_x_of_pos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hx : 0 < x) (hxz : x ≤ z) :
    DyuA1 p x y ≤ DyuA1 p z y := by
  have hmono := DyuA1_mono_x_on_Icc_pos_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (lo := x) (hi := z) (y := y) hx
  exact hmono ⟨le_rfl, hxz⟩ ⟨hxz, le_rfl⟩ hxz

private lemma DxuA1_mono_y_of_pos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y z : ℝ}
    (hx : 0 < x) (hyz : y ≤ z) :
    DxuA1 p x y ≤ DxuA1 p x z := by
  have hcoef_nonneg :
      0 ≤ alpha p * (p / 2) * x ^ (p - 2) := by
    have ha : 0 ≤ alpha p := alpha_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have hp_nonneg : 0 ≤ p / 2 := by linarith
    have hpow : 0 ≤ x ^ (p - 2) := Real.rpow_nonneg hx.le _
    positivity
  have hxpos : x > 0 := hx
  simp only [DxuA1, gt_iff_lt, hxpos, ↓reduceIte, Real.rpow_eq_pow, ge_iff_le]
  have hlin : (p - 2) / (p - 1) * x + y ≤ (p - 2) / (p - 1) * x + z := by
    linarith
  exact mul_le_mul_of_nonneg_left hlin hcoef_nonneg

private lemma hasDerivAt_DxvLeTwo_y_of_pos_leTwo
    (p x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    HasDerivAt (fun s => DxvLeTwo p x s)
      ((p * (p - 1) / 4) *
        (((x + y) / 2) ^ (p - 2) +
          coeffLeTwo p * ((x - y) / 2) ^ (p - 2))) y := by
  have hx : 0 < x := by linarith
  have hsum_nhds : {s : ℝ | 0 < (x + s) / 2} ∈ nhds y := by
    exact ((((continuous_const.add continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {s : ℝ | 0 < (x - s) / 2} ∈ nhds y := by
    exact ((((continuous_const.sub continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq :
      (fun s => DxvLeTwo p x s) =ᶠ[nhds y]
        fun s =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) -
            coeffLeTwo p * ((x - s) / 2) ^ (p - 1) * (p / 2) := by
    filter_upwards [hsum_nhds, hdiff_nhds] with s hssum hsdiff
    simp [DxvLeTwo, hx, abs_of_pos hssum, abs_of_pos hsdiff]
  have hbase_sum :
      HasDerivAt (fun s : ℝ => (x + s) / 2) (1 / 2) y := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id y).const_add x).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun s : ℝ => (x - s) / 2) (-(1 / 2)) y := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((((hasDerivAt_id y).neg).const_add x).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun s : ℝ => ((x + s) / 2) ^ (p - 1))
        ((p - 1) * ((x + y) / 2) ^ (p - 2) * (1 / 2)) y := by
    have hrpow :
        HasDerivAt (fun t : ℝ => t ^ (p - 1))
          ((p - 1) * ((x + y) / 2) ^ (p - 2)) ((x + y) / 2) := by
      have hcond : (x + y) / 2 ≠ 0 ∨ 1 ≤ p - 1 := Or.inl (ne_of_gt hsum)
      have h := (Real.hasDerivAt_rpow_const hcond :
        HasDerivAt (fun t : ℝ => t ^ (p - 1))
          ((p - 1) * ((x + y) / 2) ^ ((p - 1) - 1)) ((x + y) / 2))
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        show p + (-1 + -1) = p + -2 by ring] using h
    exact hrpow.comp y hbase_sum
  have hpow_diff :
      HasDerivAt (fun s : ℝ => ((x - s) / 2) ^ (p - 1))
        ((p - 1) * ((x - y) / 2) ^ (p - 2) * (-(1 / 2))) y := by
    have hrpow :
        HasDerivAt (fun t : ℝ => t ^ (p - 1))
          ((p - 1) * ((x - y) / 2) ^ (p - 2)) ((x - y) / 2) := by
      have hcond : (x - y) / 2 ≠ 0 ∨ 1 ≤ p - 1 := Or.inl (ne_of_gt hdiff)
      have h := (Real.hasDerivAt_rpow_const hcond :
        HasDerivAt (fun t : ℝ => t ^ (p - 1))
          ((p - 1) * ((x - y) / 2) ^ ((p - 1) - 1)) ((x - y) / 2))
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        show p + (-1 + -1) = p + -2 by ring] using h
    exact hrpow.comp y hbase_diff
  have hderiv :
      HasDerivAt
        (fun s : ℝ =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) -
            coeffLeTwo p * ((x - s) / 2) ^ (p - 1) * (p / 2))
        ((p * (p - 1) / 4) *
          (((x + y) / 2) ^ (p - 2) +
            coeffLeTwo p * ((x - y) / 2) ^ (p - 2))) y := by
    have htmp :=
      (hpow_sum.mul_const (p / 2)).sub
        ((hpow_diff.const_mul (coeffLeTwo p)).mul_const (p / 2))
    refine htmp.congr_deriv ?_
    ring
  exact hderiv.congr_of_eventuallyEq hEq

private lemma deriv_DxvLeTwo_y_nonneg_leTwo
    (p : ℝ) (hp1 : 1 < p) (x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    0 ≤ deriv (fun s => DxvLeTwo p x s) y := by
  have hderiv := hasDerivAt_DxvLeTwo_y_of_pos_leTwo p x y hsum hdiff
  rw [hderiv.deriv]
  have hpcoef : 0 ≤ p * (p - 1) / 4 := by
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hsum_pow : 0 ≤ ((x + y) / 2) ^ (p - 2) :=
    Real.rpow_nonneg hsum.le _
  have hdiff_pow : 0 ≤ ((x - y) / 2) ^ (p - 2) :=
    Real.rpow_nonneg hdiff.le _
  have hcoeff : 0 ≤ coeffLeTwo p := by
    exact Real.rpow_nonneg (inv_nonneg.mpr (by linarith)) _
  exact mul_nonneg hpcoef (add_nonneg hsum_pow (mul_nonneg hcoeff hdiff_pow))

private lemma DxvLeTwo_mono_y_on_Icc_of_pos_leTwo
    (p : ℝ) (hp1 : 1 < p) {x lo hi : ℝ}
    (hx : 0 < x)
    (hlo_sum : 0 < (x + lo) / 2) (hhi_diff : 0 < (x - hi) / 2) :
    MonotoneOn (fun t : ℝ => DxvLeTwo p x t) (Set.Icc lo hi) := by
  have hcont : ContinuousOn (fun t : ℝ => DxvLeTwo p x t) (Set.Icc lo hi) := by
    let g : ℝ → ℝ := fun t =>
      ((x + t) / 2) ^ (p - 1) * (p / 2) -
        coeffLeTwo p * ((x - t) / 2) ^ (p - 1) * (p / 2)
    have hg : ContinuousOn g (Set.Icc lo hi) := by
      dsimp [g]
      apply ContinuousOn.sub
      · exact (((continuousOn_const.add continuousOn_id).div_const 2).rpow_const
          (fun t ht => Or.inl (ne_of_gt (by
            change 0 < (x + t) / 2
            linarith [hlo_sum, ht.1])))).mul continuousOn_const
      · exact (continuousOn_const.mul
          (((continuousOn_const.sub continuousOn_id).div_const 2).rpow_const
            (fun t ht => Or.inl (ne_of_gt (by
              change 0 < (x - t) / 2
              linarith [hhi_diff, ht.2]))))).mul continuousOn_const
    refine ContinuousOn.congr hg ?_
    intro t ht
    have hsum : 0 < (x + t) / 2 := by linarith [hlo_sum, ht.1]
    have hdiff : 0 < (x - t) / 2 := by linarith [hhi_diff, ht.2]
    simp [g, DxvLeTwo, hx, abs_of_pos hsum, abs_of_pos hdiff]
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (D := Set.Icc lo hi)
    (f := fun t : ℝ => DxvLeTwo p x t)
    (f' := fun t : ℝ =>
      (p * (p - 1) / 4) *
        (((x + t) / 2) ^ (p - 2) +
          coeffLeTwo p * ((x - t) / 2) ^ (p - 2)))
    (convex_Icc lo hi) hcont ?_ ?_
  · intro t ht
    have htI : t ∈ Set.Ioo lo hi := by
      simpa [interior_Icc] using ht
    have hsum : 0 < (x + t) / 2 := by linarith [hlo_sum, htI.1]
    have hdiff : 0 < (x - t) / 2 := by linarith [hhi_diff, htI.2]
    exact (hasDerivAt_DxvLeTwo_y_of_pos_leTwo p x t hsum hdiff).hasDerivWithinAt
  · intro t ht
    have htI : t ∈ Set.Ioo lo hi := by
      simpa [interior_Icc] using ht
    have hsum : 0 < (x + t) / 2 := by linarith [hlo_sum, htI.1]
    have hdiff : 0 < (x - t) / 2 := by linarith [hhi_diff, htI.2]
    have hpcoef : 0 ≤ p * (p - 1) / 4 := by
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
    have hsum_pow : 0 ≤ ((x + t) / 2) ^ (p - 2) :=
      Real.rpow_nonneg hsum.le _
    have hdiff_pow : 0 ≤ ((x - t) / 2) ^ (p - 2) :=
      Real.rpow_nonneg hdiff.le _
    have hcoeff : 0 ≤ coeffLeTwo p := by
      exact Real.rpow_nonneg (inv_nonneg.mpr (by linarith)) _
    exact mul_nonneg hpcoef (add_nonneg hsum_pow (mul_nonneg hcoeff hdiff_pow))

private lemma DyuCandidate_mono_x_on_Q1_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p ≤ x) (hxz : x ≤ z) :
    DyuCandidate p x y ≤ DyuCandidate p z y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hx_pos : 0 < x := by
    have hy_div_pos : 0 < y / a p := div_pos hy_pos ha_pos
    exact lt_of_lt_of_le hy_div_pos hx_lower
  have hz_pos : 0 < z := lt_of_lt_of_le hx_pos hxz
  have hQx : QuarterPlane x y := by
    refine ⟨hx_pos.le, ?_, ?_⟩
    · have hy_lt_div : y < y / a p := by
        rw [div_eq_mul_inv]
        have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
        have hinv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans hy_lt_div.le hx_lower
    · linarith
  have hQz : QuarterPlane z y := by
    refine ⟨hz_pos.le, le_trans hQx.2.1 hxz, ?_⟩
    linarith
  have hclx : closureA1 p x y := by
    refine ⟨hx_pos.le, by linarith, ?_⟩
    have hmul := mul_le_mul_of_nonneg_left hx_lower ha_pos.le
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hclz : closureA1 p z y := by
    refine ⟨hz_pos.le, by linarith, ?_⟩
    have hz_lower : y / a p ≤ z := le_trans hx_lower hxz
    have hmul := mul_le_mul_of_nonneg_left hz_lower ha_pos.le
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hdx : DyuCandidate p x y = DyuA1 p x y := by
    rw [DyuCandidate_eq_Q1_leTwo p hQx]
    simp [DyauxFunction1, hclx]
  have hdz : DyuCandidate p z y = DyuA1 p z y := by
    rw [DyuCandidate_eq_Q1_leTwo p hQz]
    simp [DyauxFunction1, hclz]
  rw [hdx, hdz]
  exact DyuA1_mono_x_of_pos_leTwo p hp1 hp2 hx_pos hxz

private lemma DyuCandidate_mono_x_on_Q3_A1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y ≤ x) (hz_upper : z ≤ a p * y)
    (hxz : x ≤ z) :
    DyuCandidate p x y ≤ DyuCandidate p z y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane3 x y := by
    refine ⟨hy_pos.le, hx_lower, ?_⟩
    exact le_trans (le_trans hxz hz_upper)
      ((mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le).trans_eq (one_mul y))
  have hQz : QuarterPlane3 z y := by
    refine ⟨hy_pos.le, le_trans hx_lower hxz, ?_⟩
    exact le_trans hz_upper
      ((mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le).trans_eq (one_mul y))
  have hclx : closureA1 p y x := ⟨hy_pos.le, hx_lower, le_trans hxz hz_upper⟩
  have hclz : closureA1 p y z := ⟨hy_pos.le, le_trans hx_lower hxz, hz_upper⟩
  have hdx : DyuCandidate p x y = DxuA1 p y x := by
    rw [DyuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    simp [DxauxFunction1, hclx]
  have hdz : DyuCandidate p z y = DxuA1 p y z := by
    rw [DyuCandidate_eq_Q3_leTwo p hp1 hp2 hQz]
    simp [DxauxFunction1, hclz]
  rw [hdx, hdz]
  exact DxuA1_mono_y_of_pos_leTwo p hp1 hp2 hy_pos hxz

private lemma DyuCandidate_mono_x_on_Q2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hz_upper : z ≤ -y) (hxz : x ≤ z) :
    DyuCandidate p x y ≤ DyuCandidate p z y := by
  have hQx : QuarterPlane2 x y := ⟨by linarith, by linarith, by linarith⟩
  have hQz : QuarterPlane2 z y := ⟨by linarith, by linarith, by linarith⟩
  have hclx : closureA1 p (-x) (-y) := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    refine ⟨by linarith, by linarith, ?_⟩
    have hx_nonpos : x ≤ 0 := le_trans hxz (le_trans hz_upper (by linarith))
    have hmul : a p * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha_nonneg hx_nonpos
    linarith
  have hclz : closureA1 p (-z) (-y) := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
    refine ⟨by linarith, by linarith, ?_⟩
    have hz_nonpos : z ≤ 0 := le_trans hz_upper (by linarith)
    have hmul : a p * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha_nonneg hz_nonpos
    linarith
  have hdx : DyuCandidate p x y = -DyuA1 p (-x) (-y) := by
    rw [DyuCandidate_eq_Q2_leTwo p hQx]
    simp [DyauxFunction1, hclx]
  have hdz : DyuCandidate p z y = -DyuA1 p (-z) (-y) := by
    rw [DyuCandidate_eq_Q2_leTwo p hQz]
    simp [DyauxFunction1, hclz]
  have hzpos : 0 < -z := by linarith
  have hmono : DyuA1 p (-z) (-y) ≤ DyuA1 p (-x) (-y) :=
    DyuA1_mono_x_of_pos_leTwo p hp1 hp2 hzpos (by linarith)
  rw [hdx, hdz]
  linarith

private lemma DyuCandidate_mono_x_on_Q1_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hyx : y < x) (hz_upper : z ≤ y / a p)
    (hxz : x ≤ z) :
    DyuCandidate p x y ≤ DyuCandidate p z y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hx_pos : 0 < x := lt_of_lt_of_le hy_pos hyx.le
  have hz_pos : 0 < z := lt_of_lt_of_le hx_pos hxz
  have hQx : QuarterPlane x y := ⟨hx_pos.le, hyx.le, by linarith⟩
  have hQz : QuarterPlane z y := ⟨hz_pos.le, le_trans hyx.le hxz, by linarith⟩
  have hax : a p * x ≤ y := by
    have hmul := mul_le_mul_of_nonneg_left (le_trans hxz hz_upper) ha_pos.le
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have haz : a p * z ≤ y := by
    have hmul := mul_le_mul_of_nonneg_left hz_upper ha_pos.le
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hclx : closureA2 p x y := ⟨hx_pos.le, hax, hyx.le⟩
  have hclz : closureA2 p z y := ⟨hz_pos.le, haz, le_trans hyx.le hxz⟩
  have hdx : DyuCandidate p x y = DyvLeTwo p x y := by
    rw [DyuCandidate_eq_Q1_leTwo p hQx]
    exact auxFunction1_Dy_eq_DyvLeTwo_leTwo p hp1 hp2 x y hclx
  have hdz : DyuCandidate p z y = DyvLeTwo p z y := by
    rw [DyuCandidate_eq_Q1_leTwo p hQz]
    exact auxFunction1_Dy_eq_DyvLeTwo_leTwo p hp1 hp2 z y hclz
  have hmono := DyvLeTwo_mono_x_on_Icc_of_pos_leTwo
    (p := p) (hp1 := hp1) (lo := x) (hi := z) (y := y)
    (by linarith) (by linarith)
  rw [hdx, hdz]
  exact hmono ⟨le_rfl, hxz⟩ ⟨hxz, le_rfl⟩ hxz

private lemma DyuCandidate_mono_x_on_Q3_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y ≤ x) (hz_upper : z < y)
    (hxz : x ≤ z) :
    DyuCandidate p x y ≤ DyuCandidate p z y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane3 x y := by
    refine ⟨hy_pos.le, ?_, le_trans hxz hz_upper.le⟩
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hQz : QuarterPlane3 z y := by
    refine ⟨hy_pos.le, ?_, hz_upper.le⟩
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hclx : closureA2 p y x := ⟨hy_pos.le, hx_lower, le_trans hxz hz_upper.le⟩
  have hclz : closureA2 p y z := ⟨hy_pos.le, le_trans hx_lower hxz, hz_upper.le⟩
  have hdx : DyuCandidate p x y = DxvLeTwo p y x := by
    rw [DyuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y x hclx
  have hdz : DyuCandidate p z y = DxvLeTwo p y z := by
    rw [DyuCandidate_eq_Q3_leTwo p hp1 hp2 hQz]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y z hclz
  have hmono := DxvLeTwo_mono_y_on_Icc_of_pos_leTwo
    (p := p) (hp1 := hp1) (x := y) (lo := x) (hi := z)
    hy_pos (by
      have hsum : 0 ≤ x := by
        have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
        exact le_trans haxy_nonneg hx_lower
      linarith) (by linarith)
  rw [hdx, hdz]
  exact hmono ⟨le_rfl, hxz⟩ ⟨hxz, le_rfl⟩ hxz

private lemma DyuCandidate_mono_x_Q3_A2_to_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y ≤ x) (hx_upper : x < y) :
    DyuCandidate p x y ≤ DyuCandidate p y y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hQx : QuarterPlane3 x y := by
    refine ⟨hy_pos.le, ?_, hx_upper.le⟩
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hclx : closureA2 p y x := ⟨hy_pos.le, hx_lower, hx_upper.le⟩
  have hcly : closureA2 p y y := by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    exact ⟨hy_pos.le,
      (mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le).trans_eq (one_mul y), le_rfl⟩
  have hdx : DyuCandidate p x y = DxvLeTwo p y x := by
    rw [DyuCandidate_eq_Q3_leTwo p hp1 hp2 hQx]
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 y x hclx
  have hdy : DyuCandidate p y y = DyvLeTwo p y y := by
    rw [DyuCandidate_eq_Q1_leTwo p hQy]
    exact auxFunction1_Dy_eq_DyvLeTwo_leTwo p hp1 hp2 y y hcly
  have hsum_le : ((y + x) / 2) ^ (p - 1) ≤ y ^ (p - 1) := by
    have hbase_nonneg : 0 ≤ (y + x) / 2 := by
      have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      have hx_nonneg : 0 ≤ x := le_trans haxy_nonneg hx_lower
      linarith
    have hbase_le : (y + x) / 2 ≤ y := by linarith
    exact Real.rpow_le_rpow hbase_nonneg hbase_le (by linarith)
  have hdiff_nonneg : 0 ≤ ((y - x) / 2) ^ (p - 1) := by
    exact Real.rpow_nonneg (by linarith [hx_upper.le]) _
  have hcoeff_nonneg : 0 ≤ coeffLeTwo p := by
    exact Real.rpow_nonneg (inv_nonneg.mpr (by linarith)) _
  have hp_half_nonneg : 0 ≤ p / 2 := by linarith
  rw [hdx, hdy]
  have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
  have hx_nonneg : 0 ≤ x := by
    have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    exact le_trans haxy_nonneg hx_lower
  have hsum_pos : 0 < (y + x) / 2 := by linarith
  have hdiff_pos : 0 < (y - x) / 2 := by linarith
  simp only [DxvLeTwo, gt_iff_lt, hy_pos, ↓reduceIte, abs_of_pos hsum_pos, Real.rpow_eq_pow,
    abs_of_pos hdiff_pos, DyvLeTwo, add_self_div_two, abs_of_pos hy_pos, sub_self, zero_div,
    abs_zero, hzero, mul_zero, zero_mul, add_zero, tsub_le_iff_right, ge_iff_le]
  have hA := mul_le_mul_of_nonneg_right hsum_le hp_half_nonneg
  have hB : 0 ≤ coeffLeTwo p * ((y - x) / 2) ^ (p - 1) * (p / 2) := by
    positivity
  nlinarith

private lemma DyuCandidate_mono_x_diag_to_Q1_A2_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {z y : ℝ}
    (hy_pos : 0 < y) (hyz : y < z) (hz_upper : z ≤ y / a p) :
    DyuCandidate p y y ≤ DyuCandidate p z y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have hz_pos : 0 < z := lt_trans hy_pos hyz
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hQz : QuarterPlane z y := ⟨hz_pos.le, hyz.le, by linarith⟩
  have hcly : closureA2 p y y := by
    have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
    exact ⟨hy_pos.le,
      (mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le).trans_eq (one_mul y), le_rfl⟩
  have haz : a p * z ≤ y := by
    have hmul := mul_le_mul_of_nonneg_left hz_upper ha_pos.le
    field_simp [ha_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hclz : closureA2 p z y := ⟨hz_pos.le, haz, hyz.le⟩
  have hdy : DyuCandidate p y y = DyvLeTwo p y y := by
    rw [DyuCandidate_eq_Q1_leTwo p hQy]
    exact auxFunction1_Dy_eq_DyvLeTwo_leTwo p hp1 hp2 y y hcly
  have hdz : DyuCandidate p z y = DyvLeTwo p z y := by
    rw [DyuCandidate_eq_Q1_leTwo p hQz]
    exact auxFunction1_Dy_eq_DyvLeTwo_leTwo p hp1 hp2 z y hclz
  have hsum_le : y ^ (p - 1) ≤ ((z + y) / 2) ^ (p - 1) := by
    have hbase_nonneg : 0 ≤ y := hy_pos.le
    have hbase_le : y ≤ (z + y) / 2 := by linarith
    exact Real.rpow_le_rpow hbase_nonneg hbase_le (by linarith)
  have hdiff_nonneg : 0 ≤ ((z - y) / 2) ^ (p - 1) := by
    exact Real.rpow_nonneg (by linarith [hyz.le]) _
  have hcoeff_nonneg : 0 ≤ coeffLeTwo p := by
    exact Real.rpow_nonneg (inv_nonneg.mpr (by linarith)) _
  have hp_half_nonneg : 0 ≤ p / 2 := by linarith
  rw [hdy, hdz]
  have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
  have hsum_pos : 0 < (z + y) / 2 := by linarith
  have hdiff_pos : 0 < (z - y) / 2 := by linarith
  simp only [DyvLeTwo, gt_iff_lt, hy_pos, ↓reduceIte, add_self_div_two, abs_of_pos hy_pos,
    Real.rpow_eq_pow, sub_self, zero_div, abs_zero, hzero, mul_zero, zero_mul, add_zero, hz_pos,
    abs_of_pos hsum_pos, abs_of_pos hdiff_pos, ge_iff_le]
  have hA := mul_le_mul_of_nonneg_right hsum_le hp_half_nonneg
  have hB : 0 ≤ coeffLeTwo p * ((z - y) / 2) ^ (p - 1) * (p / 2) := by
    positivity
  nlinarith

private lemma DyuCandidate_antidiag_le_Q3_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DyuCandidate p (-y) y ≤ DyuCandidate p (a p * y) y := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hle : -y ≤ a p * y := by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  exact DyuCandidate_mono_x_on_Q3_A1_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := -y) (z := a p * y) (y := y)
    hy_pos le_rfl le_rfl hle

private lemma DyuCandidate_Q3_boundary_le_diag_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DyuCandidate p (a p * y) y ≤ DyuCandidate p y y := by
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  exact DyuCandidate_mono_x_Q3_A2_to_diag_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (x := a p * y) (y := y)
    hy_pos le_rfl (by simpa using mul_lt_mul_of_pos_right ha_lt hy_pos)

private lemma DyuCandidate_diag_le_Q1_boundary_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {y : ℝ}
    (hy_pos : 0 < y) :
    DyuCandidate p y y ≤ DyuCandidate p (y / a p) y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hy_lt_div : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  exact DyuCandidate_mono_x_diag_to_Q1_A2_leTwo
    (p := p) (hp1 := hp1) (hp2 := hp2) (z := y / a p) (y := y)
    hy_pos hy_lt_div le_rfl

private lemma DyuCandidate_mono_x_of_y_pos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hy_pos : 0 < y) (hxz : x ≤ z) :
    DyuCandidate p x y ≤ DyuCandidate p z y := by
  have ha_pos : 0 < a p := by
    rw [a_eq_leTwo p hp1 hp2]
    exact div_pos (by linarith) (by linarith)
  have ha_nonneg : 0 ≤ a p := ha_pos.le
  have ha_lt : a p < 1 := a_lt_one_of_one_lt_of_lt_two p hp1 hp2
  have hneg_le_boundary : -y ≤ a p * y := by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have hboundary_lt_diag : a p * y < y := by
    simpa using mul_lt_mul_of_pos_right ha_lt hy_pos
  have hdiag_lt_q1 : y < y / a p := by
    rw [div_eq_mul_inv]
    have hinv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    nlinarith
  by_cases hz_q2 : z ≤ -y
  · exact DyuCandidate_mono_x_on_Q2_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y)
      hy_pos hz_q2 hxz
  · have hz_gt_neg : -y < z := lt_of_not_ge hz_q2
    have start_to_neg :
        x ≤ -y →
        DyuCandidate p x y ≤ DyuCandidate p (-y) y := by
      intro hx_neg
      exact DyuCandidate_mono_x_on_Q2_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := -y) (y := y)
        hy_pos le_rfl hx_neg
    by_cases hz_q3a1 : z ≤ a p * y
    · by_cases hx_neg : x ≤ -y
      · exact le_trans (start_to_neg hx_neg)
          (DyuCandidate_mono_x_on_Q3_A1_leTwo
            (p := p) (hp1 := hp1) (hp2 := hp2)
            (x := -y) (z := z) (y := y)
            hy_pos le_rfl hz_q3a1 (le_of_lt hz_gt_neg))
      · exact DyuCandidate_mono_x_on_Q3_A1_leTwo
          (p := p) (hp1 := hp1) (hp2 := hp2)
          (x := x) (z := z) (y := y)
          hy_pos (le_of_lt (lt_of_not_ge hx_neg)) hz_q3a1 hxz
    · have hz_gt_boundary : a p * y < z := lt_of_not_ge hz_q3a1
      by_cases hz_diag : z < y
      · by_cases hx_neg : x ≤ -y
        · exact le_trans (start_to_neg hx_neg)
            (le_trans (DyuCandidate_antidiag_le_Q3_boundary_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
              (DyuCandidate_mono_x_on_Q3_A2_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2)
                (x := a p * y) (z := z) (y := y)
                hy_pos le_rfl hz_diag (le_of_lt hz_gt_boundary)))
        · by_cases hx_boundary : x ≤ a p * y
          · exact le_trans
              (DyuCandidate_mono_x_on_Q3_A1_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2)
                (x := x) (z := a p * y) (y := y)
                hy_pos (le_of_lt (lt_of_not_ge hx_neg)) le_rfl hx_boundary)
              (DyuCandidate_mono_x_on_Q3_A2_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2)
                (x := a p * y) (z := z) (y := y)
                hy_pos le_rfl hz_diag (le_of_lt hz_gt_boundary))
          · exact DyuCandidate_mono_x_on_Q3_A2_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2)
              (x := x) (z := z) (y := y)
              hy_pos (le_of_lt (lt_of_not_ge hx_boundary)) hz_diag hxz
      · have hy_le_z : y ≤ z := le_of_not_gt hz_diag
        by_cases hz_q1a2 : z ≤ y / a p
        · by_cases hx_neg : x ≤ -y
          · exact le_trans (start_to_neg hx_neg)
              (le_trans (DyuCandidate_antidiag_le_Q3_boundary_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
                (le_trans (DyuCandidate_Q3_boundary_le_diag_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
                  (by
                    rcases hy_le_z.lt_or_eq with hyz | rfl
                    · exact DyuCandidate_mono_x_diag_to_Q1_A2_leTwo
                        (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                        hy_pos hyz hz_q1a2
                    · exact le_rfl)))
          · by_cases hx_boundary : x ≤ a p * y
            · exact le_trans
                (DyuCandidate_mono_x_on_Q3_A1_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2)
                  (x := x) (z := a p * y) (y := y)
                  hy_pos (le_of_lt (lt_of_not_ge hx_neg)) le_rfl hx_boundary)
                (le_trans (DyuCandidate_Q3_boundary_le_diag_leTwo
                  (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
                  (by
                    rcases hy_le_z.lt_or_eq with hyz | rfl
                    · exact DyuCandidate_mono_x_diag_to_Q1_A2_leTwo
                        (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                        hy_pos hyz hz_q1a2
                    · exact le_rfl))
            · by_cases hx_diag : x < y
              · exact le_trans
                  (DyuCandidate_mono_x_Q3_A2_to_diag_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2)
                    (x := x) (y := y) hy_pos
                    (le_of_lt (lt_of_not_ge hx_boundary)) hx_diag)
                  (by
                    rcases hy_le_z.lt_or_eq with hyz | rfl
                    · exact DyuCandidate_mono_x_diag_to_Q1_A2_leTwo
                        (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                        hy_pos hyz hz_q1a2
                    · exact le_rfl)
              · have hy_lt_x_or_eq : y ≤ x := le_of_not_gt hx_diag
                rcases hy_lt_x_or_eq.lt_or_eq with hyx | rfl
                · exact DyuCandidate_mono_x_on_Q1_A2_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2)
                    (x := x) (z := z) (y := y) hy_pos hyx hz_q1a2 hxz
                · rcases hy_le_z.lt_or_eq with hyz | rfl
                  · exact DyuCandidate_mono_x_diag_to_Q1_A2_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (z := z) (y := y)
                      hy_pos hyz hz_q1a2
                  · exact le_rfl
        · have hz_gt_q1 : y / a p < z := lt_of_not_ge hz_q1a2
          by_cases hx_q1 : y / a p ≤ x
          · exact DyuCandidate_mono_x_on_Q1_A1_leTwo
              (p := p) (hp1 := hp1) (hp2 := hp2)
              (x := x) (z := z) (y := y) hy_pos hx_q1 hxz
          · have hx_lt_q1 : x < y / a p := lt_of_not_ge hx_q1
            have to_q1_boundary :
                DyuCandidate p x y ≤ DyuCandidate p (y / a p) y := by
              by_cases hx_neg : x ≤ -y
              · exact le_trans (start_to_neg hx_neg)
                  (le_trans (DyuCandidate_antidiag_le_Q3_boundary_leTwo
                    (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
                    (le_trans (DyuCandidate_Q3_boundary_le_diag_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
                      (DyuCandidate_diag_le_Q1_boundary_leTwo
                        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)))
              · by_cases hx_boundary : x ≤ a p * y
                · exact le_trans
                    (DyuCandidate_mono_x_on_Q3_A1_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2)
                      (x := x) (z := a p * y) (y := y)
                      hy_pos (le_of_lt (lt_of_not_ge hx_neg)) le_rfl hx_boundary)
                    (le_trans (DyuCandidate_Q3_boundary_le_diag_leTwo
                      (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
                      (DyuCandidate_diag_le_Q1_boundary_leTwo
                        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos))
                · by_cases hx_diag : x < y
                  · exact le_trans
                      (DyuCandidate_mono_x_Q3_A2_to_diag_leTwo
                        (p := p) (hp1 := hp1) (hp2 := hp2)
                        (x := x) (y := y) hy_pos
                        (le_of_lt (lt_of_not_ge hx_boundary)) hx_diag)
                      (DyuCandidate_diag_le_Q1_boundary_leTwo
                        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos)
                  · have hy_le_x : y ≤ x := le_of_not_gt hx_diag
                    rcases hy_le_x.lt_or_eq with hyx | rfl
                    · exact DyuCandidate_mono_x_on_Q1_A2_leTwo
                        (p := p) (hp1 := hp1) (hp2 := hp2)
                        (x := x) (z := y / a p) (y := y)
                        hy_pos hyx le_rfl hx_lt_q1.le
                    · exact DyuCandidate_diag_le_Q1_boundary_leTwo
                        (p := p) (hp1 := hp1) (hp2 := hp2) (y := y) hy_pos
            exact le_trans to_q1_boundary
              (DyuCandidate_mono_x_on_Q1_A1_leTwo
                (p := p) (hp1 := hp1) (hp2 := hp2)
                (x := y / a p) (z := z) (y := y)
                hy_pos le_rfl (le_of_lt hz_gt_q1))

private lemma DyuCandidate_neg_neg_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) :
    DyuCandidate p x y = -DyuCandidate p (-x) (-y) := by
  rcases mem_some_QuarterPlane_leTwo x y with hQ1 | hrest
  · have hQ2 : QuarterPlane2 (-x) (-y) := ⟨by linarith [hQ1.1],
      by linarith [hQ1.2.2], by linarith [hQ1.2.1]⟩
    rw [DyuCandidate_eq_Q1_leTwo p hQ1, DyuCandidate_eq_Q2_leTwo p hQ2]
    simp
  rcases hrest with hQ2 | hrest
  · have hQ1 : QuarterPlane (-x) (-y) := ⟨by linarith [hQ2.1],
      by linarith [hQ2.2.2], by linarith [hQ2.2.1]⟩
    rw [DyuCandidate_eq_Q2_leTwo p hQ2, DyuCandidate_eq_Q1_leTwo p hQ1]
  rcases hrest with hQ3 | hQ4
  · have hQ4 : QuarterPlane4 (-x) (-y) := ⟨by linarith [hQ3.1],
      by linarith [hQ3.2.2], by linarith [hQ3.2.1]⟩
    rw [DyuCandidate_eq_Q3_leTwo p hp1 hp2 hQ3,
      DyuCandidate_eq_Q4_leTwo p hp1 hp2 hQ4]
    simp
  · have hQ3 : QuarterPlane3 (-x) (-y) := ⟨by linarith [hQ4.1],
      by linarith [hQ4.2.2], by linarith [hQ4.2.1]⟩
    rw [DyuCandidate_eq_Q4_leTwo p hp1 hp2 hQ4,
      DyuCandidate_eq_Q3_leTwo p hp1 hp2 hQ3]

private lemma DyuA1_nonneg_of_nonneg_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (hx : 0 ≤ x) :
    0 ≤ DyuA1 p x y := by
  rcases hx.lt_or_eq with hxpos | rfl
  · have ha : 0 ≤ alpha p := alpha_nonneg_of_one_lt_of_lt_two p hp1 hp2
    have hpow : 0 ≤ x ^ (p - 1) := Real.rpow_nonneg hxpos.le _
    have hpStar_nonneg : 0 ≤ pStar p / 2 := by
      have hpStar : pStar p = q p := pStar_eq_q_of_one_lt_of_lt_two p hp1 hp2
      have hp_ne_one : p ≠ 1 := by linarith
      have hpden_pos : 0 < p - 1 := by linarith
      rw [hpStar]
      simp only [q, hp_ne_one, ↓reduceIte, ge_iff_le]
      exact div_nonneg (div_nonneg (by linarith) hpden_pos.le) (by norm_num)
    simp only [DyuA1, gt_iff_lt, hxpos, ↓reduceIte, Real.rpow_eq_pow, ge_iff_le]
    positivity
  · simp [DyuA1]

private lemma DyuCandidate_axis_nonneg_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x : ℝ} (hx : 0 ≤ x) :
    DyuCandidate p x 0 = DyuA1 p x 0 := by
  have hQ : QuarterPlane x 0 := ⟨hx, by simpa using hx, by linarith⟩
  have hcl : closureA1 p x 0 := by
    refine ⟨hx, by linarith, ?_⟩
    exact mul_nonneg (a_nonneg_of_one_lt_of_lt_two p hp1 hp2) hx
  rw [DyuCandidate_eq_Q1_leTwo p hQ]
  simp [DyauxFunction1, hcl]

private lemma DyuCandidate_axis_nonpos_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x : ℝ} (hx : x ≤ 0) :
    DyuCandidate p x 0 = -DyuA1 p (-x) 0 := by
  have hQ : QuarterPlane2 x 0 := ⟨hx, by linarith, hx⟩
  have hcl : closureA1 p (-x) 0 := by
    have hnonneg : 0 ≤ -x := by linarith
    refine ⟨hnonneg, by linarith, ?_⟩
    exact mul_nonneg (a_nonneg_of_one_lt_of_lt_two p hp1 hp2) hnonneg
  rw [DyuCandidate_eq_Q2_leTwo p hQ]
  simp [DyauxFunction1, hcl]

private lemma DyuCandidate_mono_x_axis_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z : ℝ}
    (hxz : x ≤ z) :
    DyuCandidate p x 0 ≤ DyuCandidate p z 0 := by
  by_cases hz_nonpos : z ≤ 0
  · have hx_nonpos : x ≤ 0 := le_trans hxz hz_nonpos
    rw [DyuCandidate_axis_nonpos_leTwo p hp1 hp2 hx_nonpos,
      DyuCandidate_axis_nonpos_leTwo p hp1 hp2 hz_nonpos]
    have hmono : DyuA1 p (-z) 0 ≤ DyuA1 p (-x) 0 := by
      rcases hz_nonpos.lt_or_eq with hzneg | hz0
      · exact DyuA1_mono_x_of_pos_leTwo p hp1 hp2 (by linarith) (by linarith)
      · subst z
        simpa [DyuA1] using
          DyuA1_nonneg_of_nonneg_leTwo (p := p) (hp1 := hp1) (hp2 := hp2)
            (x := -x) (y := 0) (by linarith : 0 ≤ -x)
    linarith
  · have hz_pos : 0 < z := lt_of_not_ge hz_nonpos
    by_cases hx_nonneg : 0 ≤ x
    · rw [DyuCandidate_axis_nonneg_leTwo p hp1 hp2 hx_nonneg,
        DyuCandidate_axis_nonneg_leTwo p hp1 hp2 hz_pos.le]
      rcases hx_nonneg.lt_or_eq with hxpos | rfl
      · exact DyuA1_mono_x_of_pos_leTwo p hp1 hp2 hxpos hxz
      · simpa [DyuA1] using
          DyuA1_nonneg_of_nonneg_leTwo (p := p) (hp1 := hp1) (hp2 := hp2)
            (x := z) (y := 0) hz_pos.le
    · have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
      have hleft : DyuCandidate p x 0 ≤ DyuCandidate p 0 0 := by
        rw [DyuCandidate_axis_nonpos_leTwo p hp1 hp2 hx_neg.le,
          DyuCandidate_axis_nonneg_leTwo p hp1 hp2 (le_refl 0)]
        have hnonneg : 0 ≤ DyuA1 p (-x) 0 :=
          DyuA1_nonneg_of_nonneg_leTwo (p := p) (hp1 := hp1) (hp2 := hp2)
            (x := -x) (y := 0) (by linarith)
        have hzero : DyuA1 p 0 0 = 0 := by simp [DyuA1]
        rw [hzero]
        linarith
      have hright : DyuCandidate p 0 0 ≤ DyuCandidate p z 0 := by
        rw [DyuCandidate_axis_nonneg_leTwo p hp1 hp2 (le_refl 0),
          DyuCandidate_axis_nonneg_leTwo p hp1 hp2 hz_pos.le]
        simpa [DyuA1] using
          DyuA1_nonneg_of_nonneg_leTwo (p := p) (hp1 := hp1) (hp2 := hp2)
            (x := z) (y := 0) hz_pos.le
      exact le_trans hleft hright

private lemma DyuCandidate_mono_x_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x z y : ℝ}
    (hxz : x ≤ z) :
    DyuCandidate p x y ≤ DyuCandidate p z y := by
  rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
  · have hpos : 0 < -y := by linarith
    have hmono :
        DyuCandidate p (-z) (-y) ≤ DyuCandidate p (-x) (-y) :=
      DyuCandidate_mono_x_of_y_pos_leTwo
        (p := p) (hp1 := hp1) (hp2 := hp2)
        (x := -z) (z := -x) (y := -y) hpos (by linarith)
    rw [DyuCandidate_neg_neg_leTwo p hp1 hp2 x y,
      DyuCandidate_neg_neg_leTwo p hp1 hp2 z y]
    linarith
  · subst y
    exact DyuCandidate_mono_x_axis_leTwo p hp1 hp2 hxz
  · exact DyuCandidate_mono_x_of_y_pos_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2) (x := x) (z := z) (y := y) hy_pos hxz

private lemma DyuCandidate_mixed_mono_mul_le_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y h k : ℝ}
    (hk : h * k ≤ 0) :
    DyuCandidate p (x + h) y * k ≤ DyuCandidate p x y * k := by
  rcases lt_trichotomy k 0 with hk_neg | hk_zero | hk_pos
  · have hh_nonneg : 0 ≤ h := by
      by_contra hh
      have hh_neg : h < 0 := lt_of_not_ge hh
      have hprod_pos : 0 < h * k := mul_pos_of_neg_of_neg hh_neg hk_neg
      linarith
    have hmono : DyuCandidate p x y ≤ DyuCandidate p (x + h) y :=
      DyuCandidate_mono_x_leTwo p hp1 hp2 (by linarith)
    exact mul_le_mul_of_nonpos_right hmono hk_neg.le
  · subst k
    simp
  · have hh_nonpos : h ≤ 0 := by
      by_contra hh
      have hh_pos : 0 < h := lt_of_not_ge hh
      have hprod_pos : 0 < h * k := mul_pos hh_pos hk_pos
      linarith
    have hmono : DyuCandidate p (x + h) y ≤ DyuCandidate p x y :=
      DyuCandidate_mono_x_leTwo p hp1 hp2 (by linarith)
    exact mul_le_mul_of_nonneg_right hmono hk_pos.le

private lemma uCandidate_hk_negative_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y h k : ℝ}
    (hk : h * k ≤ 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  by_cases hk0 : h * k = 0
  · exact uCandidate_axis_tangent_leTwo p hp1 hp2 hk0
  have hhor :
      uCandidate p (x + h) y ≤
        uCandidate p x y + DxuCandidate p x y * h := by
    have h := uCandidate_axis_tangent_horizontal_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2)
      (x := x) (y := y) (h := h) (k := 0) rfl
    simpa using h
  have hvert :
      uCandidate p (x + h) (y + k) ≤
        uCandidate p (x + h) y + DyuCandidate p (x + h) y * k := by
    have h := uCandidate_axis_tangent_vertical_leTwo
      (p := p) (hp1 := hp1) (hp2 := hp2)
      (x := x + h) (y := y) (h := 0) (k := k) rfl
    simpa using h
  have hmixed :
      DyuCandidate p (x + h) y * k ≤ DyuCandidate p x y * k := by
    exact DyuCandidate_mixed_mono_mul_le_leTwo p hp1 hp2 hk
  calc
    uCandidate p (x + h) (y + k)
        ≤ uCandidate p (x + h) y + DyuCandidate p (x + h) y * k := hvert
    _ ≤ (uCandidate p x y + DxuCandidate p x y * h) +
          DyuCandidate p (x + h) y * k := by
            linarith
    _ ≤ (uCandidate p x y + DxuCandidate p x y * h) +
          DyuCandidate p x y * k := by
            linarith
    _ = uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
      ring

/-! ## Polynomial growth of the candidate and its first partials -/

private def uA1GrowthConst (p : ℝ) : ℝ :=
  |alpha p| * (1 + |pStar p|)

private def vLeTwoGrowthConst (p : ℝ) : ℝ :=
  1 + |coeffLeTwo p|

private def auxGrowthConst (p : ℝ) : ℝ :=
  max (uA1GrowthConst p) (vLeTwoGrowthConst p)

private def uCandidateGrowthConst (p : ℝ) : ℝ :=
  max 0 (auxGrowthConst p)

private lemma uA1GrowthConst_nonneg (p : ℝ) :
    0 ≤ uA1GrowthConst p := by
  unfold uA1GrowthConst
  positivity

private lemma vLeTwoGrowthConst_nonneg (p : ℝ) :
    0 ≤ vLeTwoGrowthConst p := by
  unfold vLeTwoGrowthConst
  positivity

private lemma auxGrowthConst_nonneg (p : ℝ) :
    0 ≤ auxGrowthConst p := by
  unfold auxGrowthConst
  exact le_trans (uA1GrowthConst_nonneg p) (le_max_left _ _)

private lemma uCandidateGrowthConst_nonneg (p : ℝ) :
    0 ≤ uCandidateGrowthConst p := by
  unfold uCandidateGrowthConst
  exact le_max_left _ _

private lemma closureA1_x0_y0
    (p x y : ℝ) (h : closureA1 p x y) (hxnot : ¬ 0 < x) :
    x = 0 ∧ y = 0 := by
  have hx0 : x = 0 := le_antisymm (le_of_not_gt hxnot) h.1
  subst x
  have hy0 : y = 0 := by
    have hle : y ≤ 0 := by simpa using h.2.2
    have hge : 0 ≤ y := by simpa using h.2.1
    exact le_antisymm hle hge
  exact ⟨rfl, hy0⟩

private lemma closureA2_x0_y0
    (p x y : ℝ) (h : closureA2 p x y) (hxnot : ¬ 0 < x) :
    x = 0 ∧ y = 0 := by
  have hx0 : x = 0 := le_antisymm (le_of_not_gt hxnot) h.1
  subst x
  have hy0 : y = 0 := by
    have hge : 0 ≤ y := by simpa using h.2.1
    have hle : y ≤ 0 := by simpa using h.2.2
    exact le_antisymm hle hge
  exact ⟨rfl, hy0⟩

private lemma closureA1_abs_y_le_x
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (h : closureA1 p x y) :
    |y| ≤ x := by
  rcases h with ⟨hx, hlow, hup⟩
  have ha_le_one : a p ≤ 1 := (a_lt_one_of_one_lt_of_lt_two p hp1 hp2).le
  have hy_upper : y ≤ x := by
    calc
      y ≤ a p * x := hup
      _ ≤ 1 * x := mul_le_mul_of_nonneg_right ha_le_one hx
      _ = x := one_mul x
  exact abs_le.mpr ⟨hlow, hy_upper⟩

private lemma closureA2_abs_y_le_x
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (h : closureA2 p x y) :
    |y| ≤ x := by
  rcases h with ⟨hx, hlow, hup⟩
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_one_lt_of_lt_two p hp1 hp2
  have hneg : -x ≤ y := by
    exact le_trans (neg_nonpos.mpr hx) (le_trans (mul_nonneg ha_nonneg hx) hlow)
  exact abs_le.mpr ⟨hneg, hup⟩

private lemma auxFunction1_eq_uA1 (p x y : ℝ) (h1 : closureA1 p x y) :
    auxFunction1 p x y = uA1 p x y := by
  simp [auxFunction1, h1]

private lemma auxFunction1_Dx_eq_DxuA1 (p x y : ℝ) (h1 : closureA1 p x y) :
    DxauxFunction1 p x y = DxuA1 p x y := by
  simp [DxauxFunction1, h1]

private lemma auxFunction1_Dy_eq_DyuA1 (p x y : ℝ) (h1 : closureA1 p x y) :
    DyauxFunction1 p x y = DyuA1 p x y := by
  simp [DyauxFunction1, h1]

private lemma abs_uA1_le_growth
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (h : closureA1 p x y) :
    |uA1 p x y| ≤ uA1GrowthConst p * Real.rpow x p := by
  rcases h with ⟨hx, hlow, hup⟩
  by_cases hxpos : 0 < x
  · have hyabs : |y| ≤ x :=
      closureA1_abs_y_le_x p hp1 hp2 ⟨hx, hlow, hup⟩
    have hx_abs : |x| = x := abs_of_nonneg hx
    have hxmy : |x - y| ≤ 2 * x := by
      have htmp : |x - y| ≤ |x| + |y| := by
        simpa [sub_eq_add_neg] using abs_add_le x (-y)
      calc
        |x - y| ≤ |x| + |y| := htmp
        _ = x + |y| := by rw [hx_abs]
        _ ≤ x + x := by gcongr
        _ = 2 * x := by ring
    have hlin :
        |x - pStar p * (x - y) / 2| ≤ (1 + |pStar p|) * x := by
      have htmp :
          |x - pStar p * (x - y) / 2|
            ≤ |x| + |pStar p * (x - y) / 2| := by
        simpa [sub_eq_add_neg] using abs_add_le x (-(pStar p * (x - y) / 2))
      have hdiv : |pStar p * (x - y) / 2| = |pStar p| * |x - y| / 2 := by
        rw [abs_div, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      rw [hx_abs, hdiv] at htmp
      calc
        |x - pStar p * (x - y) / 2| ≤ x + |pStar p| * |x - y| / 2 := htmp
        _ ≤ x + |pStar p| * (2 * x) / 2 := by gcongr
        _ = (1 + |pStar p|) * x := by ring
    have hpow : Real.rpow x (p - 1) * x = Real.rpow x p := by
      calc
        Real.rpow x (p - 1) * x
            = Real.rpow x (p - 1) * Real.rpow x (1 : ℝ) := by simp [Real.rpow_one]
        _ = Real.rpow x ((p - 1) + 1) := by
              simpa using (Real.rpow_add hxpos (p - 1) 1).symm
        _ = Real.rpow x p := by ring_nf
    have hpow_nonneg : 0 ≤ Real.rpow x (p - 1) := Real.rpow_nonneg hx _
    calc
      |uA1 p x y|
          = |alpha p| * Real.rpow x (p - 1) *
              |x - pStar p * (x - y) / 2| := by
            simp only [uA1, hxpos, if_true]
            rw [abs_mul, abs_mul, abs_of_nonneg hpow_nonneg]
      _ ≤ |alpha p| * Real.rpow x (p - 1) * ((1 + |pStar p|) * x) := by
            gcongr
      _ = uA1GrowthConst p * Real.rpow x p := by
            unfold uA1GrowthConst
            rw [← hpow]
            ring
  · have h00 : x = 0 ∧ y = 0 := closureA1_x0_y0 p x y ⟨hx, hlow, hup⟩ hxpos
    rcases h00 with ⟨rfl, rfl⟩
    have hnonneg : 0 ≤ uA1GrowthConst p * Real.rpow 0 p :=
      mul_nonneg (uA1GrowthConst_nonneg p) (Real.rpow_nonneg le_rfl _)
    simpa [uA1] using hnonneg

private lemma closureA2_abs_add_div_two_le_x
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (h : closureA2 p x y) :
    |(x + y) / 2| ≤ x := by
  rcases h with ⟨hx, hlow, hup⟩
  have hyabs : |y| ≤ x := closureA2_abs_y_le_x p hp1 hp2 ⟨hx, hlow, hup⟩
  have hx_abs : |x| = x := abs_of_nonneg hx
  have htmp : |x + y| ≤ |x| + |y| := abs_add_le x y
  have hdiv := div_le_div_of_nonneg_right htmp (by norm_num : (0 : ℝ) ≤ 2)
  have habs_div : |(x + y) / 2| = |x + y| / 2 := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  calc
    |(x + y) / 2| = |x + y| / 2 := habs_div
    _ ≤ (|x| + |y|) / 2 := hdiv
    _ = (x + |y|) / 2 := by rw [hx_abs]
    _ ≤ (x + x) / 2 := by gcongr
    _ = x := by ring

private lemma closureA2_abs_sub_div_two_le_x
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (h : closureA2 p x y) :
    |(x - y) / 2| ≤ x := by
  rcases h with ⟨hx, hlow, hup⟩
  have hyabs : |y| ≤ x := closureA2_abs_y_le_x p hp1 hp2 ⟨hx, hlow, hup⟩
  have hx_abs : |x| = x := abs_of_nonneg hx
  have htmp : |x - y| ≤ |x| + |y| := by
    simpa [sub_eq_add_neg] using abs_add_le x (-y)
  have hdiv := div_le_div_of_nonneg_right htmp (by norm_num : (0 : ℝ) ≤ 2)
  have habs_div : |(x - y) / 2| = |x - y| / 2 := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  calc
    |(x - y) / 2| = |x - y| / 2 := habs_div
    _ ≤ (|x| + |y|) / 2 := hdiv
    _ = (x + |y|) / 2 := by rw [hx_abs]
    _ ≤ (x + x) / 2 := by gcongr
    _ = x := by ring

private lemma abs_vLeTwo_le_growth_on_closureA2
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (h : closureA2 p x y) :
    |vLeTwo p x y| ≤ vLeTwoGrowthConst p * Real.rpow x p := by
  rcases h with ⟨hx, hlow, hup⟩
  have hsum : |(x + y) / 2| ≤ x :=
    closureA2_abs_add_div_two_le_x p hp1 hp2 ⟨hx, hlow, hup⟩
  have hdiff : |(x - y) / 2| ≤ x :=
    closureA2_abs_sub_div_two_le_x p hp1 hp2 ⟨hx, hlow, hup⟩
  have hp_nonneg : 0 ≤ p := by linarith
  have hsum_pow :
      Real.rpow |(x + y) / 2| p ≤ Real.rpow x p :=
    Real.rpow_le_rpow (abs_nonneg _) hsum hp_nonneg
  have hdiff_pow :
      Real.rpow |(x - y) / 2| p ≤ Real.rpow x p :=
    Real.rpow_le_rpow (abs_nonneg _) hdiff hp_nonneg
  calc
    |vLeTwo p x y|
        ≤ Real.rpow |(x + y) / 2| p +
            |coeffLeTwo p| * Real.rpow |(x - y) / 2| p := by
          unfold vLeTwo
          calc
            |Real.rpow |(x + y) / 2| p -
                coeffLeTwo p * Real.rpow |(x - y) / 2| p|
                ≤ |Real.rpow |(x + y) / 2| p| +
                    |coeffLeTwo p * Real.rpow |(x - y) / 2| p| := by
                  simpa [sub_eq_add_neg] using
                    abs_add_le (Real.rpow |(x + y) / 2| p)
                      (-(coeffLeTwo p * Real.rpow |(x - y) / 2| p))
            _ = Real.rpow |(x + y) / 2| p +
                |coeffLeTwo p| * Real.rpow |(x - y) / 2| p := by
                  have hA :
                      |Real.rpow |(x + y) / 2| p| =
                        Real.rpow |(x + y) / 2| p :=
                    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
                  have hB :
                      |coeffLeTwo p * Real.rpow |(x - y) / 2| p| =
                        |coeffLeTwo p| * Real.rpow |(x - y) / 2| p := by
                    have hpow_nonneg :
                        0 ≤ Real.rpow |(x - y) / 2| p :=
                      Real.rpow_nonneg (abs_nonneg _) _
                    rw [abs_mul]
                    rw [abs_of_nonneg hpow_nonneg]
                  rw [hA, hB]
    _ ≤ Real.rpow x p + |coeffLeTwo p| * Real.rpow x p := by gcongr
    _ = vLeTwoGrowthConst p * Real.rpow x p := by
          unfold vLeTwoGrowthConst
          ring

private lemma abs_auxFunction1_le_growth
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} :
    |auxFunction1 p x y| ≤ auxGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by
  by_cases h1 : closureA1 p x y
  · have hx : 0 ≤ x := h1.1
    have hx_abs : |x| = x := abs_of_nonneg hx
    calc
      |auxFunction1 p x y| = |uA1 p x y| := by rw [auxFunction1_eq_uA1 p x y h1]
      _ ≤ uA1GrowthConst p * Real.rpow x p := abs_uA1_le_growth p hp1 hp2 h1
      _ ≤ auxGrowthConst p * Real.rpow |x| p := by
        rw [hx_abs]
        exact mul_le_mul_of_nonneg_right
          (by unfold auxGrowthConst; exact le_max_left _ _)
          (Real.rpow_nonneg hx _)
      _ ≤ auxGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg y) _))
          (auxGrowthConst_nonneg p)
  · by_cases h2 : closureA2 p x y
    · have hx : 0 ≤ x := h2.1
      have hx_abs : |x| = x := abs_of_nonneg hx
      calc
        |auxFunction1 p x y| = |vLeTwo p x y| := by
          rw [auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 x y h2]
        _ ≤ vLeTwoGrowthConst p * Real.rpow x p :=
          abs_vLeTwo_le_growth_on_closureA2 p hp1 hp2 h2
        _ ≤ auxGrowthConst p * Real.rpow |x| p := by
          rw [hx_abs]
          exact mul_le_mul_of_nonneg_right
            (by unfold auxGrowthConst; exact le_max_right _ _)
            (Real.rpow_nonneg hx _)
        _ ≤ auxGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by
          exact mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg y) _))
            (auxGrowthConst_nonneg p)
    · have hnonneg :
          0 ≤ auxGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by
        exact mul_nonneg (auxGrowthConst_nonneg p)
          (add_nonneg (Real.rpow_nonneg (abs_nonneg x) _)
            (Real.rpow_nonneg (abs_nonneg y) _))
      simpa [auxFunction1, h1, h2] using hnonneg

private lemma abs_uCandidate_le_growth
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) :
    |uCandidate p x y|
      ≤ uCandidateGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by
  have hCaux : auxGrowthConst p ≤ uCandidateGrowthConst p := by
    unfold uCandidateGrowthConst
    exact le_max_right _ _
  have hsum_nonneg : 0 ≤ Real.rpow |x| p + Real.rpow |y| p :=
    add_nonneg (Real.rpow_nonneg (abs_nonneg x) _)
      (Real.rpow_nonneg (abs_nonneg y) _)
  rcases mem_some_QuarterPlane_leTwo x y with hQ1 | hrest
  · have haux := abs_auxFunction1_le_growth p hp1 hp2 (x := x) (y := y)
    calc
      |uCandidate p x y| = |auxFunction1 p x y| := by rw [uCandidate_eq_Q1_leTwo p hQ1]
      _ ≤ auxGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := haux
      _ ≤ uCandidateGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) :=
        mul_le_mul_of_nonneg_right hCaux hsum_nonneg
  rcases hrest with hQ2 | hrest
  · have haux := abs_auxFunction1_le_growth p hp1 hp2 (x := -x) (y := -y)
    calc
      |uCandidate p x y| = |auxFunction1 p (-x) (-y)| := by rw [uCandidate_eq_Q2_leTwo p hQ2]
      _ ≤ auxGrowthConst p * (Real.rpow |(-x)| p + Real.rpow |(-y)| p) := haux
      _ = auxGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by simp
      _ ≤ uCandidateGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) :=
        mul_le_mul_of_nonneg_right hCaux hsum_nonneg
  rcases hrest with hQ3 | hQ4
  · have haux := abs_auxFunction1_le_growth p hp1 hp2 (x := y) (y := x)
    calc
      |uCandidate p x y| = |auxFunction1 p y x| := by rw [uCandidate_eq_Q3_leTwo p hQ3]
      _ ≤ auxGrowthConst p * (Real.rpow |y| p + Real.rpow |x| p) := haux
      _ = auxGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by ring
      _ ≤ uCandidateGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) :=
        mul_le_mul_of_nonneg_right hCaux hsum_nonneg
  · have haux := abs_auxFunction1_le_growth p hp1 hp2 (x := -y) (y := -x)
    calc
      |uCandidate p x y| = |auxFunction1 p (-y) (-x)| := by rw [uCandidate_eq_Q4_leTwo p hQ4]
      _ ≤ auxGrowthConst p * (Real.rpow |(-y)| p + Real.rpow |(-x)| p) := haux
      _ = auxGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by simp [add_comm]
      _ ≤ uCandidateGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) :=
        mul_le_mul_of_nonneg_right hCaux hsum_nonneg

private lemma uCandidate_growth_bound
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x y, |uCandidate p x y| ≤ C * (Real.rpow |x| p + Real.rpow |y| p) := by
  refine ⟨uCandidateGrowthConst p, uCandidateGrowthConst_nonneg p, ?_⟩
  intro x y
  exact abs_uCandidate_le_growth p hp1 hp2 x y

private def DxuA1GrowthConst (p : ℝ) : ℝ :=
  |alpha p| * (|p| / 2) * (|(p - 2) / (p - 1)| + 1)

private def DyuA1GrowthConst (p : ℝ) : ℝ :=
  |alpha p| * (|pStar p| / 2)

private def DvLeTwoGrowthConst (p : ℝ) : ℝ :=
  |p| / 2 * (1 + |coeffLeTwo p|)

private def auxDerivativeGrowthConst (p : ℝ) : ℝ :=
  max (max (DxuA1GrowthConst p) (DyuA1GrowthConst p)) (DvLeTwoGrowthConst p)

private def uCandidateDerivativeGrowthConst (p : ℝ) : ℝ :=
  max 0 (auxDerivativeGrowthConst p)

private lemma DxuA1GrowthConst_nonneg (p : ℝ) :
    0 ≤ DxuA1GrowthConst p := by
  unfold DxuA1GrowthConst
  positivity

private lemma DyuA1GrowthConst_nonneg (p : ℝ) :
    0 ≤ DyuA1GrowthConst p := by
  unfold DyuA1GrowthConst
  positivity

private lemma DvLeTwoGrowthConst_nonneg (p : ℝ) :
    0 ≤ DvLeTwoGrowthConst p := by
  unfold DvLeTwoGrowthConst
  positivity

private lemma auxDerivativeGrowthConst_nonneg (p : ℝ) :
    0 ≤ auxDerivativeGrowthConst p := by
  unfold auxDerivativeGrowthConst
  exact le_trans (DxuA1GrowthConst_nonneg p) (le_trans (le_max_left _ _) (le_max_left _ _))

private lemma uCandidateDerivativeGrowthConst_nonneg (p : ℝ) :
    0 ≤ uCandidateDerivativeGrowthConst p := by
  unfold uCandidateDerivativeGrowthConst
  exact le_max_left _ _

private lemma DxuA1GrowthConst_le_auxDerivativeGrowthConst (p : ℝ) :
    DxuA1GrowthConst p ≤ auxDerivativeGrowthConst p := by
  unfold auxDerivativeGrowthConst
  exact le_trans (le_max_left _ _) (le_max_left _ _)

private lemma DyuA1GrowthConst_le_auxDerivativeGrowthConst (p : ℝ) :
    DyuA1GrowthConst p ≤ auxDerivativeGrowthConst p := by
  unfold auxDerivativeGrowthConst
  exact le_trans (le_max_right _ _) (le_max_left _ _)

private lemma DvLeTwoGrowthConst_le_auxDerivativeGrowthConst (p : ℝ) :
    DvLeTwoGrowthConst p ≤ auxDerivativeGrowthConst p := by
  unfold auxDerivativeGrowthConst
  exact le_max_right _ _

private lemma auxDerivativeGrowthConst_le_uCandidateDerivativeGrowthConst (p : ℝ) :
    auxDerivativeGrowthConst p ≤ uCandidateDerivativeGrowthConst p := by
  unfold uCandidateDerivativeGrowthConst
  exact le_max_right _ _

private lemma abs_DxuA1_le_growth
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (h : closureA1 p x y) :
    |DxuA1 p x y| ≤ DxuA1GrowthConst p * Real.rpow x (p - 1) := by
  rcases h with ⟨hx, hlow, hup⟩
  by_cases hxpos : 0 < x
  · have hyabs : |y| ≤ x := by
      exact closureA1_abs_y_le_x p hp1 hp2 ⟨hx, hlow, hup⟩
    have hbr :
        |((p - 2) / (p - 1)) * x + y|
          ≤ (|(p - 2) / (p - 1)| + 1) * x := by
      have htmp :
          |((p - 2) / (p - 1)) * x + y|
            ≤ |((p - 2) / (p - 1)) * x| + |y| :=
        abs_add_le _ _
      have hx_abs : |x| = x := abs_of_nonneg hx
      calc
        |((p - 2) / (p - 1)) * x + y|
            ≤ |((p - 2) / (p - 1)) * x| + |y| := htmp
        _ = |(p - 2) / (p - 1)| * x + |y| := by rw [abs_mul, hx_abs]
        _ ≤ |(p - 2) / (p - 1)| * x + x := by gcongr
        _ = (|(p - 2) / (p - 1)| + 1) * x := by ring
    have hpow : Real.rpow x (p - 2) * x = Real.rpow x (p - 1) := by
      calc
        Real.rpow x (p - 2) * x
            = Real.rpow x (p - 2) * Real.rpow x (1 : ℝ) := by simp [Real.rpow_one]
        _ = Real.rpow x ((p - 2) + 1) := by
              simpa using (Real.rpow_add hxpos (p - 2) 1).symm
        _ = Real.rpow x (p - 1) := by ring_nf
    have hpow_nonneg : 0 ≤ Real.rpow x (p - 2) := Real.rpow_nonneg hx _
    calc
      |DxuA1 p x y|
          = |alpha p| * (|p| / 2) * Real.rpow x (p - 2) *
              |((p - 2) / (p - 1)) * x + y| := by
            simp only [DxuA1, hxpos, if_true]
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hpow_nonneg]
            rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      _ ≤ |alpha p| * (|p| / 2) * Real.rpow x (p - 2) *
            ((|(p - 2) / (p - 1)| + 1) * x) := by gcongr
      _ = DxuA1GrowthConst p * Real.rpow x (p - 1) := by
            unfold DxuA1GrowthConst
            rw [← hpow]
            ring
  · have h00 : x = 0 ∧ y = 0 := closureA1_x0_y0 p x y ⟨hx, hlow, hup⟩ hxpos
    rcases h00 with ⟨rfl, rfl⟩
    have hnonneg : 0 ≤ DxuA1GrowthConst p * Real.rpow 0 (p - 1) :=
      mul_nonneg (DxuA1GrowthConst_nonneg p) (Real.rpow_nonneg le_rfl _)
    simpa [DxuA1] using hnonneg

private lemma abs_DyuA1_le_growth
    (p : ℝ) {x y : ℝ} (h : closureA1 p x y) :
    |DyuA1 p x y| ≤ DyuA1GrowthConst p * Real.rpow x (p - 1) := by
  rcases h with ⟨hx, hlow, hup⟩
  by_cases hxpos : 0 < x
  · have hpow_nonneg : 0 ≤ Real.rpow x (p - 1) := Real.rpow_nonneg hx _
    calc
      |DyuA1 p x y|
          = |alpha p| * Real.rpow x (p - 1) * (|pStar p| / 2) := by
            simp only [DyuA1, hxpos, if_true]
            rw [abs_mul, abs_mul, abs_of_nonneg hpow_nonneg]
            rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      _ ≤ DyuA1GrowthConst p * Real.rpow x (p - 1) := by
            unfold DyuA1GrowthConst
            ring_nf
            exact le_rfl
  · have h00 : x = 0 ∧ y = 0 := closureA1_x0_y0 p x y ⟨hx, hlow, hup⟩ hxpos
    rcases h00 with ⟨rfl, rfl⟩
    have hnonneg : 0 ≤ DyuA1GrowthConst p * Real.rpow 0 (p - 1) :=
      mul_nonneg (DyuA1GrowthConst_nonneg p) (Real.rpow_nonneg le_rfl _)
    simpa [DyuA1] using hnonneg

private lemma abs_DxvLeTwo_le_growth_on_closureA2
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (h : closureA2 p x y) :
    |DxvLeTwo p x y| ≤ DvLeTwoGrowthConst p * Real.rpow x (p - 1) := by
  rcases h with ⟨hx, hlow, hup⟩
  by_cases hxpos : 0 < x
  · have hsum : |(x + y) / 2| ≤ x :=
      closureA2_abs_add_div_two_le_x p hp1 hp2 ⟨hx, hlow, hup⟩
    have hdiff : |(x - y) / 2| ≤ x :=
      closureA2_abs_sub_div_two_le_x p hp1 hp2 ⟨hx, hlow, hup⟩
    have hp1_nonneg : 0 ≤ p - 1 := by linarith
    have hsum_pow :
        Real.rpow |(x + y) / 2| (p - 1) ≤ Real.rpow x (p - 1) :=
      Real.rpow_le_rpow (abs_nonneg _) hsum hp1_nonneg
    have hdiff_pow :
        Real.rpow |(x - y) / 2| (p - 1) ≤ Real.rpow x (p - 1) :=
      Real.rpow_le_rpow (abs_nonneg _) hdiff hp1_nonneg
    calc
      |DxvLeTwo p x y|
          ≤ |p| / 2 * Real.rpow |(x + y) / 2| (p - 1) +
              |coeffLeTwo p| * (|p| / 2) *
                Real.rpow |(x - y) / 2| (p - 1) := by
            unfold DxvLeTwo
            simp only [hxpos, if_true]
            calc
              |Real.rpow |(x + y) / 2| (p - 1) * (p / 2) -
                  coeffLeTwo p * Real.rpow |(x - y) / 2| (p - 1) * (p / 2)|
                  ≤ |Real.rpow |(x + y) / 2| (p - 1) * (p / 2)| +
                      |coeffLeTwo p * Real.rpow |(x - y) / 2| (p - 1) * (p / 2)| := by
                    simpa [sub_eq_add_neg] using
                      abs_add_le
                        (Real.rpow |(x + y) / 2| (p - 1) * (p / 2))
                        (-(coeffLeTwo p *
                          Real.rpow |(x - y) / 2| (p - 1) * (p / 2)))
              _ = |p| / 2 * Real.rpow |(x + y) / 2| (p - 1) +
                    |coeffLeTwo p| * (|p| / 2) *
                      Real.rpow |(x - y) / 2| (p - 1) := by
                    have hA :
                        |Real.rpow |(x + y) / 2| (p - 1) * (p / 2)| =
                          |p| / 2 * Real.rpow |(x + y) / 2| (p - 1) := by
                      have hpow_nonneg :
                          0 ≤ Real.rpow (|x + y| / 2) (p - 1) :=
                        Real.rpow_nonneg (by positivity) _
                      rw [abs_mul, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
                      rw [abs_of_nonneg hpow_nonneg]
                      have hp_div : |p / 2| = |p| / 2 := by
                        rw [abs_div, abs_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num)]
                      rw [hp_div]
                      ring
                    have hB :
                        |coeffLeTwo p * Real.rpow |(x - y) / 2| (p - 1) * (p / 2)| =
                          |coeffLeTwo p| * (|p| / 2) *
                            Real.rpow |(x - y) / 2| (p - 1) := by
                      have hpow_nonneg :
                          0 ≤ Real.rpow (|x - y| / 2) (p - 1) :=
                        Real.rpow_nonneg (by positivity) _
                      rw [abs_mul, abs_mul, abs_div,
                        abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
                      rw [abs_of_nonneg hpow_nonneg]
                      have hp_div : |p / 2| = |p| / 2 := by
                        rw [abs_div, abs_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num)]
                      rw [hp_div]
                      ring
                    rw [hA, hB]
      _ ≤ |p| / 2 * Real.rpow x (p - 1) +
              |coeffLeTwo p| * (|p| / 2) * Real.rpow x (p - 1) := by
            gcongr
      _ = DvLeTwoGrowthConst p * Real.rpow x (p - 1) := by
            unfold DvLeTwoGrowthConst
            ring
  · have h00 : x = 0 ∧ y = 0 := closureA2_x0_y0 p x y ⟨hx, hlow, hup⟩ hxpos
    rcases h00 with ⟨rfl, rfl⟩
    have hnonneg : 0 ≤ DvLeTwoGrowthConst p * Real.rpow 0 (p - 1) :=
      mul_nonneg (DvLeTwoGrowthConst_nonneg p) (Real.rpow_nonneg le_rfl _)
    simpa [DxvLeTwo] using hnonneg

private lemma abs_DyvLeTwo_le_growth_on_closureA2
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} (h : closureA2 p x y) :
    |DyvLeTwo p x y| ≤ DvLeTwoGrowthConst p * Real.rpow x (p - 1) := by
  rcases h with ⟨hx, hlow, hup⟩
  by_cases hxpos : 0 < x
  · have hsum : |(x + y) / 2| ≤ x :=
      closureA2_abs_add_div_two_le_x p hp1 hp2 ⟨hx, hlow, hup⟩
    have hdiff : |(x - y) / 2| ≤ x :=
      closureA2_abs_sub_div_two_le_x p hp1 hp2 ⟨hx, hlow, hup⟩
    have hp1_nonneg : 0 ≤ p - 1 := by linarith
    have hsum_pow :
        Real.rpow |(x + y) / 2| (p - 1) ≤ Real.rpow x (p - 1) :=
      Real.rpow_le_rpow (abs_nonneg _) hsum hp1_nonneg
    have hdiff_pow :
        Real.rpow |(x - y) / 2| (p - 1) ≤ Real.rpow x (p - 1) :=
      Real.rpow_le_rpow (abs_nonneg _) hdiff hp1_nonneg
    calc
      |DyvLeTwo p x y|
          ≤ |p| / 2 * Real.rpow |(x + y) / 2| (p - 1) +
              |coeffLeTwo p| * (|p| / 2) *
                Real.rpow |(x - y) / 2| (p - 1) := by
            unfold DyvLeTwo
            simp only [hxpos, if_true]
            calc
              |Real.rpow |(x + y) / 2| (p - 1) * (p / 2) +
                  coeffLeTwo p * Real.rpow |(x - y) / 2| (p - 1) * (p / 2)|
                  ≤ |Real.rpow |(x + y) / 2| (p - 1) * (p / 2)| +
                      |coeffLeTwo p * Real.rpow |(x - y) / 2| (p - 1) * (p / 2)| :=
                    abs_add_le _ _
              _ = |p| / 2 * Real.rpow |(x + y) / 2| (p - 1) +
                    |coeffLeTwo p| * (|p| / 2) *
                      Real.rpow |(x - y) / 2| (p - 1) := by
                    have hA :
                        |Real.rpow |(x + y) / 2| (p - 1) * (p / 2)| =
                          |p| / 2 * Real.rpow |(x + y) / 2| (p - 1) := by
                      have hpow_nonneg :
                          0 ≤ Real.rpow (|x + y| / 2) (p - 1) :=
                        Real.rpow_nonneg (by positivity) _
                      rw [abs_mul, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
                      rw [abs_of_nonneg hpow_nonneg]
                      have hp_div : |p / 2| = |p| / 2 := by
                        rw [abs_div, abs_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num)]
                      rw [hp_div]
                      ring
                    have hB :
                        |coeffLeTwo p * Real.rpow |(x - y) / 2| (p - 1) * (p / 2)| =
                          |coeffLeTwo p| * (|p| / 2) *
                            Real.rpow |(x - y) / 2| (p - 1) := by
                      have hpow_nonneg :
                          0 ≤ Real.rpow (|x - y| / 2) (p - 1) :=
                        Real.rpow_nonneg (by positivity) _
                      rw [abs_mul, abs_mul, abs_div,
                        abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
                      rw [abs_of_nonneg hpow_nonneg]
                      have hp_div : |p / 2| = |p| / 2 := by
                        rw [abs_div, abs_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num)]
                      rw [hp_div]
                      ring
                    rw [hA, hB]
      _ ≤ |p| / 2 * Real.rpow x (p - 1) +
              |coeffLeTwo p| * (|p| / 2) * Real.rpow x (p - 1) := by
            gcongr
      _ = DvLeTwoGrowthConst p * Real.rpow x (p - 1) := by
            unfold DvLeTwoGrowthConst
            ring
  · have h00 : x = 0 ∧ y = 0 := closureA2_x0_y0 p x y ⟨hx, hlow, hup⟩ hxpos
    rcases h00 with ⟨rfl, rfl⟩
    have hnonneg : 0 ≤ DvLeTwoGrowthConst p * Real.rpow 0 (p - 1) :=
      mul_nonneg (DvLeTwoGrowthConst_nonneg p) (Real.rpow_nonneg le_rfl _)
    simpa [DyvLeTwo] using hnonneg

private lemma abs_DxauxFunction1_le_growth
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} :
    |DxauxFunction1 p x y|
      ≤ auxDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by
  by_cases h1 : closureA1 p x y
  · have hx : 0 ≤ x := h1.1
    have hx_abs : |x| = x := abs_of_nonneg hx
    calc
      |DxauxFunction1 p x y| = |DxuA1 p x y| := by
        rw [auxFunction1_Dx_eq_DxuA1 p x y h1]
      _ ≤ DxuA1GrowthConst p * Real.rpow x (p - 1) :=
        abs_DxuA1_le_growth p hp1 hp2 h1
      _ ≤ auxDerivativeGrowthConst p * Real.rpow |x| (p - 1) := by
        rw [hx_abs]
        exact mul_le_mul_of_nonneg_right
          (DxuA1GrowthConst_le_auxDerivativeGrowthConst p)
          (Real.rpow_nonneg hx _)
      _ ≤ auxDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg y) _))
          (auxDerivativeGrowthConst_nonneg p)
  · by_cases h2 : closureA2 p x y
    · have hx : 0 ≤ x := h2.1
      have hx_abs : |x| = x := abs_of_nonneg hx
      calc
        |DxauxFunction1 p x y| = |DxvLeTwo p x y| := by
          rw [auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 x y h2]
        _ ≤ DvLeTwoGrowthConst p * Real.rpow x (p - 1) :=
          abs_DxvLeTwo_le_growth_on_closureA2 p hp1 hp2 h2
        _ ≤ auxDerivativeGrowthConst p * Real.rpow |x| (p - 1) := by
          rw [hx_abs]
          exact mul_le_mul_of_nonneg_right
            (DvLeTwoGrowthConst_le_auxDerivativeGrowthConst p)
            (Real.rpow_nonneg hx _)
        _ ≤ auxDerivativeGrowthConst p *
            (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by
          exact mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg y) _))
            (auxDerivativeGrowthConst_nonneg p)
    · have hnonneg :
          0 ≤ auxDerivativeGrowthConst p *
            (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by
        exact mul_nonneg (auxDerivativeGrowthConst_nonneg p)
          (add_nonneg (Real.rpow_nonneg (abs_nonneg x) _)
            (Real.rpow_nonneg (abs_nonneg y) _))
      simpa [DxauxFunction1, h1, h2] using hnonneg

private lemma abs_DyauxFunction1_le_growth
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) {x y : ℝ} :
    |DyauxFunction1 p x y|
      ≤ auxDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by
  by_cases h1 : closureA1 p x y
  · have hx : 0 ≤ x := h1.1
    have hx_abs : |x| = x := abs_of_nonneg hx
    calc
      |DyauxFunction1 p x y| = |DyuA1 p x y| := by
        rw [auxFunction1_Dy_eq_DyuA1 p x y h1]
      _ ≤ DyuA1GrowthConst p * Real.rpow x (p - 1) :=
        abs_DyuA1_le_growth p h1
      _ ≤ auxDerivativeGrowthConst p * Real.rpow |x| (p - 1) := by
        rw [hx_abs]
        exact mul_le_mul_of_nonneg_right
          (DyuA1GrowthConst_le_auxDerivativeGrowthConst p)
          (Real.rpow_nonneg hx _)
      _ ≤ auxDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg y) _))
          (auxDerivativeGrowthConst_nonneg p)
  · by_cases h2 : closureA2 p x y
    · have hx : 0 ≤ x := h2.1
      have hx_abs : |x| = x := abs_of_nonneg hx
      calc
        |DyauxFunction1 p x y| = |DyvLeTwo p x y| := by
          rw [auxFunction1_Dy_eq_DyvLeTwo_leTwo p hp1 hp2 x y h2]
        _ ≤ DvLeTwoGrowthConst p * Real.rpow x (p - 1) :=
          abs_DyvLeTwo_le_growth_on_closureA2 p hp1 hp2 h2
        _ ≤ auxDerivativeGrowthConst p * Real.rpow |x| (p - 1) := by
          rw [hx_abs]
          exact mul_le_mul_of_nonneg_right
            (DvLeTwoGrowthConst_le_auxDerivativeGrowthConst p)
            (Real.rpow_nonneg hx _)
        _ ≤ auxDerivativeGrowthConst p *
            (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by
          exact mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg y) _))
            (auxDerivativeGrowthConst_nonneg p)
    · have hnonneg :
          0 ≤ auxDerivativeGrowthConst p *
            (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by
        exact mul_nonneg (auxDerivativeGrowthConst_nonneg p)
          (add_nonneg (Real.rpow_nonneg (abs_nonneg x) _)
            (Real.rpow_nonneg (abs_nonneg y) _))
      simpa [DyauxFunction1, h1, h2] using hnonneg

private lemma abs_DxuCandidate_le_growth
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) :
    |DxuCandidate p x y|
      ≤ uCandidateDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by
  have hC : auxDerivativeGrowthConst p ≤ uCandidateDerivativeGrowthConst p :=
    auxDerivativeGrowthConst_le_uCandidateDerivativeGrowthConst p
  have hsum_nonneg :
      0 ≤ Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1) :=
    add_nonneg (Real.rpow_nonneg (abs_nonneg x) _)
      (Real.rpow_nonneg (abs_nonneg y) _)
  rcases mem_some_QuarterPlane_leTwo x y with hQ1 | hrest
  · have haux := abs_DxauxFunction1_le_growth p hp1 hp2 (x := x) (y := y)
    calc
      |DxuCandidate p x y| = |DxauxFunction1 p x y| := by
        rw [DxuCandidate_eq_Q1_leTwo p hQ1]
      _ ≤ auxDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := haux
      _ ≤ uCandidateDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) :=
        mul_le_mul_of_nonneg_right hC hsum_nonneg
  rcases hrest with hQ2 | hrest
  · have haux := abs_DxauxFunction1_le_growth p hp1 hp2 (x := -x) (y := -y)
    calc
      |DxuCandidate p x y| = |DxauxFunction1 p (-x) (-y)| := by
        rw [DxuCandidate_eq_Q2_leTwo p hQ2, abs_neg]
      _ ≤ auxDerivativeGrowthConst p *
          (Real.rpow |(-x)| (p - 1) + Real.rpow |(-y)| (p - 1)) := haux
      _ = auxDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by simp
      _ ≤ uCandidateDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) :=
        mul_le_mul_of_nonneg_right hC hsum_nonneg
  rcases hrest with hQ3 | hQ4
  · have haux := abs_DyauxFunction1_le_growth p hp1 hp2 (x := y) (y := x)
    calc
      |DxuCandidate p x y| = |DyauxFunction1 p y x| := by
        rw [DxuCandidate_eq_Q3_leTwo p hp1 hp2 hQ3]
      _ ≤ auxDerivativeGrowthConst p *
          (Real.rpow |y| (p - 1) + Real.rpow |x| (p - 1)) := haux
      _ = auxDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by ring
      _ ≤ uCandidateDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) :=
        mul_le_mul_of_nonneg_right hC hsum_nonneg
  · have haux := abs_DyauxFunction1_le_growth p hp1 hp2 (x := -y) (y := -x)
    calc
      |DxuCandidate p x y| = |DyauxFunction1 p (-y) (-x)| := by
        rw [DxuCandidate_eq_Q4_leTwo p hp1 hp2 hQ4, abs_neg]
      _ ≤ auxDerivativeGrowthConst p *
          (Real.rpow |(-y)| (p - 1) + Real.rpow |(-x)| (p - 1)) := haux
      _ = auxDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by simp [add_comm]
      _ ≤ uCandidateDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) :=
        mul_le_mul_of_nonneg_right hC hsum_nonneg

private lemma abs_DyuCandidate_le_growth
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (x y : ℝ) :
    |DyuCandidate p x y|
      ≤ uCandidateDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by
  have h := abs_DxuCandidate_le_growth p hp1 hp2 y x
  rw [DyuCandidate_eq_DxuCandidate_swap_leTwo p hp1 hp2 x y]
  simpa [add_comm] using h

private lemma uCandidate_derivative_growth_bound
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x y,
        |DxuCandidate p x y| ≤
          C * (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1))) ∧
      (∀ x y,
        |DyuCandidate p x y| ≤
          C * (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1))) := by
  refine ⟨uCandidateDerivativeGrowthConst p, uCandidateDerivativeGrowthConst_nonneg p, ?_, ?_⟩
  · intro x y
    exact abs_DxuCandidate_le_growth p hp1 hp2 x y
  · intro x y
    exact abs_DyuCandidate_le_growth p hp1 hp2 x y

/-! ## Continuity of the glued candidate and its first partials -/

private lemma uA1_eq_smooth_of_nonneg_leTwo
    (p : ℝ) (hp1 : 1 < p) (x y : ℝ) (hx : 0 ≤ x) :
    uA1 p x y = alpha p * Real.rpow x (p - 1) *
      (x - pStar p * (x - y) / 2) := by
  have hexp_ne : p - 1 ≠ 0 := by linarith
  unfold uA1
  rcases hx.lt_or_eq with hxpos | hxeq
  · exact if_pos hxpos
  · subst x
    simp [Real.zero_rpow hexp_ne]

private lemma continuousOn_uA1_leTwo (p : ℝ) (hp1 : 1 < p) :
    ContinuousOn (fun z : ℝ × ℝ => uA1 p z.1 z.2) {z | 0 ≤ z.1} := by
  have hexp_nonneg : 0 ≤ p - 1 := by linarith
  have heq : ∀ z : ℝ × ℝ, z ∈ {z : ℝ × ℝ | 0 ≤ z.1} →
      uA1 p z.1 z.2 =
        alpha p * Real.rpow z.1 (p - 1) * (z.1 - pStar p * (z.1 - z.2) / 2) :=
    fun ⟨x, y⟩ hx => uA1_eq_smooth_of_nonneg_leTwo p hp1 x y hx
  apply ContinuousOn.congr _ heq
  apply ContinuousOn.mul
  · exact continuousOn_const.mul
      (continuousOn_fst.rpow_const fun _ _ => Or.inr hexp_nonneg)
  · exact continuousOn_fst.sub
      ((continuousOn_const.mul (continuousOn_fst.sub continuousOn_snd)).div_const 2)

private lemma isClosed_closureA1_set_leTwo (p : ℝ) :
    IsClosed {z : ℝ × ℝ | closureA1 p z.1 z.2} := by
  simp only [closureA1]
  apply IsClosed.inter
  · exact isClosed_le continuous_const continuous_fst
  apply IsClosed.inter
  · exact isClosed_le continuous_fst.neg continuous_snd
  · exact isClosed_le continuous_snd (continuous_const.mul continuous_fst)

private lemma isClosed_closureA2_set_leTwo (p : ℝ) :
    IsClosed {z : ℝ × ℝ | closureA2 p z.1 z.2} := by
  simp only [closureA2]
  apply IsClosed.inter
  · exact isClosed_le continuous_const continuous_fst
  apply IsClosed.inter
  · exact isClosed_le (continuous_const.mul continuous_fst) continuous_snd
  · exact isClosed_le continuous_snd continuous_fst

private lemma continuousOn_DxuA1_closureA1_leTwo
    (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    ContinuousOn (DxuA1Fun p) (closureA1Set p) := by
  intro z hz
  rcases z with ⟨x, y⟩
  rcases hz with ⟨hx, hlow, hup⟩
  by_cases hx0 : 0 < x
  · have hpos : {w : ℝ × ℝ | 0 < w.1} ∈ nhds (x, y) := by
      exact continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx0)
    have hEvent :
        DxuA1Fun p =ᶠ[nhds (x, y)]
          fun w : ℝ × ℝ =>
            alpha p * (p / 2) * Real.rpow w.1 (p - 2) *
              (((p - 2) / (p - 1)) * w.1 + w.2) := by
      filter_upwards [hpos] with w hw
      simp [DxuA1Fun, DxuA1, hw]
    have hcont_rpow :
        ContinuousAt (fun w : ℝ × ℝ => Real.rpow w.1 (p - 2)) (x, y) :=
      continuous_fst.continuousAt.rpow_const (Or.inl (ne_of_gt hx0))
    have hcont :
        ContinuousAt
          (fun w : ℝ × ℝ =>
            alpha p * (p / 2) * Real.rpow w.1 (p - 2) *
              (((p - 2) / (p - 1)) * w.1 + w.2)) (x, y) := by
      have hlin :
          ContinuousAt (fun w : ℝ × ℝ => ((p - 2) / (p - 1)) * w.1 + w.2) (x, y) := by
        exact (continuous_const.mul continuous_fst).continuousAt.add continuous_snd.continuousAt
      have halpha :
          ContinuousAt (fun _ : ℝ × ℝ => alpha p) (x, y) :=
        continuous_const.continuousAt
      have hpdiv :
          ContinuousAt (fun _ : ℝ × ℝ => p / 2) (x, y) :=
        continuous_const.continuousAt
      exact ((halpha.mul hpdiv).mul hcont_rpow).mul hlin
    exact (hcont.congr_of_eventuallyEq hEvent).continuousWithinAt
  · have h00 := closureA1_x0_y0 p x y ⟨hx, hlow, hup⟩ hx0
    rcases h00 with ⟨rfl, rfl⟩
    rw [ContinuousWithinAt, DxuA1Fun]
    simp only [DxuA1, lt_irrefl, ite_false]
    rw [tendsto_zero_iff_abs_tendsto_zero]
    let C : ℝ := DxuA1GrowthConst p
    have hbound :
        ∀ᶠ z : ℝ × ℝ in nhdsWithin (0, 0) (closureA1Set p),
          |DxuA1Fun p z| ≤ C * Real.rpow z.1 (p - 1) := by
      refine Filter.mem_of_superset self_mem_nhdsWithin ?_
      intro z hz'
      simpa [closureA1Set, DxuA1Fun, C] using
        abs_DxuA1_le_growth p hp1 hp2 (x := z.1) (y := z.2) hz'
    have hrpow :
        Filter.Tendsto (fun z : ℝ × ℝ => Real.rpow z.1 (p - 1))
          (nhdsWithin (0, 0) (closureA1Set p)) (nhds 0) := by
      have hcont :
          ContinuousAt (fun z : ℝ × ℝ => Real.rpow z.1 (p - 1)) (0, 0) :=
        continuous_fst.continuousAt.rpow_const (Or.inr (by linarith : 0 ≤ p - 1))
      have hzero : Real.rpow (0 : ℝ) (p - 1) = 0 := Real.zero_rpow (by linarith)
      have ht : Filter.Tendsto (fun z : ℝ × ℝ => Real.rpow z.1 (p - 1))
          (nhds (0, 0)) (nhds 0) := by
        convert hcont.tendsto using 1
        simpa using hzero.symm
      exact ht.mono_left nhdsWithin_le_nhds
    have hmajor :
        Filter.Tendsto (fun z : ℝ × ℝ => C * Real.rpow z.1 (p - 1))
          (nhdsWithin (0, 0) (closureA1Set p)) (nhds 0) := by
      simpa using tendsto_const_nhds.mul hrpow
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) hbound hmajor

private lemma continuousOn_DyuA1_closureA1_leTwo
    (p : ℝ) (hp1 : 1 < p) :
    ContinuousOn (DyuA1Fun p) (closureA1Set p) := by
  intro z hz
  rcases z with ⟨x, y⟩
  rcases hz with ⟨hx, hlow, hup⟩
  by_cases hx0 : 0 < x
  · have hpos : {w : ℝ × ℝ | 0 < w.1} ∈ nhds (x, y) := by
      exact continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx0)
    have hEvent :
        DyuA1Fun p =ᶠ[nhds (x, y)]
          fun w : ℝ × ℝ => alpha p * Real.rpow w.1 (p - 1) * (pStar p / 2) := by
      filter_upwards [hpos] with w hw
      simp [DyuA1Fun, DyuA1, hw]
    have hcont :
        ContinuousAt
          (fun w : ℝ × ℝ => alpha p * Real.rpow w.1 (p - 1) * (pStar p / 2))
          (x, y) := by
      have hcont_rpow :
          ContinuousAt (fun w : ℝ × ℝ => Real.rpow w.1 (p - 1)) (x, y) :=
        continuous_fst.continuousAt.rpow_const (Or.inl (ne_of_gt hx0))
      exact (continuous_const.continuousAt.mul hcont_rpow).mul continuous_const.continuousAt
    exact (hcont.congr_of_eventuallyEq hEvent).continuousWithinAt
  · have h00 := closureA1_x0_y0 p x y ⟨hx, hlow, hup⟩ hx0
    rcases h00 with ⟨rfl, rfl⟩
    rw [ContinuousWithinAt, DyuA1Fun]
    simp only [DyuA1, lt_irrefl, ite_false]
    rw [tendsto_zero_iff_abs_tendsto_zero]
    let C : ℝ := DyuA1GrowthConst p
    have hbound :
        ∀ᶠ z : ℝ × ℝ in nhdsWithin (0, 0) (closureA1Set p),
          |DyuA1Fun p z| ≤ C * Real.rpow z.1 (p - 1) := by
      refine Filter.mem_of_superset self_mem_nhdsWithin ?_
      intro z hz'
      simpa [closureA1Set, DyuA1Fun, C] using
        abs_DyuA1_le_growth p (x := z.1) (y := z.2) hz'
    have hrpow :
        Filter.Tendsto (fun z : ℝ × ℝ => Real.rpow z.1 (p - 1))
          (nhdsWithin (0, 0) (closureA1Set p)) (nhds 0) := by
      have hcont :
          ContinuousAt (fun z : ℝ × ℝ => Real.rpow z.1 (p - 1)) (0, 0) :=
        continuous_fst.continuousAt.rpow_const (Or.inr (by linarith : 0 ≤ p - 1))
      have hzero : Real.rpow (0 : ℝ) (p - 1) = 0 := Real.zero_rpow (by linarith)
      have ht : Filter.Tendsto (fun z : ℝ × ℝ => Real.rpow z.1 (p - 1))
          (nhds (0, 0)) (nhds 0) := by
        convert hcont.tendsto using 1
        simpa using hzero.symm
      exact ht.mono_left nhdsWithin_le_nhds
    have hmajor :
        Filter.Tendsto (fun z : ℝ × ℝ => C * Real.rpow z.1 (p - 1))
          (nhdsWithin (0, 0) (closureA1Set p)) (nhds 0) := by
      simpa using tendsto_const_nhds.mul hrpow
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) hbound hmajor

private lemma DxvLeTwo_eq_formula_on_closureA2_leTwo
    (p : ℝ) (hp1 : 1 < p) (z : ℝ × ℝ) (hz : z ∈ closureA2Set p) :
    DxvLeTwoFun p z = DxvLeTwoFormula p z := by
  rcases z with ⟨x, y⟩
  rcases hz with ⟨hx, hlow, hup⟩
  by_cases hx0 : 0 < x
  · simp [DxvLeTwoFun, DxvLeTwoFormula, DxvLeTwo, hx0]
  · have h00 := closureA2_x0_y0 p x y ⟨hx, hlow, hup⟩ hx0
    rcases h00 with ⟨rfl, rfl⟩
    have hp1_ne : p - 1 ≠ 0 := by linarith
    have hzero : Real.rpow (0 : ℝ) (p - 1) = 0 := Real.zero_rpow hp1_ne
    simp [DxvLeTwoFun, DxvLeTwoFormula, DxvLeTwo, Real.zero_rpow hp1_ne]

private lemma DyvLeTwo_eq_formula_on_closureA2_leTwo
    (p : ℝ) (hp1 : 1 < p) (z : ℝ × ℝ) (hz : z ∈ closureA2Set p) :
    DyvLeTwoFun p z = DyvLeTwoFormula p z := by
  rcases z with ⟨x, y⟩
  rcases hz with ⟨hx, hlow, hup⟩
  by_cases hx0 : 0 < x
  · simp [DyvLeTwoFun, DyvLeTwoFormula, DyvLeTwo, hx0]
  · have h00 := closureA2_x0_y0 p x y ⟨hx, hlow, hup⟩ hx0
    rcases h00 with ⟨rfl, rfl⟩
    have hp1_ne : p - 1 ≠ 0 := by linarith
    have hzero : Real.rpow (0 : ℝ) (p - 1) = 0 := Real.zero_rpow hp1_ne
    simp [DyvLeTwoFun, DyvLeTwoFormula, DyvLeTwo, Real.zero_rpow hp1_ne]

private lemma continuousOn_DxvLeTwo_closureA2_leTwo
    (p : ℝ) (hp1 : 1 < p) :
    ContinuousOn (DxvLeTwoFun p) (closureA2Set p) := by
  have hp1_nonneg : 0 ≤ p - 1 := by linarith
  have hcont : Continuous (DxvLeTwoFormula p) := by
    have hsum :
        Continuous (fun z : ℝ × ℝ => Real.rpow (|((z.1 + z.2) / 2)|) (p - 1)) := by
      exact Continuous.rpow_const (((continuous_fst.add continuous_snd).div_const 2).abs)
        (fun _ => Or.inr hp1_nonneg)
    have hdiff :
        Continuous (fun z : ℝ × ℝ => Real.rpow (|((z.1 - z.2) / 2)|) (p - 1)) := by
      exact Continuous.rpow_const (((continuous_fst.sub continuous_snd).div_const 2).abs)
        (fun _ => Or.inr hp1_nonneg)
    have htmp :
        Continuous (fun z : ℝ × ℝ =>
          Real.rpow (|((z.1 + z.2) / 2)|) (p - 1) * (p / 2)
            - coeffLeTwo p * Real.rpow (|((z.1 - z.2) / 2)|) (p - 1) * (p / 2)) :=
      (hsum.mul (continuous_const : Continuous (fun _ : ℝ × ℝ => (p / 2 : ℝ)))).sub
        (((continuous_const : Continuous (fun _ : ℝ × ℝ => coeffLeTwo p)).mul hdiff).mul
          (continuous_const : Continuous (fun _ : ℝ × ℝ => (p / 2 : ℝ))))
    unfold DxvLeTwoFormula
    exact htmp
  apply ContinuousOn.congr hcont.continuousOn
  intro z hz
  exact DxvLeTwo_eq_formula_on_closureA2_leTwo p hp1 z hz

private lemma continuousOn_DyvLeTwo_closureA2_leTwo
    (p : ℝ) (hp1 : 1 < p) :
    ContinuousOn (DyvLeTwoFun p) (closureA2Set p) := by
  have hp1_nonneg : 0 ≤ p - 1 := by linarith
  have hcont : Continuous (DyvLeTwoFormula p) := by
    have hsum :
        Continuous (fun z : ℝ × ℝ => Real.rpow (|((z.1 + z.2) / 2)|) (p - 1)) := by
      exact Continuous.rpow_const (((continuous_fst.add continuous_snd).div_const 2).abs)
        (fun _ => Or.inr hp1_nonneg)
    have hdiff :
        Continuous (fun z : ℝ × ℝ => Real.rpow (|((z.1 - z.2) / 2)|) (p - 1)) := by
      exact Continuous.rpow_const (((continuous_fst.sub continuous_snd).div_const 2).abs)
        (fun _ => Or.inr hp1_nonneg)
    have htmp :
        Continuous (fun z : ℝ × ℝ =>
          Real.rpow (|((z.1 + z.2) / 2)|) (p - 1) * (p / 2)
            + coeffLeTwo p * Real.rpow (|((z.1 - z.2) / 2)|) (p - 1) * (p / 2)) :=
      (hsum.mul (continuous_const : Continuous (fun _ : ℝ × ℝ => (p / 2 : ℝ)))).add
        (((continuous_const : Continuous (fun _ : ℝ × ℝ => coeffLeTwo p)).mul hdiff).mul
          (continuous_const : Continuous (fun _ : ℝ × ℝ => (p / 2 : ℝ))))
    unfold DyvLeTwoFormula
    exact htmp
  apply ContinuousOn.congr hcont.continuousOn
  intro z hz
  exact DyvLeTwo_eq_formula_on_closureA2_leTwo p hp1 z hz

private lemma continuousOn_auxFunction1_leTwo (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    ContinuousOn (fun z : ℝ × ℝ => auxFunction1 p z.1 z.2)
      {z | QuarterPlane z.1 z.2} := by
  let S : Set (ℝ × ℝ) := {z | QuarterPlane z.1 z.2}
  let S1 : Set (ℝ × ℝ) := {z | closureA1 p z.1 z.2}
  let S2 : Set (ℝ × ℝ) := {z | closureA2 p z.1 z.2}
  have hcover : S ⊆ S1 ∪ S2 := by
    intro ⟨x, y⟩ hz
    simp only [QuarterPlane, closureA1, closureA2, S, S1, S2,
      Set.mem_union, Set.mem_setOf_eq] at *
    rcases hz with ⟨hx, hyx, hneg⟩
    by_cases h : a p * x ≤ y
    · exact Or.inr ⟨hx, h, hyx⟩
    · exact Or.inl ⟨hx, hneg, le_of_lt (not_le.mp h)⟩
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => auxFunction1 p z.1 z.2) (S ∩ S1) := by
    apply ContinuousOn.congr ((continuousOn_uA1_leTwo p hp1).mono
      (fun z hz => hz.2.1))
    intro z hz
    exact auxFunction1_eq_uA1 p z.1 z.2 hz.2
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => auxFunction1 p z.1 z.2) (S ∩ S2) := by
    apply ContinuousOn.congr ((continuous_vLeTwo_leTwo p hp1).continuousOn.mono
      Set.inter_subset_left)
    intro z hz
    exact auxFunction1_eq_vLeTwo_leTwo p hp1 hp2 z.1 z.2 hz.2
  have hcl1 : IsClosed (S ∩ S1) := by
    apply IsClosed.inter _ (isClosed_closureA1_set_leTwo p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst.neg continuous_snd))
  have hcl2 : IsClosed (S ∩ S2) := by
    apply IsClosed.inter _ (isClosed_closureA2_set_leTwo p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst.neg continuous_snd))
  have hcover' : S ⊆ S ∩ S1 ∪ S ∩ S2 := fun z hz =>
    (hcover hz).imp (And.intro hz) (And.intro hz)
  apply ContinuousOn.mono _ hcover'
  exact hc1.union_of_isClosed hc2 hcl1 hcl2

private lemma continuousOn_DxauxFunction1_leTwo (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    ContinuousOn (fun z : ℝ × ℝ => DxauxFunction1 p z.1 z.2)
      {z | QuarterPlane z.1 z.2} := by
  let S : Set (ℝ × ℝ) := {z | QuarterPlane z.1 z.2}
  let S1 : Set (ℝ × ℝ) := {z | closureA1 p z.1 z.2}
  let S2 : Set (ℝ × ℝ) := {z | closureA2 p z.1 z.2}
  have hcover : S ⊆ S1 ∪ S2 := by
    intro ⟨x, y⟩ hz
    simp only [QuarterPlane, closureA1, closureA2, S, S1, S2,
      Set.mem_union, Set.mem_setOf_eq] at *
    rcases hz with ⟨hx, hyx, hneg⟩
    by_cases h : a p * x ≤ y
    · exact Or.inr ⟨hx, h, hyx⟩
    · exact Or.inl ⟨hx, hneg, le_of_lt (not_le.mp h)⟩
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => DxauxFunction1 p z.1 z.2) (S ∩ S1) := by
    apply ContinuousOn.congr ((continuousOn_DxuA1_closureA1_leTwo p hp1 hp2).mono
      (fun _ h => h.2))
    intro z hz
    exact auxFunction1_Dx_eq_DxuA1 p z.1 z.2 hz.2
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => DxauxFunction1 p z.1 z.2) (S ∩ S2) := by
    apply ContinuousOn.congr ((continuousOn_DxvLeTwo_closureA2_leTwo p hp1).mono
      (fun _ h => h.2))
    intro z hz
    exact auxFunction1_Dx_eq_DxvLeTwo_leTwo p hp1 hp2 z.1 z.2 hz.2
  have hcl1 : IsClosed (S ∩ S1) := by
    apply IsClosed.inter _ (isClosed_closureA1_set_leTwo p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst.neg continuous_snd))
  have hcl2 : IsClosed (S ∩ S2) := by
    apply IsClosed.inter _ (isClosed_closureA2_set_leTwo p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst.neg continuous_snd))
  have hcover' : S ⊆ S ∩ S1 ∪ S ∩ S2 := fun z hz =>
    (hcover hz).imp (And.intro hz) (And.intro hz)
  apply ContinuousOn.mono _ hcover'
  exact hc1.union_of_isClosed hc2 hcl1 hcl2

private lemma continuousOn_DyauxFunction1_leTwo (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    ContinuousOn (fun z : ℝ × ℝ => DyauxFunction1 p z.1 z.2)
      {z | QuarterPlane z.1 z.2} := by
  let S : Set (ℝ × ℝ) := {z | QuarterPlane z.1 z.2}
  let S1 : Set (ℝ × ℝ) := {z | closureA1 p z.1 z.2}
  let S2 : Set (ℝ × ℝ) := {z | closureA2 p z.1 z.2}
  have hcover : S ⊆ S1 ∪ S2 := by
    intro ⟨x, y⟩ hz
    simp only [QuarterPlane, closureA1, closureA2, S, S1, S2,
      Set.mem_union, Set.mem_setOf_eq] at *
    rcases hz with ⟨hx, hyx, hneg⟩
    by_cases h : a p * x ≤ y
    · exact Or.inr ⟨hx, h, hyx⟩
    · exact Or.inl ⟨hx, hneg, le_of_lt (not_le.mp h)⟩
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => DyauxFunction1 p z.1 z.2) (S ∩ S1) := by
    apply ContinuousOn.congr ((continuousOn_DyuA1_closureA1_leTwo p hp1).mono
      (fun _ h => h.2))
    intro z hz
    exact auxFunction1_Dy_eq_DyuA1 p z.1 z.2 hz.2
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => DyauxFunction1 p z.1 z.2) (S ∩ S2) := by
    apply ContinuousOn.congr ((continuousOn_DyvLeTwo_closureA2_leTwo p hp1).mono
      (fun _ h => h.2))
    intro z hz
    exact auxFunction1_Dy_eq_DyvLeTwo_leTwo p hp1 hp2 z.1 z.2 hz.2
  have hcl1 : IsClosed (S ∩ S1) := by
    apply IsClosed.inter _ (isClosed_closureA1_set_leTwo p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst.neg continuous_snd))
  have hcl2 : IsClosed (S ∩ S2) := by
    apply IsClosed.inter _ (isClosed_closureA2_set_leTwo p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst.neg continuous_snd))
  have hcover' : S ⊆ S ∩ S1 ∪ S ∩ S2 := fun z hz =>
    (hcover hz).imp (And.intro hz) (And.intro hz)
  apply ContinuousOn.mono _ hcover'
  exact hc1.union_of_isClosed hc2 hcl1 hcl2

private lemma isClosed_Q1_leTwo : IsClosed {z : ℝ × ℝ | QuarterPlane z.1 z.2} := by
  simp only [QuarterPlane, Set.setOf_and]
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_snd continuous_fst).inter
      (isClosed_le continuous_fst.neg continuous_snd))

private lemma isClosed_Q2_leTwo : IsClosed {z : ℝ × ℝ | QuarterPlane2 z.1 z.2} := by
  simp only [QuarterPlane2, Set.setOf_and]
  exact (isClosed_le continuous_fst continuous_const).inter
    ((isClosed_le continuous_snd continuous_fst.neg).inter
      (isClosed_le continuous_fst continuous_snd))

private lemma isClosed_Q3_leTwo : IsClosed {z : ℝ × ℝ | QuarterPlane3 z.1 z.2} := by
  simp only [QuarterPlane3, Set.setOf_and]
  exact (isClosed_le continuous_const continuous_snd).inter
    ((isClosed_le continuous_snd.neg continuous_fst).inter
      (isClosed_le continuous_fst continuous_snd))

private lemma isClosed_Q4_leTwo : IsClosed {z : ℝ × ℝ | QuarterPlane4 z.1 z.2} := by
  simp only [QuarterPlane4, Set.setOf_and]
  exact (isClosed_le continuous_snd continuous_const).inter
    ((isClosed_le continuous_snd continuous_fst).inter
      (isClosed_le continuous_fst continuous_snd.neg))

private lemma univ_subset_quarters_leTwo :
    Set.univ ⊆
      {z : ℝ × ℝ | QuarterPlane z.1 z.2} ∪
      {z : ℝ × ℝ | QuarterPlane2 z.1 z.2} ∪
      {z : ℝ × ℝ | QuarterPlane3 z.1 z.2} ∪
      {z : ℝ × ℝ | QuarterPlane4 z.1 z.2} := by
  intro z _
  rcases z with ⟨x, y⟩
  rcases mem_some_QuarterPlane_leTwo x y with hQ1 | hrest
  · exact Or.inl (Or.inl (Or.inl hQ1))
  rcases hrest with hQ2 | hrest
  · exact Or.inl (Or.inl (Or.inr hQ2))
  rcases hrest with hQ3 | hQ4
  · exact Or.inl (Or.inr hQ3)
  · exact Or.inr hQ4

private lemma continuousuCandidate_leTwo (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Set.univ := by
  let Q1 : Set (ℝ × ℝ) := {z | QuarterPlane z.1 z.2}
  let Q2 : Set (ℝ × ℝ) := {z | QuarterPlane2 z.1 z.2}
  let Q3 : Set (ℝ × ℝ) := {z | QuarterPlane3 z.1 z.2}
  let Q4 : Set (ℝ × ℝ) := {z | QuarterPlane4 z.1 z.2}
  have hcont1 : ContinuousOn (fun z : ℝ × ℝ => auxFunction1 p z.1 z.2) Q1 := by
    simpa [Q1] using continuousOn_auxFunction1_leTwo p hp1 hp2
  have hcont2 : ContinuousOn (fun z : ℝ × ℝ => auxFunction1 p (-z.1) (-z.2)) Q2 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.1, -z.2)) Q2 Q1 := by
      intro z hz
      rcases hz with ⟨hx, hy, hxy⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hneg : Continuous (fun z : ℝ × ℝ => (-z.1, -z.2)) := by continuity
    simpa [Q1, Q2, Function.comp_def] using
      (continuousOn_auxFunction1_leTwo p hp1 hp2).comp hneg.continuousOn hmap
  have hcont3 : ContinuousOn (fun z : ℝ × ℝ => auxFunction1 p z.2 z.1) Q3 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (z.2, z.1)) Q3 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hnyx, hxy⟩
      exact ⟨hy, hxy, hnyx⟩
    have hswap : Continuous (fun z : ℝ × ℝ => (z.2, z.1)) := by continuity
    simpa [Q1, Q3, Function.comp_def] using
      (continuousOn_auxFunction1_leTwo p hp1 hp2).comp hswap.continuousOn hmap
  have hcont4 : ContinuousOn (fun z : ℝ × ℝ => auxFunction1 p (-z.2) (-z.1)) Q4 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.2, -z.1)) Q4 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hyx, hxn⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hns : Continuous (fun z : ℝ × ℝ => (-z.2, -z.1)) := by continuity
    simpa [Q1, Q4, Function.comp_def] using
      (continuousOn_auxFunction1_leTwo p hp1 hp2).comp hns.continuousOn hmap
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Q1 := by
    apply ContinuousOn.congr hcont1
    intro z hz
    exact uCandidate_eq_Q1_leTwo p hz
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Q2 := by
    apply ContinuousOn.congr hcont2
    intro z hz
    exact uCandidate_eq_Q2_leTwo p hz
  have hc3 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Q3 := by
    apply ContinuousOn.congr hcont3
    intro z hz
    exact uCandidate_eq_Q3_leTwo p hz
  have hc4 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Q4 := by
    apply ContinuousOn.congr hcont4
    intro z hz
    exact uCandidate_eq_Q4_leTwo p hz
  have hcl1 : IsClosed Q1 := by simpa [Q1] using isClosed_Q1_leTwo
  have hcl2 : IsClosed Q2 := by simpa [Q2] using isClosed_Q2_leTwo
  have hcl3 : IsClosed Q3 := by simpa [Q3] using isClosed_Q3_leTwo
  have hcl4 : IsClosed Q4 := by simpa [Q4] using isClosed_Q4_leTwo
  have hc12 := hc1.union_of_isClosed hc2 hcl1 hcl2
  have hcl12 : IsClosed (Q1 ∪ Q2) := hcl1.union hcl2
  have hc123 := hc12.union_of_isClosed hc3 hcl12 hcl3
  have hcl123 : IsClosed (Q1 ∪ Q2 ∪ Q3) := hcl12.union hcl3
  have hc1234 := hc123.union_of_isClosed hc4 hcl123 hcl4
  apply ContinuousOn.mono hc1234
  simpa [Q1, Q2, Q3, Q4] using univ_subset_quarters_leTwo

private lemma continuousDxuCandidate_leTwo (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Set.univ := by
  let Q1 : Set (ℝ × ℝ) := {z | QuarterPlane z.1 z.2}
  let Q2 : Set (ℝ × ℝ) := {z | QuarterPlane2 z.1 z.2}
  let Q3 : Set (ℝ × ℝ) := {z | QuarterPlane3 z.1 z.2}
  let Q4 : Set (ℝ × ℝ) := {z | QuarterPlane4 z.1 z.2}
  have hcont1 : ContinuousOn (fun z : ℝ × ℝ => DxauxFunction1 p z.1 z.2) Q1 := by
    simpa [Q1] using continuousOn_DxauxFunction1_leTwo p hp1 hp2
  have hcont2 : ContinuousOn (fun z : ℝ × ℝ => -DxauxFunction1 p (-z.1) (-z.2)) Q2 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.1, -z.2)) Q2 Q1 := by
      intro z hz
      rcases hz with ⟨hx, hy, hxy⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hneg : Continuous (fun z : ℝ × ℝ => (-z.1, -z.2)) := by continuity
    simpa [Q1, Q2, Function.comp_def] using
      ((continuousOn_DxauxFunction1_leTwo p hp1 hp2).comp hneg.continuousOn hmap).neg
  have hcont3 : ContinuousOn (fun z : ℝ × ℝ => DyauxFunction1 p z.2 z.1) Q3 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (z.2, z.1)) Q3 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hnyx, hxy⟩
      exact ⟨hy, hxy, hnyx⟩
    have hswap : Continuous (fun z : ℝ × ℝ => (z.2, z.1)) := by continuity
    simpa [Q1, Q3, Function.comp_def] using
      (continuousOn_DyauxFunction1_leTwo p hp1 hp2).comp hswap.continuousOn hmap
  have hcont4 : ContinuousOn (fun z : ℝ × ℝ => -DyauxFunction1 p (-z.2) (-z.1)) Q4 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.2, -z.1)) Q4 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hyx, hxn⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hns : Continuous (fun z : ℝ × ℝ => (-z.2, -z.1)) := by continuity
    simpa [Q1, Q4, Function.comp_def] using
      ((continuousOn_DyauxFunction1_leTwo p hp1 hp2).comp hns.continuousOn hmap).neg
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Q1 := by
    apply ContinuousOn.congr hcont1
    intro z hz
    exact DxuCandidate_eq_Q1_leTwo p hz
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Q2 := by
    apply ContinuousOn.congr hcont2
    intro z hz
    exact DxuCandidate_eq_Q2_leTwo p hz
  have hc3 : ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Q3 := by
    apply ContinuousOn.congr hcont3
    intro z hz
    exact DxuCandidate_eq_Q3_leTwo p hp1 hp2 hz
  have hc4 : ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Q4 := by
    apply ContinuousOn.congr hcont4
    intro z hz
    exact DxuCandidate_eq_Q4_leTwo p hp1 hp2 hz
  have hcl1 : IsClosed Q1 := by simpa [Q1] using isClosed_Q1_leTwo
  have hcl2 : IsClosed Q2 := by simpa [Q2] using isClosed_Q2_leTwo
  have hcl3 : IsClosed Q3 := by simpa [Q3] using isClosed_Q3_leTwo
  have hcl4 : IsClosed Q4 := by simpa [Q4] using isClosed_Q4_leTwo
  have hc12 := hc1.union_of_isClosed hc2 hcl1 hcl2
  have hcl12 : IsClosed (Q1 ∪ Q2) := hcl1.union hcl2
  have hc123 := hc12.union_of_isClosed hc3 hcl12 hcl3
  have hcl123 : IsClosed (Q1 ∪ Q2 ∪ Q3) := hcl12.union hcl3
  have hc1234 := hc123.union_of_isClosed hc4 hcl123 hcl4
  apply ContinuousOn.mono hc1234
  simpa [Q1, Q2, Q3, Q4] using univ_subset_quarters_leTwo

private lemma continuousDyuCandidate_leTwo (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    ContinuousOn (fun z : ℝ × ℝ => DyuCandidate p z.1 z.2) Set.univ := by
  have hdx := continuousDxuCandidate_leTwo p hp1 hp2
  have hswap : Continuous (fun z : ℝ × ℝ => (z.2, z.1)) := by continuity
  have hcomp :
      ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.2 z.1) Set.univ := by
    exact hdx.comp hswap.continuousOn (by intro z hz; trivial)
  apply ContinuousOn.congr hcomp
  intro z hz
  exact DyuCandidate_eq_DxuCandidate_swap_leTwo p hp1 hp2 z.1 z.2


end MajorantPL2



/--
Existence of a Burkholder majorant in the regime `1 < p < 2`.

This theorem takes the low-exponent candidate and proves it satisfies the same
full checklist as in the other regimes: continuity, quantitative growth bounds
for `u` and its first derivatives, the tangent-step inequality, domination of
`v`, and negativity on the opposite-sign region (with strict axis negativity
away from the origin).
-/
theorem exists_majorant_leTwo (p : ℝ) (hp : 1 < p ∧ p < 2) :
    ∃ u du_dx du_dy : ℝ → ℝ → ℝ, ∃ C : ℝ,
      0 ≤ C ∧
      ContinuousOn (fun z : ℝ × ℝ => u z.1 z.2) Set.univ ∧
      ContinuousOn (fun z : ℝ × ℝ => du_dx z.1 z.2) Set.univ ∧
      ContinuousOn (fun z : ℝ × ℝ => du_dy z.1 z.2) Set.univ ∧
      (∀ x y,
        |u x y| ≤ C * (Real.rpow |x| p + Real.rpow |y| p)) ∧
      (∀ x y,
        |du_dx x y| ≤ C * (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1))) ∧
      (∀ x y,
        |du_dy x y| ≤ C * (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1))) ∧
      (∀ x y h k, h * k ≤  0 →
          u (x + h) (y + k) ≤ u x y + du_dx x y * h + du_dy x y * k) ∧
      (∀ x y, v p x y ≤ u x y) ∧
      (∀ x y, x * y ≤ 0 → u x y ≤ 0) ∧
      (∀ x y, x*y = 0 ∧ (x,y) ≠ (0,0) → u x y < 0)  := by
  obtain ⟨Cu, hCu_nonneg, hu_abs_growth⟩ :=
    MajorantPL2.uCandidate_growth_bound p hp.1 hp.2
  obtain ⟨Cdu, hCdu_nonneg, hDxu_growth, hDyu_growth⟩ :=
    MajorantPL2.uCandidate_derivative_growth_bound p hp.1 hp.2
  let C : ℝ := max Cu Cdu
  have hC_nonneg : 0 ≤ C := by
    exact le_trans hCu_nonneg (le_max_left _ _)
  have hCu_le : Cu ≤ C := le_max_left _ _
  have hCdu_le : Cdu ≤ C := le_max_right _ _
  use MajorantPL2.uCandidate p
  use MajorantPL2.DxuCandidate p
  use MajorantPL2.DyuCandidate p
  use C
  refine ⟨hC_nonneg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact MajorantPL2.continuousuCandidate_leTwo p hp.1 hp.2
  · exact MajorantPL2.continuousDxuCandidate_leTwo p hp.1 hp.2
  · exact MajorantPL2.continuousDyuCandidate_leTwo p hp.1 hp.2
  · intro x y
    have hsum_nonneg : 0 ≤ Real.rpow |x| p + Real.rpow |y| p :=
      add_nonneg (Real.rpow_nonneg (abs_nonneg x) _)
        (Real.rpow_nonneg (abs_nonneg y) _)
    calc
      |MajorantPL2.uCandidate p x y|
          ≤ Cu * (Real.rpow |x| p + Real.rpow |y| p) := hu_abs_growth x y
      _ ≤ C * (Real.rpow |x| p + Real.rpow |y| p) :=
        mul_le_mul_of_nonneg_right hCu_le hsum_nonneg
  · intro x y
    have hsum_nonneg : 0 ≤ Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1) :=
      add_nonneg (Real.rpow_nonneg (abs_nonneg x) _)
        (Real.rpow_nonneg (abs_nonneg y) _)
    exact (hDxu_growth x y).trans
      (mul_le_mul_of_nonneg_right hCdu_le hsum_nonneg)
  · intro x y
    have hsum_nonneg : 0 ≤ Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1) :=
      add_nonneg (Real.rpow_nonneg (abs_nonneg x) _)
        (Real.rpow_nonneg (abs_nonneg y) _)
    exact (hDyu_growth x y).trans
      (mul_le_mul_of_nonneg_right hCdu_le hsum_nonneg)
  · intro x y h k hk
    exact MajorantPL2.uCandidate_hk_negative_leTwo p hp.1 hp.2 hk
  · intro x y
    rw [MajorantPL2.v_eq_vLeTwo_of_one_lt_of_lt_two p x y hp.1 hp.2]
    exact MajorantPL2.vLeTwo_le_uCandidate_leTwo p hp.1 hp.2 x y
  · intro x y hxy
    exact MajorantPL2.uCandidate_le_zero_of_mul_nonpos_leTwo p x y hp.1 hp.2 hxy
  · intro x y hxy
    rcases hxy with ⟨hxy0, hne⟩
    exact MajorantPL2.uCandidate_le_zero_of_mul_neg_LeTwo p x y hp hxy0 hne

end Majorants
