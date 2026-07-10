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
# Burkholder majorant for `p > 2`

Constructs and verifies the Burkholder majorant in the regime `p > 2`,
including the explicit derivatives, concavity, and tangent estimates.
-/

noncomputable section

namespace Majorants

namespace  MajorantPG2

/-!
# Burkholder majorant candidate

This file builds and studies the piecewise candidate `uCandidate`.

The proof architecture is organized as follows.

1. **Definitions.**  We define the Burkholder parameters, the two local formulas
   `uA1` and `vGeTwo`, their first partial derivatives, the first quadrant
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


private lemma pStar_eq_self_of_two_le (p : ℝ) (hp : 2 ≤ p) : pStar p = p := by
  unfold pStar
  apply max_eq_left
  unfold q
  have hp_ne_one : p ≠ 1 := by linarith
  simp only [hp_ne_one, ↓reduceIte, ge_iff_le]
  have hden : 0 < p - 1 := by linarith
  have hnonneg : 0 ≤ p := by linarith
  have h1 : 1 ≤ p - 1 := by linarith
  have hmul : p * 1 ≤ p * (p - 1) := mul_le_mul_of_nonneg_left h1 hnonneg
  have hp_le : p ≤ p * (p - 1) := by simpa using hmul
  have hden_ne : p - 1 ≠ 0 := by linarith
  have h_inv_nonneg : 0 ≤ (p - 1)⁻¹ := by positivity
  have hmul' : p * (p - 1)⁻¹ ≤ (p * (p - 1)) * (p - 1)⁻¹ :=
    mul_le_mul_of_nonneg_right hp_le h_inv_nonneg
  simpa [div_eq_mul_inv, hden_ne, mul_assoc, mul_comm, mul_left_comm] using hmul'






/-- The same expression specialized to the `p ≥ 2` regime. -/
private def vGeTwo (p x y : ℝ) : ℝ :=
  Real.rpow (|((x + y) / 2)|) p
    - Real.rpow (p - 1) p * Real.rpow (|((x - y) / 2)|) p



/-- Open first-quadrant sector where the formula `uA1` is used. -/
private def A1 (p x y : ℝ) : Prop := 0 < x ∧ (a p) * x < y ∧ y < x

/-- Closed version of `A1`, used for gluing and continuity. -/
private def closureA1 (p x y : ℝ) : Prop := 0 ≤ x ∧ (a p) * x ≤ y ∧ y ≤ x

/-- Open first-quadrant sector where the formula `vGeTwo` is used. -/
private def A2 (p x y : ℝ) : Prop := 0 < x ∧ -x < y ∧ y < (a p) * x

/-- Closed version of `A2`, used for gluing and continuity. -/
private def closureA2 (p x y : ℝ) : Prop := 0 ≤ x ∧ -x ≤ y ∧ y ≤ (a p) * x

/-- Local majorant formula on `A1`; outside `x > 0` it is set to zero. -/
private def uA1 (p x y : ℝ) : ℝ :=
  if x > 0 then
     alpha p * Real.rpow x (p-1) * (x - (pStar p) * (x - y) /2)
     else 0

/-- `x`-partial of `uA1`. -/
private def DxuA1 (p x y : ℝ) : ℝ :=
  if x > 0 then
     alpha p * (p / 2) * Real.rpow x (p - 2) * ((2 - p) * x + (p - 1) * y)
     else 0

/-- `y`-partial of `uA1`. -/
private def DyuA1 (p x _y : ℝ) : ℝ :=
  if x > 0 then
     alpha p * Real.rpow x (p - 1) * (pStar p / 2)
     else 0

/-- `x`-partial of `vGeTwo` in the first quadrant. -/
private def DxvGeTwo (p x y : ℝ) : ℝ :=
  if x > 0 then
     Real.rpow (|((x + y) / 2)|) (p - 1) * (p / 2)
     - Real.rpow (p - 1) p * Real.rpow (|((x - y) / 2)|) (p - 1) * (p / 2)
     else 0

/-- `y`-partial of `vGeTwo` in the first quadrant. -/
private def DyvGeTwo (p x y : ℝ) : ℝ :=
  if x > 0 then
     Real.rpow (|((x + y) / 2)|) (p - 1) * (p / 2)
     + Real.rpow (p - 1) p * Real.rpow (|((x - y) / 2)|) (p - 1) * (p / 2)
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
  fun z => alpha p * (p / 2) * Real.rpow z.1 (p - 2) * ((2 - p) * z.1 + (p - 1) * z.2)

private def DyuA1Formula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => alpha p * Real.rpow z.1 (p - 1) * (pStar p / 2)

private def DxvGeTwoFun (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => DxvGeTwo p z.1 z.2

private def DyvGeTwoFun (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z => DyvGeTwo p z.1 z.2

private def DxvGeTwoFormula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z =>
    Real.rpow (|((z.1 + z.2) / 2)|) (p - 1) * (p / 2) -
      Real.rpow (p - 1) p * Real.rpow (|((z.1 - z.2) / 2)|) (p - 1) * (p / 2)

private def DyvGeTwoFormula (p : ℝ) : ℝ × ℝ → ℝ :=
  fun z =>
    Real.rpow (|((z.1 + z.2) / 2)|) (p - 1) * (p / 2) +
      Real.rpow (p - 1) p * Real.rpow (|((z.1 - z.2) / 2)|) (p - 1) * (p / 2)


open Topology

/-! ## 2. Continuity of the local first partials -/

/-
The next block proves continuity of the explicit first-partial formulas on the
closed sectors.  This is needed later when the sector formulas are glued along
boundaries.
-/


private lemma continuousAt_DxuA1_interior
    (p x y : ℝ) (hx : 0 < x) :
    ContinuousAt (DxuA1Fun p) (x, y) := by
  have hpos : {z : ℝ × ℝ | 0 < z.1} ∈ nhds (x, y) := by
    exact continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx)
  have hEvent :
      DxuA1Fun p =ᶠ[nhds (x, y)] DxuA1Formula p := by
    filter_upwards [hpos] with z hz
    simp [DxuA1Fun, DxuA1Formula, DxuA1, hz]
  have hcont_rpow :
      ContinuousAt (fun z : ℝ × ℝ => z.1 ^ (p - 2)) (x, y) := by
    exact continuous_fst.continuousAt.rpow_const (Or.inl (ne_of_gt hx))
  have hcont_sub : ContinuousAt (fun z : ℝ × ℝ => z.1 - z.2) (x, y) := by
    exact continuous_fst.continuousAt.sub continuous_snd.continuousAt
  have hcont_lin :
      ContinuousAt
        (fun z : ℝ × ℝ => (2 - p) * z.1 + (p - 1) * z.2)
        (x, y) := by
    exact
      (continuous_const.continuousAt.mul continuous_fst.continuousAt).add
        (continuous_const.continuousAt.mul continuous_snd.continuousAt)
  have hcont : ContinuousAt (DxuA1Formula p) (x, y) := by
    change ContinuousAt
      (fun z : ℝ × ℝ =>
        alpha p * (p / 2) * z.1 ^ (p - 2) * ((2 - p) * z.1 + (p - 1) * z.2))
      (x, y)
    have hcoeff : ContinuousAt (fun _ : ℝ × ℝ => alpha p * (p / 2)) (x, y) :=
      continuousAt_const
    exact (hcoeff.mul hcont_rpow).mul hcont_lin
  exact hcont.congr_of_eventuallyEq hEvent










private lemma closureA1_x0_y0
    (p x y : ℝ) (h : closureA1 p x y) (hx : ¬ 0 < x) :
    x = 0 ∧ y = 0 := by
  rcases h with ⟨hxnonneg, hylow, hyup⟩
  have hx0 : x = 0 := by linarith
  have hy0 : y = 0 := by
    subst hx0
    linarith
  exact ⟨hx0, hy0⟩

private lemma closureA2_x0_y0
    (p x y : ℝ) (h : closureA2 p x y) (hx : ¬ 0 < x) :
    x = 0 ∧ y = 0 := by
  rcases h with ⟨hxnonneg, hylow, hyup⟩
  have hx0 : x = 0 := by linarith
  have hy0 : y = 0 := by
    subst hx0
    linarith
  exact ⟨hx0, hy0⟩

/-- On `closureA1`, `|y|` is bounded by a constant multiple of `x`. -/
private lemma abs_y_le_const_mul_x
    (p x y : ℝ) (h : closureA1 p x y) :
    |y| ≤ (max 1 |a p|) * x := by
  rcases h with ⟨hx, hlow, hup⟩
  have hx' : 0 ≤ x := hx
  have h1 : y ≤ x := hup
  have h2 : -(max 1 |a p| * x) ≤ y := by
    have ha : -(max 1 |a p|) ≤ a p := by
      have hmax : |a p| ≤ max 1 |a p| := le_max_right _ _
      have hneg : -(max 1 |a p|) ≤ -|a p| := by linarith
      have habs : -|a p| ≤ a p := by
        exact neg_abs_le (a p)
      linarith
    have := mul_le_mul_of_nonneg_right ha hx'
    linarith
  have h3 : y ≤ max 1 |a p| * x := by
    have hmax1 : 1 ≤ max 1 |a p| := le_max_left _ _
    have := mul_le_mul_of_nonneg_right hmax1 hx'
    linarith
  exact abs_le.mpr ⟨h2, h3⟩

/-- A coarse boundary estimate:
`|DxuA1| ≤ C * x^(p-1)` on `closureA1`. -/
private lemma abs_DxuA1_le
    (p x y : ℝ) (h : closureA1 p x y) :
    |DxuA1 p x y|
      ≤ |alpha p| * (|p| / 2) * (|2 - p| + |p - 1| * max 1 |a p|) * Real.rpow x (p - 1) := by
  rcases h with ⟨hx, hlow, hup⟩
  by_cases hx0 : 0 < x
  · have hxnonneg : 0 ≤ x := le_of_lt hx0
    have hyabs : |y| ≤ (max 1 |a p|) * x := by
      exact abs_y_le_const_mul_x p x y ⟨hx, hlow, hup⟩
    have hx_abs : |x| = x := abs_of_nonneg hxnonneg
    have hlin :
        |(2 - p) * x + (p - 1) * y|
          ≤ (|2 - p| + |p - 1| * max 1 |a p|) * x := by
      have htmp :
          |(2 - p) * x + (p - 1) * y|
            ≤ |(2 - p) * x| + |(p - 1) * y| := by
        simpa using abs_add_le ((2 - p) * x) ((p - 1) * y)
      have hmulx : |(2 - p) * x| = |2 - p| * x := by
        rw [abs_mul, hx_abs]
      have hmuly : |(p - 1) * y| = |p - 1| * |y| := by
        rw [abs_mul]
      rw [hmulx, hmuly] at htmp
      calc
        |(2 - p) * x + (p - 1) * y|
            ≤ |2 - p| * x + |p - 1| * |y| := htmp
        _ ≤ |2 - p| * x + |p - 1| * (max 1 |a p| * x) := by
            gcongr
        _ = (|2 - p| + |p - 1| * max 1 |a p|) * x := by
            ring
    have hrpow_nonneg : 0 ≤ Real.rpow x (p - 2) := Real.rpow_nonneg hxnonneg _
    have hpow :
        Real.rpow x (p - 2) * x = Real.rpow x (p - 1) := by
      have hexp : (p - 2) + 1 = p - 1 := by ring
      nth_rewrite 2 [show x = Real.rpow x (1 : ℝ) by simp]
      calc
        Real.rpow x (p - 2) * Real.rpow x (1 : ℝ)
            = Real.rpow x ((p - 2) + 1) := by
                simpa using (Real.rpow_add hx0 (p - 2) 1).symm
        _ = Real.rpow x (p - 1) := by simp [hexp]
    have habs :
        |alpha p * (p / 2) * Real.rpow x (p - 2) * ((2 - p) * x + (p - 1) * y)|
          = |alpha p| * (|p| / 2) * Real.rpow x (p - 2) * |(2 - p) * x + (p - 1) * y| := by
      have hmul :
          |alpha p * (p / 2) * Real.rpow x (p - 2)|
            = |alpha p| * (|p| / 2) * Real.rpow x (p - 2) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hrpow_nonneg, abs_div,
          abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      calc
        |alpha p * (p / 2) * Real.rpow x (p - 2) * ((2 - p) * x + (p - 1) * y)|
            = |(alpha p * (p / 2) * Real.rpow x (p - 2)) * ((2 - p) * x + (p - 1) * y)| := by
                ring_nf
        _ = |alpha p * (p / 2) * Real.rpow x (p - 2)| * |(2 - p) * x + (p - 1) * y| := by
            rw [abs_mul]
        _ = (|alpha p| * (|p| / 2) * Real.rpow x (p - 2)) * |(2 - p) * x + (p - 1) * y| := by
            rw [hmul]
        _ = |alpha p| * (|p| / 2) * Real.rpow x (p - 2) * |(2 - p) * x + (p - 1) * y| := by ring
    calc
      |DxuA1 p x y|
          = |alpha p * (p / 2) * Real.rpow x (p - 2) * ((2 - p) * x + (p - 1) * y)| := by
              simp [DxuA1, hx0]
      _ = |alpha p| * (|p| / 2) * Real.rpow x (p - 2) * |(2 - p) * x + (p - 1) * y| := habs
      _ ≤ |alpha p| * (|p| / 2) * Real.rpow x (p - 2) *
            ((|2 - p| + |p - 1| * max 1 |a p|) * x) := by
              gcongr
      _ = |alpha p| * (|p| / 2) * (|2 - p| + |p - 1| * max 1 |a p|) *
            (Real.rpow x (p - 2) * x) := by
              ring
      _ = |alpha p| * (|p| / 2) * (|2 - p| + |p - 1| * max 1 |a p|) *
            Real.rpow x (p - 1) := by
              rw [hpow]
  · have h00 : x = 0 ∧ y = 0 := closureA1_x0_y0 p x y ⟨hx, hlow, hup⟩ hx0
    rcases h00 with ⟨rfl, rfl⟩
    have hnonneg :
        0 ≤ |alpha p| * (|p| / 2) * (|2 - p| + |p - 1| * max 1 |a p|) * Real.rpow 0 (p - 1) := by
      have hrpow_nonneg : 0 ≤ Real.rpow (0 : ℝ) (p - 1) := Real.zero_rpow_nonneg (p - 1)
      positivity
    simpa [DxuA1] using hnonneg


private lemma continuousOn_DxuA1_closureA1
    (p : ℝ) (hp : 1 < p) :
    ContinuousOn (DxuA1Fun p) (closureA1Set p) := by
  intro z hz
  rcases z with ⟨x, y⟩
  rcases hz with ⟨hx, hlow, hup⟩
  by_cases hx0 : 0 < x
  · exact (continuousAt_DxuA1_interior p x y hx0).continuousWithinAt
  · have h00 := closureA1_x0_y0 p x y ⟨hx, hlow, hup⟩ hx0
    rcases h00 with ⟨rfl, rfl⟩
    rw [ContinuousWithinAt, DxuA1Fun]
    simp only [DxuA1, lt_irrefl, ite_false]
    rw [tendsto_zero_iff_abs_tendsto_zero]
    let C : ℝ := |alpha p| * (|p| / 2) * (|2 - p| + |p - 1| * max 1 |a p|)
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      positivity
    have hbound :
        ∀ᶠ z : ℝ × ℝ in nhdsWithin (0, 0) (closureA1Set p),
          |DxuA1Fun p z| ≤ C * Real.rpow z.1 (p - 1) := by
      refine Filter.mem_of_superset self_mem_nhdsWithin ?_
      intro z hz'
      simpa [closureA1Set, DxuA1Fun, C] using abs_DxuA1_le p z.1 z.2 hz'
    have hrpow :
        Filter.Tendsto (fun z : ℝ × ℝ => Real.rpow z.1 (p - 1))
          (nhdsWithin (0, 0) (closureA1Set p)) (nhds 0) := by
      have hcont :
          ContinuousAt (fun z : ℝ × ℝ => Real.rpow z.1 (p - 1)) (0, 0) := by
        exact continuous_fst.continuousAt.rpow_const (Or.inr (by linarith : 0 ≤ p - 1))
      have hzero : Real.rpow (0 : ℝ) (p - 1) = 0 := by
        exact Real.zero_rpow (by linarith)
      have ht : Filter.Tendsto (fun z : ℝ × ℝ => Real.rpow z.1 (p - 1)) (nhds (0, 0)) (nhds 0) := by
        convert hcont.tendsto using 1
        simpa using hzero.symm
      exact ht.mono_left nhdsWithin_le_nhds
    have hmajor :
        Filter.Tendsto (fun z : ℝ × ℝ => C * Real.rpow z.1 (p - 1))
          (nhdsWithin (0, 0) (closureA1Set p)) (nhds 0) := by
      simpa using tendsto_const_nhds.mul hrpow
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) hbound hmajor



private lemma continuousOn_DyuA1_closureA1
    (p : ℝ) (hp : 2 < p) :
    ContinuousOn (DyuA1Fun p) (closureA1Set p) := by
  intro z hz
  rcases z with ⟨x, y⟩
  rcases hz with ⟨hx, hlow, hup⟩
  by_cases hx0 : 0 < x
  · have hpos : {w : ℝ × ℝ | 0 < w.1} ∈ nhds (x, y) := by
      exact continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx0)
    have hEvent :
        DyuA1Fun p =ᶠ[nhds (x, y)]
          (fun w : ℝ × ℝ => alpha p * Real.rpow w.1 (p - 1) * (pStar p / 2)) := by
      filter_upwards [hpos] with w hw
      simp [DyuA1Fun, DyuA1, hw]
    have hcont_rpow :
        ContinuousAt (fun w : ℝ × ℝ => Real.rpow w.1 (p - 1)) (x, y) := by
      exact continuous_fst.continuousAt.rpow_const (Or.inl (ne_of_gt hx0))
    have hcont :
        ContinuousAt
          (fun w : ℝ × ℝ => alpha p * Real.rpow w.1 (p - 1) * (pStar p / 2))
          (x, y) := by
      exact (continuous_const.continuousAt.mul hcont_rpow).mul continuous_const.continuousAt
    exact (hcont.congr_of_eventuallyEq hEvent).continuousWithinAt
  · have h00 := closureA1_x0_y0 p x y ⟨hx, hlow, hup⟩ hx0
    rcases h00 with ⟨rfl, rfl⟩
    rw [ContinuousWithinAt, DyuA1Fun]
    simp only [DyuA1, lt_irrefl, ite_false]
    rw [tendsto_zero_iff_abs_tendsto_zero]
    let C : ℝ := |alpha p * (pStar p / 2)|
    have hbound :
        ∀ᶠ w : ℝ × ℝ in nhdsWithin (0, 0) (closureA1Set p),
          |DyuA1Fun p w| ≤ C * Real.rpow w.1 (p - 1) := by
      refine Filter.mem_of_superset self_mem_nhdsWithin ?_
      intro w hw
      rcases hw with ⟨hwx, hwlow, hwup⟩
      by_cases hw0 : 0 < w.1
      · have habs :
            |DyuA1Fun p w| =
              C * Real.rpow w.1 (p - 1) := by
          calc
            |DyuA1Fun p w|
                = |alpha p| * Real.rpow w.1 (p - 1) * |pStar p / 2| := by
                    simp [DyuA1Fun, DyuA1, hw0, abs_mul, Real.rpow_nonneg hwx, mul_assoc]
            _ = (|alpha p| * |pStar p / 2|) * Real.rpow w.1 (p - 1) := by ring
            _ = C * Real.rpow w.1 (p - 1) := by
                    simp [C, abs_mul, mul_assoc]
        exact le_of_eq habs
      · have h00 := closureA1_x0_y0 p w.1 w.2 ⟨hwx, hwlow, hwup⟩ hw0
        rcases h00 with ⟨hw1, hw2⟩
        simp only [DyuA1Fun, DyuA1, gt_iff_lt, Real.rpow_eq_pow, abs_mul, Set.mem_setOf_eq, hw1,
          lt_self_iff_false, ↓reduceIte, abs_zero, ge_iff_le, C]
        positivity
    have hrpow :
        Filter.Tendsto (fun w : ℝ × ℝ => Real.rpow w.1 (p - 1))
          (nhdsWithin (0, 0) (closureA1Set p)) (nhds 0) := by
      have hcont :
          ContinuousAt (fun w : ℝ × ℝ => Real.rpow w.1 (p - 1)) (0, 0) := by
        exact continuous_fst.continuousAt.rpow_const (Or.inr (by linarith : 0 ≤ p - 1))
      have hzero : Real.rpow (0 : ℝ) (p - 1) = 0 := by
        exact Real.zero_rpow (by linarith)
      have ht :
          Filter.Tendsto (fun w : ℝ × ℝ => Real.rpow w.1 (p - 1)) (nhds (0, 0)) (nhds 0) := by
        convert hcont.tendsto using 1
        simpa using hzero.symm
      exact ht.mono_left nhdsWithin_le_nhds
    have hmajor :
        Filter.Tendsto (fun w : ℝ × ℝ => C * Real.rpow w.1 (p - 1))
          (nhdsWithin (0, 0) (closureA1Set p)) (nhds 0) := by
      simpa using tendsto_const_nhds.mul hrpow
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) hbound hmajor

private lemma DxvGeTwo_eq_formula_on_closureA2
    (p : ℝ) (hp : 2 ≤ p) (z : ℝ × ℝ) (hz : z ∈ closureA2Set p) :
    DxvGeTwoFun p z = DxvGeTwoFormula p z := by
  rcases z with ⟨x, y⟩
  rcases hz with ⟨hx, hlow, hup⟩
  by_cases hx0 : 0 < x
  · simp [DxvGeTwoFun, DxvGeTwoFormula, DxvGeTwo, hx0]
  · have h00 := closureA2_x0_y0 p x y ⟨hx, hlow, hup⟩ hx0
    rcases h00 with ⟨rfl, rfl⟩
    have hp1 : p - 1 ≠ 0 := by linarith
    have hzero : Real.rpow (0 : ℝ) (p - 1) = 0 := Real.zero_rpow hp1
    simp only [DxvGeTwoFun, DxvGeTwo, gt_iff_lt, lt_self_iff_false, ↓reduceIte, DxvGeTwoFormula,
      add_zero, zero_div, abs_zero, Real.rpow_eq_pow, sub_self]
    rw [show (0 : ℝ) ^ (p - 1) = 0 by simpa using hzero]
    ring

private lemma DyvGeTwo_eq_formula_on_closureA2
    (p : ℝ) (hp : 2 ≤ p) (z : ℝ × ℝ) (hz : z ∈ closureA2Set p) :
    DyvGeTwoFun p z = DyvGeTwoFormula p z := by
  rcases z with ⟨x, y⟩
  rcases hz with ⟨hx, hlow, hup⟩
  by_cases hx0 : 0 < x
  · simp [DyvGeTwoFun, DyvGeTwoFormula, DyvGeTwo, hx0]
  · have h00 := closureA2_x0_y0 p x y ⟨hx, hlow, hup⟩ hx0
    rcases h00 with ⟨rfl, rfl⟩
    have hp1 : p - 1 ≠ 0 := by linarith
    have hzero : Real.rpow (0 : ℝ) (p - 1) = 0 := Real.zero_rpow hp1
    simp only [DyvGeTwoFun, DyvGeTwo, gt_iff_lt, lt_self_iff_false, ↓reduceIte, DyvGeTwoFormula,
      add_zero, zero_div, abs_zero, Real.rpow_eq_pow, sub_self]
    rw [show (0 : ℝ) ^ (p - 1) = 0 by simpa using hzero]
    ring

private lemma continuousOn_DxvGeTwo_closureA2
    (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (DxvGeTwoFun p) (closureA2Set p) := by
  have hp1 : 0 ≤ p - 1 := by linarith
  have hcont : Continuous (DxvGeTwoFormula p) := by
    have hsum :
        Continuous (fun z : ℝ × ℝ => Real.rpow (|((z.1 + z.2) / 2)|) (p - 1)) := by
      exact Continuous.rpow_const (((continuous_fst.add continuous_snd).div_const 2).abs)
        (fun _ => Or.inr hp1)
    have hdiff :
        Continuous (fun z : ℝ × ℝ => Real.rpow (|((z.1 - z.2) / 2)|) (p - 1)) := by
      exact Continuous.rpow_const (((continuous_fst.sub continuous_snd).div_const 2).abs)
        (fun _ => Or.inr hp1)
    unfold DxvGeTwoFormula
    exact (hsum.mul continuous_const).sub
      ((continuous_const.mul hdiff).mul continuous_const)
  apply ContinuousOn.congr hcont.continuousOn
  intro z hz
  exact DxvGeTwo_eq_formula_on_closureA2 p hp z hz

private lemma continuousOn_DyvGeTwo_closureA2
    (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (DyvGeTwoFun p) (closureA2Set p) := by
  have hp1 : 0 ≤ p - 1 := by linarith
  have hcont : Continuous (DyvGeTwoFormula p) := by
    have hsum :
        Continuous (fun z : ℝ × ℝ => Real.rpow (|((z.1 + z.2) / 2)|) (p - 1)) := by
      exact Continuous.rpow_const (((continuous_fst.add continuous_snd).div_const 2).abs)
        (fun _ => Or.inr hp1)
    have hdiff :
        Continuous (fun z : ℝ × ℝ => Real.rpow (|((z.1 - z.2) / 2)|) (p - 1)) := by
      exact Continuous.rpow_const (((continuous_fst.sub continuous_snd).div_const 2).abs)
        (fun _ => Or.inr hp1)
    unfold DyvGeTwoFormula
    exact (hsum.mul continuous_const).add
      ((continuous_const.mul hdiff).mul continuous_const)
  apply ContinuousOn.congr hcont.continuousOn
  intro z hz
  exact DyvGeTwo_eq_formula_on_closureA2 p hp z hz




private def auxFunction1 (p x y : ℝ) : ℝ :=
    by
    classical
    exact
      if  closureA1 p x y then
         uA1 p x y
      else if closureA2 p x y then
          vGeTwo p x y
        else 0

private def DxauxFunction1 (p x y : ℝ) : ℝ :=
    by
    classical
    exact
      if closureA1 p x y then
        DxuA1 p x y
      else if closureA2 p x y then
        DxvGeTwo p x y
      else 0

private def DyauxFunction1 (p x y : ℝ) : ℝ :=
    by
    classical
    exact
      if closureA1 p x y then
        DyuA1 p x y
      else if closureA2 p x y then
        DyvGeTwo p x y
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

/-
This block shows that the formulas agree on all relevant shared boundaries:
the internal A1/A2 boundary, the diagonal, and the antidiagonal.  These
compatibility private lemmas are used twice: first for continuity of the glued
candidate, and later for differentiability/tangent estimates at break points.
-/

/-- For x ≥ 0, uA1 equals the smooth expression (using 0^(p-1)=0 when x=0). -/
private lemma uA1_eq_smooth_of_nonneg (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hx : 0 ≤ x) :
    uA1 p x y = alpha p * x ^ (p - 1) * (x - pStar p * (x - y) / 2) := by
  have hexp_ne : p - 1 ≠ 0 := by linarith
  unfold uA1
  rcases hx.lt_or_eq with hxpos | hxeq
  · exact if_pos hxpos
  · have hx0 : x = 0 := hxeq.symm
    subst hx0
    simp [Real.zero_rpow hexp_ne]

/-- uA1 is continuous on {(x, y) | 0 ≤ x} when p ≥ 2. -/
private lemma continuousOn_uA1 (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (fun z : ℝ × ℝ => uA1 p z.1 z.2) {z | 0 ≤ z.1} := by
  have hexp_pos : 0 < p - 1 := by linarith
  have heq : ∀ z : ℝ × ℝ, z ∈ {z : ℝ × ℝ | 0 ≤ z.1} →
      uA1 p z.1 z.2 = alpha p * z.1 ^ (p - 1) * (z.1 - pStar p * (z.1 - z.2) / 2) :=
    fun ⟨x, y⟩ hx => uA1_eq_smooth_of_nonneg p hp x y hx
  apply ContinuousOn.congr _ heq
  apply ContinuousOn.mul
  · exact continuousOn_const.mul
      (continuousOn_fst.rpow_const fun _ _ => Or.inr hexp_pos.le)
  · exact continuousOn_fst.sub
      ((continuousOn_const.mul (continuousOn_fst.sub continuousOn_snd)).div_const 2)




/-- On the A1/A2 boundary (y = a(p)·x, x > 0), uA1 vanishes. -/
private lemma uA1_eq_zero_on_boundary (p x : ℝ) (hp : 2 ≤ p) (hx : 0 < x) :
    uA1 p x ((a p) * x) = 0 := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  unfold uA1
  rw [if_pos hx]
  have hfactor : x - pStar p * (x - a p * x) / 2 = 0 := by
    simp only [a, hpStar]
    field_simp [hp_pos.ne']
    ring
  rw [hfactor, mul_zero]

/-- On the A1/A2 boundary (y = a(p)·x, x > 0), vGeTwo vanishes. -/
private lemma vGeTwo_eq_zero_on_boundary (p x : ℝ) (hp : 2 ≤ p) (hx : 0 < x) :
    vGeTwo p x ((a p) * x) = 0 := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  simp only [vGeTwo, a, hpStar]
  have h_sum : (x + (1 - 2 / p) * x) / 2 = (p - 1) / p * x := by
    field_simp [hp_pos.ne']; ring
  have h_diff : (x - (1 - 2 / p) * x) / 2 = x / p := by
    field_simp [hp_pos.ne']; ring
  rw [h_sum, h_diff,
      abs_of_pos (mul_pos (div_pos (by linarith) hp_pos) hx),
      abs_of_pos (div_pos hx hp_pos)]
  have key : ((p - 1) / p * x) ^ p = (p - 1) ^ p * (x / p) ^ p := by
    rw [Real.mul_rpow (div_nonneg (by linarith) hp_pos.le) hx.le,
        Real.div_rpow (by linarith : 0 ≤ p - 1) hp_pos.le,
        Real.div_rpow hx.le hp_pos.le]
    ring
  exact sub_eq_zero.mpr key

/-- Both formulas agree on the shared A1/A2 boundary. -/
private lemma uA1_eq_vGeTwo_on_A1A2_boundary (p x : ℝ) (hp : 2 ≤ p) (hx : 0 < x) :
    uA1 p x ((a p) * x) = vGeTwo p x ((a p) * x) :=
  (uA1_eq_zero_on_boundary p x hp hx).trans (vGeTwo_eq_zero_on_boundary p x hp hx).symm

/- Continuity auxiliary functions -/

/-- As x → 0⁺, x ^ (p - 1) → 0 when p > 1. -/
private lemma tendsto_rpow_nhdsWithin_Ioi_zero (p : ℝ) (hp : 1 < p) :
    Filter.Tendsto (fun x : ℝ => x ^ (p - 1)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hexp : 0 < p - 1 := by linarith
  have h0 : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow hexp.ne'
  have hcont : ContinuousAt (fun x : ℝ => x ^ (p - 1)) 0 :=
    continuousAt_id.rpow_const (Or.inr hexp.le)
  have key : Filter.Tendsto (fun x : ℝ => x ^ (p - 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((0 : ℝ) ^ (p - 1))) :=
    hcont.continuousWithinAt
  rwa [h0] at key


/-- vGeTwo is continuous on ℝ² when p > 1. -/
private lemma continuous_vGeTwo (p : ℝ) (hp : 1 < p) :
    Continuous (fun z : ℝ × ℝ => vGeTwo p z.1 z.2) := by
  have hp_pos : (0 : ℝ) ≤ p := by linarith
  simp only [vGeTwo]
  apply Continuous.sub
  · apply Continuous.rpow_const _ (fun _ => Or.inr hp_pos)
    exact ((continuous_fst.add continuous_snd).div_const 2).abs
  · apply Continuous.mul continuous_const
    apply Continuous.rpow_const _ (fun _ => Or.inr hp_pos)
    exact ((continuous_fst.sub continuous_snd).div_const 2).abs








/-- closureA1 and closureA2 are closed subsets of ℝ². -/
private lemma isClosed_closureA1_set (p : ℝ) :
    IsClosed {z : ℝ × ℝ | closureA1 p z.1 z.2} := by
  simp only [closureA1]
  apply IsClosed.inter
  · exact isClosed_le continuous_const continuous_fst
  apply IsClosed.inter
  · exact isClosed_le (continuous_const.mul continuous_fst) continuous_snd
  · exact isClosed_le continuous_snd continuous_fst

private lemma isClosed_closureA2_set (p : ℝ) :
    IsClosed {z : ℝ × ℝ | closureA2 p z.1 z.2} := by
  simp only [closureA2]
  apply IsClosed.inter
  · exact isClosed_le continuous_const continuous_fst
  apply IsClosed.inter
  · exact isClosed_le continuous_fst.neg continuous_snd
  · exact isClosed_le continuous_snd (continuous_const.mul continuous_fst)

/-- On the boundary closureA1 ∩ closureA2, uA1 = vGeTwo (both equal 0). -/
private lemma uA1_eq_vGeTwo_on_inter (p : ℝ) (hp : 2 ≤ p) (x y : ℝ)
    (h1 : closureA1 p x y) (h2 : closureA2 p x y) :
    uA1 p x y = vGeTwo p x y := by
  obtain ⟨hx, hay, hyx⟩ := h1
  obtain ⟨_, hmy, hyay⟩ := h2
  have heq : y = a p * x := le_antisymm hyay hay
  rcases hx.lt_or_eq with hxpos | hxeq
  · rw [heq]; exact uA1_eq_vGeTwo_on_A1A2_boundary p x hp hxpos
  · -- x = 0, so both sides are 0
    have hx0 : x = 0 := hxeq.symm
    subst hx0
    simp only [uA1, lt_irrefl, ite_false, vGeTwo]
    have hy0 : y = 0 := le_antisymm (by linarith) (by linarith)
    subst hy0
    simp [Real.zero_rpow (by linarith : p ≠ 0)]

/-- auxFunction1 = uA1 on closureA1. -/
private lemma auxFunction1_eq_uA1 (p x y : ℝ) (h : closureA1 p x y) :
    auxFunction1 p x y = uA1 p x y := by
  simp only [auxFunction1, h, ite_true]

/-- auxFunction1 = vGeTwo on closureA2, given p ≥ 2. -/
private lemma auxFunction1_eq_vGeTwo (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (h2 : closureA2 p x y) :
    auxFunction1 p x y = vGeTwo p x y := by
  simp only [auxFunction1]
  by_cases h1 : closureA1 p x y
  · simp only [h1, ite_true]
    exact uA1_eq_vGeTwo_on_inter p hp x y h1 h2
  · simp only [h1, ite_false, h2, ite_true]

/-- On the A1/A2 boundary, the x-partial formulas agree. -/
private lemma alpha_eq_boundary_coeff (p : ℝ) (hp : 2 ≤ p) :
    alpha p = p * Real.rpow ((p - 1) / p) (p - 1) := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  have hp1_nonneg : 0 ≤ p - 1 := by linarith
  rw [alpha, hpStar]
  simp_rw [Real.rpow_eq_pow]
  calc
    p * (p / (p - 1)) ^ (1 - p)
        = p * (p / (p - 1)) ^ (-(p - 1)) := by
            congr 2
            ring
    _ = p * ((p / (p - 1)) ^ (p - 1))⁻¹ := by
          rw [Real.rpow_neg (div_nonneg hp_pos.le hp1_nonneg)]
    _ = p * (p ^ (p - 1) / (p - 1) ^ (p - 1))⁻¹ := by
          rw [Real.div_rpow hp_pos.le hp1_nonneg]
    _ = p * ((p - 1) ^ (p - 1) / p ^ (p - 1)) := by
          field_simp
    _ = p * ((p - 1) / p) ^ (p - 1) := by
          rw [Real.div_rpow hp1_nonneg hp_pos.le]

/--
The normalization constant dominates one for `p ≥ 2`.

This is the endpoint estimate used in the pointwise majorization proof on
`A1`: on the diagonal, `uA1 p x x = alpha p * x^p` while
`vGeTwo p x x = x^p`.
-/
private lemma one_le_alpha (p : ℝ) (hp : 2 ≤ p) :
    1 ≤ alpha p := by
  rw [alpha_eq_boundary_coeff p hp]
  change 1 ≤ p * ((p - 1) / p) ^ (p - 1)
  let G : ℝ → ℝ := fun t =>
    Real.log t - (t - 1) * Real.log (t / (t - 1))
  have hp_pos : 0 < p := by linarith
  have hp1_pos : 0 < p - 1 := by linarith
  have hG_nonneg : 0 ≤ G p := by
    have hderiv_formula :
        ∀ x, 2 < x → HasDerivAt G (2 / x - Real.log (x / (x - 1))) x := by
      intro x hx2
      have hx_pos : 0 < x := by linarith
      have hx1_pos : 0 < x - 1 := by linarith
      have hdiv_ne : x - 1 ≠ 0 := by linarith
      have hquot_pos : 0 < x / (x - 1) := div_pos hx_pos hx1_pos
      have hquot_ne : x / (x - 1) ≠ 0 := ne_of_gt hquot_pos
      have hlogx : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := by
        simpa [one_div] using Real.hasDerivAt_log (show x ≠ 0 by linarith)
      have hid1 : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
        simpa using (hasDerivAt_id x).sub_const 1
      have hquot :
          HasDerivAt (fun y : ℝ => y / (y - 1)) (-1 / (x - 1) ^ 2) x := by
        have hq := (hasDerivAt_id x).div hid1 hdiv_ne
        simp only [Pi.div_def, id_eq] at hq
        refine hq.congr_deriv ?_
        ring
      have hlogquot :
          HasDerivAt (fun y : ℝ => Real.log (y / (y - 1)))
            ((-1 / (x - 1) ^ 2) / (x / (x - 1))) x := by
        simpa [one_div] using hquot.log hquot_ne
      have hmul :
          HasDerivAt (fun y : ℝ => (y - 1) * Real.log (y / (y - 1)))
            (1 * Real.log (x / (x - 1)) +
              (x - 1) * ((-1 / (x - 1) ^ 2) / (x / (x - 1)))) x :=
        hid1.mul hlogquot
      have hsub := hlogx.sub hmul
      refine hsub.congr_deriv ?_
      field_simp [hx_pos.ne', hx1_pos.ne']
      ring
    have hmono : MonotoneOn G (Set.Ici 2) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 2) ?hcont ?hdiff ?hderiv
      · unfold G
        apply ContinuousOn.sub
        · exact ContinuousOn.log continuousOn_id (by
            intro x hx
            exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx))
        · apply ContinuousOn.mul
          · exact (continuous_id.sub continuous_const).continuousOn
          · apply ContinuousOn.log
            · exact (continuousOn_id.div (continuousOn_id.sub continuousOn_const) (by
                intro x hx
                have hx2 : (2 : ℝ) ≤ x := hx
                linarith))
            · intro x hx
              have hx2 : (2 : ℝ) ≤ x := hx
              exact div_ne_zero (by linarith) (by linarith)
      · intro x hx
        have hx2 : 2 < x := by simpa [interior_Ici] using hx
        exact (hderiv_formula x hx2).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx2 : 2 < x := by simpa [interior_Ici] using hx
        rw [(hderiv_formula x hx2).deriv]
        have hx_pos : 0 < x := by linarith
        have hx1_pos : 0 < x - 1 := by linarith
        have hlog : Real.log (x / (x - 1)) ≤ 1 / (x - 1) := by
          have hpos : 0 < x / (x - 1) := div_pos hx_pos hx1_pos
          have h := Real.log_le_sub_one_of_pos hpos
          have hs : x / (x - 1) - 1 = 1 / (x - 1) := by
            field_simp [hx1_pos.ne']
            ring
          simpa [hs] using h
        have hfrac : 1 / (x - 1) ≤ 2 / x := by
          field_simp [hx_pos.ne', hx1_pos.ne']
          nlinarith
        linarith
    have h2mem : (2 : ℝ) ∈ Set.Ici 2 := by simp
    have hpmem : p ∈ Set.Ici 2 := hp
    have hle := hmono h2mem hpmem hp
    have hG2 : G 2 = 0 := by
      unfold G
      norm_num [Real.log_one]
    linarith
  have hbase_pos : 0 < (p - 1) / p := div_pos hp1_pos hp_pos
  have hpow_pos : 0 < ((p - 1) / p) ^ (p - 1) :=
    Real.rpow_pos_of_pos hbase_pos _
  have hpos : 0 < p * ((p - 1) / p) ^ (p - 1) := mul_pos hp_pos hpow_pos
  have hlogeq :
      Real.log (p * ((p - 1) / p) ^ (p - 1)) = G p := by
    unfold G
    rw [Real.log_mul hp_pos.ne' (ne_of_gt hpow_pos)]
    rw [Real.log_rpow hbase_pos]
    have hlogdiv : Real.log ((p - 1) / p) = -Real.log (p / (p - 1)) := by
      have hinv : ((p - 1) / p)⁻¹ = p / (p - 1) := by
        field_simp [hp_pos.ne', hp1_pos.ne']
      have h := Real.log_inv (x := ((p - 1) / p))
      rw [hinv] at h
      linarith
    rw [hlogdiv]
    ring
  have hlog_nonneg : 0 ≤ Real.log (p * ((p - 1) / p) ^ (p - 1)) := by
    rwa [hlogeq]
  rw [← Real.log_le_log_iff zero_lt_one hpos]
  simpa [Real.log_one] using hlog_nonneg

/-- On the diagonal endpoint of `A1`, `uA1` dominates `vGeTwo`. -/
private lemma vGeTwo_le_uA1_on_diag
    (p : ℝ) (hp : 2 ≤ p) {x : ℝ} (hx : 0 ≤ x) :
    vGeTwo p x x ≤ uA1 p x x := by
  rcases hx.eq_or_lt with rfl | hxpos
  · simp [vGeTwo, uA1, Real.zero_rpow (by linarith : p ≠ 0)]
  · have hp_pos : 0 < p := by linarith
    have hx_nonneg : 0 ≤ x := le_of_lt hxpos
    have halpha := one_le_alpha p hp
    have hv : vGeTwo p x x = x ^ p := by
      have hsum : (x + x) / 2 = x := by ring
      have hdiff : (x - x) / 2 = 0 := by ring
      simp [vGeTwo, hsum, abs_of_pos hxpos, Real.zero_rpow hp_pos.ne']
    have hu : uA1 p x x = alpha p * x ^ p := by
      have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
      have hpow : x ^ (p - 1) * x = x ^ p := by
        have h := Real.rpow_one_add' hx_nonneg (by linarith : 1 + (p - 1) ≠ 0)
        have h' : x ^ p = x * x ^ (p - 1) := by
          -- `rpow_one_add'` writes the product as `x * x^(p-1)`.
          simpa [show 1 + (p - 1) = p by ring] using h
        rw [h']
        ring
      calc
        uA1 p x x =
            alpha p * x ^ (p - 1) * (x - p * (x - x) / 2) := by
          simp [uA1, hxpos, hpStar]
        _ = alpha p * (x ^ (p - 1) * x) := by ring
        _ = alpha p * x ^ p := by rw [hpow]
    rw [hv, hu]
    simpa [one_mul] using
      mul_le_mul_of_nonneg_right halpha (Real.rpow_nonneg hx_nonneg p)

/-- On the A1/A2 boundary, the x-partial formulas agree. -/
private lemma DxuA1_eq_DxvGeTwo_on_A1A2_boundary (p x : ℝ) (hp : 2 ≤ p) (hx : 0 < x) :
    DxuA1 p x ((a p) * x) = DxvGeTwo p x ((a p) * x) := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  have hp1_pos : 0 < p - 1 := by linarith
  simp only [DxuA1, gt_iff_lt, hx, ↓reduceIte, Real.rpow_eq_pow, a, hpStar, DxvGeTwo]
  have h_sum : (x + (1 - 2 / p) * x) / 2 = ((p - 1) / p) * x := by
    field_simp [hp_pos.ne]
    ring
  have h_diff : (x - (1 - 2 / p) * x) / 2 = x / p := by
    field_simp [hp_pos.ne]
    ring
  rw [h_sum, h_diff,
      abs_of_pos (mul_pos (div_pos hp1_pos hp_pos) hx),
      abs_of_pos (div_pos hx hp_pos),
      alpha_eq_boundary_coeff p hp]
  simp_rw [Real.rpow_eq_pow]
  rw [Real.mul_rpow (div_nonneg (by linarith) hp_pos.le) hx.le,
      Real.div_rpow (by linarith : 0 ≤ p - 1) hp_pos.le,
      Real.div_rpow hx.le hp_pos.le]
  have hsplit : (p - 1) ^ p = (p - 1) ^ (p - 1) * (p - 1) := by
    calc
      (p - 1) ^ p = (p - 1) ^ ((p - 1) + 1) := by
        congr 2
        ring
      _ = (p - 1) ^ (p - 1) * (p - 1) ^ (1 : ℝ) := by
            rw [Real.rpow_add hp1_pos]
      _ = (p - 1) ^ (p - 1) * (p - 1) := by
            rw [Real.rpow_one]
  rw [hsplit]
  have hlin : (2 - p) * x + (p - 1) * ((1 - 2 / p) * x) = ((2 - p) / p) * x := by
    field_simp [hp_pos.ne]
    ring
  rw [hlin]
  have hxpow : x ^ (p - 1) = x ^ (p - 2) * x := by
    calc
      x ^ (p - 1) = x ^ ((p - 2) + 1) := by
        congr 2
        ring
      _ = x ^ (p - 2) * x ^ (1 : ℝ) := by
            rw [Real.rpow_add hx]
      _ = x ^ (p - 2) * x := by
            rw [Real.rpow_one]
  calc
    p * ((p - 1) ^ (p - 1) / p ^ (p - 1)) * (p / 2) *
        x ^ (p - 2) * (((2 - p) / p) * x)
        = p * ((p - 1) ^ (p - 1) / p ^ (p - 1)) * (p / 2) *
            (((2 - p) / p) * (x ^ (p - 2) * x)) := by
              ring
    _ = p * ((p - 1) ^ (p - 1) / p ^ (p - 1)) * (p / 2) *
          (((2 - p) / p) * x ^ (p - 1)) := by
            rw [← hxpow]
    _ = ((p - 1) ^ (p - 1) / p ^ (p - 1)) *
          x ^ (p - 1) * (p / 2) -
          (p - 1) ^ (p - 1) * (p - 1) *
            (x ^ (p - 1) / p ^ (p - 1)) * (p / 2) := by
              field_simp [hp_pos.ne]
              ring

/-- On the A1/A2 boundary, the y-partial formulas agree. -/
private lemma DyuA1_eq_DyvGeTwo_on_A1A2_boundary (p x : ℝ) (hp : 2 ≤ p) (hx : 0 < x) :
    DyuA1 p x ((a p) * x) = DyvGeTwo p x ((a p) * x) := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  have hp1_pos : 0 < p - 1 := by linarith
  simp only [DyuA1, gt_iff_lt, hx, ↓reduceIte, Real.rpow_eq_pow, hpStar, DyvGeTwo, a]
  have h_sum : (x + (1 - 2 / p) * x) / 2 = ((p - 1) / p) * x := by
    field_simp [hp_pos.ne]
    ring
  have h_diff : (x - (1 - 2 / p) * x) / 2 = x / p := by
    field_simp [hp_pos.ne]
    ring
  rw [h_sum, h_diff,
      abs_of_pos (mul_pos (div_pos hp1_pos hp_pos) hx),
      abs_of_pos (div_pos hx hp_pos),
      alpha_eq_boundary_coeff p hp]
  simp_rw [Real.rpow_eq_pow]
  rw [Real.mul_rpow (div_nonneg (by linarith) hp_pos.le) hx.le,
      Real.div_rpow (by linarith : 0 ≤ p - 1) hp_pos.le,
      Real.div_rpow hx.le hp_pos.le]
  have hsplit : (p - 1) ^ p = (p - 1) ^ (p - 1) * (p - 1) := by
    calc
      (p - 1) ^ p = (p - 1) ^ ((p - 1) + 1) := by
        congr 2
        ring
      _ = (p - 1) ^ (p - 1) * (p - 1) ^ (1 : ℝ) := by
            rw [Real.rpow_add hp1_pos]
      _ = (p - 1) ^ (p - 1) * (p - 1) := by
            rw [Real.rpow_one]
  rw [hsplit]
  ring

private lemma DxuA1_eq_DxvGeTwo_on_inter (p : ℝ) (hp : 2 ≤ p) (x y : ℝ)
    (h1 : closureA1 p x y) (h2 : closureA2 p x y) :
    DxuA1 p x y = DxvGeTwo p x y := by
  obtain ⟨hx, hay, hyx⟩ := h1
  obtain ⟨_, hmy, hyay⟩ := h2
  have heq : y = a p * x := le_antisymm hyay hay
  rcases hx.lt_or_eq with hxpos | hxeq
  · rw [heq]
    exact DxuA1_eq_DxvGeTwo_on_A1A2_boundary p x hp hxpos
  · have hx0 : x = 0 := hxeq.symm
    subst hx0
    have hy0 : y = 0 := by linarith
    subst hy0
    simp [DxuA1, DxvGeTwo]

private lemma DyuA1_eq_DyvGeTwo_on_inter (p : ℝ) (hp : 2 ≤ p) (x y : ℝ)
    (h1 : closureA1 p x y) (h2 : closureA2 p x y) :
    DyuA1 p x y = DyvGeTwo p x y := by
  obtain ⟨hx, hay, hyx⟩ := h1
  obtain ⟨_, hmy, hyay⟩ := h2
  have heq : y = a p * x := le_antisymm hyay hay
  rcases hx.lt_or_eq with hxpos | hxeq
  · rw [heq]
    exact DyuA1_eq_DyvGeTwo_on_A1A2_boundary p x hp hxpos
  · have hx0 : x = 0 := hxeq.symm
    subst hx0
    have hy0 : y = 0 := by linarith
    subst hy0
    simp [DyuA1, DyvGeTwo]

private lemma auxFunction1_Dx_eq_DxuA1 (p x y : ℝ) (h : closureA1 p x y) :
    DxauxFunction1 p x y = DxuA1 p x y := by
  simp only [DxauxFunction1, h, ite_true]

private lemma auxFunction1_Dx_eq_DxvGeTwo (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (h2 : closureA2 p x y) :
    DxauxFunction1 p x y = DxvGeTwo p x y := by
  simp only [DxauxFunction1]
  by_cases h1 : closureA1 p x y
  · simp only [h1, ite_true]
    exact DxuA1_eq_DxvGeTwo_on_inter p hp x y h1 h2
  · simp only [h1, ite_false, h2, ite_true]

private lemma auxFunction1_Dy_eq_DyuA1 (p x y : ℝ) (h : closureA1 p x y) :
    DyauxFunction1 p x y = DyuA1 p x y := by
  simp only [DyauxFunction1, h, ite_true]

private lemma auxFunction1_Dy_eq_DyvGeTwo (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (h2 : closureA2 p x y) :
    DyauxFunction1 p x y = DyvGeTwo p x y := by
  simp only [DyauxFunction1]
  by_cases h1 : closureA1 p x y
  · simp only [h1, ite_true]
    exact DyuA1_eq_DyvGeTwo_on_inter p hp x y h1 h2
  · simp only [h1, ite_false, h2, ite_true]

private lemma DxauxFunction1_eq_DyauxFunction1_on_diag (p : ℝ) (hp : 2 < p) (x : ℝ)
    (hx : 0 ≤ x) :
    DxauxFunction1 p x x = DyauxFunction1 p x x := by
  have hp' : 2 ≤ p := by linarith
  rcases hx.lt_or_eq with hxpos | hxeq
  · have hlt : a p < 1 := by
      have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
      have hp_pos : 0 < p := by linarith
      rw [a, hpStar]
      have hdiv : 0 < 2 / p := by positivity
      linarith
    have hax : a p * x ≤ x := (mul_le_mul_of_nonneg_right hlt.le hx).trans_eq (one_mul x)
    have hcl : closureA1 p x x := ⟨hx, hax, le_rfl⟩
    calc
      DxauxFunction1 p x x = DxuA1 p x x := auxFunction1_Dx_eq_DxuA1 p x x hcl
      _ = DyuA1 p x x := by
        have hxpow : x ^ (p - 1) = x ^ (p - 2) * x := by
          calc
            x ^ (p - 1) = x ^ ((p - 2) + 1) := by ring_nf
            _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hxpos]
            _ = x ^ (p - 2) * x := by rw [Real.rpow_one]
        simp only [DxuA1, gt_iff_lt, hxpos, ↓reduceIte, Real.rpow_eq_pow, DyuA1,
          pStar_eq_self_of_two_le p hp']
        rw [hxpow]
        ring
      _ = DyauxFunction1 p x x := (auxFunction1_Dy_eq_DyuA1 p x x hcl).symm
  · subst hxeq
    simp [DxauxFunction1, DyauxFunction1, closureA1, DxuA1, DyuA1]

private lemma DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag (p : ℝ) (hp : 2 < p) (x : ℝ)
    (hx : 0 ≤ x) :
    DxauxFunction1 p x (-x) = -DyauxFunction1 p x (-x) := by
  have hp' : 2 ≤ p := by linarith
  rcases hx.lt_or_eq with hxpos | hxeq
  · have ha_nonneg : 0 ≤ a p := by
      have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
      have hp_pos : 0 < p := by linarith
      rw [a, hpStar]
      field_simp [hp_pos.ne]
      nlinarith
    have hcl : closureA2 p x (-x) := by
      refine ⟨hx, le_rfl, ?_⟩
      exact le_trans (neg_nonpos.mpr hx) (mul_nonneg ha_nonneg hx)
    calc
      DxauxFunction1 p x (-x) = DxvGeTwo p x (-x) :=
        auxFunction1_Dx_eq_DxvGeTwo p hp' x (-x) hcl
      _ = -DyvGeTwo p x (-x) := by
        have hp1_ne : p - 1 ≠ 0 := by linarith
        have hdiff : (x - -x) / 2 = x := by ring
        simp [DxvGeTwo, DyvGeTwo, hxpos, hp1_ne, abs_of_pos hxpos]
      _ = -DyauxFunction1 p x (-x) := by
        rw [auxFunction1_Dy_eq_DyvGeTwo p hp' x (-x) hcl]
  · subst hxeq
    simp [DxauxFunction1, DyauxFunction1, closureA1, DxuA1, DyuA1]

private lemma continuousOn_DxauxFunction1 (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (fun z : ℝ × ℝ => DxauxFunction1 p z.1 z.2)
      {z | QuarterPlane z.1 z.2} := by
  have hp1 : 1 < p := by linarith
  let S  := {z : ℝ × ℝ | QuarterPlane z.1 z.2}
  let S1 := {z : ℝ × ℝ | closureA1 p z.1 z.2}
  let S2 := {z : ℝ × ℝ | closureA2 p z.1 z.2}
  have hcover : S ⊆ S1 ∪ S2 := by
    intro ⟨x, y⟩ hz
    simp only [QuarterPlane, closureA1, closureA2, S, S1, S2,
               Set.mem_union, Set.mem_setOf_eq] at *
    obtain ⟨hx, hyx, hmx⟩ := hz
    by_cases h : a p * x ≤ y
    · exact Or.inl ⟨hx, h, hyx⟩
    · exact Or.inr ⟨hx, hmx, le_of_lt (not_le.mp h)⟩
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => DxauxFunction1 p z.1 z.2) (S ∩ S1) := by
    apply ContinuousOn.congr ((continuousOn_DxuA1_closureA1 p hp1).mono
      (fun _ h => h.2))
    intro z hz
    exact auxFunction1_Dx_eq_DxuA1 p z.1 z.2 hz.2
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => DxauxFunction1 p z.1 z.2) (S ∩ S2) := by
    apply ContinuousOn.congr ((continuousOn_DxvGeTwo_closureA2 p hp).mono
      (fun _ h => h.2))
    intro z hz
    exact auxFunction1_Dx_eq_DxvGeTwo p hp z.1 z.2 hz.2
  have hcl1 : IsClosed (S ∩ S1) := by
    apply IsClosed.inter _ (isClosed_closureA1_set p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
       (isClosed_le continuous_fst.neg continuous_snd))
  have hcl2 : IsClosed (S ∩ S2) := by
    apply IsClosed.inter _ (isClosed_closureA2_set p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
       (isClosed_le continuous_fst.neg continuous_snd))
  have hcover' : S ⊆ S ∩ S1 ∪ S ∩ S2 := fun z hz =>
    (hcover hz).imp (And.intro hz) (And.intro hz)
  apply ContinuousOn.mono _ hcover'
  exact hc1.union_of_isClosed hc2 hcl1 hcl2

private lemma continuousOn_DyauxFunction1 (p : ℝ) (hp : 2 < p) :
    ContinuousOn (fun z : ℝ × ℝ => DyauxFunction1 p z.1 z.2)
      {z | QuarterPlane z.1 z.2} := by
  let S  := {z : ℝ × ℝ | QuarterPlane z.1 z.2}
  let S1 := {z : ℝ × ℝ | closureA1 p z.1 z.2}
  let S2 := {z : ℝ × ℝ | closureA2 p z.1 z.2}
  have hp' : 2 ≤ p := by linarith
  have hcover : S ⊆ S1 ∪ S2 := by
    intro ⟨x, y⟩ hz
    simp only [QuarterPlane, closureA1, closureA2, S, S1, S2,
               Set.mem_union, Set.mem_setOf_eq] at *
    obtain ⟨hx, hyx, hmx⟩ := hz
    by_cases h : a p * x ≤ y
    · exact Or.inl ⟨hx, h, hyx⟩
    · exact Or.inr ⟨hx, hmx, le_of_lt (not_le.mp h)⟩
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => DyauxFunction1 p z.1 z.2) (S ∩ S1) := by
    apply ContinuousOn.congr ((continuousOn_DyuA1_closureA1 p hp).mono
      (fun _ h => h.2))
    intro z hz
    exact auxFunction1_Dy_eq_DyuA1 p z.1 z.2 hz.2
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => DyauxFunction1 p z.1 z.2) (S ∩ S2) := by
    apply ContinuousOn.congr ((continuousOn_DyvGeTwo_closureA2 p hp').mono
      (fun _ h => h.2))
    intro z hz
    exact auxFunction1_Dy_eq_DyvGeTwo p hp' z.1 z.2 hz.2
  have hcl1 : IsClosed (S ∩ S1) := by
    apply IsClosed.inter _ (isClosed_closureA1_set p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
       (isClosed_le continuous_fst.neg continuous_snd))
  have hcl2 : IsClosed (S ∩ S2) := by
    apply IsClosed.inter _ (isClosed_closureA2_set p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
       (isClosed_le continuous_fst.neg continuous_snd))
  have hcover' : S ⊆ S ∩ S1 ∪ S ∩ S2 := fun z hz =>
    (hcover hz).imp (And.intro hz) (And.intro hz)
  apply ContinuousOn.mono _ hcover'
  exact hc1.union_of_isClosed hc2 hcl1 hcl2

/-- auxFunction1 is continuous on the QuarterPlane when p ≥ 2. -/
private lemma continuousOn_auxFunction1 (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (fun z : ℝ × ℝ => auxFunction1 p z.1 z.2)
      {z | QuarterPlane z.1 z.2} := by
  have hp1 : 1 < p := by linarith
  let S  := {z : ℝ × ℝ | QuarterPlane z.1 z.2}
  let S1 := {z : ℝ × ℝ | closureA1 p z.1 z.2}
  let S2 := {z : ℝ × ℝ | closureA2 p z.1 z.2}
  -- S is covered by S1 ∪ S2
  have hcover : S ⊆ S1 ∪ S2 := by
    intro ⟨x, y⟩ hz
    simp only [QuarterPlane, closureA1, closureA2, S, S1, S2,
               Set.mem_union, Set.mem_setOf_eq] at *
    obtain ⟨hx, hyx, hmx⟩ := hz
    by_cases h : a p * x ≤ y
    · exact Or.inl ⟨hx, h, hyx⟩
    · exact Or.inr ⟨hx, hmx, le_of_lt (not_le.mp h)⟩
  -- auxFunction1 = uA1 on S1
  have heq1 : ∀ z : ℝ × ℝ, z ∈ S1 →
      auxFunction1 p z.1 z.2 = uA1 p z.1 z.2 :=
    fun ⟨x, y⟩ h1 => auxFunction1_eq_uA1 p x y h1
  -- auxFunction1 = vGeTwo on S2
  have heq2 : ∀ z : ℝ × ℝ, z ∈ S2 →
      auxFunction1 p z.1 z.2 = vGeTwo p z.1 z.2 :=
    fun ⟨x, y⟩ h2 => auxFunction1_eq_vGeTwo p hp x y h2
  -- ContinuousOn on each piece (intersected with S)
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => auxFunction1 p z.1 z.2) (S ∩ S1) := by
    apply ContinuousOn.congr ((continuousOn_uA1 p hp).mono
      (fun ⟨_, _⟩ ⟨hq, _⟩ => hq.1))
    exact fun z ⟨_, h1⟩ => heq1 z h1
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => auxFunction1 p z.1 z.2) (S ∩ S2) := by
    apply ContinuousOn.congr ((continuous_vGeTwo p hp1).continuousOn.mono
      Set.inter_subset_left)
    exact fun z ⟨_, h2⟩ => heq2 z h2
  -- Pieces are closed (as subsets of ℝ²)
  have hcl1 : IsClosed (S ∩ S1) := by
    apply IsClosed.inter _ (isClosed_closureA1_set p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
       (isClosed_le continuous_fst.neg continuous_snd))
  have hcl2 : IsClosed (S ∩ S2) := by
    apply IsClosed.inter _ (isClosed_closureA2_set p)
    simp only [QuarterPlane, S, Set.setOf_and]
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_snd continuous_fst).inter
       (isClosed_le continuous_fst.neg continuous_snd))
  -- Glue on S = (S ∩ S1) ∪ (S ∩ S2)
  have hcover' : S ⊆ S ∩ S1 ∪ S ∩ S2 := fun z hz =>
    (hcover hz).imp (And.intro hz) (And.intro hz)
  apply ContinuousOn.mono _ hcover'
  exact hc1.union_of_isClosed hc2 hcl1 hcl2

private lemma isClosed_setOf_QuarterPlane :
    IsClosed {z : ℝ × ℝ | QuarterPlane z.1 z.2} := by
  simp only [QuarterPlane, Set.setOf_and]
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_snd continuous_fst).inter
      (isClosed_le continuous_fst.neg continuous_snd))

private lemma isClosed_setOf_QuarterPlane2 :
    IsClosed {z : ℝ × ℝ | QuarterPlane2 z.1 z.2} := by
  simp only [QuarterPlane2, Set.setOf_and]
  exact (isClosed_le continuous_fst continuous_const).inter
    ((isClosed_le continuous_snd continuous_fst.neg).inter
      (isClosed_le continuous_fst continuous_snd))

private lemma isClosed_setOf_QuarterPlane3 :
    IsClosed {z : ℝ × ℝ | QuarterPlane3 z.1 z.2} := by
  simp only [QuarterPlane3, Set.setOf_and]
  exact (isClosed_le continuous_const continuous_snd).inter
    ((isClosed_le continuous_snd.neg continuous_fst).inter
      (isClosed_le continuous_fst continuous_snd))

private lemma isClosed_setOf_QuarterPlane4 :
    IsClosed {z : ℝ × ℝ | QuarterPlane4 z.1 z.2} := by
  simp only [QuarterPlane4, Set.setOf_and]
  exact (isClosed_le continuous_snd continuous_const).inter
    ((isClosed_le continuous_snd continuous_fst).inter
      (isClosed_le continuous_fst continuous_snd.neg))

private lemma continuousuCandidate (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Set.univ := by
  let Q1 : Set (ℝ × ℝ) := {z | QuarterPlane z.1 z.2}
  let Q2 : Set (ℝ × ℝ) := {z | QuarterPlane2 z.1 z.2}
  let Q3 : Set (ℝ × ℝ) := {z | QuarterPlane3 z.1 z.2}
  let Q4 : Set (ℝ × ℝ) := {z | QuarterPlane4 z.1 z.2}
  let f1 : ℝ × ℝ → ℝ := fun z => auxFunction1 p z.1 z.2
  let f2 : ℝ × ℝ → ℝ := fun z => auxFunction1 p (-z.1) (-z.2)
  let f3 : ℝ × ℝ → ℝ := fun z => auxFunction1 p z.2 z.1
  let f4 : ℝ × ℝ → ℝ := fun z => auxFunction1 p (-z.2) (-z.1)
  have hcont1 : ContinuousOn f1 Q1 := by
    simpa [Q1, f1] using continuousOn_auxFunction1 p hp
  have hcont2 : ContinuousOn f2 Q2 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.1, -z.2)) Q2 Q1 := by
      intro z hz
      rcases hz with ⟨hx, hy, hxy⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hneg : Continuous (fun z : ℝ × ℝ => (-z.1, -z.2)) := by
      continuity
    simpa [Q1, Q2, f2, Function.comp_def] using
      (continuousOn_auxFunction1 p hp).comp hneg.continuousOn hmap
  have hcont3 : ContinuousOn f3 Q3 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (z.2, z.1)) Q3 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hnyx, hxy⟩
      exact ⟨hy, hxy, hnyx⟩
    have hswap : Continuous (fun z : ℝ × ℝ => (z.2, z.1)) := by
      continuity
    simpa [Q1, Q3, f3, Function.comp_def] using
      (continuousOn_auxFunction1 p hp).comp hswap.continuousOn hmap
  have hcont4 : ContinuousOn f4 Q4 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.2, -z.1)) Q4 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hyx, hxn⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hns : Continuous (fun z : ℝ × ℝ => (-z.2, -z.1)) := by
      continuity
    simpa [Q1, Q4, f4, Function.comp_def] using
      (continuousOn_auxFunction1 p hp).comp hns.continuousOn hmap
  have hcl1 : IsClosed Q1 := isClosed_setOf_QuarterPlane
  have hcl2 : IsClosed Q2 := isClosed_setOf_QuarterPlane2
  have hcl3 : IsClosed Q3 := isClosed_setOf_QuarterPlane3
  have hcl4 : IsClosed Q4 := isClosed_setOf_QuarterPlane4
  have h12 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q2 → f1 z = f2 z := by
    intro z hz1 hz2
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨hx0, hyx, hmx⟩
    rcases hz2 with ⟨hx1, hy, hxy⟩
    have hx : x = 0 := le_antisymm hx1 hx0
    have hy0 : y = 0 := by
      have hy_le : y ≤ 0 := by simpa [hx] using hyx
      have hy_ge : 0 ≤ y := by simpa [hx] using hxy
      exact le_antisymm hy_le hy_ge
    simp [f1, f2, hx, hy0]
  have h13 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q3 → f1 z = f3 z := by
    intro z hz1 hz3
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨_, hyx, _⟩
    rcases hz3 with ⟨_, _, hxy⟩
    have hxy' : x = y := le_antisymm hxy hyx
    simp [f1, f3, hxy']
  have h14 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q4 → f1 z = f4 z := by
    intro z hz1 hz4
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨_, _, hmx⟩
    rcases hz4 with ⟨_, _, hxn⟩
    have hy : y = -x := by linarith [hxn, hmx]
    simp [f1, f4, hy]
  have h23 : ∀ z : ℝ × ℝ, z ∈ Q2 → z ∈ Q3 → f2 z = f3 z := by
    intro z hz2 hz3
    rcases z with ⟨x, y⟩
    rcases hz2 with ⟨_, hy, _⟩
    rcases hz3 with ⟨_, hnyx, _⟩
    have hx : x = -y := le_antisymm (by linarith [hy]) hnyx
    simp [f2, f3, hx]
  have h24 : ∀ z : ℝ × ℝ, z ∈ Q2 → z ∈ Q4 → f2 z = f4 z := by
    intro z hz2 hz4
    rcases z with ⟨x, y⟩
    rcases hz2 with ⟨_, _, hxy⟩
    rcases hz4 with ⟨_, hyx, _⟩
    have hxy' : x = y := le_antisymm hxy hyx
    simp [f2, f4, hxy']
  have h34 : ∀ z : ℝ × ℝ, z ∈ Q3 → z ∈ Q4 → f3 z = f4 z := by
    intro z hz3 hz4
    rcases z with ⟨x, y⟩
    rcases hz3 with ⟨hy0, hnyx, hxy⟩
    rcases hz4 with ⟨hy1, hyx, hxn⟩
    have hy : y = 0 := le_antisymm hy1 hy0
    have hx : x = 0 := by
      have hx_le : x ≤ 0 := by simpa [hy] using hxn
      have hx_ge : 0 ≤ x := by simpa [hy] using hnyx
      exact le_antisymm hx_le hx_ge
    simp [f3, f4, hx, hy]
  have heq1 : ∀ z : ℝ × ℝ, z ∈ Q1 → uCandidate p z.1 z.2 = f1 z := by
    intro z hz1
    have hq1 : QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
    simp [uCandidate, f1, hq1]
  have heq2 : ∀ z : ℝ × ℝ, z ∈ Q2 → uCandidate p z.1 z.2 = f2 z := by
    intro z hz2
    by_cases hz1 : z ∈ Q1
    · have hu : uCandidate p z.1 z.2 = f1 z := heq1 z hz1
      exact hu.trans (h12 z hz1 hz2)
    · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
      have hq2 : QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
      simp [uCandidate, f2, hq1, hq2]
  have heq3 : ∀ z : ℝ × ℝ, z ∈ Q3 → uCandidate p z.1 z.2 = f3 z := by
    intro z hz3
    by_cases hz1 : z ∈ Q1
    · have hu : uCandidate p z.1 z.2 = f1 z := heq1 z hz1
      exact hu.trans (h13 z hz1 hz3)
    · by_cases hz2 : z ∈ Q2
      · have hu : uCandidate p z.1 z.2 = f2 z := heq2 z hz2
        exact hu.trans (h23 z hz2 hz3)
      · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
        have hq2 : ¬ QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
        have hq3 : QuarterPlane3 z.1 z.2 := by simpa [Q3] using hz3
        simp [uCandidate, f3, hq1, hq2, hq3]
  have heq4 : ∀ z : ℝ × ℝ, z ∈ Q4 → uCandidate p z.1 z.2 = f4 z := by
    intro z hz4
    by_cases hz1 : z ∈ Q1
    · have hu : uCandidate p z.1 z.2 = f1 z := heq1 z hz1
      exact hu.trans (h14 z hz1 hz4)
    · by_cases hz2 : z ∈ Q2
      · have hu : uCandidate p z.1 z.2 = f2 z := heq2 z hz2
        exact hu.trans (h24 z hz2 hz4)
      · by_cases hz3 : z ∈ Q3
        · have hu : uCandidate p z.1 z.2 = f3 z := heq3 z hz3
          exact hu.trans (h34 z hz3 hz4)
        · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
          have hq2 : ¬ QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
          have hq3 : ¬ QuarterPlane3 z.1 z.2 := by simpa [Q3] using hz3
          have hq4 : QuarterPlane4 z.1 z.2 := by simpa [Q4] using hz4
          simp [uCandidate, f4, hq1, hq2, hq3, hq4]
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Q1 := by
    apply ContinuousOn.congr hcont1
    intro z hz
    simpa using (heq1 z hz)
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Q2 := by
    apply ContinuousOn.congr hcont2
    intro z hz
    simpa using (heq2 z hz)
  have hc3 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Q3 := by
    apply ContinuousOn.congr hcont3
    intro z hz
    simpa using (heq3 z hz)
  have hc4 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) Q4 := by
    apply ContinuousOn.congr hcont4
    intro z hz
    simpa using (heq4 z hz)
  have hcover : Set.univ ⊆ Q1 ∪ Q2 ∪ Q3 ∪ Q4 := by
    intro z _
    rcases z with ⟨x, y⟩
    by_cases hxy : |x| ≤ |y|
    · by_cases hy : 0 ≤ y
      · have habs : |x| ≤ y := by simpa [abs_of_nonneg hy] using hxy
        rcases abs_le.mp habs with ⟨h1, h2⟩
        -- h1 : -y ≤ x, h2 : x ≤ y
        -- pertence a Q3
        exact Or.inl (Or.inr ⟨hy, h1, h2⟩)
      · have hy' : y < 0 := lt_of_not_ge hy
        have habs : |x| ≤ -y := by
          simpa [abs_of_neg hy'] using hxy
        rcases abs_le.mp habs with ⟨h1, h2⟩
        have h1' : y ≤ x := by
          simpa using h1
        exact Or.inr ⟨le_of_lt hy', h1', h2⟩
    · have hyx : |y| ≤ |x| := by
        rw [not_le] at hxy
        exact le_of_lt hxy
      by_cases hx : 0 ≤ x
      · have habs : |y| ≤ x := by simpa [abs_of_nonneg hx] using hyx
        rcases abs_le.mp habs with ⟨h1, h2⟩
        -- h1 : -x ≤ y, h2 : y ≤ x
        -- pertence a Q1
        exact Or.inl (Or.inl (Or.inl ⟨hx, h2, h1⟩))
      · have hx' : x < 0 := lt_of_not_ge hx
        have habs : |y| ≤ -x := by
         simpa [abs_of_neg hx'] using hyx
        rcases abs_le.mp habs with ⟨h1, h2⟩
        have h1' : x ≤ y := by
         simpa using h1
        exact Or.inl (Or.inl (Or.inr ⟨le_of_lt hx', h2, h1'⟩))
  have hc12 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) (Q1 ∪ Q2) :=
    hc1.union_of_isClosed hc2 hcl1 hcl2
  have hcl12 : IsClosed (Q1 ∪ Q2) := hcl1.union hcl2
  have hc123 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) (Q1 ∪ Q2 ∪ Q3) :=
    hc12.union_of_isClosed hc3 hcl12 hcl3
  have hcl123 : IsClosed (Q1 ∪ Q2 ∪ Q3) := hcl12.union hcl3
  have hc1234 : ContinuousOn (fun z : ℝ × ℝ => uCandidate p z.1 z.2) (Q1 ∪ Q2 ∪ Q3 ∪ Q4) :=
    hc123.union_of_isClosed hc4 hcl123 hcl4
  apply ContinuousOn.mono hc1234
  intro z hz
  exact hcover hz




private lemma continuousDxuCandidate (p : ℝ) (hp : 2 < p) :
    ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Set.univ := by
  have hp' : 2 ≤ p := by linarith
  let Q1 : Set (ℝ × ℝ) := {z | QuarterPlane z.1 z.2}
  let Q2 : Set (ℝ × ℝ) := {z | QuarterPlane2 z.1 z.2}
  let Q3 : Set (ℝ × ℝ) := {z | QuarterPlane3 z.1 z.2}
  let Q4 : Set (ℝ × ℝ) := {z | QuarterPlane4 z.1 z.2}
  let f1 : ℝ × ℝ → ℝ := fun z => DxauxFunction1 p z.1 z.2
  let f2 : ℝ × ℝ → ℝ := fun z => -DxauxFunction1 p (-z.1) (-z.2)
  let f3 : ℝ × ℝ → ℝ := fun z => DyauxFunction1 p z.2 z.1
  let f4 : ℝ × ℝ → ℝ := fun z => -DyauxFunction1 p (-z.2) (-z.1)
  have hcont1 : ContinuousOn f1 Q1 := by
    simpa [Q1, f1] using continuousOn_DxauxFunction1 p hp'
  have hcont2 : ContinuousOn f2 Q2 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.1, -z.2)) Q2 Q1 := by
      intro z hz
      rcases hz with ⟨hx, hy, hxy⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hneg : Continuous (fun z : ℝ × ℝ => (-z.1, -z.2)) := by continuity
    simpa [Q1, Q2, f2, Function.comp_def] using
      ((continuousOn_DxauxFunction1 p hp').comp hneg.continuousOn hmap).neg
  have hcont3 : ContinuousOn f3 Q3 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (z.2, z.1)) Q3 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hnyx, hxy⟩
      exact ⟨hy, hxy, hnyx⟩
    have hswap : Continuous (fun z : ℝ × ℝ => (z.2, z.1)) := by continuity
    simpa [Q1, Q3, f3, Function.comp_def] using
      (continuousOn_DyauxFunction1 p hp).comp hswap.continuousOn hmap
  have hcont4 : ContinuousOn f4 Q4 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.2, -z.1)) Q4 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hyx, hxn⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hns : Continuous (fun z : ℝ × ℝ => (-z.2, -z.1)) := by continuity
    simpa [Q1, Q4, f4, Function.comp_def] using
      ((continuousOn_DyauxFunction1 p hp).comp hns.continuousOn hmap).neg
  have hcl1 : IsClosed Q1 := isClosed_setOf_QuarterPlane
  have hcl2 : IsClosed Q2 := isClosed_setOf_QuarterPlane2
  have hcl3 : IsClosed Q3 := isClosed_setOf_QuarterPlane3
  have hcl4 : IsClosed Q4 := isClosed_setOf_QuarterPlane4
  have h12 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q2 → f1 z = f2 z := by
    intro z hz1 hz2
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨hx0, hyx, _⟩
    rcases hz2 with ⟨hx1, _, hxy⟩
    have hx : x = 0 := le_antisymm hx1 hx0
    have hy : y = 0 := by
      have hy_le : y ≤ 0 := by simpa [hx] using hyx
      have hy_ge : 0 ≤ y := by simpa [hx] using hxy
      exact le_antisymm hy_le hy_ge
    simp [f1, f2, hx, hy, DxauxFunction1, closureA1, DxuA1]
  have h13 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q3 → f1 z = f3 z := by
    intro z hz1 hz3
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨_, hyx, _⟩
    rcases hz3 with ⟨hy0, _, hxy⟩
    have hxy' : x = y := le_antisymm hxy hyx
    subst x
    simpa [f1, f3] using DxauxFunction1_eq_DyauxFunction1_on_diag p hp y hy0
  have h14 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q4 → f1 z = f4 z := by
    intro z hz1 hz4
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨hx0, _, hmx⟩
    rcases hz4 with ⟨_, _, hxn⟩
    have hy : y = -x := by linarith [hxn, hmx]
    subst hy
    simpa [f1, f4] using DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp x hx0
  have h23 : ∀ z : ℝ × ℝ, z ∈ Q2 → z ∈ Q3 → f2 z = f3 z := by
    intro z hz2 hz3
    rcases z with ⟨x, y⟩
    rcases hz2 with ⟨_, hy, _⟩
    rcases hz3 with ⟨hy0, hnyx, _⟩
    have hx : x = -y := le_antisymm (by linarith [hy]) hnyx
    subst x
    have h := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp y hy0
    have h' : -DxauxFunction1 p y (-y) = DyauxFunction1 p y (-y) := by
      linarith
    simpa [f2, f3] using h'
  have h24 : ∀ z : ℝ × ℝ, z ∈ Q2 → z ∈ Q4 → f2 z = f4 z := by
    intro z hz2 hz4
    rcases z with ⟨x, y⟩
    rcases hz2 with ⟨hx0, _, hxy⟩
    rcases hz4 with ⟨_, hyx, _⟩
    have hxy' : x = y := le_antisymm hxy hyx
    subst x
    have hnonneg : 0 ≤ -y := by linarith
    have h := DxauxFunction1_eq_DyauxFunction1_on_diag p hp (-y) hnonneg
    simpa [f2, f4] using congrArg Neg.neg h
  have h34 : ∀ z : ℝ × ℝ, z ∈ Q3 → z ∈ Q4 → f3 z = f4 z := by
    intro z hz3 hz4
    rcases z with ⟨x, y⟩
    rcases hz3 with ⟨hy0, hnyx, _⟩
    rcases hz4 with ⟨hy1, _, hxn⟩
    have hy : y = 0 := le_antisymm hy1 hy0
    have hx : x = 0 := by
      have hx_le : x ≤ 0 := by simpa [hy] using hxn
      have hx_ge : 0 ≤ x := by simpa [hy] using hnyx
      exact le_antisymm hx_le hx_ge
    simp [f3, f4, hx, hy, DyauxFunction1, closureA1, DyuA1]
  have heq1 : ∀ z : ℝ × ℝ, z ∈ Q1 → DxuCandidate p z.1 z.2 = f1 z := by
    intro z hz1
    have hq1 : QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
    simp [DxuCandidate, f1, hq1]
  have heq2 : ∀ z : ℝ × ℝ, z ∈ Q2 → DxuCandidate p z.1 z.2 = f2 z := by
    intro z hz2
    by_cases hz1 : z ∈ Q1
    · exact (heq1 z hz1).trans (h12 z hz1 hz2)
    · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
      have hq2 : QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
      simp [DxuCandidate, f2, hq1, hq2]
  have heq3 : ∀ z : ℝ × ℝ, z ∈ Q3 → DxuCandidate p z.1 z.2 = f3 z := by
    intro z hz3
    by_cases hz1 : z ∈ Q1
    · exact (heq1 z hz1).trans (h13 z hz1 hz3)
    · by_cases hz2 : z ∈ Q2
      · exact (heq2 z hz2).trans (h23 z hz2 hz3)
      · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
        have hq2 : ¬ QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
        have hq3 : QuarterPlane3 z.1 z.2 := by simpa [Q3] using hz3
        simp [DxuCandidate, f3, hq1, hq2, hq3]
  have heq4 : ∀ z : ℝ × ℝ, z ∈ Q4 → DxuCandidate p z.1 z.2 = f4 z := by
    intro z hz4
    by_cases hz1 : z ∈ Q1
    · exact (heq1 z hz1).trans (h14 z hz1 hz4)
    · by_cases hz2 : z ∈ Q2
      · exact (heq2 z hz2).trans (h24 z hz2 hz4)
      · by_cases hz3 : z ∈ Q3
        · exact (heq3 z hz3).trans (h34 z hz3 hz4)
        · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
          have hq2 : ¬ QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
          have hq3 : ¬ QuarterPlane3 z.1 z.2 := by simpa [Q3] using hz3
          have hq4 : QuarterPlane4 z.1 z.2 := by simpa [Q4] using hz4
          simp [DxuCandidate, f4, hq1, hq2, hq3, hq4]
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Q1 := by
    apply ContinuousOn.congr hcont1
    intro z hz
    simpa using heq1 z hz
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Q2 := by
    apply ContinuousOn.congr hcont2
    intro z hz
    simpa using heq2 z hz
  have hc3 : ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Q3 := by
    apply ContinuousOn.congr hcont3
    intro z hz
    simpa using heq3 z hz
  have hc4 : ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Q4 := by
    apply ContinuousOn.congr hcont4
    intro z hz
    simpa using heq4 z hz
  have hcover : Set.univ ⊆ Q1 ∪ Q2 ∪ Q3 ∪ Q4 := by
    intro z _
    rcases z with ⟨x, y⟩
    by_cases hxy : |x| ≤ |y|
    · by_cases hy : 0 ≤ y
      · have habs : |x| ≤ y := by simpa [abs_of_nonneg hy] using hxy
        rcases abs_le.mp habs with ⟨h1, h2⟩
        exact Or.inl (Or.inr ⟨hy, h1, h2⟩)
      · have hy' : y < 0 := lt_of_not_ge hy
        have habs : |x| ≤ -y := by simpa [abs_of_neg hy'] using hxy
        rcases abs_le.mp habs with ⟨h1, h2⟩
        have h1' : y ≤ x := by simpa using h1
        exact Or.inr ⟨le_of_lt hy', h1', h2⟩
    · have hyx : |y| ≤ |x| := le_of_lt (not_le.mp hxy)
      by_cases hx : 0 ≤ x
      · have habs : |y| ≤ x := by simpa [abs_of_nonneg hx] using hyx
        rcases abs_le.mp habs with ⟨h1, h2⟩
        exact Or.inl (Or.inl (Or.inl ⟨hx, h2, h1⟩))
      · have hx' : x < 0 := lt_of_not_ge hx
        have habs : |y| ≤ -x := by simpa [abs_of_neg hx'] using hyx
        rcases abs_le.mp habs with ⟨h1, h2⟩
        have h1' : x ≤ y := by simpa using h1
        exact Or.inl (Or.inl (Or.inr ⟨le_of_lt hx', h2, h1'⟩))
  have hc12 := hc1.union_of_isClosed hc2 hcl1 hcl2
  have hcl12 : IsClosed (Q1 ∪ Q2) := hcl1.union hcl2
  have hc123 := hc12.union_of_isClosed hc3 hcl12 hcl3
  have hcl123 : IsClosed (Q1 ∪ Q2 ∪ Q3) := hcl12.union hcl3
  have hc1234 := hc123.union_of_isClosed hc4 hcl123 hcl4
  exact ContinuousOn.mono hc1234 hcover

private lemma continuousDyuCandidate (p : ℝ) (hp : 2 < p) :
    ContinuousOn (fun z : ℝ × ℝ => DyuCandidate p z.1 z.2) Set.univ := by
  have hp' : 2 ≤ p := by linarith
  let Q1 : Set (ℝ × ℝ) := {z | QuarterPlane z.1 z.2}
  let Q2 : Set (ℝ × ℝ) := {z | QuarterPlane2 z.1 z.2}
  let Q3 : Set (ℝ × ℝ) := {z | QuarterPlane3 z.1 z.2}
  let Q4 : Set (ℝ × ℝ) := {z | QuarterPlane4 z.1 z.2}
  let f1 : ℝ × ℝ → ℝ := fun z => DyauxFunction1 p z.1 z.2
  let f2 : ℝ × ℝ → ℝ := fun z => -DyauxFunction1 p (-z.1) (-z.2)
  let f3 : ℝ × ℝ → ℝ := fun z => DxauxFunction1 p z.2 z.1
  let f4 : ℝ × ℝ → ℝ := fun z => -DxauxFunction1 p (-z.2) (-z.1)
  have hcont1 : ContinuousOn f1 Q1 := by
    simpa [Q1, f1] using continuousOn_DyauxFunction1 p hp
  have hcont2 : ContinuousOn f2 Q2 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.1, -z.2)) Q2 Q1 := by
      intro z hz
      rcases hz with ⟨hx, hy, hxy⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hneg : Continuous (fun z : ℝ × ℝ => (-z.1, -z.2)) := by continuity
    simpa [Q1, Q2, f2, Function.comp_def] using
      ((continuousOn_DyauxFunction1 p hp).comp hneg.continuousOn hmap).neg
  have hcont3 : ContinuousOn f3 Q3 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (z.2, z.1)) Q3 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hnyx, hxy⟩
      exact ⟨hy, hxy, hnyx⟩
    have hswap : Continuous (fun z : ℝ × ℝ => (z.2, z.1)) := by continuity
    simpa [Q1, Q3, f3, Function.comp_def] using
      (continuousOn_DxauxFunction1 p hp').comp hswap.continuousOn hmap
  have hcont4 : ContinuousOn f4 Q4 := by
    have hmap : Set.MapsTo (fun z : ℝ × ℝ => (-z.2, -z.1)) Q4 Q1 := by
      intro z hz
      rcases hz with ⟨hy, hyx, hxn⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    have hns : Continuous (fun z : ℝ × ℝ => (-z.2, -z.1)) := by continuity
    simpa [Q1, Q4, f4, Function.comp_def] using
      ((continuousOn_DxauxFunction1 p hp').comp hns.continuousOn hmap).neg
  have hcl1 : IsClosed Q1 := isClosed_setOf_QuarterPlane
  have hcl2 : IsClosed Q2 := isClosed_setOf_QuarterPlane2
  have hcl3 : IsClosed Q3 := isClosed_setOf_QuarterPlane3
  have hcl4 : IsClosed Q4 := isClosed_setOf_QuarterPlane4
  have h12 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q2 → f1 z = f2 z := by
    intro z hz1 hz2
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨hx0, hyx, _⟩
    rcases hz2 with ⟨hx1, _, hxy⟩
    have hx : x = 0 := le_antisymm hx1 hx0
    have hy : y = 0 := by
      have hy_le : y ≤ 0 := by simpa [hx] using hyx
      have hy_ge : 0 ≤ y := by simpa [hx] using hxy
      exact le_antisymm hy_le hy_ge
    simp [f1, f2, hx, hy, DyauxFunction1, closureA1, DyuA1]
  have h13 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q3 → f1 z = f3 z := by
    intro z hz1 hz3
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨_, hyx, _⟩
    rcases hz3 with ⟨hy0, _, hxy⟩
    have hxy' : x = y := le_antisymm hxy hyx
    subst x
    simpa [f1, f3] using (DxauxFunction1_eq_DyauxFunction1_on_diag p hp y hy0).symm
  have h14 : ∀ z : ℝ × ℝ, z ∈ Q1 → z ∈ Q4 → f1 z = f4 z := by
    intro z hz1 hz4
    rcases z with ⟨x, y⟩
    rcases hz1 with ⟨hx0, _, hmx⟩
    rcases hz4 with ⟨_, _, hxn⟩
    have hy : y = -x := by linarith [hxn, hmx]
    subst y
    have h := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp x hx0
    have h' : DyauxFunction1 p x (-x) = -DxauxFunction1 p x (-x) := by
      linarith
    simpa [f1, f4] using h'
  have h23 : ∀ z : ℝ × ℝ, z ∈ Q2 → z ∈ Q3 → f2 z = f3 z := by
    intro z hz2 hz3
    rcases z with ⟨x, y⟩
    rcases hz2 with ⟨_, hy, _⟩
    rcases hz3 with ⟨hy0, hnyx, _⟩
    have hx : x = -y := le_antisymm (by linarith [hy]) hnyx
    subst x
    have h := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp y hy0
    simpa [f2, f3] using h.symm
  have h24 : ∀ z : ℝ × ℝ, z ∈ Q2 → z ∈ Q4 → f2 z = f4 z := by
    intro z hz2 hz4
    rcases z with ⟨x, y⟩
    rcases hz2 with ⟨hx0, _, hxy⟩
    rcases hz4 with ⟨_, hyx, _⟩
    have hxy' : x = y := le_antisymm hxy hyx
    subst x
    have hnonneg : 0 ≤ -y := by linarith
    have h := DxauxFunction1_eq_DyauxFunction1_on_diag p hp (-y) hnonneg
    simpa [f2, f4] using congrArg Neg.neg h.symm
  have h34 : ∀ z : ℝ × ℝ, z ∈ Q3 → z ∈ Q4 → f3 z = f4 z := by
    intro z hz3 hz4
    rcases z with ⟨x, y⟩
    rcases hz3 with ⟨hy0, hnyx, _⟩
    rcases hz4 with ⟨hy1, _, hxn⟩
    have hy : y = 0 := le_antisymm hy1 hy0
    have hx : x = 0 := by
      have hx_le : x ≤ 0 := by simpa [hy] using hxn
      have hx_ge : 0 ≤ x := by simpa [hy] using hnyx
      exact le_antisymm hx_le hx_ge
    simp [f3, f4, hx, hy, DxauxFunction1, closureA1, DxuA1]
  have heq1 : ∀ z : ℝ × ℝ, z ∈ Q1 → DyuCandidate p z.1 z.2 = f1 z := by
    intro z hz1
    have hq1 : QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
    simp [DyuCandidate, f1, hq1]
  have heq2 : ∀ z : ℝ × ℝ, z ∈ Q2 → DyuCandidate p z.1 z.2 = f2 z := by
    intro z hz2
    by_cases hz1 : z ∈ Q1
    · exact (heq1 z hz1).trans (h12 z hz1 hz2)
    · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
      have hq2 : QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
      simp [DyuCandidate, f2, hq1, hq2]
  have heq3 : ∀ z : ℝ × ℝ, z ∈ Q3 → DyuCandidate p z.1 z.2 = f3 z := by
    intro z hz3
    by_cases hz1 : z ∈ Q1
    · exact (heq1 z hz1).trans (h13 z hz1 hz3)
    · by_cases hz2 : z ∈ Q2
      · exact (heq2 z hz2).trans (h23 z hz2 hz3)
      · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
        have hq2 : ¬ QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
        have hq3 : QuarterPlane3 z.1 z.2 := by simpa [Q3] using hz3
        simp [DyuCandidate, f3, hq1, hq2, hq3]
  have heq4 : ∀ z : ℝ × ℝ, z ∈ Q4 → DyuCandidate p z.1 z.2 = f4 z := by
    intro z hz4
    by_cases hz1 : z ∈ Q1
    · exact (heq1 z hz1).trans (h14 z hz1 hz4)
    · by_cases hz2 : z ∈ Q2
      · exact (heq2 z hz2).trans (h24 z hz2 hz4)
      · by_cases hz3 : z ∈ Q3
        · exact (heq3 z hz3).trans (h34 z hz3 hz4)
        · have hq1 : ¬ QuarterPlane z.1 z.2 := by simpa [Q1] using hz1
          have hq2 : ¬ QuarterPlane2 z.1 z.2 := by simpa [Q2] using hz2
          have hq3 : ¬ QuarterPlane3 z.1 z.2 := by simpa [Q3] using hz3
          have hq4 : QuarterPlane4 z.1 z.2 := by simpa [Q4] using hz4
          simp [DyuCandidate, f4, hq1, hq2, hq3, hq4]
  have hc1 : ContinuousOn (fun z : ℝ × ℝ => DyuCandidate p z.1 z.2) Q1 := by
    apply ContinuousOn.congr hcont1
    intro z hz
    simpa using heq1 z hz
  have hc2 : ContinuousOn (fun z : ℝ × ℝ => DyuCandidate p z.1 z.2) Q2 := by
    apply ContinuousOn.congr hcont2
    intro z hz
    simpa using heq2 z hz
  have hc3 : ContinuousOn (fun z : ℝ × ℝ => DyuCandidate p z.1 z.2) Q3 := by
    apply ContinuousOn.congr hcont3
    intro z hz
    simpa using heq3 z hz
  have hc4 : ContinuousOn (fun z : ℝ × ℝ => DyuCandidate p z.1 z.2) Q4 := by
    apply ContinuousOn.congr hcont4
    intro z hz
    simpa using heq4 z hz
  have hcover : Set.univ ⊆ Q1 ∪ Q2 ∪ Q3 ∪ Q4 := by
    intro z _
    rcases z with ⟨x, y⟩
    by_cases hxy : |x| ≤ |y|
    · by_cases hy : 0 ≤ y
      · have habs : |x| ≤ y := by simpa [abs_of_nonneg hy] using hxy
        rcases abs_le.mp habs with ⟨h1, h2⟩
        exact Or.inl (Or.inr ⟨hy, h1, h2⟩)
      · have hy' : y < 0 := lt_of_not_ge hy
        have habs : |x| ≤ -y := by simpa [abs_of_neg hy'] using hxy
        rcases abs_le.mp habs with ⟨h1, h2⟩
        have h1' : y ≤ x := by simpa using h1
        exact Or.inr ⟨le_of_lt hy', h1', h2⟩
    · have hyx : |y| ≤ |x| := le_of_lt (not_le.mp hxy)
      by_cases hx : 0 ≤ x
      · have habs : |y| ≤ x := by simpa [abs_of_nonneg hx] using hyx
        rcases abs_le.mp habs with ⟨h1, h2⟩
        exact Or.inl (Or.inl (Or.inl ⟨hx, h2, h1⟩))
      · have hx' : x < 0 := lt_of_not_ge hx
        have habs : |y| ≤ -x := by simpa [abs_of_neg hx'] using hyx
        rcases abs_le.mp habs with ⟨h1, h2⟩
        have h1' : x ≤ y := by simpa using h1
        exact Or.inl (Or.inl (Or.inr ⟨le_of_lt hx', h2, h1'⟩))
  have hc12 := hc1.union_of_isClosed hc2 hcl1 hcl2
  have hcl12 : IsClosed (Q1 ∪ Q2) := hcl1.union hcl2
  have hc123 := hc12.union_of_isClosed hc3 hcl12 hcl3
  have hcl123 : IsClosed (Q1 ∪ Q2 ∪ Q3) := hcl12.union hcl3
  have hc1234 := hc123.union_of_isClosed hc4 hcl123 hcl4
  exact ContinuousOn.mono hc1234 hcover
/-- For p > 2, DxuCandidate p x y is continuous in (x, y) on all of ℝ². -/
private lemma continuous_firstPartials_uCandidate (p : ℝ) (hp : 2 < p) :
    ContinuousOn (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) Set.univ ∧
    ContinuousOn (fun z : ℝ × ℝ => DyuCandidate p z.1 z.2) Set.univ := by
  exact ⟨continuousDxuCandidate p hp, continuousDyuCandidate p hp⟩

/-! ## 5. Abstract tangent and gluing private lemmas -/

/-
The analytic target is always a tangent inequality of the form

`f z ≤ f x + d x * (z - x)`.

Inside one smooth sector this follows from concavity.  Across sector boundaries
we prove the estimate on each subsegment and then use the `tangent_glue_*`
private lemmas below.  The derivative comparison hypotheses say that the derivative at
each later break point is no larger than the derivative at the starting point;
this is exactly what lets a tangent line from the start dominate all later
pieces.
-/

private lemma axis_tangent_inequality_of_coordinate_tangents
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

private lemma uCandidate_axis_tangent_inequality_of_coordinate_tangents
    (p : ℝ)
    (hx_tangent :
      ∀ x y h,
        uCandidate p (x + h) y ≤
          uCandidate p x y + DxuCandidate p x y * h)
    (hy_tangent :
      ∀ x y k,
        uCandidate p x (y + k) ≤
          uCandidate p x y + DyuCandidate p x y * k)
    (x y h k : ℝ) (hk : h * k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  exact axis_tangent_inequality_of_coordinate_tangents
    (uCandidate p) (DxuCandidate p) (DyuCandidate p)
    hx_tangent hy_tangent x y h k hk

/-- The displayed axis-tangent inequality for `uCandidate` when the increment is
supported on one coordinate. -/
private lemma uCandidate_axis_tangent_inequality
    (p x y h k : ℝ) (hk : h * k = 0)
    (hx_tangent :
      uCandidate p (x + h) y ≤
        uCandidate p x y + DxuCandidate p x y * h)
    (hy_tangent :
      uCandidate p x (y + k) ≤
        uCandidate p x y + DyuCandidate p x y * k) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  rcases mul_eq_zero.mp hk with hh | hk'
  · subst h
    simpa [add_assoc] using hy_tangent
  · subst k
    simpa [add_assoc] using hx_tangent

private lemma tangent_glue_two_forward
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

/-- Glue two tangent estimates when the target point is to the left of the
starting point.  The sign of `z - m` reverses the derivative comparison. -/
private lemma tangent_glue_two_backward
    (f d : ℝ → ℝ) {x m z : ℝ}
    (hz_m : z ≤ m) (_hmx : m ≤ x)
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

private lemma tangent_glue_three_forward
    (f d : ℝ → ℝ) {x m n z : ℝ}
    (hxm : x ≤ m) (hmn : m ≤ n) (hnz : n ≤ z)
    (hxm_tangent : f m ≤ f x + d x * (m - x))
    (hmn_tangent : f n ≤ f m + d m * (n - m))
    (hnz_tangent : f z ≤ f n + d n * (z - n))
    (hd_mx : d m ≤ d x) (hd_nx : d n ≤ d x) :
    f z ≤ f x + d x * (z - x) := by
  have hxz : x ≤ n := le_trans hxm hmn
  have hxn_tangent : f n ≤ f x + d x * (n - x) :=
    tangent_glue_two_forward f d hxm hmn hxm_tangent hmn_tangent hd_mx
  exact tangent_glue_two_forward f d hxz hnz hxn_tangent hnz_tangent hd_nx

private lemma tangent_glue_three_backward
    (f d : ℝ → ℝ) {x m n z : ℝ}
    (hzn : z ≤ n) (hnm : n ≤ m) (hmx : m ≤ x)
    (hxm_tangent : f m ≤ f x + d x * (m - x))
    (hmn_tangent : f n ≤ f m + d m * (n - m))
    (hnz_tangent : f z ≤ f n + d n * (z - n))
    (hd_xm : d x ≤ d m) (hd_xn : d x ≤ d n) :
    f z ≤ f x + d x * (z - x) := by
  have hnx : n ≤ x := le_trans hnm hmx
  have hxn_tangent : f n ≤ f x + d x * (n - x) :=
    tangent_glue_two_backward f d hnm hmx hxm_tangent hmn_tangent hd_xm
  exact tangent_glue_two_backward f d hzn hnx hxn_tangent hnz_tangent hd_xn

private lemma tangent_glue_four_forward
    (f d : ℝ → ℝ) {x m n r z : ℝ}
    (hxm : x ≤ m) (hmn : m ≤ n) (hnr : n ≤ r) (hrz : r ≤ z)
    (hxm_tangent : f m ≤ f x + d x * (m - x))
    (hmn_tangent : f n ≤ f m + d m * (n - m))
    (hnr_tangent : f r ≤ f n + d n * (r - n))
    (hrz_tangent : f z ≤ f r + d r * (z - r))
    (hd_mx : d m ≤ d x) (hd_nx : d n ≤ d x) (hd_rx : d r ≤ d x) :
    f z ≤ f x + d x * (z - x) := by
  have hxr : x ≤ r := le_trans (le_trans hxm hmn) hnr
  have hxr_tangent : f r ≤ f x + d x * (r - x) :=
    tangent_glue_three_forward f d hxm hmn hnr
      hxm_tangent hmn_tangent hnr_tangent hd_mx hd_nx
  exact tangent_glue_two_forward f d hxr hrz hxr_tangent hrz_tangent hd_rx

private lemma tangent_glue_four_backward
    (f d : ℝ → ℝ) {x m n r z : ℝ}
    (hzr : z ≤ r) (hrn : r ≤ n) (hnm : n ≤ m) (hmx : m ≤ x)
    (hxm_tangent : f m ≤ f x + d x * (m - x))
    (hmn_tangent : f n ≤ f m + d m * (n - m))
    (hnr_tangent : f r ≤ f n + d n * (r - n))
    (hrz_tangent : f z ≤ f r + d r * (z - r))
    (hd_xm : d x ≤ d m) (hd_xn : d x ≤ d n) (hd_xr : d x ≤ d r) :
    f z ≤ f x + d x * (z - x) := by
  have hrx : r ≤ x := le_trans (le_trans hrn hnm) hmx
  have hxr_tangent : f r ≤ f x + d x * (r - x) :=
    tangent_glue_three_backward f d hrn hnm hmx
      hxm_tangent hmn_tangent hnr_tangent hd_xm hd_xn
  exact tangent_glue_two_backward f d hzr hrx hxr_tangent hrz_tangent hd_xr

private lemma concave_tangent_inequality_of_hasDerivAt
    {f : ℝ → ℝ} {x f' : ℝ}
    (hf : ConcaveOn ℝ Set.univ f) (hderiv : HasDerivAt f f' x) (h : ℝ) :
    f (x + h) ≤ f x + f' * h := by
  rcases lt_trichotomy h 0 with hneg | hzero | hpos
  · have hxy : x + h < x := by linarith
    have hslope : f' ≤ slope f (x + h) x :=
      hf.le_slope_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) hxy hderiv
    have hslope' : f' ≤ (f x - f (x + h)) / (x - (x + h)) := by
      simpa [slope_def_field] using hslope
    have hden_pos : 0 < x - (x + h) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hslope' hden_pos.le
    field_simp [hden_pos.ne'] at hmul
    linarith
  · subst h
    simp
  · have hxy : x < x + h := by linarith
    have hslope : slope f x (x + h) ≤ f' :=
      hf.slope_le_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) hxy hderiv
    have hslope' : (f (x + h) - f x) / ((x + h) - x) ≤ f' := by
      simpa [slope_def_field] using hslope
    have hden_pos : 0 < (x + h) - x := by linarith
    have hmul := mul_le_mul_of_nonneg_right hslope' hden_pos.le
    field_simp [hden_pos.ne'] at hmul
    linarith

private lemma concaveOn_Icc_tangent_inequality_of_hasDerivAt
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

private lemma tangent_inequality_on_Icc_of_deriv2_nonpos
    {f : ℝ → ℝ} {a b x z f' : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hfd : DifferentiableOn ℝ f (interior (Set.Icc a b)))
    (hfdd : DifferentiableOn ℝ (deriv f) (interior (Set.Icc a b)))
    (hdd_nonpos : ∀ t ∈ interior (Set.Icc a b), deriv^[2] f t ≤ 0)
    (hx : x ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b)
    (hderiv : HasDerivAt f f' x) :
    f z ≤ f x + f' * (z - x) := by
  exact concaveOn_Icc_tangent_inequality_of_hasDerivAt
    (concaveOn_of_deriv2_nonpos (convex_Icc a b) hcont hfd hfdd hdd_nonpos)
    hx hz hderiv

private lemma tangent_inequality_on_Icc_of_hasDerivWithinAt2_nonpos
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
  exact concaveOn_Icc_tangent_inequality_of_hasDerivAt
    (concaveOn_of_hasDerivWithinAt2_nonpos
      (convex_Icc a b) hcont hf₁ hf₂ hf₂_nonpos)
    hx hz hderiv

private lemma concaveOn_univ_of_hasDerivAt2_nonpos
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''_nonpos : ∀ x, f'' x ≤ 0) :
    ConcaveOn ℝ Set.univ f := by
  have hdiff_all : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hcont : ContinuousOn f Set.univ :=
    hdiff_all.continuous.continuousOn
  have hdiff : DifferentiableOn ℝ f (interior (Set.univ : Set ℝ)) := by
    intro x _
    exact (hdiff_all x).differentiableWithinAt
  have hanti : AntitoneOn (deriv f) (interior (Set.univ : Set ℝ)) := by
    intro x _ y _ hxy
    rw [(hf x).deriv, (hf y).deriv]
    exact antitone_of_hasDerivAt_nonpos hf' hf''_nonpos hxy
  exact hanti.concaveOn_of_deriv convex_univ hcont hdiff

private lemma tangent_inequality_of_hasDerivAt2_nonpos
    {f f' f'' : ℝ → ℝ} {x : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''_nonpos : ∀ x, f'' x ≤ 0) (h : ℝ) :
    f (x + h) ≤ f x + f' x * h := by
  exact concave_tangent_inequality_of_hasDerivAt
    (concaveOn_univ_of_hasDerivAt2_nonpos hf hf' hf''_nonpos) (hf x) h

/-! ## 6. Coordinate-axis tangent inequality under concavity hypotheses -/

/-
These private lemmas are abstract versions of the displayed inequality.  They say that
once we have tangent estimates in each coordinate separately, the `h * k = 0`
case follows immediately by deciding which coordinate increment is zero.
-/

private lemma uCandidate_axis_tangent_inequality_of_concavity
    (p : ℝ)
    (hconc_x : ∀ y, ConcaveOn ℝ Set.univ (fun x => uCandidate p x y))
    (hconc_y : ∀ x, ConcaveOn ℝ Set.univ (fun y => uCandidate p x y))
    (hdx : ∀ x y, HasDerivAt (fun t => uCandidate p t y) (DxuCandidate p x y) x)
    (hdy : ∀ x y, HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x y) y)
    (x y h k : ℝ) (hk : h * k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  apply uCandidate_axis_tangent_inequality_of_coordinate_tangents
  · intro x y h
    exact concave_tangent_inequality_of_hasDerivAt (hconc_x y) (hdx x y) h
  · intro x y k
    exact concave_tangent_inequality_of_hasDerivAt (hconc_y x) (hdy x y) k
  · exact hk

/-- The displayed tangent inequality for `uCandidate` under the coordinatewise
concavity condition.  This is the `hk = 0` (one-coordinate increment) step:
concavity in the active coordinate gives the tangent bound, and the inactive
coordinate contributes zero. -/
private lemma uCandidate_tangent_inequality_of_concavity_condition
    (p x y h k : ℝ) (hk : h * k = 0)
    (hconc_x : ∀ y, ConcaveOn ℝ Set.univ (fun x => uCandidate p x y))
    (hconc_y : ∀ x, ConcaveOn ℝ Set.univ (fun y => uCandidate p x y))
    (hdx : ∀ x y, HasDerivAt (fun t => uCandidate p t y) (DxuCandidate p x y) x)
    (hdy : ∀ x y, HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x y) y) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  exact uCandidate_axis_tangent_inequality_of_concavity
    p hconc_x hconc_y hdx hdy x y h k hk

private lemma uCandidate_axis_tangent_inequality_of_second_derivatives
    (p : ℝ)
    (hdx : ∀ x y, HasDerivAt (fun t => uCandidate p t y) (DxuCandidate p x y) x)
    (hdy : ∀ x y, HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x y) y)
    (hDxx :
      ∀ y, ∃ Dxx : ℝ → ℝ,
        (∀ x, HasDerivAt (fun t => DxuCandidate p t y) (Dxx x) x) ∧
        ∀ x, Dxx x ≤ 0)
    (hDyy :
      ∀ x, ∃ Dyy : ℝ → ℝ,
        (∀ y, HasDerivAt (fun s => DyuCandidate p x s) (Dyy y) y) ∧
        ∀ y, Dyy y ≤ 0)
    (x y h k : ℝ) (hk : h * k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  apply uCandidate_axis_tangent_inequality_of_concavity
  · intro y
    rcases hDxx y with ⟨Dxx, hDxx_deriv, hDxx_nonpos⟩
    exact concaveOn_univ_of_hasDerivAt2_nonpos
      (fun x => hdx x y) hDxx_deriv hDxx_nonpos
  · intro x
    rcases hDyy x with ⟨Dyy, hDyy_deriv, hDyy_nonpos⟩
    exact concaveOn_univ_of_hasDerivAt2_nonpos
      (fun y => hdy x y) hDyy_deriv hDyy_nonpos
  · exact hdx
  · exact hdy
  · exact hk


/-! ## 7. Local differentiability and concavity inside smooth sectors -/

/-
From here on the file proves the concrete hypotheses needed by the abstract
private lemmas above.

The local formulas are smooth away from the axes and sector boundaries.  For
`uA1` and `vGeTwo` we identify their first derivatives, prove that the relevant
second derivatives are non-positive, and package this as tangent inequalities
on intervals contained in one sector.
-/

/-- For p ≥ 2, uA1 p x y is linear (hence concave) in y for fixed x. -/
private lemma concaveOn_uA1_in_y (p : ℝ) (hp : 2 ≤ p) (x : ℝ) :
    ConcaveOn ℝ Set.univ (fun y => uA1 p x y) := by
  rcases le_or_gt x 0 with hx | hx
  · have h0 : ∀ y, uA1 p x y = 0 := fun y => by simp [uA1, not_lt.mpr hx]
    simp_rw [h0]; exact concaveOn_const _ convex_univ
  · -- uA1 p x y is affine in y: slope = alpha p * x^(p-1) * pStar p / 2 ≥ 0
    have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
    -- Write uA1 as a + b * y where a, b are constants in y
    let b := alpha p * x ^ (p - 1) * p / 2
    let a := alpha p * x ^ (p - 1) * x - b * x
    have hcoeff : ∀ y, uA1 p x y = a + b * y := by
      intro y
      simp only [uA1, if_pos hx, hpStar, a, b]
      change alpha p * x ^ (p - 1) * (x - p * (x - y) / 2) =
           alpha p * x ^ (p - 1) * x - alpha p * x ^ (p - 1) * p / 2 * x +
           alpha p * x ^ (p - 1) * p / 2 * y
      ring
    have hb_nn : 0 ≤ b := by
      simp only [b]
      apply div_nonneg _ (by norm_num)
      apply mul_nonneg _ (by linarith)
      apply mul_nonneg _ (Real.rpow_nonneg hx.le _)
      simp only [alpha, hpStar]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg (div_nonneg (by linarith) (by linarith)) _)
    simp_rw [hcoeff]
    exact (concaveOn_const a convex_univ).add
      ((concaveOn_id convex_univ).smul hb_nn)

/-- For p ≥ 2, uA1 p x y is concave in x on {x | y ≤ x}.
    Note: the domain must be {x | y ≤ x}, not {x | 0 ≤ x} — for y > 0 the second
    derivative f''(x) = αp·p·(p-1)·(p-2)/2·x^(p-3)·(y-x) is positive when x < y. -/
private lemma deriv_uA1_eq_DxuA1Fun_on_A1 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA1 : A1 p x y) :
    deriv (fun t => uA1 p t y) x = DxuA1Fun p (x, y) := by
  rcases hA1 with ⟨hx, -, -⟩
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  let g : ℝ → ℝ := fun t =>
    alpha p * ((1 - p / 2) * t ^ p + (p * y / 2) * t ^ (p - 1))
  have hEq : (fun t => uA1 p t y) =ᶠ[nhds x] g := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have ht0 : 0 < t := by simpa [Set.mem_Ioi] using ht
    have hpow : t ^ p = t ^ (p - 1) * t := by
      calc
        t ^ p = t ^ ((p - 1) + (1 : ℝ)) := by ring_nf
        _ = t ^ (p - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_add ht0]
        _ = t ^ (p - 1) * t := by rw [Real.rpow_one]
    simp only [uA1, gt_iff_lt, ht0, ↓reduceIte, Real.rpow_eq_pow, hpStar, g]
    rw [hpow]
    ring
  have hderiv :
      deriv (fun t => uA1 p t y) x = deriv g x := hEq.deriv_eq
  have hxne : x ≠ 0 := by linarith
  have hg :
      deriv g x =
        alpha p * (p / 2) * x ^ (p - 2) * ((2 - p) * x + (p - 1) * y) := by
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
            ((1 - p / 2) * (p * x ^ (p - 1)) +
              (p * y / 2) * ((p - 1) * x ^ (p - 2)))) x := by
      dsimp [g]
      have hsum :=
        ((hd1.const_mul (1 - p / 2)).add (hd2.const_mul (p * y / 2))).const_mul (alpha p)
      simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hsum
    have hpow : x ^ (p - 1) = x ^ (p - 2) * x := by
      calc
        x ^ (p - 1) = x ^ ((p - 2) + (1 : ℝ)) := by ring_nf
        _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hx]
        _ = x ^ (p - 2) * x := by rw [Real.rpow_one]
    calc
      deriv g x
          = alpha p *
              ((1 - p / 2) * (p * x ^ (p - 1)) +
                (p * y / 2) * ((p - 1) * x ^ (p - 2))) := hd.deriv
      _ = alpha p *
            ((1 - p / 2) * (p * (x ^ (p - 2) * x)) +
              (p * y / 2) * ((p - 1) * x ^ (p - 2))) := by rw [hpow]
      _ = alpha p * (p / 2) * x ^ (p - 2) * ((2 - p) * x + (p - 1) * y) := by
          ring_nf
  calc
    deriv (fun t => uA1 p t y) x = deriv g x := hderiv
    _ = alpha p * (p / 2) * x ^ (p - 2) * ((2 - p) * x + (p - 1) * y) := hg
    _ = DxuA1Fun p (x, y) := by simp [DxuA1Fun, DxuA1, hx]

private lemma hasDerivAt_uA1_x_of_pos (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => uA1 p t y) (DxuA1Fun p (x, y)) x := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  let g : ℝ → ℝ := fun t =>
    alpha p * ((1 - p / 2) * t ^ p + (p * y / 2) * t ^ (p - 1))
  have hEq : (fun t => uA1 p t y) =ᶠ[nhds x] g := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have ht0 : 0 < t := by simpa [Set.mem_Ioi] using ht
    have hpow : t ^ p = t ^ (p - 1) * t := by
      calc
        t ^ p = t ^ ((p - 1) + (1 : ℝ)) := by ring_nf
        _ = t ^ (p - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_add ht0]
        _ = t ^ (p - 1) * t := by rw [Real.rpow_one]
    simp only [uA1, gt_iff_lt, ht0, ↓reduceIte, Real.rpow_eq_pow, hpStar, g]
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
          ((1 - p / 2) * (p * x ^ (p - 1)) +
            (p * y / 2) * ((p - 1) * x ^ (p - 2)))) x := by
    dsimp [g]
    have hsum :=
      ((hd1.const_mul (1 - p / 2)).add (hd2.const_mul (p * y / 2))).const_mul (alpha p)
    simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hsum
  have hpow : x ^ (p - 1) = x ^ (p - 2) * x := by
    calc
      x ^ (p - 1) = x ^ ((p - 2) + (1 : ℝ)) := by ring_nf
      _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hx]
      _ = x ^ (p - 2) * x := by rw [Real.rpow_one]
  have hg :
      HasDerivAt g
        (alpha p * (p / 2) * x ^ (p - 2) * ((2 - p) * x + (p - 1) * y)) x := by
    refine hd.congr_deriv ?_
    calc
      alpha p *
          ((1 - p / 2) * (p * x ^ (p - 1)) +
            (p * y / 2) * ((p - 1) * x ^ (p - 2)))
        = alpha p *
            ((1 - p / 2) * (p * (x ^ (p - 2) * x)) +
              (p * y / 2) * ((p - 1) * x ^ (p - 2))) := by rw [hpow]
      _ = alpha p * (p / 2) * x ^ (p - 2) * ((2 - p) * x + (p - 1) * y) := by ring_nf
  refine (hg.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DxuA1Fun, DxuA1, hx]

private lemma differentiableAt_DxuA1Fun_x_of_pos
    (p x y : ℝ) (hx : 0 < x) :
    DifferentiableAt ℝ (fun t => DxuA1Fun p (t, y)) x := by
  have hEq :
      (fun t => DxuA1Fun p (t, y)) =ᶠ[nhds x]
        fun t => alpha p * (p / 2) * t ^ (p - 2) *
          ((2 - p) * t + (p - 1) * y) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have htpos : 0 < t := by simpa using ht
    simp [DxuA1Fun, DxuA1, htpos]
  have hpow :
      DifferentiableAt ℝ (fun t : ℝ => t ^ (p - 2)) x := by
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).differentiableAt
  have hlin :
      DifferentiableAt ℝ (fun t : ℝ => (2 - p) * t + (p - 1) * y) x := by
    exact ((differentiableAt_id.const_mul (2 - p)).add
      (differentiableAt_const ((p - 1) * y)))
  have hformula :
      DifferentiableAt ℝ
        (fun t : ℝ => alpha p * (p / 2) * t ^ (p - 2) *
          ((2 - p) * t + (p - 1) * y)) x := by
    exact ((hpow.const_mul (alpha p * (p / 2))).mul hlin)
  exact hformula.congr_of_eventuallyEq hEq

private lemma Dxx_uA1_nonpos (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA1 : A1 p x y)
    : 0 ≥ deriv (deriv (fun x => uA1 p x y)) x := by
  rcases hA1 with ⟨hx, hax, hyx⟩
  let g : ℝ → ℝ := fun t =>
    alpha p * ((1 - p / 2) * t ^ p + (p * y / 2) * t ^ (p - 1))
  have hEq : (fun t => uA1 p t y) =ᶠ[nhds x] g := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    have ht0 : 0 < t := by simpa [Set.mem_Ioi] using ht
    have hpow : t ^ p = t ^ (p - 1) * t := by
      calc
        t ^ p = t ^ ((p - 1) + (1 : ℝ)) := by ring_nf
        _ = t ^ (p - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_add ht0]
        _ = t ^ (p - 1) * t := by rw [Real.rpow_one]
    simp only [uA1, gt_iff_lt, ht0, ↓reduceIte, Real.rpow_eq_pow, pStar_eq_self_of_two_le p hp, g]
    rw [hpow]
    ring
  have hderiv2 :
      deriv (deriv (fun t => uA1 p t y)) x = deriv (deriv g) x := by
    exact hEq.deriv.deriv_eq
  have hxne : x ≠ 0 := by linarith
  have hp_ge1 : 1 ≤ p := by linarith
  have hp1_ge1 : 1 ≤ p - 1 := by linarith
  have hg1_formula :
      deriv g x =
        alpha p *
          ((1 - p / 2) * (p * x ^ (p - 1)) +
            (p * y / 2) * ((p - 1) * x ^ (p - 2))) := by
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
            ((1 - p / 2) * (p * x ^ (p - 1)) +
              (p * y / 2) * ((p - 1) * x ^ (p - 2)))) x := by
      dsimp [g]
      have h :=
        ((hd1.const_mul (1 - p / 2)).add (hd2.const_mul (p * y / 2))).const_mul (alpha p)
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    exact hd.deriv
  have hg2 :
      deriv (deriv g) x =
        -(alpha p * p * (p - 1) * (p - 2) * x ^ (p - 3) * (x - y) / 2) := by
    have hxne2 : x ≠ 0 ∨ 1 ≤ p - 1 := Or.inl hxne
    have hxne3 : x ≠ 0 ∨ 1 ≤ p - 2 := Or.inl hxne
    have hd1 :
        HasDerivAt (fun t : ℝ => t ^ (p - 1)) ((p - 1) * x ^ (p - 2)) x := by
      have h := (Real.hasDerivAt_rpow_const hxne2 :
        HasDerivAt (fun t : ℝ => t ^ (p - 1))
          ((p - 1) * x ^ ((p - 1) - 1)) x)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        show p + (-1 + -1) = p + -2 by ring] using h
    have hd2 :
        HasDerivAt (fun t : ℝ => t ^ (p - 2)) ((p - 2) * x ^ (p - 3)) x := by
      have h := (Real.hasDerivAt_rpow_const hxne3 :
        HasDerivAt (fun t : ℝ => t ^ (p - 2))
          ((p - 2) * x ^ ((p - 2) - 1)) x)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        show p + (-1 + -2) = p + -3 by ring] using h
    have hd :
        HasDerivAt
          (fun t =>
            alpha p *
              ((1 - p / 2) * (p * t ^ (p - 1)) +
                (p * y / 2) * ((p - 1) * t ^ (p - 2))))
          (alpha p *
            ((1 - p / 2) * (p * ((p - 1) * x ^ (p - 2))) +
              (p * y / 2) * ((p - 1) * ((p - 2) * x ^ (p - 3))))) x := by
      have h_deriv_combined :
          HasDerivAt
            (fun t =>
              alpha p *
                (p * (1 - p / 2) * t ^ (p - 1) +
                  (p * y / 2 * (p - 1)) * t ^ (p - 2)))
            (alpha p *
              (p * (1 - p / 2) * ((p - 1) * x ^ (p - 2)) +
                (p * y / 2 * (p - 1)) * ((p - 2) * x ^ (p - 3)))) x := by
        exact
          ((hd1.const_mul (p * (1 - p / 2))).add
            (hd2.const_mul (p * y / 2 * (p - 1)))).const_mul (alpha p)
      simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using
        h_deriv_combined
    have hfun :
        deriv g =
          fun t =>
            alpha p *
              ((1 - p / 2) * (p * t ^ (p - 1)) +
                (p * y / 2) * ((p - 1) * t ^ (p - 2))) := by
      funext t
      have hp_t : t ≠ 0 ∨ 1 ≤ p := Or.inr hp_ge1
      have hp1_t : t ≠ 0 ∨ 1 ≤ p - 1 := Or.inr hp1_ge1
      have hd1t :
          HasDerivAt (fun s : ℝ => s ^ p) (p * t ^ (p - 1)) t := by
        simpa using
          (Real.hasDerivAt_rpow_const hp_t :
            HasDerivAt (fun s : ℝ => s ^ p) (p * t ^ (p - 1)) t)
      have hd2t :
          HasDerivAt (fun s : ℝ => s ^ (p - 1)) ((p - 1) * t ^ (p - 2)) t := by
        have h := (Real.hasDerivAt_rpow_const hp1_t :
          HasDerivAt (fun s : ℝ => s ^ (p - 1))
            ((p - 1) * t ^ ((p - 1) - 1)) t)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
          show p + (-1 + -1) = p + -2 by ring] using h
      have hdt :
          HasDerivAt g
            (alpha p *
              ((1 - p / 2) * (p * t ^ (p - 1)) +
                (p * y / 2) * ((p - 1) * t ^ (p - 2)))) t := by
        dsimp [g]
        have h :=
          ((hd1t.const_mul (1 - p / 2)).add
            (hd2t.const_mul (p * y / 2))).const_mul (alpha p)
        simpa using h
      exact hdt.deriv
    rw [hfun]
    rw [hd.deriv]
    have hx_pos : (0 : ℝ) < x := hx
    have hshift : x ^ (p - 3) * x = x ^ (p - 2) := by
      nth_rewrite 2 [← Real.rpow_one x]
      rw [← Real.rpow_add hx_pos (p - 3) 1]
      congr 1
      ring
    have hshift' : x ^ (p - 2) = x ^ (p - 3) * x := by
      simpa [eq_comm] using hshift
    rw [hshift']
    ring
  rw [hderiv2, hg2]
  have hα : 0 ≤ alpha p := by
    rw [alpha, pStar_eq_self_of_two_le p hp]
    apply mul_nonneg
    · linarith
    · apply Real.rpow_nonneg
      apply div_nonneg <;> linarith
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hp2 : 0 ≤ p - 2 := by linarith
  have hpow : 0 ≤ x ^ (p - 3) := by
    exact Real.rpow_nonneg hx.le _
  have hxy : 0 ≤ x - y := by
    linarith
  have hnonneg :
      0 ≤ alpha p * p * (p - 1) * (p - 2) * x ^ (p - 3) * (x - y) / 2 := by
    apply div_nonneg
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg hα hp0)
              hp1)
            hp2)
          hpow)
        hxy
    · norm_num
  linarith

private lemma deriv_DxuA1Fun_x_nonpos_on_A1
    (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA1 : A1 p x y) :
    deriv (fun t => DxuA1Fun p (t, y)) x ≤ 0 := by
  rcases hA1 with ⟨hx, hay, hyx⟩
  have hEq :
      (fun t => deriv (fun s => uA1 p s y) t) =ᶠ[nhds x]
        fun t => DxuA1Fun p (t, y) := by
    have h0 : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
    have hA : {t : ℝ | a p * t < y} ∈ nhds x := by
      have hcont : ContinuousAt (fun t : ℝ => y - a p * t) x :=
        (continuous_const.sub (continuous_const.mul continuous_id')).continuousAt
      have hypos : 0 < y - a p * x := by linarith
      simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hypos)
    have hY : {t : ℝ | y < t} ∈ nhds x := Ioi_mem_nhds hyx
    filter_upwards [h0, hA, hY] with t ht0 htA htY
    exact deriv_uA1_eq_DxuA1Fun_on_A1 p hp t y ⟨ht0, htA, htY⟩
  have hDxx : deriv (deriv (fun s => uA1 p s y)) x ≤ 0 :=
    Dxx_uA1_nonpos p hp x y ⟨hx, hay, hyx⟩
  rwa [hEq.deriv_eq] at hDxx

private lemma uA1_tangent_x_on_Icc_of_A1
    (p : ℝ) (hp : 2 ≤ p) {a b x z y f' : ℝ}
    (hIcc_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ t)
    (hA1_int : ∀ t ∈ interior (Set.Icc a b), A1 p t y)
    (hx : x ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b)
    (hderiv : HasDerivAt (fun t => uA1 p t y) f' x) :
    uA1 p z y ≤ uA1 p x y + f' * (z - x) := by
  apply tangent_inequality_on_Icc_of_hasDerivWithinAt2_nonpos
      (f := fun t => uA1 p t y)
      (f₁ := fun t => DxuA1Fun p (t, y))
      (f₂ := fun t => deriv (fun s => DxuA1Fun p (s, y)) t)
  · have hpair : ContinuousOn (fun t : ℝ => (t, y)) (Set.Icc a b) :=
      (by continuity : Continuous (fun t : ℝ => (t, y))).continuousOn
    exact (continuousOn_uA1 p hp).comp hpair (by
      intro t ht
      exact hIcc_nonneg t ht)
  · intro t ht
    exact (hasDerivAt_uA1_x_of_pos p hp t y (hA1_int t ht).1).hasDerivWithinAt
  · intro t ht
    exact (differentiableAt_DxuA1Fun_x_of_pos p t y (hA1_int t ht).1).hasDerivAt.hasDerivWithinAt
  · intro t ht
    exact deriv_DxuA1Fun_x_nonpos_on_A1 p hp t y (hA1_int t ht)
  · exact hx
  · exact hz
  · exact hderiv

private lemma Dyy_uA1_nonpos (p : ℝ) (_hp : 2 ≤ p) (x y : ℝ) (hA1 : A1 p x y)
    : 0 ≥ deriv (deriv (fun y => uA1 p x y)) y := by
  rcases hA1 with ⟨hx, -, -⟩
  let c : ℝ := alpha p * x ^ (p - 1) * (x - pStar p * x / 2)
  let m : ℝ := alpha p * x ^ (p - 1) * (pStar p / 2)
  have hrepr : (fun t => uA1 p x t) = fun t => c + m * t := by
    funext t
    simp [uA1, hx, c, m]
    ring
  rw [hrepr]
  have hderiv_lin : deriv (fun t => c + m * t) = fun _ => m := by
    funext t
    have hlin : HasDerivAt (fun s : ℝ => c + m * s) m t := by
      simpa [one_mul] using (((hasDerivAt_id t).const_mul m).const_add c)
    exact hlin.deriv
  rw [hderiv_lin]
  simp

private lemma deriv_uA1_eq_DyuA1Fun_on_A1 (p : ℝ) (hp : 2 < p) (x y : ℝ) (hA1 : A1 p x y) :
    deriv (fun s => uA1 p x s) y = DyuA1Fun p (x, y) := by
  rcases hA1 with ⟨hx, -, -⟩
  have hp' : 2 ≤ p := by linarith
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
  let c : ℝ := alpha p * x ^ (p - 1) * (x - pStar p * x / 2)
  let m : ℝ := alpha p * x ^ (p - 1) * (pStar p / 2)
  have hrepr : (fun s => uA1 p x s) = fun s => c + m * s := by
    funext s
    simp [uA1, hx, c, m]
    ring
  have hderiv_lin : deriv (fun s => c + m * s) = fun _ => m := by
    funext s
    have hlin : HasDerivAt (fun z : ℝ => c + m * z) m s := by
      simpa [one_mul] using (((hasDerivAt_id s).const_mul m).const_add c)
    exact hlin.deriv
  calc
    deriv (fun s => uA1 p x s) y = deriv (fun s => c + m * s) y := by rw [hrepr]
    _ = m := by rw [hderiv_lin]
    _ = DyuA1Fun p (x, y) := by
        simp [DyuA1Fun, DyuA1, m, hx, hpStar]

private lemma hasDerivAt_uA1_y_of_pos (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hx : 0 < x) :
    HasDerivAt (fun s => uA1 p x s) (DyuA1Fun p (x, y)) y := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  let c : ℝ := alpha p * x ^ (p - 1) * (x - pStar p * x / 2)
  let m : ℝ := alpha p * x ^ (p - 1) * (pStar p / 2)
  have hrepr : (fun s => uA1 p x s) = fun s => c + m * s := by
    funext s
    simp [uA1, hx, c, m]
    ring
  have hderiv_lin : HasDerivAt (fun s => c + m * s) m y := by
    simpa [one_mul] using (((hasDerivAt_id y).const_mul m).const_add c)
  rw [hrepr]
  convert hderiv_lin using 1
  simp [DyuA1Fun, DyuA1, m, hx, hpStar]

private lemma differentiableAt_DyuA1Fun_y_of_pos
    (p x y : ℝ) (hx : 0 < x) :
    DifferentiableAt ℝ (fun s => DyuA1Fun p (x, s)) y := by
  have hEq :
      (fun s => DyuA1Fun p (x, s)) =ᶠ[nhds y]
        fun _s => alpha p * x ^ (p - 1) * (pStar p / 2) := by
    filter_upwards with s
    simp [DyuA1Fun, DyuA1, hx]
  exact (differentiableAt_const
    (alpha p * x ^ (p - 1) * (pStar p / 2))).congr_of_eventuallyEq hEq

private lemma deriv_DyuA1Fun_y_nonpos_on_A1
    (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA1 : A1 p x y) :
    deriv (fun s => DyuA1Fun p (x, s)) y ≤ 0 := by
  rcases hA1 with ⟨hx, hay, hyx⟩
  have hEq :
      (fun s => deriv (fun r => uA1 p x r) s) =ᶠ[nhds y]
        fun s => DyuA1Fun p (x, s) := by
    have hA : {s : ℝ | a p * x < s} ∈ nhds y := Ioi_mem_nhds hay
    have hY : {s : ℝ | s < x} ∈ nhds y := Iio_mem_nhds hyx
    filter_upwards [hA, hY] with s hsA hsY
    exact (hasDerivAt_uA1_y_of_pos p hp x s hx).deriv
  have hDyy : deriv (deriv (fun r => uA1 p x r)) y ≤ 0 :=
    Dyy_uA1_nonpos p hp x y ⟨hx, hay, hyx⟩
  rwa [hEq.deriv_eq] at hDyy

private lemma uA1_tangent_y_on_Icc_of_A1
    (p : ℝ) (hp : 2 ≤ p) {lo hi y z x f' : ℝ}
    (hx_pos : 0 < x)
    (hA1_int : ∀ t ∈ interior (Set.Icc lo hi), A1 p x t)
    (hy : y ∈ Set.Icc lo hi) (hz : z ∈ Set.Icc lo hi)
    (hderiv : HasDerivAt (fun t => uA1 p x t) f' y) :
    uA1 p x z ≤ uA1 p x y + f' * (z - y) := by
  have hcont : ContinuousOn (fun t => uA1 p x t) (Set.Icc lo hi) := by
    have hpair : ContinuousOn (fun t : ℝ => (x, t)) (Set.Icc lo hi) :=
      (by continuity : Continuous (fun t : ℝ => (x, t))).continuousOn
    exact (continuousOn_uA1 p hp).comp hpair (by
      intro t _ht
      exact hx_pos.le)
  apply tangent_inequality_on_Icc_of_hasDerivWithinAt2_nonpos
      (f := fun t => uA1 p x t)
      (f₁ := fun t => DyuA1Fun p (x, t))
      (f₂ := fun t => deriv (fun s => DyuA1Fun p (x, s)) t)
  · exact hcont
  · intro t _ht
    exact (hasDerivAt_uA1_y_of_pos p hp x t hx_pos).hasDerivWithinAt
  · intro t _ht
    exact (differentiableAt_DyuA1Fun_y_of_pos p x t hx_pos).hasDerivAt.hasDerivWithinAt
  · intro t ht
    exact deriv_DyuA1Fun_y_nonpos_on_A1 p hp x t (hA1_int t ht)
  · exact hy
  · exact hz
  · exact hderiv

private lemma Dxy_uA1_nonneg (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA1 : A1 p x y) :
    0 ≤ deriv (fun x => deriv (fun y => uA1 p x y) y) x := by
    rcases hA1 with ⟨hx, -, -⟩
    have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
    let g : ℝ → ℝ := fun t => alpha p * (p / 2) * t ^ (p - 1)
    have hEq :
        (fun t => deriv (fun y => uA1 p t y) y) =ᶠ[nhds x] g := by
      filter_upwards [Ioi_mem_nhds hx] with t ht
      have ht0 : 0 < t := by simpa [Set.mem_Ioi] using ht
      let c : ℝ := alpha p * t ^ (p - 1) * (t - pStar p * t / 2)
      let m : ℝ := alpha p * t ^ (p - 1) * (pStar p / 2)
      have hrepr : (fun s => uA1 p t s) = fun s => c + m * s := by
        funext s
        simp [uA1, ht0, c, m]
        ring
      have hderiv_lin : deriv (fun s => c + m * s) = fun _ => m := by
        funext s
        have hlin : HasDerivAt (fun z : ℝ => c + m * z) m s := by
          simpa [one_mul] using (((hasDerivAt_id s).const_mul m).const_add c)
        exact hlin.deriv
      calc
        deriv (fun y => uA1 p t y) y = deriv (fun s => c + m * s) y := by rw [hrepr]
        _ = m := by rw [hderiv_lin]
        _ = g t := by
          simp [g, m, hpStar]; ring
    have hderiv_outer :
        deriv (fun x => deriv (fun y => uA1 p x y) y) x = deriv g x :=
      hEq.deriv_eq
    have hxne : x ≠ 0 := by linarith
    have hg :
        deriv g x = alpha p * (p / 2) * ((p - 1) * x ^ (p - 2)) := by
      have hxne1 : x ≠ 0 ∨ 1 ≤ p - 1 := Or.inl hxne
      have hrpow :
          HasDerivAt (fun t : ℝ => t ^ (p - 1)) ((p - 1) * x ^ (p - 2)) x := by
        have h := (Real.hasDerivAt_rpow_const hxne1 :
          HasDerivAt (fun t : ℝ => t ^ (p - 1))
            ((p - 1) * x ^ ((p - 1) - 1)) x)
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
          show p + (-1 + -1) = p + -2 by ring] using h
      have hg' :
          HasDerivAt g (alpha p * (p / 2) * ((p - 1) * x ^ (p - 2))) x := by
        simpa [g, mul_assoc, mul_left_comm, mul_comm] using
          (hrpow.const_mul (alpha p * (p / 2)))
      exact hg'.deriv
    rw [hderiv_outer, hg]
    have hα : 0 ≤ alpha p := by
      rw [alpha, hpStar]
      apply mul_nonneg
      · linarith
      · apply Real.rpow_nonneg
        apply div_nonneg <;> linarith
    have hp0 : 0 ≤ p / 2 := by linarith
    have hp1 : 0 ≤ p - 1 := by linarith
    have hpow : 0 ≤ x ^ (p - 2) := Real.rpow_nonneg hx.le _
    exact mul_nonneg
      (mul_nonneg hα hp0)
      (mul_nonneg hp1 hpow)

private lemma deriv_vGeTwo_eq_DxvGeTwo_on_A2 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    deriv (fun t => vGeTwo p t y) x = DxvGeTwo p x y := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hp1 : 1 ≤ p := by linarith
  have hyx : y < x := by
    rw [a, pStar_eq_self_of_two_le p hp] at hay
    have hp0 : 0 < p := by linarith
    have hcoeff : 1 - 2 / p < (1 : ℝ) := by
      have hdiv : 0 < 2 / p := by positivity
      linarith
    have hax_lt_x : (1 - 2 / p) * x < x := by
      simpa using mul_lt_mul_of_pos_right hcoeff hx
    linarith
  have hsum : 0 < (x + y) / 2 := by linarith
  have hdiff : 0 < (x - y) / 2 := by linarith
  let g : ℝ → ℝ := fun t =>
    ((t + y) / 2) ^ p - (p - 1) ^ p * (((t - y) / 2) ^ p)
  have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq : (fun t => vGeTwo p t y) =ᶠ[nhds x] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with t ht_sum ht_diff
    simp [vGeTwo, g, abs_of_pos ht_sum, abs_of_pos ht_diff]
  have hderiv :
      deriv (fun t => vGeTwo p t y) x = deriv g x := hEq.deriv_eq
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
  have hg :
      deriv g x =
        ((x + y) / 2) ^ (p - 1) * (p / 2) -
          (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2) := by
    have hd :
        HasDerivAt g
          (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((x - y) / 2) ^ (p - 1)) * (1 / 2))) x := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    calc
      deriv g x
          = p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
              (p - 1) ^ p * (p * (((x - y) / 2) ^ (p - 1)) * (1 / 2)) := hd.deriv
      _ = ((x + y) / 2) ^ (p - 1) * (p / 2) -
            (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2) := by ring
  calc
    deriv (fun t => vGeTwo p t y) x = deriv g x := hderiv
    _ = ((x + y) / 2) ^ (p - 1) * (p / 2) -
          (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2) := hg
    _ = DxvGeTwo p x y := by
      simp [DxvGeTwo, hx, abs_of_pos hsum, abs_of_pos hdiff]

private lemma hasDerivAt_vGeTwo_x_of_pos (p : ℝ) (_hp : 2 ≤ p) (x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    HasDerivAt (fun t => vGeTwo p t y) (DxvGeTwo p x y) x := by
  let g : ℝ → ℝ := fun t =>
    ((t + y) / 2) ^ p - (p - 1) ^ p * (((t - y) / 2) ^ p)
  have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq : (fun t => vGeTwo p t y) =ᶠ[nhds x] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with t ht_sum ht_diff
    simp [vGeTwo, g, abs_of_pos ht_sum, abs_of_pos ht_diff]
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
          (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2)) x := by
    have htmp :
        HasDerivAt g
          (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((x - y) / 2) ^ (p - 1)) * (1 / 2))) x := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    refine htmp.congr_deriv ?_
    ring
  have hx : 0 < x := by linarith
  refine (hd.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DxvGeTwo, hx, abs_of_pos hsum, abs_of_pos hdiff]

private lemma differentiableAt_DxvGeTwo_x_of_pos (p x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    DifferentiableAt ℝ (fun t => DxvGeTwo p t y) x := by
  have hx : 0 < x := by linarith
  have hEq :
      (fun t => DxvGeTwo p t y) =ᶠ[nhds x]
        fun t =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) -
            (p - 1) ^ p * ((t - y) / 2) ^ (p - 1) * (p / 2) := by
    have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
      exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hsum))
    have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
      exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hdiff))
    have hx_nhds : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
    filter_upwards [hx_nhds, hsum_nhds, hdiff_nhds] with t ht htsum htdiff
    simp [DxvGeTwo, ht, abs_of_pos htsum, abs_of_pos htdiff]
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
            (p - 1) ^ p * ((t - y) / 2) ^ (p - 1) * (p / 2)) x := by
    exact (hsum_diff.mul_const (p / 2)).sub
      ((hdiff_diff.const_mul ((p - 1) ^ p)).mul_const (p / 2))
  exact hformula.congr_of_eventuallyEq hEq

private lemma deriv_vGeTwo_eq_DyvGeTwo_on_A2 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    deriv (fun s => vGeTwo p x s) y = DyvGeTwo p x y := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hp1 : 1 ≤ p := by linarith
  have hyx : y < x := by
    rw [a, pStar_eq_self_of_two_le p hp] at hay
    have hp0 : 0 < p := by linarith
    have hcoeff : 1 - 2 / p < (1 : ℝ) := by
      have hdiv : 0 < 2 / p := by positivity
      linarith
    have hax_lt_x : (1 - 2 / p) * x < x := by
      simpa using mul_lt_mul_of_pos_right hcoeff hx
    linarith
  have hsum : 0 < (x + y) / 2 := by linarith
  have hdiff : 0 < (x - y) / 2 := by linarith
  let g : ℝ → ℝ := fun s =>
    ((x + s) / 2) ^ p - (p - 1) ^ p * (((x - s) / 2) ^ p)
  have hsum_nhds : {s : ℝ | 0 < (x + s) / 2} ∈ nhds y := by
    exact ((((continuous_const.add continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {s : ℝ | 0 < (x - s) / 2} ∈ nhds y := by
    exact ((((continuous_const.sub continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq : (fun s => vGeTwo p x s) =ᶠ[nhds y] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with s hs_sum hs_diff
    simp [vGeTwo, g, abs_of_pos hs_sum, abs_of_pos hs_diff]
  have hderiv :
      deriv (fun s => vGeTwo p x s) y = deriv g y := hEq.deriv_eq
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
  have hg :
      deriv g y =
        ((x + y) / 2) ^ (p - 1) * (p / 2) +
          (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2) := by
    have hd :
        HasDerivAt g
          (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((x - y) / 2) ^ (p - 1)) * (-(1 / 2)))) y := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    calc
      deriv g y
          = p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
              (p - 1) ^ p * (p * (((x - y) / 2) ^ (p - 1)) * (-(1 / 2))) := hd.deriv
      _ = ((x + y) / 2) ^ (p - 1) * (p / 2) +
            (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2) := by ring
  calc
    deriv (fun s => vGeTwo p x s) y = deriv g y := hderiv
    _ = ((x + y) / 2) ^ (p - 1) * (p / 2) +
          (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2) := hg
    _ = DyvGeTwo p x y := by
      simp [DyvGeTwo, hx, abs_of_pos hsum, abs_of_pos hdiff]

private lemma hasDerivAt_vGeTwo_y_of_pos (p : ℝ) (_hp : 2 ≤ p) (x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    HasDerivAt (fun s => vGeTwo p x s) (DyvGeTwo p x y) y := by
  let g : ℝ → ℝ := fun s =>
    ((x + s) / 2) ^ p - (p - 1) ^ p * (((x - s) / 2) ^ p)
  have hsum_nhds : {s : ℝ | 0 < (x + s) / 2} ∈ nhds y := by
    exact ((((continuous_const.add continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {s : ℝ | 0 < (x - s) / 2} ∈ nhds y := by
    exact ((((continuous_const.sub continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq : (fun s => vGeTwo p x s) =ᶠ[nhds y] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with s hs_sum hs_diff
    simp [vGeTwo, g, abs_of_pos hs_sum, abs_of_pos hs_diff]
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
          (p - 1) ^ p * (((x - y) / 2) ^ (p - 1)) * (p / 2)) y := by
    have htmp :
        HasDerivAt g
          (p * (((x + y) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((x - y) / 2) ^ (p - 1)) * (-(1 / 2)))) y := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    refine htmp.congr_deriv ?_
    ring
  have hx : 0 < x := by linarith
  refine (hd.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DyvGeTwo, hx, abs_of_pos hsum, abs_of_pos hdiff]

private lemma differentiableAt_DyvGeTwo_y_of_pos (p x y : ℝ)
    (hsum : 0 < (x + y) / 2) (hdiff : 0 < (x - y) / 2) :
    DifferentiableAt ℝ (fun s => DyvGeTwo p x s) y := by
  have hx : 0 < x := by linarith
  have hEq :
      (fun s => DyvGeTwo p x s) =ᶠ[nhds y]
        fun s =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) +
            (p - 1) ^ p * ((x - s) / 2) ^ (p - 1) * (p / 2) := by
    have hsum_nhds : {s : ℝ | 0 < (x + s) / 2} ∈ nhds y := by
      exact ((((continuous_const.add continuous_id').div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hsum))
    have hdiff_nhds : {s : ℝ | 0 < (x - s) / 2} ∈ nhds y := by
      exact ((((continuous_const.sub continuous_id').div_const 2).continuousAt).preimage_mem_nhds
        (Ioi_mem_nhds hdiff))
    filter_upwards [hsum_nhds, hdiff_nhds] with s hssum hsdiff
    simp [DyvGeTwo, hx, abs_of_pos hssum, abs_of_pos hsdiff]
  have hsum_diff :
      DifferentiableAt ℝ (fun s : ℝ => ((x + s) / 2) ^ (p - 1)) y := by
    have hbase : DifferentiableAt ℝ (fun s : ℝ => (x + s) / 2) y :=
      by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          ((((differentiableAt_const x).add differentiableAt_id).const_mul (1 / 2 : ℝ)))
    exact hbase.rpow_const (Or.inl (ne_of_gt hsum))
  have hdiff_diff :
      DifferentiableAt ℝ (fun s : ℝ => ((x - s) / 2) ^ (p - 1)) y := by
    have hbase : DifferentiableAt ℝ (fun s : ℝ => (x - s) / 2) y :=
      by
        simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          ((((differentiableAt_const x).sub differentiableAt_id).const_mul (1 / 2 : ℝ)))
    exact hbase.rpow_const (Or.inl (ne_of_gt hdiff))
  have hformula :
      DifferentiableAt ℝ
        (fun s : ℝ =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) +
            (p - 1) ^ p * ((x - s) / 2) ^ (p - 1) * (p / 2)) y := by
    exact (hsum_diff.mul_const (p / 2)).add
      ((hdiff_diff.const_mul ((p - 1) ^ p)).mul_const (p / 2))
  exact hformula.congr_of_eventuallyEq hEq

private lemma hasDerivAt_vGeTwo_x_on_antidiag_pos (p : ℝ) (hp : 2 < p)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => vGeTwo p t (-x)) (DxvGeTwo p x (-x)) x := by
  let g : ℝ → ℝ := fun t =>
    |((t - x) / 2)| ^ p - (p - 1) ^ p * |((t + x) / 2)| ^ p
  have hEq : (fun t => vGeTwo p t (-x)) = g := by
    ext t
    simp [vGeTwo, g, sub_eq_add_neg]
  have hp1 : 1 < p := by linarith
  have hbase_sum :
      HasDerivAt (fun t : ℝ => (t - x) / 2) (1 / 2) x := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).add_const (-x)).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun t : ℝ => (t + x) / 2) (1 / 2) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).add_const x).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun t : ℝ => |((t - x) / 2)| ^ p) 0 x := by
    have h :
        HasDerivAt (fun s : ℝ => |s| ^ p)
          (p * |(x - x) / 2| ^ (p - 2) * ((x - x) / 2)) ((x - x) / 2) :=
      hasDerivAt_abs_rpow ((x - x) / 2) hp1
    have hcomp := h.comp x hbase_sum
    simp only [Function.comp_def] at hcomp
    refine hcomp.congr_deriv ?_
    simp
  have hpow_diff :
      HasDerivAt (fun t : ℝ => |((t + x) / 2)| ^ p)
        (p * x ^ (p - 1) * (1 / 2)) x := by
    have h :
        HasDerivAt (fun s : ℝ => |s| ^ p)
          (p * |(x + x) / 2| ^ (p - 2) * ((x + x) / 2)) ((x + x) / 2) :=
      hasDerivAt_abs_rpow ((x + x) / 2) hp1
    have hcomp := h.comp x hbase_diff
    refine hcomp.congr_deriv ?_
    have hpow : x ^ (p - 1) = x ^ (p - 2) * x := by
      calc
        x ^ (p - 1) = x ^ ((p - 2) + (1 : ℝ)) := by ring_nf
        _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hx]
        _ = x ^ (p - 2) * x := by rw [Real.rpow_one]
    simp [abs_of_pos hx, hpow]
    ring
  have hd :
      HasDerivAt g
        (-(p - 1) ^ p * (p * x ^ (p - 1) * (1 / 2))) x := by
    have htmp :
        HasDerivAt g
          (0 - (p - 1) ^ p * (p * x ^ (p - 1) * (1 / 2))) x := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    simpa using htmp
  rw [hEq]
  refine hd.congr_deriv ?_
  have hp1_ne : p - 1 ≠ 0 := by linarith
  simp [DxvGeTwo, hx, hp1_ne, abs_of_pos hx]
  ring

private lemma hasDerivAt_vGeTwo_y_on_antidiag_pos (p : ℝ) (hp : 2 < p)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun s => vGeTwo p x s) (DyvGeTwo p x (-x)) (-x) := by
  let g : ℝ → ℝ := fun s =>
    |((x + s) / 2)| ^ p - (p - 1) ^ p * |((x - s) / 2)| ^ p
  have hEq : (fun s => vGeTwo p x s) = g := by
    ext s
    rfl
  have hp1 : 1 < p := by linarith
  have hbase_sum :
      HasDerivAt (fun s : ℝ => (x + s) / 2) (1 / 2) (-x) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id (-x)).const_add x).const_mul (1 / 2 : ℝ))
  have hbase_diff :
      HasDerivAt (fun s : ℝ => (x - s) / 2) (-(1 / 2)) (-x) := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((((hasDerivAt_id (-x)).neg).const_add x).const_mul (1 / 2 : ℝ))
  have hpow_sum :
      HasDerivAt (fun s : ℝ => |((x + s) / 2)| ^ p) 0 (-x) := by
    have h :
        HasDerivAt (fun t : ℝ => |t| ^ p)
          (p * |(x + -x) / 2| ^ (p - 2) * ((x + -x) / 2)) ((x + -x) / 2) :=
      hasDerivAt_abs_rpow ((x + -x) / 2) hp1
    have hcomp := h.comp (-x) hbase_sum
    simp only [Function.comp_def] at hcomp
    refine hcomp.congr_deriv ?_
    simp
  have hpow_diff :
      HasDerivAt (fun s : ℝ => |((x - s) / 2)| ^ p)
        (p * x ^ (p - 1) * (-(1 / 2))) (-x) := by
    have h :
        HasDerivAt (fun t : ℝ => |t| ^ p)
          (p * |(x - -x) / 2| ^ (p - 2) * ((x - -x) / 2)) ((x - -x) / 2) :=
      hasDerivAt_abs_rpow ((x - -x) / 2) hp1
    have hcomp := h.comp (-x) hbase_diff
    refine hcomp.congr_deriv ?_
    have hpow : x ^ (p - 1) = x ^ (p - 2) * x := by
      calc
        x ^ (p - 1) = x ^ ((p - 2) + (1 : ℝ)) := by ring_nf
        _ = x ^ (p - 2) * x ^ (1 : ℝ) := by rw [Real.rpow_add hx]
        _ = x ^ (p - 2) * x := by rw [Real.rpow_one]
    simp [abs_of_pos hx, hpow]
    ring
  have hd :
      HasDerivAt g
        (-((p - 1) ^ p * (p * x ^ (p - 1) * (-(1 / 2))))) (-x) := by
    have htmp :
        HasDerivAt g
          (0 - (p - 1) ^ p * (p * x ^ (p - 1) * (-(1 / 2)))) (-x) := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    simpa using htmp
  rw [hEq]
  refine hd.congr_deriv ?_
  have hp1_ne : p - 1 ≠ 0 := by linarith
  simp [DyvGeTwo, hx, hp1_ne, abs_of_pos hx]
  ring

private lemma vGeTwo_A2_second_bracket_nonpos (p : ℝ) (hp : 2 ≤ p)
    (x y : ℝ) (hA2 : A2 p x y) :
    ((x + y) / 2) ^ (p - 2) -
      (p - 1) ^ p * ((x - y) / 2) ^ (p - 2) ≤ 0 := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  have hp1_nonneg : 0 ≤ p - 1 := by linarith
  have hp1_one : 1 ≤ p - 1 := by linarith
  have hp2_nonneg : 0 ≤ p - 2 := by linarith
  have hsum_pos : 0 < (x + y) / 2 := by linarith
  have hdiff_pos : 0 < (x - y) / 2 := by
    have hyx : y < x := by
      rw [a, hpStar] at hay
      have hcoeff : 1 - 2 / p < (1 : ℝ) := by
        have hdiv : 0 < 2 / p := by positivity
        linarith
      have hax_lt_x : (1 - 2 / p) * x < x := by
        simpa using mul_lt_mul_of_pos_right hcoeff hx
      linarith
    linarith
  have hay' : p * y < (p - 2) * x := by
    rw [a, hpStar] at hay
    have h := mul_lt_mul_of_pos_left hay hp_pos
    field_simp [hp_pos.ne] at h
    linarith
  have hAB : (x + y) / 2 ≤ (p - 1) * ((x - y) / 2) := by
    nlinarith [le_of_lt hay']
  have hpow_le :
      ((x + y) / 2) ^ (p - 2) ≤
        ((p - 1) * ((x - y) / 2)) ^ (p - 2) :=
    Real.rpow_le_rpow hsum_pos.le hAB hp2_nonneg
  have hsplit :
      ((p - 1) * ((x - y) / 2)) ^ (p - 2) =
        (p - 1) ^ (p - 2) * ((x - y) / 2) ^ (p - 2) := by
    rw [Real.mul_rpow hp1_nonneg hdiff_pos.le]
  have hbase :
      (p - 1) ^ (p - 2) ≤ (p - 1) ^ p :=
    Real.rpow_le_rpow_of_exponent_le hp1_one (by linarith)
  have hright :
      (p - 1) ^ (p - 2) * ((x - y) / 2) ^ (p - 2) ≤
        (p - 1) ^ p * ((x - y) / 2) ^ (p - 2) :=
    mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hdiff_pos.le _)
  linarith

private lemma Dxx_vGeTwo_formula_on_A2 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    deriv (deriv (fun t => vGeTwo p t y)) x =
      (p * (p - 1) / 4) *
        (((x + y) / 2) ^ (p - 2) -
          (p - 1) ^ p * ((x - y) / 2) ^ (p - 2)) := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hp_ge1 : 1 ≤ p := by linarith
  have hp1_ge1 : 1 ≤ p - 1 := by linarith
  have hyx : y < x := by
    rw [a, pStar_eq_self_of_two_le p hp] at hay
    have hp0 : 0 < p := by linarith
    have hcoeff : 1 - 2 / p < (1 : ℝ) := by
      have hdiv : 0 < 2 / p := by positivity
      linarith
    have hax_lt_x : (1 - 2 / p) * x < x := by
      simpa using mul_lt_mul_of_pos_right hcoeff hx
    linarith
  have hsum : 0 < (x + y) / 2 := by linarith
  have hdiff : 0 < (x - y) / 2 := by linarith
  let g : ℝ → ℝ := fun t =>
    ((t + y) / 2) ^ p - (p - 1) ^ p * (((t - y) / 2) ^ p)
  have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq : (fun t => vGeTwo p t y) =ᶠ[nhds x] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with t ht_sum ht_diff
    simp [vGeTwo, g, abs_of_pos ht_sum, abs_of_pos ht_diff]
  have hderiv2 :
      deriv (deriv (fun t => vGeTwo p t y)) x = deriv (deriv g) x :=
    hEq.deriv.deriv_eq
  have hfun :
      deriv g =
        fun t =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) -
            (p - 1) ^ p * (((t - y) / 2) ^ (p - 1)) * (p / 2) := by
    funext t
    have hbase_sum :
        HasDerivAt (fun s : ℝ => (s + y) / 2) (1 / 2) t := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id t).add_const y).const_mul (1 / 2 : ℝ))
    have hbase_diff :
        HasDerivAt (fun s : ℝ => (s - y) / 2) (1 / 2) t := by
      simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id t).add_const (-y)).const_mul (1 / 2 : ℝ))
    have hpow_sum :
        HasDerivAt (fun s : ℝ => ((s + y) / 2) ^ p)
          (p * (((t + y) / 2) ^ (p - 1)) * (1 / 2)) t := by
      have hrpow :
          HasDerivAt (fun u : ℝ => u ^ p) (p * (((t + y) / 2) ^ (p - 1)))
            ((t + y) / 2) := by
        simpa using
          (Real.hasDerivAt_rpow_const (Or.inr hp_ge1) :
            HasDerivAt (fun u : ℝ => u ^ p) (p * ((t + y) / 2) ^ (p - 1))
              ((t + y) / 2))
      have hcomp := hrpow.comp t hbase_sum
      simp only [Function.comp_def] at hcomp
      convert hcomp using 2
    have hpow_diff :
        HasDerivAt (fun s : ℝ => ((s - y) / 2) ^ p)
          (p * (((t - y) / 2) ^ (p - 1)) * (1 / 2)) t := by
      have hrpow :
          HasDerivAt (fun u : ℝ => u ^ p) (p * (((t - y) / 2) ^ (p - 1)))
            ((t - y) / 2) := by
        simpa using
          (Real.hasDerivAt_rpow_const (Or.inr hp_ge1) :
            HasDerivAt (fun u : ℝ => u ^ p) (p * ((t - y) / 2) ^ (p - 1))
              ((t - y) / 2))
      have hcomp := hrpow.comp t hbase_diff
      simp only [Function.comp_def] at hcomp
      convert hcomp using 2
    have hd :
        HasDerivAt g
          (p * (((t + y) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((t - y) / 2) ^ (p - 1)) * (1 / 2))) t := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    calc
      deriv g t =
          p * (((t + y) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((t - y) / 2) ^ (p - 1)) * (1 / 2)) := hd.deriv
      _ = ((t + y) / 2) ^ (p - 1) * (p / 2) -
            (p - 1) ^ p * (((t - y) / 2) ^ (p - 1)) * (p / 2) := by ring
  have hd2 :
      HasDerivAt
        (fun t =>
          ((t + y) / 2) ^ (p - 1) * (p / 2) -
            (p - 1) ^ p * (((t - y) / 2) ^ (p - 1)) * (p / 2))
        ((p * (p - 1) / 4) *
          (((x + y) / 2) ^ (p - 2) -
            (p - 1) ^ p * ((x - y) / 2) ^ (p - 2))) x := by
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
          (Real.hasDerivAt_rpow_const (Or.inr hp1_ge1) :
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
          (Real.hasDerivAt_rpow_const (Or.inr hp1_ge1) :
            HasDerivAt (fun u : ℝ => u ^ (p - 1))
              ((p - 1) * ((x - y) / 2) ^ ((p - 1) - 1)) ((x - y) / 2))
      have hcomp := hrpow.comp x hbase_diff
      simp only [Function.comp_def] at hcomp
      convert hcomp using 2
    have hd :
        HasDerivAt
          (fun t =>
            ((t + y) / 2) ^ (p - 1) * (p / 2) -
              (p - 1) ^ p * (((t - y) / 2) ^ (p - 1)) * (p / 2))
          (((p - 1) * (((x + y) / 2) ^ (p - 2)) * (1 / 2)) * (p / 2) -
            (p - 1) ^ p *
              (((p - 1) * (((x - y) / 2) ^ (p - 2)) * (1 / 2))) *
                (p / 2)) x := by
      exact (hpow_sum.mul_const (p / 2)).sub
        ((hpow_diff.const_mul ((p - 1) ^ p)).mul_const (p / 2))
    refine hd.congr_deriv ?_
    ring
  rw [hderiv2, hfun]
  exact hd2.deriv

private lemma Dxx_vGeTwo_nonpos (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    0 ≥ deriv (deriv (fun x => vGeTwo p x y)) x := by
  rw [Dxx_vGeTwo_formula_on_A2 p hp x y hA2]
  have hcoef : 0 ≤ p * (p - 1) / 4 := by
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hbr := vGeTwo_A2_second_bracket_nonpos p hp x y hA2
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hcoef hbr]

private lemma deriv_DxvGeTwo_x_nonpos_on_A2
    (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    deriv (fun t => DxvGeTwo p t y) x ≤ 0 := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hEq :
      (fun t => deriv (fun s => vGeTwo p s y) t) =ᶠ[nhds x]
        fun t => DxvGeTwo p t y := by
    have h0 : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
    have hN : {t : ℝ | -t < y} ∈ nhds x := by
      have hxy : -y < x := by linarith
      have hset : {t : ℝ | -t < y} = Set.Ioi (-y) := by
        ext t; simp [neg_lt]
      rw [hset]
      exact Ioi_mem_nhds hxy
    have hA : {t : ℝ | y < a p * t} ∈ nhds x := by
      have hcont : ContinuousAt (fun t : ℝ => a p * t - y) x :=
        ((continuous_const.mul continuous_id').sub continuous_const).continuousAt
      have hapos : 0 < a p * x - y := by linarith
      simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hapos)
    filter_upwards [h0, hN, hA] with t ht0 htN htA
    exact deriv_vGeTwo_eq_DxvGeTwo_on_A2 p hp t y ⟨ht0, htN, htA⟩
  have hDxx : deriv (deriv (fun s => vGeTwo p s y)) x ≤ 0 :=
    Dxx_vGeTwo_nonpos p hp x y ⟨hx, hneg, hay⟩
  rwa [hEq.deriv_eq] at hDxx

private lemma vGeTwo_tangent_x_on_Icc_of_A2
    (p : ℝ) (hp : 2 ≤ p) {lo hi x z y f' : ℝ}
    (hA2_int : ∀ t ∈ interior (Set.Icc lo hi), A2 p t y)
    (hx : x ∈ Set.Icc lo hi) (hz : z ∈ Set.Icc lo hi)
    (hderiv : HasDerivAt (fun t => vGeTwo p t y) f' x) :
    vGeTwo p z y ≤ vGeTwo p x y + f' * (z - x) := by
  have hcont : ContinuousOn (fun t => vGeTwo p t y) (Set.Icc lo hi) := by
    have hp1 : 1 < p := by linarith
    have hpair : Continuous (fun t : ℝ => (t, y)) := by continuity
    have hcomp := ((continuous_vGeTwo p hp1).comp hpair).continuousOn
      (s := Set.Icc lo hi)
    simpa [Function.comp_def] using hcomp
  apply tangent_inequality_on_Icc_of_hasDerivWithinAt2_nonpos
      (f := fun t => vGeTwo p t y)
      (f₁ := fun t => DxvGeTwo p t y)
      (f₂ := fun t => deriv (fun s => DxvGeTwo p s y) t)
  · exact hcont
  · intro t ht
    have hA2 := hA2_int t ht
    have hsum : 0 < (t + y) / 2 := by linarith [hA2.1, hA2.2.1]
    have hdiff : 0 < (t - y) / 2 := by
      have hyx : y < t := by
        have hp0 : 0 < p := by linarith
        have hcoeff : 1 - 2 / p < (1 : ℝ) := by
          have hdiv : 0 < 2 / p := by positivity
          linarith
        have hay : y < (1 - 2 / p) * t := by
          simpa [a, pStar_eq_self_of_two_le p hp] using hA2.2.2
        have hax_lt_x : (1 - 2 / p) * t < t := by
          simpa using mul_lt_mul_of_pos_right hcoeff hA2.1
        linarith
      linarith
    exact (hasDerivAt_vGeTwo_x_of_pos p hp t y hsum hdiff).hasDerivWithinAt
  · intro t ht
    have hA2 := hA2_int t ht
    have hsum : 0 < (t + y) / 2 := by linarith [hA2.1, hA2.2.1]
    have hdiff : 0 < (t - y) / 2 := by
      have hyx : y < t := by
        have hp0 : 0 < p := by linarith
        have hcoeff : 1 - 2 / p < (1 : ℝ) := by
          have hdiv : 0 < 2 / p := by positivity
          linarith
        have hay : y < (1 - 2 / p) * t := by
          simpa [a, pStar_eq_self_of_two_le p hp] using hA2.2.2
        have hax_lt_x : (1 - 2 / p) * t < t := by
          simpa using mul_lt_mul_of_pos_right hcoeff hA2.1
        linarith
      linarith
    exact (differentiableAt_DxvGeTwo_x_of_pos p t y hsum hdiff).hasDerivAt.hasDerivWithinAt
  · intro t ht
    exact deriv_DxvGeTwo_x_nonpos_on_A2 p hp t y (hA2_int t ht)
  · exact hx
  · exact hz
  · exact hderiv

private lemma Dyy_vGeTwo_formula_on_A2 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    deriv (deriv (fun s => vGeTwo p x s)) y =
      (p * (p - 1) / 4) *
        (((x + y) / 2) ^ (p - 2) -
          (p - 1) ^ p * ((x - y) / 2) ^ (p - 2)) := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hp_ge1 : 1 ≤ p := by linarith
  have hp1_ge1 : 1 ≤ p - 1 := by linarith
  have hyx : y < x := by
    rw [a, pStar_eq_self_of_two_le p hp] at hay
    have hp0 : 0 < p := by linarith
    have hcoeff : 1 - 2 / p < (1 : ℝ) := by
      have hdiv : 0 < 2 / p := by positivity
      linarith
    have hax_lt_x : (1 - 2 / p) * x < x := by
      simpa using mul_lt_mul_of_pos_right hcoeff hx
    linarith
  have hsum : 0 < (x + y) / 2 := by linarith
  have hdiff : 0 < (x - y) / 2 := by linarith
  let g : ℝ → ℝ := fun s =>
    ((x + s) / 2) ^ p - (p - 1) ^ p * (((x - s) / 2) ^ p)
  have hsum_nhds : {s : ℝ | 0 < (x + s) / 2} ∈ nhds y := by
    exact ((((continuous_const.add continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {s : ℝ | 0 < (x - s) / 2} ∈ nhds y := by
    exact ((((continuous_const.sub continuous_id').div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq : (fun s => vGeTwo p x s) =ᶠ[nhds y] g := by
    filter_upwards [hsum_nhds, hdiff_nhds] with s hs_sum hs_diff
    simp [vGeTwo, g, abs_of_pos hs_sum, abs_of_pos hs_diff]
  have hderiv2 :
      deriv (deriv (fun s => vGeTwo p x s)) y = deriv (deriv g) y :=
    hEq.deriv.deriv_eq
  have hfun :
      deriv g =
        fun s =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) +
            (p - 1) ^ p * (((x - s) / 2) ^ (p - 1)) * (p / 2) := by
    funext s
    have hbase_sum :
        HasDerivAt (fun u : ℝ => (x + u) / 2) (1 / 2) s := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id s).const_add x).const_mul (1 / 2 : ℝ))
    have hbase_diff :
        HasDerivAt (fun u : ℝ => (x - u) / 2) (-(1 / 2)) s := by
      simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        ((((hasDerivAt_id s).neg).const_add x).const_mul (1 / 2 : ℝ))
    have hpow_sum :
        HasDerivAt (fun u : ℝ => ((x + u) / 2) ^ p)
          (p * (((x + s) / 2) ^ (p - 1)) * (1 / 2)) s := by
      have hrpow :
          HasDerivAt (fun u : ℝ => u ^ p) (p * (((x + s) / 2) ^ (p - 1)))
            ((x + s) / 2) := by
        simpa using
          (Real.hasDerivAt_rpow_const (Or.inr hp_ge1) :
            HasDerivAt (fun u : ℝ => u ^ p) (p * ((x + s) / 2) ^ (p - 1))
              ((x + s) / 2))
      have hcomp := hrpow.comp s hbase_sum
      simp only [Function.comp_def] at hcomp
      convert hcomp using 2
    have hpow_diff :
        HasDerivAt (fun u : ℝ => ((x - u) / 2) ^ p)
          (p * (((x - s) / 2) ^ (p - 1)) * (-(1 / 2))) s := by
      have hrpow :
          HasDerivAt (fun u : ℝ => u ^ p) (p * (((x - s) / 2) ^ (p - 1)))
            ((x - s) / 2) := by
        simpa using
          (Real.hasDerivAt_rpow_const (Or.inr hp_ge1) :
            HasDerivAt (fun u : ℝ => u ^ p) (p * ((x - s) / 2) ^ (p - 1))
              ((x - s) / 2))
      have hcomp := hrpow.comp s hbase_diff
      simp only [Function.comp_def] at hcomp
      convert hcomp using 2
    have hd :
        HasDerivAt g
          (p * (((x + s) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((x - s) / 2) ^ (p - 1)) * (-(1 / 2)))) s := by
      dsimp [g]
      exact hpow_sum.sub (hpow_diff.const_mul ((p - 1) ^ p))
    calc
      deriv g s =
          p * (((x + s) / 2) ^ (p - 1)) * (1 / 2) -
            (p - 1) ^ p * (p * (((x - s) / 2) ^ (p - 1)) * (-(1 / 2))) := hd.deriv
      _ = ((x + s) / 2) ^ (p - 1) * (p / 2) +
            (p - 1) ^ p * (((x - s) / 2) ^ (p - 1)) * (p / 2) := by ring
  have hd2 :
      HasDerivAt
        (fun s =>
          ((x + s) / 2) ^ (p - 1) * (p / 2) +
            (p - 1) ^ p * (((x - s) / 2) ^ (p - 1)) * (p / 2))
        ((p * (p - 1) / 4) *
          (((x + y) / 2) ^ (p - 2) -
            (p - 1) ^ p * ((x - y) / 2) ^ (p - 2))) y := by
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
          (Real.hasDerivAt_rpow_const (Or.inr hp1_ge1) :
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
          (Real.hasDerivAt_rpow_const (Or.inr hp1_ge1) :
            HasDerivAt (fun u : ℝ => u ^ (p - 1))
              ((p - 1) * ((x - y) / 2) ^ ((p - 1) - 1)) ((x - y) / 2))
      have hcomp := hrpow.comp y hbase_diff
      simp only [Function.comp_def] at hcomp
      convert hcomp using 2
    have hd :
        HasDerivAt
          (fun s =>
            ((x + s) / 2) ^ (p - 1) * (p / 2) +
              (p - 1) ^ p * (((x - s) / 2) ^ (p - 1)) * (p / 2))
          (((p - 1) * (((x + y) / 2) ^ (p - 2)) * (1 / 2)) * (p / 2) +
            (p - 1) ^ p *
              (((p - 1) * (((x - y) / 2) ^ (p - 2)) * (-(1 / 2)))) *
                (p / 2)) y := by
      exact (hpow_sum.mul_const (p / 2)).add
        ((hpow_diff.const_mul ((p - 1) ^ p)).mul_const (p / 2))
    refine hd.congr_deriv ?_
    ring
  rw [hderiv2, hfun]
  exact hd2.deriv

private lemma Dyy_vGeTwo_nonpos (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    0 ≥ deriv (deriv (fun y => vGeTwo p x y)) y := by
  rw [Dyy_vGeTwo_formula_on_A2 p hp x y hA2]
  have hcoef : 0 ≤ p * (p - 1) / 4 := by
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hbr := vGeTwo_A2_second_bracket_nonpos p hp x y hA2
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hcoef hbr]

private lemma deriv_DyvGeTwo_y_nonpos_on_A2
    (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    deriv (fun s => DyvGeTwo p x s) y ≤ 0 := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hEq :
      (fun s => deriv (fun r => vGeTwo p x r) s) =ᶠ[nhds y]
        fun s => DyvGeTwo p x s := by
    have hN : {s : ℝ | -x < s} ∈ nhds y := Ioi_mem_nhds hneg
    have hA : {s : ℝ | s < a p * x} ∈ nhds y := Iio_mem_nhds hay
    filter_upwards [hN, hA] with s hsN hsA
    exact deriv_vGeTwo_eq_DyvGeTwo_on_A2 p hp x s ⟨hx, hsN, hsA⟩
  have hDyy : deriv (deriv (fun r => vGeTwo p x r)) y ≤ 0 :=
    Dyy_vGeTwo_nonpos p hp x y ⟨hx, hneg, hay⟩
  rwa [hEq.deriv_eq] at hDyy

private lemma vGeTwo_tangent_y_on_Icc_of_A2
    (p : ℝ) (hp : 2 ≤ p) {lo hi y z x f' : ℝ}
    (hA2_int : ∀ t ∈ interior (Set.Icc lo hi), A2 p x t)
    (hy : y ∈ Set.Icc lo hi) (hz : z ∈ Set.Icc lo hi)
    (hderiv : HasDerivAt (fun t => vGeTwo p x t) f' y) :
    vGeTwo p x z ≤ vGeTwo p x y + f' * (z - y) := by
  have hcont : ContinuousOn (fun t => vGeTwo p x t) (Set.Icc lo hi) := by
    have hp1 : 1 < p := by linarith
    have hpair : Continuous (fun t : ℝ => (x, t)) := by continuity
    have hcomp := ((continuous_vGeTwo p hp1).comp hpair).continuousOn
      (s := Set.Icc lo hi)
    simpa [Function.comp_def] using hcomp
  apply tangent_inequality_on_Icc_of_hasDerivWithinAt2_nonpos
      (f := fun t => vGeTwo p x t)
      (f₁ := fun t => DyvGeTwo p x t)
      (f₂ := fun t => deriv (fun s => DyvGeTwo p x s) t)
  · exact hcont
  · intro t ht
    have hA2 := hA2_int t ht
    have hyx : t < x := by
      have hcoeff : 1 - 2 / p < (1 : ℝ) := by
        have hdiv : 0 < 2 / p := by positivity
        linarith
      have hat : t < (1 - 2 / p) * x := by
        simpa [a, pStar_eq_self_of_two_le p hp] using hA2.2.2
      have hax_lt_x : (1 - 2 / p) * x < x := by
        simpa using mul_lt_mul_of_pos_right hcoeff hA2.1
      linarith
    have hsum : 0 < (x + t) / 2 := by linarith [hA2.1, hA2.2.1]
    have hdiff : 0 < (x - t) / 2 := by linarith
    exact (hasDerivAt_vGeTwo_y_of_pos p hp x t hsum hdiff).hasDerivWithinAt
  · intro t ht
    have hA2 := hA2_int t ht
    have hyx : t < x := by
      have hcoeff : 1 - 2 / p < (1 : ℝ) := by
        have hdiv : 0 < 2 / p := by positivity
        linarith
      have hat : t < (1 - 2 / p) * x := by
        simpa [a, pStar_eq_self_of_two_le p hp] using hA2.2.2
      have hax_lt_x : (1 - 2 / p) * x < x := by
        simpa using mul_lt_mul_of_pos_right hcoeff hA2.1
      linarith
    have hsum : 0 < (x + t) / 2 := by linarith [hA2.1, hA2.2.1]
    have hdiff : 0 < (x - t) / 2 := by linarith
    exact (differentiableAt_DyvGeTwo_y_of_pos p x t hsum hdiff).hasDerivAt.hasDerivWithinAt
  · intro t ht
    exact deriv_DyvGeTwo_y_nonpos_on_A2 p hp x t (hA2_int t ht)
  · exact hy
  · exact hz
  · exact hderiv

private lemma Dxy_vGeTwo_formula_on_A2 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    deriv (fun x => deriv (fun y => vGeTwo p x y) y) x =
      (p * (p - 1) / 4) *
        (((x + y) / 2) ^ (p - 2) +
          (p - 1) ^ p * ((x - y) / 2) ^ (p - 2)) := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hp1_ge1 : 1 ≤ p - 1 := by linarith
  have hyx : y < x := by
    rw [a, pStar_eq_self_of_two_le p hp] at hay
    have hp0 : 0 < p := by linarith
    have hcoeff : 1 - 2 / p < (1 : ℝ) := by
      have hdiv : 0 < 2 / p := by positivity
      linarith
    have hax_lt_x : (1 - 2 / p) * x < x := by
      simpa using mul_lt_mul_of_pos_right hcoeff hx
    linarith
  have hsum : 0 < (x + y) / 2 := by linarith
  have hdiff : 0 < (x - y) / 2 := by linarith
  let g : ℝ → ℝ := fun t =>
    ((t + y) / 2) ^ (p - 1) * (p / 2) +
      (p - 1) ^ p * (((t - y) / 2) ^ (p - 1)) * (p / 2)
  have ht0_nhds : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
  have hneg_nhds : {t : ℝ | -t < y} ∈ nhds x := by
    have hxy : -y < x := by linarith
    have hset : {t : ℝ | -t < y} = Set.Ioi (-y) := by
      ext t; simp [neg_lt]
    rw [hset]
    exact Ioi_mem_nhds hxy
  have hA_nhds : {t : ℝ | y < a p * t} ∈ nhds x := by
    have hcont : ContinuousAt (fun t : ℝ => a p * t - y) x :=
      ((continuous_const.mul continuous_id').sub continuous_const).continuousAt
    have hapos : 0 < a p * x - y := by linarith
    simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hapos)
  have hsum_nhds : {t : ℝ | 0 < (t + y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.add continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hsum))
  have hdiff_nhds : {t : ℝ | 0 < (t - y) / 2} ∈ nhds x := by
    exact ((((continuous_id'.sub continuous_const).div_const 2).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds hdiff))
  have hEq :
      (fun t => deriv (fun s => vGeTwo p t s) y) =ᶠ[nhds x] g := by
    filter_upwards [ht0_nhds, hneg_nhds, hA_nhds, hsum_nhds, hdiff_nhds] with
      t ht0 htneg htA htsum htdiff
    have hA2t : A2 p t y := ⟨ht0, htneg, htA⟩
    calc
      deriv (fun s => vGeTwo p t s) y = DyvGeTwo p t y :=
        deriv_vGeTwo_eq_DyvGeTwo_on_A2 p hp t y hA2t
      _ = g t := by
        simp [g, DyvGeTwo, ht0, abs_of_pos htsum, abs_of_pos htdiff]
  have hd :
      HasDerivAt g
        ((p * (p - 1) / 4) *
          (((x + y) / 2) ^ (p - 2) +
            (p - 1) ^ p * ((x - y) / 2) ^ (p - 2))) x := by
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
          (Real.hasDerivAt_rpow_const (Or.inr hp1_ge1) :
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
          (Real.hasDerivAt_rpow_const (Or.inr hp1_ge1) :
            HasDerivAt (fun u : ℝ => u ^ (p - 1))
              ((p - 1) * ((x - y) / 2) ^ ((p - 1) - 1)) ((x - y) / 2))
      have hcomp := hrpow.comp x hbase_diff
      simp only [Function.comp_def] at hcomp
      convert hcomp using 2
    have hd' :
        HasDerivAt g
          (((p - 1) * (((x + y) / 2) ^ (p - 2)) * (1 / 2)) * (p / 2) +
            (p - 1) ^ p *
              (((p - 1) * (((x - y) / 2) ^ (p - 2)) * (1 / 2))) *
                (p / 2)) x := by
      dsimp [g]
      exact (hpow_sum.mul_const (p / 2)).add
        ((hpow_diff.const_mul ((p - 1) ^ p)).mul_const (p / 2))
    refine hd'.congr_deriv ?_
    ring
  rw [hEq.deriv_eq]
  exact hd.deriv

private lemma Dxy_vGeTwo_nonneg (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hA2 : A2 p x y) :
    0 ≤ deriv (fun x => deriv (fun y => vGeTwo p x y) y) x := by
  rw [Dxy_vGeTwo_formula_on_A2 p hp x y hA2]
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hpcoef : 0 ≤ p * (p - 1) / 4 := by
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  have hsum : 0 ≤ ((x + y) / 2) ^ (p - 2) := by
    have hpos : 0 < (x + y) / 2 := by
      have hp' : 2 ≤ p := hp
      rw [a, pStar_eq_self_of_two_le p hp'] at hay
      have hp0 : 0 < p := by linarith
      have hcoeff : 1 - 2 / p < (1 : ℝ) := by
        have hdiv : 0 < 2 / p := by positivity
        linarith
      have hyx : y < x := by
        have hax_lt_x : (1 - 2 / p) * x < x := by
          simpa using mul_lt_mul_of_pos_right hcoeff hx
        linarith
      linarith
    exact Real.rpow_nonneg hpos.le _
  have hdiff : 0 ≤ ((x - y) / 2) ^ (p - 2) := by
    have hpos : 0 < (x - y) / 2 := by
      rw [a, pStar_eq_self_of_two_le p hp] at hay
      have hp0 : 0 < p := by linarith
      have hcoeff : 1 - 2 / p < (1 : ℝ) := by
        have hdiv : 0 < 2 / p := by positivity
        linarith
      have hyx : y < x := by
        have hax_lt_x : (1 - 2 / p) * x < x := by
          simpa using mul_lt_mul_of_pos_right hcoeff hx
        linarith
      linarith
    exact Real.rpow_nonneg hpos.le _
  have hpbase : 0 ≤ (p - 1) ^ p := Real.rpow_nonneg (by linarith) _
  have hsumbr :
      0 ≤ ((x + y) / 2) ^ (p - 2) +
        (p - 1) ^ p * ((x - y) / 2) ^ (p - 2) :=
    add_nonneg hsum (mul_nonneg hpbase hdiff)
  exact mul_nonneg hpcoef hsumbr

/-! ## 8. First-quadrant geometry and `auxFunction1` tangent estimates -/

/-
The first-quadrant auxiliary function is glued from `uA1` and `vGeTwo`.  A
horizontal or vertical segment may cross the internal boundary
`y = a(p) * x`.  The next private lemmas locate that boundary, prove derivative
comparisons there, and glue the local A1/A2 tangent inequalities.
-/

private lemma a_nonneg_of_two_le (p : ℝ) (hp : 2 ≤ p) : 0 ≤ a p := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  rw [a, hpStar]
  field_simp [hp_pos.ne]
  nlinarith

private lemma a_pos_of_two_lt (p : ℝ) (hp : 2 < p) : 0 < a p := by
  have hp' : 2 ≤ p := by linarith
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
  have hp_pos : 0 < p := by linarith
  rw [a, hpStar]
  field_simp [hp_pos.ne']
  linarith

private lemma a_lt_one_of_two_le (p : ℝ) (hp : 2 ≤ p) : a p < 1 := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hp_pos : 0 < p := by linarith
  rw [a, hpStar]
  have hdiv : 0 < 2 / p := by positivity
  linarith

private lemma horizontal_boundary_closureA1_closureA2
    (p y : ℝ) (hp : 2 < p) (hy : 0 < y) :
    closureA1 p (y / a p) y ∧ closureA2 p (y / a p) y := by
  have hp' : 2 ≤ p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  have ha_lt : a p < 1 := a_lt_one_of_two_le p hp'
  have hboundary : a p * (y / a p) = y := by
    field_simp [ha_pos.ne']
  have hx_pos : 0 < y / a p := div_pos hy ha_pos
  have hyx : y < y / a p := by
    have hlt_inv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    have hmul := mul_lt_mul_of_pos_left hlt_inv hy
    simpa [div_eq_mul_inv] using hmul
  have hneg : -(y / a p) < y := by
    linarith [hx_pos, hy]
  constructor
  · exact ⟨hx_pos.le, hboundary.le, hyx.le⟩
  · exact ⟨hx_pos.le, le_of_lt hneg, hboundary.ge⟩

private lemma DxauxFunction1_A1_boundary_le
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hx : 0 < x) (hax : (a p) * x < y) (hyx : y < x) :
    DxauxFunction1 p (y / a p) y ≤ DxauxFunction1 p x y := by
  have hp' : 2 ≤ p := by linarith
  have hp1 : 1 < p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hxc : x < c := by
    have hmul : a p * x < a p * c := by simpa [hac] using hax
    nlinarith [hmul, ha_pos]
  have hy_pos : 0 < y := by
    have hax_pos : 0 < a p * x := mul_pos ha_pos hx
    exact lt_trans hax_pos hax
  have hboundary := horizontal_boundary_closureA1_closureA2 p y hp hy_pos
  have hcl_x : closureA1 p x y := ⟨hx.le, le_of_lt hax, le_of_lt hyx⟩
  have hanti :
      AntitoneOn (fun t : ℝ => DxuA1Fun p (t, y)) (Set.Icc x c) := by
    have hcont : ContinuousOn (fun t : ℝ => DxuA1Fun p (t, y)) (Set.Icc x c) := by
      have hpair : ContinuousOn (fun t : ℝ => (t, y)) (Set.Icc x c) :=
        (by continuity : Continuous (fun t : ℝ => (t, y))).continuousOn
      exact (continuousOn_DxuA1_closureA1 p hp1).comp hpair (by
        intro t ht
        have htc : t ≤ c := ht.2
        have hxt : x ≤ t := ht.1
        have h_at : a p * t ≤ y := by
          have hmul : a p * t ≤ a p * c :=
            mul_le_mul_of_nonneg_left htc ha_pos.le
          simpa [hac] using hmul
        exact ⟨le_trans hx.le hxt, h_at, le_trans hyx.le hxt⟩)
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc x c)
      (f := fun t : ℝ => DxuA1Fun p (t, y))
      (f' := fun t : ℝ => deriv (fun s => DxuA1Fun p (s, y)) t)
      (convex_Icc x c) hcont ?_ ?_
    · intro t ht
      have htIoo : t ∈ Set.Ioo x c := by
        simpa [interior_Icc] using ht
      exact (differentiableAt_DxuA1Fun_x_of_pos p t y
        (lt_trans hx htIoo.1)).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htIoo : t ∈ Set.Ioo x c := by
        simpa [interior_Icc] using ht
      have hA1 : A1 p t y := by
        have h_at : a p * t < y := by
          have hmul : a p * t < a p * c :=
            mul_lt_mul_of_pos_left htIoo.2 ha_pos
          simpa [hac] using hmul
        exact ⟨lt_trans hx htIoo.1, h_at, lt_trans hyx htIoo.1⟩
      exact deriv_DxuA1Fun_x_nonpos_on_A1 p hp' t y hA1
  have hx_mem : x ∈ Set.Icc x c := ⟨le_rfl, hxc.le⟩
  have hc_mem : c ∈ Set.Icc x c := ⟨hxc.le, le_rfl⟩
  have hle : DxuA1Fun p (c, y) ≤ DxuA1Fun p (x, y) :=
    hanti hx_mem hc_mem hxc.le
  simpa [c, auxFunction1_Dx_eq_DxuA1 p x y hcl_x,
    auxFunction1_Dx_eq_DxuA1 p (y / a p) y hboundary.1,
    DxuA1Fun] using hle

private lemma DxauxFunction1_A2_le_boundary
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hx : 0 < x) (hy_pos : 0 < y) (hay : y < (a p) * x) :
    DxauxFunction1 p x y ≤ DxauxFunction1 p (y / a p) y := by
  have hp' : 2 ≤ p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hcx : c < x := by
    have hmul : a p * c < a p * x := by simpa [hac] using hay
    nlinarith [hmul, ha_pos]
  have hboundary := horizontal_boundary_closureA1_closureA2 p y hp hy_pos
  have hcl_x : closureA2 p x y := ⟨hx.le, by linarith [hx, hy_pos], le_of_lt hay⟩
  have hanti :
      AntitoneOn (fun t : ℝ => DxvGeTwo p t y) (Set.Icc c x) := by
    have hcont : ContinuousOn (fun t : ℝ => DxvGeTwo p t y) (Set.Icc c x) := by
      have hpair : ContinuousOn (fun t : ℝ => (t, y)) (Set.Icc c x) :=
        (by continuity : Continuous (fun t : ℝ => (t, y))).continuousOn
      exact (continuousOn_DxvGeTwo_closureA2 p hp').comp hpair (by
        intro t ht
        have hc_pos : 0 < c := div_pos hy_pos ha_pos
        have hyt : y ≤ a p * t := by
          have hmul : a p * c ≤ a p * t :=
            mul_le_mul_of_nonneg_left ht.1 ha_pos.le
          simpa [hac] using hmul
        have ht_nonneg : 0 ≤ t := le_trans hc_pos.le ht.1
        exact ⟨ht_nonneg, by linarith [ht_nonneg, hy_pos], hyt⟩)
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc c x)
      (f := fun t : ℝ => DxvGeTwo p t y)
      (f' := fun t : ℝ => deriv (fun s => DxvGeTwo p s y) t)
      (convex_Icc c x) hcont ?_ ?_
    · intro t ht
      have htIoo : t ∈ Set.Ioo c x := by
        simpa [interior_Icc] using ht
      have hsum : 0 < (t + y) / 2 := by
        have hc_pos : 0 < c := div_pos hy_pos ha_pos
        linarith [htIoo.1]
      have hdiff : 0 < (t - y) / 2 := by
        have hlt_one : a p < 1 := a_lt_one_of_two_le p hp'
        have hy_lt_c : y < c := by
          have hlt_inv : 1 < (a p)⁻¹ := by
            rw [one_lt_inv₀ ha_pos]
            exact hlt_one
          have hmul := mul_lt_mul_of_pos_left hlt_inv hy_pos
          simpa [c, div_eq_mul_inv] using hmul
        linarith [hy_lt_c, htIoo.1]
      exact (differentiableAt_DxvGeTwo_x_of_pos p t y hsum hdiff).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htIoo : t ∈ Set.Ioo c x := by
        simpa [interior_Icc] using ht
      have hA2 : A2 p t y := by
        have hc_pos : 0 < c := div_pos hy_pos ha_pos
        have hyt : y < a p * t := by
          have hmul : a p * c < a p * t :=
            mul_lt_mul_of_pos_left htIoo.1 ha_pos
          simpa [hac] using hmul
        have hneg_t : -t < y := by
          have ht_pos : 0 < t := lt_trans hc_pos htIoo.1
          linarith [ht_pos, hy_pos]
        exact ⟨lt_trans hc_pos htIoo.1, hneg_t, hyt⟩
      exact deriv_DxvGeTwo_x_nonpos_on_A2 p hp' t y hA2
  have hc_mem : c ∈ Set.Icc c x := ⟨le_rfl, hcx.le⟩
  have hx_mem : x ∈ Set.Icc c x := ⟨hcx.le, le_rfl⟩
  have hle : DxvGeTwo p x y ≤ DxvGeTwo p c y :=
    hanti hc_mem hx_mem hcx.le
  simpa [c, auxFunction1_Dx_eq_DxvGeTwo p hp' x y hcl_x,
    auxFunction1_Dx_eq_DxvGeTwo p hp' (y / a p) y hboundary.2] using hle

private lemma deriv_auxFunction1_eq_DxauxFunction1_on_A1 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ)
    (hA1 : A1 p x y) :
    deriv (fun t => auxFunction1 p t y) x = DxauxFunction1 p x y := by
  rcases hA1 with ⟨hx, hay, hyx⟩
  have hEq : (fun t => auxFunction1 p t y) =ᶠ[nhds x] fun t => uA1 p t y := by
    have h0 : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
    have hA : {t : ℝ | a p * t < y} ∈ nhds x := by
      have hcont : ContinuousAt (fun t : ℝ => y - a p * t) x :=
        (continuous_const.sub (continuous_const.mul continuous_id')).continuousAt
      have hypos : 0 < y - a p * x := by linarith
      simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hypos)
    have hY : {t : ℝ | y < t} ∈ nhds x := Ioi_mem_nhds hyx
    filter_upwards [h0, hA, hY] with t ht0 htA htY
    exact auxFunction1_eq_uA1 p t y ⟨le_of_lt ht0, le_of_lt htA, le_of_lt htY⟩
  calc
    deriv (fun t => auxFunction1 p t y) x = deriv (fun t => uA1 p t y) x := hEq.deriv_eq
    _ = DxuA1Fun p (x, y) := deriv_uA1_eq_DxuA1Fun_on_A1 p hp x y ⟨hx, hay, hyx⟩
    _ = DxauxFunction1 p x y := by
          symm
          exact auxFunction1_Dx_eq_DxuA1 p x y ⟨le_of_lt hx, le_of_lt hay, le_of_lt hyx⟩

private lemma deriv_auxFunction1_eq_DxauxFunction1_on_A2 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ)
    (hA2 : A2 p x y) :
    deriv (fun t => auxFunction1 p t y) x = DxauxFunction1 p x y := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hEq : (fun t => auxFunction1 p t y) =ᶠ[nhds x] fun t => vGeTwo p t y := by
    have h0 : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
    have hN : {t : ℝ | -t < y} ∈ nhds x := by
      have hxy : -y < x := by linarith
      have hset : {t : ℝ | -t < y} = Set.Ioi (-y) := by
        ext t; simp [neg_lt]
      rw [hset]
      exact Ioi_mem_nhds hxy
    have hA : {t : ℝ | y < a p * t} ∈ nhds x := by
      have hcont : ContinuousAt (fun t : ℝ => a p * t - y) x :=
        ((continuous_const.mul continuous_id').sub continuous_const).continuousAt
      have hapos : 0 < a p * x - y := by linarith
      simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hapos)
    filter_upwards [h0, hN, hA] with t ht0 htN htA
    exact auxFunction1_eq_vGeTwo p hp t y ⟨le_of_lt ht0, le_of_lt htN, le_of_lt htA⟩
  calc
    deriv (fun t => auxFunction1 p t y) x = deriv (fun t => vGeTwo p t y) x := hEq.deriv_eq
    _ = DxvGeTwo p x y := deriv_vGeTwo_eq_DxvGeTwo_on_A2 p hp x y ⟨hx, hneg, hay⟩
    _ = DxauxFunction1 p x y := by
          symm
          exact auxFunction1_Dx_eq_DxvGeTwo p hp x y ⟨le_of_lt hx, le_of_lt hneg, le_of_lt hay⟩

private lemma hasDerivAt_auxFunction1_x_on_boundary (p x : ℝ) (hp : 2 ≤ p) (hx : 0 < x) :
    HasDerivAt (fun t => auxFunction1 p t ((a p) * x))
      (DxauxFunction1 p x ((a p) * x)) x := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
  have hy_nonneg : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
  have hyx : a p * x < x := by
    have hlt : a p < 1 := a_lt_one_of_two_le p hp
    simpa using mul_lt_mul_of_pos_right hlt hx
  have hsum : 0 < (x + a p * x) / 2 := by
    have : 0 < x + a p * x := by nlinarith
    linarith
  have hdiff : 0 < (x - a p * x) / 2 := by
    have : 0 < x - a p * x := by nlinarith
    linarith
  have hleftEq :
      (fun t => auxFunction1 p t ((a p) * x)) =ᶠ[𝓝[Set.Iic x] x]
        fun t => uA1 p t ((a p) * x) := by
    have hmem : {t : ℝ | t ≤ x ∧ a p * x < t} ∈ 𝓝[Set.Iic x] x := by
      have hset : {t : ℝ | t ≤ x ∧ a p * x < t} = Set.Iic x ∩ Set.Ioi (a p * x) := by
        ext t; simp [Set.mem_Iic, Set.mem_Ioi]
      rw [hset]
      exact inter_mem_nhdsWithin (Set.Iic x) (Ioi_mem_nhds hyx)
    filter_upwards [hmem] with t ht
    rcases ht with ⟨htle, hty⟩
    have hmul : a p * t ≤ a p * x := mul_le_mul_of_nonneg_left htle ha_nonneg
    have hcl : closureA1 p t ((a p) * x) := by
      refine ⟨le_of_lt (lt_of_le_of_lt hy_nonneg hty), hmul, le_of_lt hty⟩
    exact auxFunction1_eq_uA1 p t ((a p) * x) hcl
  have hrightEq :
      (fun t => auxFunction1 p t ((a p) * x)) =ᶠ[𝓝[Set.Ici x] x]
        fun t => vGeTwo p t ((a p) * x) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hcl : closureA2 p t ((a p) * x) := by
      refine ⟨le_trans hx.le ht, ?_, ?_⟩
      · have htpos : 0 < t := lt_of_lt_of_le hx ht
        linarith
      · exact mul_le_mul_of_nonneg_left ht ha_nonneg
    exact auxFunction1_eq_vGeTwo p hp t ((a p) * x) hcl
  have hleft :
      HasDerivWithinAt (fun t => auxFunction1 p t ((a p) * x))
        (DxauxFunction1 p x ((a p) * x)) (Set.Iic x) x := by
    have hbase :
        HasDerivWithinAt (fun t => uA1 p t ((a p) * x))
          (DxuA1Fun p (x, (a p) * x)) (Set.Iic x) x :=
      (hasDerivAt_uA1_x_of_pos p hp x ((a p) * x) hx).hasDerivWithinAt
    refine (hbase.congr_of_eventuallyEq_of_mem hleftEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxuA1 p x ((a p) * x)
      ⟨hx.le, le_rfl, le_of_lt hyx⟩).symm
  have hright :
      HasDerivWithinAt (fun t => auxFunction1 p t ((a p) * x))
        (DxauxFunction1 p x ((a p) * x)) (Set.Ici x) x := by
    have hbase :
        HasDerivWithinAt (fun t => vGeTwo p t ((a p) * x))
          (DxvGeTwo p x ((a p) * x)) (Set.Ici x) x :=
      (hasDerivAt_vGeTwo_x_of_pos p hp x ((a p) * x) hsum hdiff).hasDerivWithinAt
    refine (hbase.congr_of_eventuallyEq_of_mem hrightEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxvGeTwo p hp x ((a p) * x)
      ⟨hx.le, by linarith, le_rfl⟩).symm
  simpa [Set.Iic_union_Ici] using hleft.union hright

private lemma deriv_auxFunction1_eq_DyauxFunction1_on_A1 (p : ℝ) (hp : 2 < p) (x y : ℝ)
    (hA1 : A1 p x y) :
    deriv (fun s => auxFunction1 p x s) y = DyauxFunction1 p x y := by
  rcases hA1 with ⟨hx, hay, hyx⟩
  have hEq : (fun s => auxFunction1 p x s) =ᶠ[nhds y] fun s => uA1 p x s := by
    have h1 : {s : ℝ | a p * x < s} ∈ nhds y := Ioi_mem_nhds hay
    have h2 : {s : ℝ | s < x} ∈ nhds y := Iio_mem_nhds hyx
    filter_upwards [h1, h2] with s hs1 hs2
    exact auxFunction1_eq_uA1 p x s ⟨le_of_lt hx, le_of_lt hs1, le_of_lt hs2⟩
  calc
    deriv (fun s => auxFunction1 p x s) y = deriv (fun s => uA1 p x s) y := hEq.deriv_eq
    _ = DyuA1Fun p (x, y) := deriv_uA1_eq_DyuA1Fun_on_A1 p hp x y ⟨hx, hay, hyx⟩
    _ = DyauxFunction1 p x y := by
          symm
          exact auxFunction1_Dy_eq_DyuA1 p x y ⟨le_of_lt hx, le_of_lt hay, le_of_lt hyx⟩

private lemma deriv_auxFunction1_eq_DyauxFunction1_on_A2 (p : ℝ) (hp : 2 ≤ p) (x y : ℝ)
    (hA2 : A2 p x y) :
    deriv (fun s => auxFunction1 p x s) y = DyauxFunction1 p x y := by
  rcases hA2 with ⟨hx, hneg, hay⟩
  have hEq : (fun s => auxFunction1 p x s) =ᶠ[nhds y] fun s => vGeTwo p x s := by
    have h1 : {s : ℝ | -x < s} ∈ nhds y := Ioi_mem_nhds hneg
    have h2 : {s : ℝ | s < a p * x} ∈ nhds y := Iio_mem_nhds hay
    filter_upwards [h1, h2] with s hs1 hs2
    exact auxFunction1_eq_vGeTwo p hp x s ⟨le_of_lt hx, le_of_lt hs1, le_of_lt hs2⟩
  calc
    deriv (fun s => auxFunction1 p x s) y = deriv (fun s => vGeTwo p x s) y := hEq.deriv_eq
    _ = DyvGeTwo p x y := deriv_vGeTwo_eq_DyvGeTwo_on_A2 p hp x y ⟨hx, hneg, hay⟩
    _ = DyauxFunction1 p x y := by
          symm
          exact auxFunction1_Dy_eq_DyvGeTwo p hp x y ⟨le_of_lt hx, le_of_lt hneg, le_of_lt hay⟩

private lemma hasDerivAt_auxFunction1_y_on_boundary (p x : ℝ) (hp : 2 < p) (hx : 0 < x) :
    HasDerivAt (fun s => auxFunction1 p x s)
      (DyauxFunction1 p x ((a p) * x)) ((a p) * x) := by
  have hp' : 2 ≤ p := by linarith
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
  have hy_nonneg : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
  have hneg : -x < a p * x := by linarith
  have hyx : a p * x < x := by
    have hlt : a p < 1 := a_lt_one_of_two_le p hp'
    simpa using mul_lt_mul_of_pos_right hlt hx
  have hsum : 0 < (x + a p * x) / 2 := by
    have : 0 < x + a p * x := by nlinarith
    linarith
  have hdiff : 0 < (x - a p * x) / 2 := by
    have : 0 < x - a p * x := by nlinarith
    linarith
  have hleftEq :
      (fun s => auxFunction1 p x s) =ᶠ[𝓝[Set.Iic (a p * x)] (a p * x)]
        fun s => vGeTwo p x s := by
    have hmem : {s : ℝ | -x < s ∧ s ≤ a p * x} ∈ 𝓝[Set.Iic (a p * x)] (a p * x) := by
      exact Filter.inter_mem
        (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hneg))
        self_mem_nhdsWithin
    filter_upwards [hmem] with s hs
    rcases hs with ⟨hs1, hs2⟩
    have hcl : closureA2 p x s := ⟨hx.le, le_of_lt hs1, hs2⟩
    exact auxFunction1_eq_vGeTwo p hp' x s hcl
  have hrightEq :
      (fun s => auxFunction1 p x s) =ᶠ[𝓝[Set.Ici (a p * x)] (a p * x)]
        fun s => uA1 p x s := by
    have hmem : {s : ℝ | a p * x ≤ s ∧ s < x} ∈ 𝓝[Set.Ici (a p * x)] (a p * x) := by
      have hset : {s : ℝ | a p * x ≤ s ∧ s < x} = Set.Ici (a p * x) ∩ Set.Iio x := by
        ext s; simp [Set.mem_Ici, Set.mem_Iio]
      rw [hset]
      exact inter_mem_nhdsWithin (Set.Ici (a p * x)) (Iio_mem_nhds hyx)
    filter_upwards [hmem] with s hs
    rcases hs with ⟨hs1, hs2⟩
    have hcl : closureA1 p x s := ⟨hx.le, hs1, le_of_lt hs2⟩
    exact auxFunction1_eq_uA1 p x s hcl
  have hleft :
      HasDerivWithinAt (fun s => auxFunction1 p x s)
        (DyauxFunction1 p x ((a p) * x)) (Set.Iic ((a p) * x)) ((a p) * x) := by
    have hbase :
        HasDerivWithinAt (fun s => vGeTwo p x s)
          (DyvGeTwo p x ((a p) * x)) (Set.Iic ((a p) * x)) ((a p) * x) :=
      (hasDerivAt_vGeTwo_y_of_pos p hp' x ((a p) * x) hsum hdiff).hasDerivWithinAt
    refine (hbase.congr_of_eventuallyEq_of_mem hleftEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
    exact (auxFunction1_Dy_eq_DyvGeTwo p hp' x ((a p) * x)
      ⟨hx.le, le_of_lt hneg, le_rfl⟩).symm
  have hright :
      HasDerivWithinAt (fun s => auxFunction1 p x s)
        (DyauxFunction1 p x ((a p) * x)) (Set.Ici ((a p) * x)) ((a p) * x) := by
    have hbase :
        HasDerivWithinAt (fun s => uA1 p x s)
          (DyuA1Fun p (x, (a p) * x)) (Set.Ici ((a p) * x)) ((a p) * x) :=
      (hasDerivAt_uA1_y_of_pos p hp' x ((a p) * x) hx).hasDerivWithinAt
    refine (hbase.congr_of_eventuallyEq_of_mem hrightEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
    exact (auxFunction1_Dy_eq_DyuA1 p x ((a p) * x)
      ⟨hx.le, le_rfl, le_of_lt hyx⟩).symm
  simpa [Set.Iic_union_Ici] using hleft.union hright

private lemma DyauxFunction1_A2_boundary_le
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ}
    (hx : 0 < x) (hy_lower : -x < y) (hy_upper : y ≤ (a p) * x) :
    DyauxFunction1 p x ((a p) * x) ≤ DyauxFunction1 p x y := by
  have hanti :
      AntitoneOn (fun t : ℝ => DyvGeTwo p x t) (Set.Icc y ((a p) * x)) := by
    have hcont : ContinuousOn (fun t : ℝ => DyvGeTwo p x t) (Set.Icc y ((a p) * x)) := by
      have hpair : ContinuousOn (fun t : ℝ => (x, t)) (Set.Icc y ((a p) * x)) :=
        (by continuity : Continuous (fun t : ℝ => (x, t))).continuousOn
      exact (continuousOn_DyvGeTwo_closureA2 p hp).comp hpair (by
        intro t ht
        exact ⟨hx.le, by linarith [ht.1], ht.2⟩)
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc y ((a p) * x))
      (f := fun t : ℝ => DyvGeTwo p x t)
      (f' := fun t : ℝ => deriv (fun s => DyvGeTwo p x s) t)
      (convex_Icc y ((a p) * x)) hcont ?_ ?_
    · intro t ht
      have htIoo : t ∈ Set.Ioo y ((a p) * x) := by
        simpa [interior_Icc] using ht
      have hA2 : A2 p x t := by
        exact ⟨hx, by linarith [htIoo.1], htIoo.2⟩
      have hyx : t < x := by
        have hcoeff : a p < 1 := a_lt_one_of_two_le p hp
        have hax_lt_x : a p * x < x := by
          simpa using mul_lt_mul_of_pos_right hcoeff hx
        exact lt_trans htIoo.2 hax_lt_x
      have hsum : 0 < (x + t) / 2 := by linarith [hA2.2.1]
      have hdiff : 0 < (x - t) / 2 := by linarith
      exact (differentiableAt_DyvGeTwo_y_of_pos p x t hsum hdiff).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htIoo : t ∈ Set.Ioo y ((a p) * x) := by
        simpa [interior_Icc] using ht
      have hA2 : A2 p x t := by
        exact ⟨hx, by linarith [htIoo.1], htIoo.2⟩
      exact deriv_DyvGeTwo_y_nonpos_on_A2 p hp x t hA2
  have hy_mem : y ∈ Set.Icc y ((a p) * x) := ⟨le_rfl, hy_upper⟩
  have hc_mem : (a p) * x ∈ Set.Icc y ((a p) * x) := ⟨hy_upper, le_rfl⟩
  have hle_v : DyvGeTwo p x ((a p) * x) ≤ DyvGeTwo p x y :=
    hanti hy_mem hc_mem hy_upper
  have hcl_y : closureA2 p x y := ⟨hx.le, le_of_lt hy_lower, hy_upper⟩
  have hcl_c : closureA2 p x ((a p) * x) := by
    have hneg : -x ≤ (a p) * x := by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
      nlinarith [mul_nonneg ha_nonneg hx.le]
    exact ⟨hx.le, hneg, le_rfl⟩
  rwa [auxFunction1_Dy_eq_DyvGeTwo p hp x ((a p) * x) hcl_c,
    auxFunction1_Dy_eq_DyvGeTwo p hp x y hcl_y]

private lemma auxFunction1_tangent_y_forward_cross_A2_A1
    (p : ℝ) (hp : 2 ≤ p) {x y z : ℝ}
    (hx : 0 < x) (hy_lower : -x < y) (hy_boundary : y ≤ (a p) * x)
    (hz_boundary : (a p) * x ≤ z) (hz_upper : z < x) :
    auxFunction1 p x z ≤
      auxFunction1 p x y + DyauxFunction1 p x y * (z - y) := by
  let c : ℝ := (a p) * x
  have hc_lt_x : c < x := by
    have hlt : a p < 1 := a_lt_one_of_two_le p hp
    simpa [c] using mul_lt_mul_of_pos_right hlt hx
  have hneg_c : -x < c := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
    nlinarith [mul_nonneg ha_nonneg hx.le]
  have hcl_y_A2 : closureA2 p x y := ⟨hx.le, le_of_lt hy_lower, hy_boundary⟩
  have hcl_c_A2 : closureA2 p x c := by
    exact ⟨hx.le, le_of_lt hneg_c, by simp [c]⟩
  have hcl_c_A1 : closureA1 p x c := by
    exact ⟨hx.le, by simp [c], le_of_lt hc_lt_x⟩
  have hcl_z_A1 : closureA1 p x z := ⟨hx.le, hz_boundary, le_of_lt hz_upper⟩
  have hderiv_y :
      HasDerivAt (fun t => vGeTwo p x t) (DyauxFunction1 p x y) y := by
    have hsum : 0 < (x + y) / 2 := by linarith
    have hdiff : 0 < (x - y) / 2 := by linarith [hy_boundary, hc_lt_x]
    refine (hasDerivAt_vGeTwo_y_of_pos p hp x y hsum hdiff).congr_deriv ?_
    exact (auxFunction1_Dy_eq_DyvGeTwo p hp x y hcl_y_A2).symm
  have hderiv_c :
      HasDerivAt (fun t => uA1 p x t) (DyauxFunction1 p x c) c := by
    refine (hasDerivAt_uA1_y_of_pos p hp x c hx).congr_deriv ?_
    exact (auxFunction1_Dy_eq_DyuA1 p x c hcl_c_A1).symm
  have h_yc_v :
      vGeTwo p x c ≤ vGeTwo p x y + DyauxFunction1 p x y * (c - y) := by
    apply vGeTwo_tangent_y_on_Icc_of_A2
      (p := p) (hp := hp) (lo := y) (hi := c) (x := x) (y := y) (z := c)
    · intro t ht
      rw [interior_Icc] at ht
      exact ⟨hx, by linarith [ht.1], ht.2⟩
    · exact ⟨le_rfl, hy_boundary⟩
    · exact ⟨hy_boundary, le_rfl⟩
    · exact hderiv_y
  have h_cz_u :
      uA1 p x z ≤ uA1 p x c + DyauxFunction1 p x c * (z - c) := by
    apply uA1_tangent_y_on_Icc_of_A1
      (p := p) (hp := hp) (lo := c) (hi := z) (x := x) (y := c) (z := z)
    · exact hx
    · intro t ht
      rw [interior_Icc] at ht
      exact ⟨hx, ht.1, by linarith [ht.2, hz_upper]⟩
    · exact ⟨le_rfl, hz_boundary⟩
    · exact ⟨hz_boundary, le_rfl⟩
    · exact hderiv_c
  have h_yc :
      auxFunction1 p x c ≤ auxFunction1 p x y + DyauxFunction1 p x y * (c - y) := by
    simpa [auxFunction1_eq_vGeTwo p hp x c hcl_c_A2,
      auxFunction1_eq_vGeTwo p hp x y hcl_y_A2] using h_yc_v
  have h_cz :
      auxFunction1 p x z ≤ auxFunction1 p x c + DyauxFunction1 p x c * (z - c) := by
    simpa [auxFunction1_eq_uA1 p x z hcl_z_A1,
      auxFunction1_eq_uA1 p x c hcl_c_A1] using h_cz_u
  have hd :
      DyauxFunction1 p x c ≤ DyauxFunction1 p x y := by
    simpa [c] using
      DyauxFunction1_A2_boundary_le p hp hx hy_lower hy_boundary
  exact tangent_glue_two_forward
    (fun t => auxFunction1 p x t) (fun t => DyauxFunction1 p x t)
    hy_boundary hz_boundary h_yc h_cz hd

private lemma auxFunction1_tangent_y_backward_cross_A1_A2
    (p : ℝ) (hp : 2 ≤ p) {x y z : ℝ}
    (hx : 0 < x) (hy_boundary : (a p) * x ≤ y) (hy_upper : y < x)
    (hz_lower : -x < z) (hz_boundary : z ≤ (a p) * x) :
    auxFunction1 p x z ≤
      auxFunction1 p x y + DyauxFunction1 p x y * (z - y) := by
  let c : ℝ := (a p) * x
  have hc_lt_x : c < x := by
    have hlt : a p < 1 := a_lt_one_of_two_le p hp
    simpa [c] using mul_lt_mul_of_pos_right hlt hx
  have hneg_c : -x < c := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
    nlinarith [mul_nonneg ha_nonneg hx.le]
  have hcl_y_A1 : closureA1 p x y := ⟨hx.le, hy_boundary, le_of_lt hy_upper⟩
  have hcl_c_A1 : closureA1 p x c := by
    exact ⟨hx.le, by simp [c], le_of_lt hc_lt_x⟩
  have hcl_c_A2 : closureA2 p x c := by
    exact ⟨hx.le, le_of_lt hneg_c, by simp [c]⟩
  have hcl_z_A2 : closureA2 p x z := ⟨hx.le, le_of_lt hz_lower, hz_boundary⟩
  have hderiv_y :
      HasDerivAt (fun t => uA1 p x t) (DyauxFunction1 p x y) y := by
    refine (hasDerivAt_uA1_y_of_pos p hp x y hx).congr_deriv ?_
    exact (auxFunction1_Dy_eq_DyuA1 p x y hcl_y_A1).symm
  have hderiv_c :
      HasDerivAt (fun t => vGeTwo p x t) (DyauxFunction1 p x c) c := by
    have hsum : 0 < (x + c) / 2 := by linarith [hneg_c]
    have hdiff : 0 < (x - c) / 2 := by linarith [hc_lt_x]
    refine (hasDerivAt_vGeTwo_y_of_pos p hp x c hsum hdiff).congr_deriv ?_
    exact (auxFunction1_Dy_eq_DyvGeTwo p hp x c hcl_c_A2).symm
  have h_yc_u :
      uA1 p x c ≤ uA1 p x y + DyauxFunction1 p x y * (c - y) := by
    apply uA1_tangent_y_on_Icc_of_A1
      (p := p) (hp := hp) (lo := c) (hi := y) (x := x) (y := y) (z := c)
    · exact hx
    · intro t ht
      have htIoo : t ∈ Set.Ioo c y := by
        simpa [interior_Icc] using ht
      exact ⟨hx, htIoo.1, by linarith [htIoo.2, hy_upper]⟩
    · exact ⟨hy_boundary, le_rfl⟩
    · exact ⟨le_rfl, hy_boundary⟩
    · exact hderiv_y
  have h_cz_v :
      vGeTwo p x z ≤ vGeTwo p x c + DyauxFunction1 p x c * (z - c) := by
    apply vGeTwo_tangent_y_on_Icc_of_A2
      (p := p) (hp := hp) (lo := z) (hi := c) (x := x) (y := c) (z := z)
    · intro t ht
      have htIoo : t ∈ Set.Ioo z c := by
        simpa [interior_Icc] using ht
      exact ⟨hx, by linarith [htIoo.1], htIoo.2⟩
    · exact ⟨hz_boundary, le_rfl⟩
    · exact ⟨le_rfl, hz_boundary⟩
    · exact hderiv_c
  have h_yc :
      auxFunction1 p x c ≤ auxFunction1 p x y + DyauxFunction1 p x y * (c - y) := by
    simpa [auxFunction1_eq_uA1 p x c hcl_c_A1,
      auxFunction1_eq_uA1 p x y hcl_y_A1] using h_yc_u
  have h_cz :
      auxFunction1 p x z ≤ auxFunction1 p x c + DyauxFunction1 p x c * (z - c) := by
    simpa [auxFunction1_eq_vGeTwo p hp x z hcl_z_A2,
      auxFunction1_eq_vGeTwo p hp x c hcl_c_A2] using h_cz_v
  have hd :
      DyauxFunction1 p x y ≤ DyauxFunction1 p x c := by
    have hy_eq : DyauxFunction1 p x y = DyuA1 p x y :=
      auxFunction1_Dy_eq_DyuA1 p x y hcl_y_A1
    have hc_eq : DyauxFunction1 p x c = DyuA1 p x c :=
      auxFunction1_Dy_eq_DyuA1 p x c hcl_c_A1
    rw [hy_eq, hc_eq]
    simp [DyuA1]
  exact tangent_glue_two_backward
    (fun t => auxFunction1 p x t) (fun t => DyauxFunction1 p x t)
    hz_boundary hy_boundary h_yc h_cz hd

private lemma auxFunction1_tangent_y_on_A2_segment
    (p : ℝ) (hp : 2 ≤ p) {x y z : ℝ}
    (hx : 0 < x) (hy_lower : -x < y) (hy_boundary : y ≤ (a p) * x)
    (hz_lower : -x < z) (hz_boundary : z ≤ (a p) * x) :
    auxFunction1 p x z ≤
      auxFunction1 p x y + DyauxFunction1 p x y * (z - y) := by
  let lo : ℝ := min y z
  let hi : ℝ := max y z
  have hcl_y : closureA2 p x y := ⟨hx.le, le_of_lt hy_lower, hy_boundary⟩
  have hcl_z : closureA2 p x z := ⟨hx.le, le_of_lt hz_lower, hz_boundary⟩
  have hderiv_y :
      HasDerivAt (fun t => vGeTwo p x t) (DyauxFunction1 p x y) y := by
    have hc_lt_x : (a p) * x < x := by
      have hlt : a p < 1 := a_lt_one_of_two_le p hp
      simpa using mul_lt_mul_of_pos_right hlt hx
    have hsum : 0 < (x + y) / 2 := by linarith
    have hdiff : 0 < (x - y) / 2 := by linarith
    refine (hasDerivAt_vGeTwo_y_of_pos p hp x y hsum hdiff).congr_deriv ?_
    exact (auxFunction1_Dy_eq_DyvGeTwo p hp x y hcl_y).symm
  have h_v :
      vGeTwo p x z ≤ vGeTwo p x y + DyauxFunction1 p x y * (z - y) := by
    apply vGeTwo_tangent_y_on_Icc_of_A2
      (p := p) (hp := hp) (lo := lo) (hi := hi) (x := x) (y := y) (z := z)
    · intro t ht
      have htIoo : t ∈ Set.Ioo lo hi := by
        simpa [interior_Icc] using ht
      have hlo_lower : -x < lo := by
        exact lt_min hy_lower hz_lower
      have hhi_boundary : hi ≤ (a p) * x := by
        exact max_le hy_boundary hz_boundary
      exact ⟨hx, by linarith [hlo_lower, htIoo.1], by linarith [htIoo.2, hhi_boundary]⟩
    · exact ⟨by simp [lo], by simp [hi]⟩
    · exact ⟨by simp [lo], by simp [hi]⟩
    · exact hderiv_y
  simpa [auxFunction1_eq_vGeTwo p hp x z hcl_z,
    auxFunction1_eq_vGeTwo p hp x y hcl_y] using h_v

private lemma auxFunction1_tangent_y_on_A1_segment
    (p : ℝ) (hp : 2 ≤ p) {x y z : ℝ}
    (hx : 0 < x) (hy_boundary : (a p) * x ≤ y) (hy_upper : y < x)
    (hz_boundary : (a p) * x ≤ z) (hz_upper : z < x) :
    auxFunction1 p x z ≤
      auxFunction1 p x y + DyauxFunction1 p x y * (z - y) := by
  let lo : ℝ := min y z
  let hi : ℝ := max y z
  have hcl_y : closureA1 p x y := ⟨hx.le, hy_boundary, le_of_lt hy_upper⟩
  have hcl_z : closureA1 p x z := ⟨hx.le, hz_boundary, le_of_lt hz_upper⟩
  have hderiv_y :
      HasDerivAt (fun t => uA1 p x t) (DyauxFunction1 p x y) y := by
    refine (hasDerivAt_uA1_y_of_pos p hp x y hx).congr_deriv ?_
    exact (auxFunction1_Dy_eq_DyuA1 p x y hcl_y).symm
  have h_u :
      uA1 p x z ≤ uA1 p x y + DyauxFunction1 p x y * (z - y) := by
    apply uA1_tangent_y_on_Icc_of_A1
      (p := p) (hp := hp) (lo := lo) (hi := hi) (x := x) (y := y) (z := z)
    · exact hx
    · intro t ht
      have htIoo : t ∈ Set.Ioo lo hi := by
        simpa [interior_Icc] using ht
      have hlo_boundary : (a p) * x ≤ lo := by
        exact le_min hy_boundary hz_boundary
      have hhi_upper : hi < x := by
        exact max_lt hy_upper hz_upper
      exact ⟨hx, by linarith [hlo_boundary, htIoo.1], by linarith [htIoo.2, hhi_upper]⟩
    · exact ⟨by simp [lo], by simp [hi]⟩
    · exact ⟨by simp [lo], by simp [hi]⟩
    · exact hderiv_y
  simpa [auxFunction1_eq_uA1 p x z hcl_z,
    auxFunction1_eq_uA1 p x y hcl_y] using h_u

private lemma auxFunction1_tangent_y_on_QuarterPlaneOpen_segment
    (p : ℝ) (hp : 2 ≤ p) {x y z : ℝ}
    (hx : 0 < x) (hy_lower : -x < y) (hy_upper : y < x)
    (hz_lower : -x < z) (hz_upper : z < x) :
    auxFunction1 p x z ≤
      auxFunction1 p x y + DyauxFunction1 p x y * (z - y) := by
  rcases le_total y ((a p) * x) with hy_boundary | hy_boundary
  · rcases le_total z ((a p) * x) with hz_boundary | hz_boundary
    · exact auxFunction1_tangent_y_on_A2_segment p hp hx
        hy_lower hy_boundary hz_lower hz_boundary
    · exact auxFunction1_tangent_y_forward_cross_A2_A1 p hp hx
        hy_lower hy_boundary hz_boundary hz_upper
  · rcases le_total ((a p) * x) z with hz_boundary | hz_boundary
    · exact auxFunction1_tangent_y_on_A1_segment p hp hx
        hy_boundary hy_upper hz_boundary hz_upper
    · exact auxFunction1_tangent_y_backward_cross_A1_A2 p hp hx
        hy_boundary hy_upper hz_lower hz_boundary

private lemma auxFunction1_tangent_y_to_diag_from_QuarterPlaneOpen_segment
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ}
    (hx : 0 < x) (hy_lower : -x < y) (hy_upper : y < x) :
    auxFunction1 p x x ≤
      auxFunction1 p x y + DyauxFunction1 p x y * (x - y) := by
  let c : ℝ := (a p) * x
  have hc_lt_x : c < x := by
    have hlt : a p < 1 := a_lt_one_of_two_le p hp
    simpa [c] using mul_lt_mul_of_pos_right hlt hx
  have hdiag : closureA1 p x x := by
    refine ⟨hx.le, ?_, le_rfl⟩
    exact (le_of_lt hc_lt_x)
  rcases le_total y c with hyc | hcy
  · have hcl_y_A2 : closureA2 p x y := ⟨hx.le, le_of_lt hy_lower, hyc⟩
    have hcl_c_A2 : closureA2 p x c := by
      have hneg_c : -x < c := by
        have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
        nlinarith [mul_nonneg ha_nonneg hx.le]
      exact ⟨hx.le, le_of_lt hneg_c, le_rfl⟩
    have hcl_c_A1 : closureA1 p x c := ⟨hx.le, le_rfl, le_of_lt hc_lt_x⟩
    have hderiv_y :
        HasDerivAt (fun t => vGeTwo p x t) (DyauxFunction1 p x y) y := by
      have hsum : 0 < (x + y) / 2 := by linarith
      have hdiff : 0 < (x - y) / 2 := by linarith
      refine (hasDerivAt_vGeTwo_y_of_pos p hp x y hsum hdiff).congr_deriv ?_
      exact (auxFunction1_Dy_eq_DyvGeTwo p hp x y hcl_y_A2).symm
    have hderiv_c :
        HasDerivAt (fun t => uA1 p x t) (DyauxFunction1 p x c) c := by
      refine (hasDerivAt_uA1_y_of_pos p hp x c hx).congr_deriv ?_
      exact (auxFunction1_Dy_eq_DyuA1 p x c hcl_c_A1).symm
    have h_yc_v :
        vGeTwo p x c ≤ vGeTwo p x y + DyauxFunction1 p x y * (c - y) := by
      apply vGeTwo_tangent_y_on_Icc_of_A2
        (p := p) (hp := hp) (lo := y) (hi := c) (x := x) (y := y) (z := c)
      · intro t ht
        have htIoo : t ∈ Set.Ioo y c := by
          simpa [interior_Icc] using ht
        exact ⟨hx, by linarith [htIoo.1], htIoo.2⟩
      · exact ⟨le_rfl, hyc⟩
      · exact ⟨hyc, le_rfl⟩
      · exact hderiv_y
    have h_cx_u :
        uA1 p x x ≤ uA1 p x c + DyauxFunction1 p x c * (x - c) := by
      apply uA1_tangent_y_on_Icc_of_A1
        (p := p) (hp := hp) (lo := c) (hi := x) (x := x) (y := c) (z := x)
      · exact hx
      · intro t ht
        have htIoo : t ∈ Set.Ioo c x := by
          simpa [interior_Icc] using ht
        exact ⟨hx, htIoo.1, htIoo.2⟩
      · exact ⟨le_rfl, hc_lt_x.le⟩
      · exact ⟨hc_lt_x.le, le_rfl⟩
      · exact hderiv_c
    have h_yc :
        auxFunction1 p x c ≤ auxFunction1 p x y + DyauxFunction1 p x y * (c - y) := by
      simpa [auxFunction1_eq_vGeTwo p hp x c hcl_c_A2,
        auxFunction1_eq_vGeTwo p hp x y hcl_y_A2] using h_yc_v
    have h_cx :
        auxFunction1 p x x ≤ auxFunction1 p x c + DyauxFunction1 p x c * (x - c) := by
      simpa [auxFunction1_eq_uA1 p x x hdiag,
        auxFunction1_eq_uA1 p x c hcl_c_A1] using h_cx_u
    have hd : DyauxFunction1 p x c ≤ DyauxFunction1 p x y := by
      simpa [c] using DyauxFunction1_A2_boundary_le p hp hx hy_lower hyc
    exact tangent_glue_two_forward
      (fun t => auxFunction1 p x t) (fun t => DyauxFunction1 p x t)
      hyc hc_lt_x.le h_yc h_cx hd
  · have hcl_y_A1 : closureA1 p x y := ⟨hx.le, hcy, le_of_lt hy_upper⟩
    have hderiv_y :
        HasDerivAt (fun t => uA1 p x t) (DyauxFunction1 p x y) y := by
      refine (hasDerivAt_uA1_y_of_pos p hp x y hx).congr_deriv ?_
      exact (auxFunction1_Dy_eq_DyuA1 p x y hcl_y_A1).symm
    have h_u :
        uA1 p x x ≤ uA1 p x y + DyauxFunction1 p x y * (x - y) := by
      apply uA1_tangent_y_on_Icc_of_A1
        (p := p) (hp := hp) (lo := y) (hi := x) (x := x) (y := y) (z := x)
      · exact hx
      · intro t ht
        have htIoo : t ∈ Set.Ioo y x := by
          simpa [interior_Icc] using ht
        exact ⟨hx, lt_of_le_of_lt hcy htIoo.1, htIoo.2⟩
      · exact ⟨le_rfl, hy_upper.le⟩
      · exact ⟨hy_upper.le, le_rfl⟩
      · exact hderiv_y
    simpa [auxFunction1_eq_uA1 p x x hdiag,
      auxFunction1_eq_uA1 p x y hcl_y_A1] using h_u

private lemma DyauxFunction1_diag_le_of_QuarterPlaneOpen
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ}
    (hx : 0 < x) (hy_lower : -x < y) (hy_upper : y < x) :
    DyauxFunction1 p x x ≤ DyauxFunction1 p x y := by
  let c : ℝ := (a p) * x
  have hc_lt_x : c < x := by
    have hlt : a p < 1 := a_lt_one_of_two_le p hp
    simpa [c] using mul_lt_mul_of_pos_right hlt hx
  have hdiag : closureA1 p x x := ⟨hx.le, le_of_lt hc_lt_x, le_rfl⟩
  rcases le_total y c with hyc | hcy
  · have hcl_c_A1 : closureA1 p x c := ⟨hx.le, le_rfl, le_of_lt hc_lt_x⟩
    have h_eq : DyauxFunction1 p x x = DyauxFunction1 p x c := by
      rw [auxFunction1_Dy_eq_DyuA1 p x x hdiag,
        auxFunction1_Dy_eq_DyuA1 p x c hcl_c_A1]
      simp [DyuA1]
    calc
      DyauxFunction1 p x x = DyauxFunction1 p x c := h_eq
      _ ≤ DyauxFunction1 p x y := by
        simpa [c] using DyauxFunction1_A2_boundary_le p hp hx hy_lower hyc
  · have hcl_y_A1 : closureA1 p x y := ⟨hx.le, hcy, le_of_lt hy_upper⟩
    have h_eq : DyauxFunction1 p x x = DyauxFunction1 p x y := by
      rw [auxFunction1_Dy_eq_DyuA1 p x x hdiag,
        auxFunction1_Dy_eq_DyuA1 p x y hcl_y_A1]
      simp [DyuA1]
    exact le_of_eq h_eq

private lemma auxFunction1_tangent_x_on_A1_segment
    (p : ℝ) (hp : 2 ≤ p) {x z y : ℝ}
    (hx_pos : 0 < x) (hx_boundary : (a p) * x < y) (hyx : y < x)
    (hz_pos : 0 < z) (hz_boundary : (a p) * z < y) (hyz : y < z) :
    auxFunction1 p z y ≤
      auxFunction1 p x y + DxauxFunction1 p x y * (z - x) := by
  let lo : ℝ := min x z
  let hi : ℝ := max x z
  have hcl_x : closureA1 p x y := ⟨hx_pos.le, le_of_lt hx_boundary, le_of_lt hyx⟩
  have hcl_z : closureA1 p z y := ⟨hz_pos.le, le_of_lt hz_boundary, le_of_lt hyz⟩
  have hderiv_x :
      HasDerivAt (fun t => uA1 p t y) (DxauxFunction1 p x y) x := by
    refine (hasDerivAt_uA1_x_of_pos p hp x y hx_pos).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxuA1 p x y hcl_x).symm
  have h_u :
      uA1 p z y ≤ uA1 p x y + DxauxFunction1 p x y * (z - x) := by
    apply uA1_tangent_x_on_Icc_of_A1
      (p := p) (hp := hp) (a := lo) (b := hi) (x := x) (z := z) (y := y)
    · intro t ht
      have hlo_pos : 0 < lo := lt_min hx_pos hz_pos
      exact le_of_lt (lt_of_lt_of_le hlo_pos ht.1)
    · intro t ht
      have htIoo : t ∈ Set.Ioo lo hi := by
        simpa [interior_Icc] using ht
      have hhi_boundary : (a p) * hi < y := by
        have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
        rcases le_total x z with hxz | hzx
        · have hhi_eq : hi = z := max_eq_right hxz
          simpa [hi, hhi_eq] using hz_boundary
        · have hhi_eq : hi = x := max_eq_left hzx
          simpa [hi, hhi_eq] using hx_boundary
      have hlo_y : y < lo := lt_min hyx hyz
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
      have hle_t : lo ≤ t := le_of_lt htIoo.1
      have hmul : (a p) * t ≤ (a p) * hi :=
        mul_le_mul_of_nonneg_left (le_of_lt htIoo.2) ha_nonneg
      exact ⟨lt_of_lt_of_le (lt_min hx_pos hz_pos) hle_t,
        lt_of_le_of_lt hmul hhi_boundary, lt_trans hlo_y htIoo.1⟩
    · exact ⟨by simp [lo], by simp [hi]⟩
    · exact ⟨by simp [lo], by simp [hi]⟩
    · exact hderiv_x
  simpa [auxFunction1_eq_uA1 p z y hcl_z,
    auxFunction1_eq_uA1 p x y hcl_x] using h_u

private lemma auxFunction1_tangent_x_on_A2_segment
    (p : ℝ) (hp : 2 ≤ p) {x z y : ℝ}
    (hx_pos : 0 < x) (hneg_x : -x < y) (hx_boundary : y < (a p) * x)
    (hz_pos : 0 < z) (hneg_z : -z < y) (hz_boundary : y < (a p) * z) :
    auxFunction1 p z y ≤
      auxFunction1 p x y + DxauxFunction1 p x y * (z - x) := by
  let lo : ℝ := min x z
  let hi : ℝ := max x z
  have hcl_x : closureA2 p x y := ⟨hx_pos.le, le_of_lt hneg_x, le_of_lt hx_boundary⟩
  have hcl_z : closureA2 p z y := ⟨hz_pos.le, le_of_lt hneg_z, le_of_lt hz_boundary⟩
  have hderiv_x :
      HasDerivAt (fun t => vGeTwo p t y) (DxauxFunction1 p x y) x := by
    have hsum : 0 < (x + y) / 2 := by linarith
    have hdiff : 0 < (x - y) / 2 := by
      have hx_lt : (a p) * x < x := by
        have hlt : a p < 1 := a_lt_one_of_two_le p hp
        simpa using mul_lt_mul_of_pos_right hlt hx_pos
      linarith
    refine (hasDerivAt_vGeTwo_x_of_pos p hp x y hsum hdiff).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxvGeTwo p hp x y hcl_x).symm
  have h_v :
      vGeTwo p z y ≤ vGeTwo p x y + DxauxFunction1 p x y * (z - x) := by
    apply vGeTwo_tangent_x_on_Icc_of_A2
      (p := p) (hp := hp) (lo := lo) (hi := hi) (x := x) (z := z) (y := y)
    · intro t ht
      have htIoo : t ∈ Set.Ioo lo hi := by
        simpa [interior_Icc] using ht
      have hlo_pos : 0 < lo := lt_min hx_pos hz_pos
      have hlo_neg : -lo < y := by
        rcases le_total x z with hxz | hzx
        · have hlo_eq : lo = x := min_eq_left hxz
          simpa [lo, hlo_eq] using hneg_x
        · have hlo_eq : lo = z := min_eq_right hzx
          simpa [lo, hlo_eq] using hneg_z
      have hlo_boundary : y < (a p) * lo := by
        have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
        rcases le_total x z with hxz | hzx
        · have hlo_eq : lo = x := min_eq_left hxz
          simpa [lo, hlo_eq] using hx_boundary
        · have hlo_eq : lo = z := min_eq_right hzx
          simpa [lo, hlo_eq] using hz_boundary
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
      have ht_pos : 0 < t := lt_of_lt_of_le hlo_pos (le_of_lt htIoo.1)
      have hneg_t : -t < y := by linarith [hlo_neg, htIoo.1]
      have hmul : (a p) * lo ≤ (a p) * t :=
        mul_le_mul_of_nonneg_left (le_of_lt htIoo.1) ha_nonneg
      exact ⟨ht_pos, hneg_t, lt_of_lt_of_le hlo_boundary hmul⟩
    · exact ⟨by simp [lo], by simp [hi]⟩
    · exact ⟨by simp [lo], by simp [hi]⟩
    · exact hderiv_x
  simpa [auxFunction1_eq_vGeTwo p hp z y hcl_z,
    auxFunction1_eq_vGeTwo p hp x y hcl_x] using h_v

private lemma auxFunction1_tangent_x_forward_cross_A1_A2
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hx : 0 < x) (hax : (a p) * x < y) (hyx : y < x)
    (hz_boundary : y < (a p) * z) :
    auxFunction1 p z y ≤
      auxFunction1 p x y + DxauxFunction1 p x y * (z - x) := by
  have hp' : 2 ≤ p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hxc : x < c := by
    have hmul : a p * x < a p * c := by simpa [hac] using hax
    nlinarith [hmul, ha_pos]
  have hcz : c < z := by
    have hmul : a p * c < a p * z := by simpa [hac] using hz_boundary
    nlinarith [hmul, ha_pos]
  have hy_pos : 0 < y := by
    have hax_pos : 0 < a p * x := mul_pos ha_pos hx
    exact lt_trans hax_pos hax
  have hboundary := horizontal_boundary_closureA1_closureA2 p y hp hy_pos
  have hcl_x_A1 : closureA1 p x y := ⟨hx.le, le_of_lt hax, le_of_lt hyx⟩
  have hz_pos : 0 < z := lt_trans (div_pos hy_pos ha_pos) hcz
  have hcl_z_A2 : closureA2 p z y := by
    exact ⟨hz_pos.le, by linarith [hz_pos, hy_pos], le_of_lt hz_boundary⟩
  have hderiv_x :
      HasDerivAt (fun t => uA1 p t y) (DxauxFunction1 p x y) x := by
    refine (hasDerivAt_uA1_x_of_pos p hp' x y hx).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxuA1 p x y hcl_x_A1).symm
  have hderiv_c :
      HasDerivAt (fun t => vGeTwo p t y) (DxauxFunction1 p c y) c := by
    have hc_pos : 0 < c := div_pos hy_pos ha_pos
    have hyc : y < c := by
      have ha_lt : a p < 1 := a_lt_one_of_two_le p hp'
      have hlt_inv : 1 < (a p)⁻¹ := by
        rw [one_lt_inv₀ ha_pos]
        exact ha_lt
      have hmul := mul_lt_mul_of_pos_left hlt_inv hy_pos
      simpa [c, div_eq_mul_inv] using hmul
    have hsum : 0 < (c + y) / 2 := by linarith
    have hdiff : 0 < (c - y) / 2 := by linarith
    refine (hasDerivAt_vGeTwo_x_of_pos p hp' c y hsum hdiff).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxvGeTwo p hp' c y hboundary.2).symm
  have h_xc_u :
      uA1 p c y ≤ uA1 p x y + DxauxFunction1 p x y * (c - x) := by
    apply uA1_tangent_x_on_Icc_of_A1
      (p := p) (hp := hp') (a := x) (b := c) (x := x) (z := c) (y := y)
    · intro t ht
      exact le_trans hx.le ht.1
    · intro t ht
      have htIoo : t ∈ Set.Ioo x c := by
        simpa [interior_Icc] using ht
      have h_at : a p * t < y := by
        have hmul : a p * t < a p * c :=
          mul_lt_mul_of_pos_left htIoo.2 ha_pos
        simpa [hac] using hmul
      exact ⟨lt_trans hx htIoo.1, h_at, lt_trans hyx htIoo.1⟩
    · exact ⟨le_rfl, hxc.le⟩
    · exact ⟨hxc.le, le_rfl⟩
    · exact hderiv_x
  have h_cz_v :
      vGeTwo p z y ≤ vGeTwo p c y + DxauxFunction1 p c y * (z - c) := by
    apply vGeTwo_tangent_x_on_Icc_of_A2
      (p := p) (hp := hp') (lo := c) (hi := z) (x := c) (z := z) (y := y)
    · intro t ht
      have htIoo : t ∈ Set.Ioo c z := by
        simpa [interior_Icc] using ht
      have hc_pos : 0 < c := div_pos hy_pos ha_pos
      have hyt : y < a p * t := by
        have hmul : a p * c < a p * t :=
          mul_lt_mul_of_pos_left htIoo.1 ha_pos
        simpa [hac] using hmul
      have ht_pos : 0 < t := lt_trans hc_pos htIoo.1
      exact ⟨ht_pos, by linarith [ht_pos, hy_pos], hyt⟩
    · exact ⟨le_rfl, hcz.le⟩
    · exact ⟨hcz.le, le_rfl⟩
    · exact hderiv_c
  have h_xc :
      auxFunction1 p c y ≤ auxFunction1 p x y + DxauxFunction1 p x y * (c - x) := by
    simpa [auxFunction1_eq_uA1 p c y hboundary.1,
      auxFunction1_eq_uA1 p x y hcl_x_A1] using h_xc_u
  have h_cz :
      auxFunction1 p z y ≤ auxFunction1 p c y + DxauxFunction1 p c y * (z - c) := by
    simpa [auxFunction1_eq_vGeTwo p hp' z y hcl_z_A2,
      auxFunction1_eq_vGeTwo p hp' c y hboundary.2] using h_cz_v
  have hd : DxauxFunction1 p c y ≤ DxauxFunction1 p x y := by
    simpa [c] using DxauxFunction1_A1_boundary_le p hp hx hax hyx
  exact tangent_glue_two_forward
    (fun t => auxFunction1 p t y) (fun t => DxauxFunction1 p t y)
    hxc.le hcz.le h_xc h_cz hd

private lemma auxFunction1_tangent_x_backward_cross_A2_A1
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hx : 0 < x) (hy_pos : 0 < y) (hay : y < (a p) * x)
    (hz_boundary : (a p) * z < y) (hyz : y < z) :
    auxFunction1 p z y ≤
      auxFunction1 p x y + DxauxFunction1 p x y * (z - x) := by
  have hp' : 2 ≤ p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hcx : c < x := by
    have hmul : a p * c < a p * x := by simpa [hac] using hay
    nlinarith [hmul, ha_pos]
  have hzc : z < c := by
    have hmul : a p * z < a p * c := by simpa [hac] using hz_boundary
    nlinarith [hmul, ha_pos]
  have hboundary := horizontal_boundary_closureA1_closureA2 p y hp hy_pos
  have hcl_x_A2 : closureA2 p x y := by
    exact ⟨hx.le, by linarith [hx, hy_pos], le_of_lt hay⟩
  have hz_pos : 0 < z := lt_trans hy_pos hyz
  have hcl_z_A1 : closureA1 p z y := ⟨hz_pos.le, le_of_lt hz_boundary, le_of_lt hyz⟩
  have hderiv_x :
      HasDerivAt (fun t => vGeTwo p t y) (DxauxFunction1 p x y) x := by
    have hsum : 0 < (x + y) / 2 := by linarith
    have hdiff : 0 < (x - y) / 2 := by
      have hlt_one : a p < 1 := a_lt_one_of_two_le p hp'
      have hax_lt_x : a p * x < x := by
        simpa using mul_lt_mul_of_pos_right hlt_one hx
      linarith
    refine (hasDerivAt_vGeTwo_x_of_pos p hp' x y hsum hdiff).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxvGeTwo p hp' x y hcl_x_A2).symm
  have hderiv_c :
      HasDerivAt (fun t => uA1 p t y) (DxauxFunction1 p c y) c := by
    have hc_pos : 0 < c := div_pos hy_pos ha_pos
    refine (hasDerivAt_uA1_x_of_pos p hp' c y hc_pos).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxuA1 p c y hboundary.1).symm
  have h_xc_v :
      vGeTwo p c y ≤ vGeTwo p x y + DxauxFunction1 p x y * (c - x) := by
    apply vGeTwo_tangent_x_on_Icc_of_A2
      (p := p) (hp := hp') (lo := c) (hi := x) (x := x) (z := c) (y := y)
    · intro t ht
      have htIoo : t ∈ Set.Ioo c x := by
        simpa [interior_Icc] using ht
      have hc_pos : 0 < c := div_pos hy_pos ha_pos
      have hyt : y < a p * t := by
        have hmul : a p * c < a p * t :=
          mul_lt_mul_of_pos_left htIoo.1 ha_pos
        simpa [hac] using hmul
      have ht_pos : 0 < t := lt_trans hc_pos htIoo.1
      exact ⟨ht_pos, by linarith [ht_pos, hy_pos], hyt⟩
    · exact ⟨hcx.le, le_rfl⟩
    · exact ⟨le_rfl, hcx.le⟩
    · exact hderiv_x
  have h_cz_u :
      uA1 p z y ≤ uA1 p c y + DxauxFunction1 p c y * (z - c) := by
    apply uA1_tangent_x_on_Icc_of_A1
      (p := p) (hp := hp') (a := z) (b := c) (x := c) (z := z) (y := y)
    · intro t ht
      exact le_trans hz_pos.le ht.1
    · intro t ht
      have htIoo : t ∈ Set.Ioo z c := by
        simpa [interior_Icc] using ht
      have h_at : a p * t < y := by
        have hmul : a p * t < a p * c :=
          mul_lt_mul_of_pos_left htIoo.2 ha_pos
        simpa [hac] using hmul
      exact ⟨lt_trans hz_pos htIoo.1, h_at, lt_trans hyz htIoo.1⟩
    · exact ⟨hzc.le, le_rfl⟩
    · exact ⟨le_rfl, hzc.le⟩
    · exact hderiv_c
  have h_xc :
      auxFunction1 p c y ≤ auxFunction1 p x y + DxauxFunction1 p x y * (c - x) := by
    simpa [auxFunction1_eq_vGeTwo p hp' c y hboundary.2,
      auxFunction1_eq_vGeTwo p hp' x y hcl_x_A2] using h_xc_v
  have h_cz :
      auxFunction1 p z y ≤ auxFunction1 p c y + DxauxFunction1 p c y * (z - c) := by
    simpa [auxFunction1_eq_uA1 p z y hcl_z_A1,
      auxFunction1_eq_uA1 p c y hboundary.1] using h_cz_u
  have hd : DxauxFunction1 p x y ≤ DxauxFunction1 p c y := by
    simpa [c] using DxauxFunction1_A2_le_boundary p hp hx hy_pos hay
  exact tangent_glue_two_backward
    (fun t => auxFunction1 p t y) (fun t => DxauxFunction1 p t y)
    hzc.le hcx.le h_xc h_cz hd

private lemma auxFunction1_tangent_x_A1_to_boundary
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hx : 0 < x) (hax : (a p) * x < y) (hyx : y < x) :
    auxFunction1 p (y / a p) y ≤
      auxFunction1 p x y + DxauxFunction1 p x y * (y / a p - x) := by
  have hp' : 2 ≤ p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hxc : x < c := by
    have hmul : a p * x < a p * c := by simpa [hac] using hax
    nlinarith [hmul, ha_pos]
  have hy_pos : 0 < y := by
    have hax_pos : 0 < a p * x := mul_pos ha_pos hx
    exact lt_trans hax_pos hax
  have hboundary := horizontal_boundary_closureA1_closureA2 p y hp hy_pos
  have hcl_x : closureA1 p x y := ⟨hx.le, le_of_lt hax, le_of_lt hyx⟩
  have hderiv_x :
      HasDerivAt (fun t => uA1 p t y) (DxauxFunction1 p x y) x := by
    refine (hasDerivAt_uA1_x_of_pos p hp' x y hx).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxuA1 p x y hcl_x).symm
  have h_u :
      uA1 p c y ≤ uA1 p x y + DxauxFunction1 p x y * (c - x) := by
    apply uA1_tangent_x_on_Icc_of_A1
      (p := p) (hp := hp') (a := x) (b := c) (x := x) (z := c) (y := y)
    · intro t ht
      exact le_trans hx.le ht.1
    · intro t ht
      have htIoo : t ∈ Set.Ioo x c := by
        simpa [interior_Icc] using ht
      have h_at : a p * t < y := by
        have hmul : a p * t < a p * c :=
          mul_lt_mul_of_pos_left htIoo.2 ha_pos
        simpa [hac] using hmul
      exact ⟨lt_trans hx htIoo.1, h_at, lt_trans hyx htIoo.1⟩
    · exact ⟨le_rfl, hxc.le⟩
    · exact ⟨hxc.le, le_rfl⟩
    · exact hderiv_x
  simpa [c, auxFunction1_eq_uA1 p (y / a p) y hboundary.1,
    auxFunction1_eq_uA1 p x y hcl_x] using h_u

private lemma auxFunction1_tangent_x_A2_to_boundary
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hx : 0 < x) (hy_pos : 0 < y) (hay : y < (a p) * x) :
    auxFunction1 p (y / a p) y ≤
      auxFunction1 p x y + DxauxFunction1 p x y * (y / a p - x) := by
  have hp' : 2 ≤ p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hcx : c < x := by
    have hmul : a p * c < a p * x := by simpa [hac] using hay
    nlinarith [hmul, ha_pos]
  have hboundary := horizontal_boundary_closureA1_closureA2 p y hp hy_pos
  have hcl_x : closureA2 p x y := ⟨hx.le, by linarith [hx, hy_pos], le_of_lt hay⟩
  have hderiv_x :
      HasDerivAt (fun t => vGeTwo p t y) (DxauxFunction1 p x y) x := by
    have hsum : 0 < (x + y) / 2 := by linarith
    have hdiff : 0 < (x - y) / 2 := by
      have hlt_one : a p < 1 := a_lt_one_of_two_le p hp'
      have hax_lt_x : a p * x < x := by
        simpa using mul_lt_mul_of_pos_right hlt_one hx
      linarith
    refine (hasDerivAt_vGeTwo_x_of_pos p hp' x y hsum hdiff).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxvGeTwo p hp' x y hcl_x).symm
  have h_v :
      vGeTwo p c y ≤ vGeTwo p x y + DxauxFunction1 p x y * (c - x) := by
    apply vGeTwo_tangent_x_on_Icc_of_A2
      (p := p) (hp := hp') (lo := c) (hi := x) (x := x) (z := c) (y := y)
    · intro t ht
      have htIoo : t ∈ Set.Ioo c x := by
        simpa [interior_Icc] using ht
      have hc_pos : 0 < c := div_pos hy_pos ha_pos
      have hyt : y < a p * t := by
        have hmul : a p * c < a p * t :=
          mul_lt_mul_of_pos_left htIoo.1 ha_pos
        simpa [hac] using hmul
      have ht_pos : 0 < t := lt_trans hc_pos htIoo.1
      exact ⟨ht_pos, by linarith [ht_pos, hy_pos], hyt⟩
    · exact ⟨hcx.le, le_rfl⟩
    · exact ⟨le_rfl, hcx.le⟩
    · exact hderiv_x
  simpa [c, auxFunction1_eq_vGeTwo p hp' (y / a p) y hboundary.2,
    auxFunction1_eq_vGeTwo p hp' x y hcl_x] using h_v

private lemma auxFunction1_tangent_x_boundary_to_A1
    (p : ℝ) (hp : 2 < p) {z y : ℝ}
    (hy_pos : 0 < y) (hz_boundary : (a p) * z < y) (hyz : y < z) :
    auxFunction1 p z y ≤
      auxFunction1 p (y / a p) y +
        DxauxFunction1 p (y / a p) y * (z - y / a p) := by
  have hp' : 2 ≤ p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hzc : z < c := by
    have hmul : a p * z < a p * c := by simpa [hac] using hz_boundary
    nlinarith [hmul, ha_pos]
  have hz_pos : 0 < z := lt_trans hy_pos hyz
  have hboundary := horizontal_boundary_closureA1_closureA2 p y hp hy_pos
  have hcl_z : closureA1 p z y := ⟨hz_pos.le, le_of_lt hz_boundary, le_of_lt hyz⟩
  have hderiv_c :
      HasDerivAt (fun t => uA1 p t y) (DxauxFunction1 p c y) c := by
    have hc_pos : 0 < c := div_pos hy_pos ha_pos
    refine (hasDerivAt_uA1_x_of_pos p hp' c y hc_pos).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxuA1 p c y hboundary.1).symm
  have h_u :
      uA1 p z y ≤ uA1 p c y + DxauxFunction1 p c y * (z - c) := by
    apply uA1_tangent_x_on_Icc_of_A1
      (p := p) (hp := hp') (a := z) (b := c) (x := c) (z := z) (y := y)
    · intro t ht
      exact le_trans hz_pos.le ht.1
    · intro t ht
      have htIoo : t ∈ Set.Ioo z c := by
        simpa [interior_Icc] using ht
      have h_at : a p * t < y := by
        have hmul : a p * t < a p * c :=
          mul_lt_mul_of_pos_left htIoo.2 ha_pos
        simpa [hac] using hmul
      exact ⟨lt_trans hz_pos htIoo.1, h_at, lt_trans hyz htIoo.1⟩
    · exact ⟨hzc.le, le_rfl⟩
    · exact ⟨le_rfl, hzc.le⟩
    · exact hderiv_c
  simpa [c, auxFunction1_eq_uA1 p z y hcl_z,
    auxFunction1_eq_uA1 p (y / a p) y hboundary.1] using h_u

private lemma auxFunction1_tangent_x_boundary_to_A2
    (p : ℝ) (hp : 2 < p) {z y : ℝ}
    (hy_pos : 0 < y) (hz_boundary : y < (a p) * z) :
    auxFunction1 p z y ≤
      auxFunction1 p (y / a p) y +
        DxauxFunction1 p (y / a p) y * (z - y / a p) := by
  have hp' : 2 ≤ p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hcz : c < z := by
    have hmul : a p * c < a p * z := by simpa [hac] using hz_boundary
    nlinarith [hmul, ha_pos]
  have hc_pos : 0 < c := div_pos hy_pos ha_pos
  have hz_pos : 0 < z := lt_trans hc_pos hcz
  have hboundary := horizontal_boundary_closureA1_closureA2 p y hp hy_pos
  have hcl_z : closureA2 p z y := ⟨hz_pos.le, by linarith [hz_pos, hy_pos], le_of_lt hz_boundary⟩
  have hderiv_c :
      HasDerivAt (fun t => vGeTwo p t y) (DxauxFunction1 p c y) c := by
    have ha_lt : a p < 1 := a_lt_one_of_two_le p hp'
    have hyc : y < c := by
      have hlt_inv : 1 < (a p)⁻¹ := by
        rw [one_lt_inv₀ ha_pos]
        exact ha_lt
      have hmul := mul_lt_mul_of_pos_left hlt_inv hy_pos
      simpa [c, div_eq_mul_inv] using hmul
    have hsum : 0 < (c + y) / 2 := by linarith
    have hdiff : 0 < (c - y) / 2 := by linarith
    refine (hasDerivAt_vGeTwo_x_of_pos p hp' c y hsum hdiff).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxvGeTwo p hp' c y hboundary.2).symm
  have h_v :
      vGeTwo p z y ≤ vGeTwo p c y + DxauxFunction1 p c y * (z - c) := by
    apply vGeTwo_tangent_x_on_Icc_of_A2
      (p := p) (hp := hp') (lo := c) (hi := z) (x := c) (z := z) (y := y)
    · intro t ht
      have htIoo : t ∈ Set.Ioo c z := by
        simpa [interior_Icc] using ht
      have hyt : y < a p * t := by
        have hmul : a p * c < a p * t :=
          mul_lt_mul_of_pos_left htIoo.1 ha_pos
        simpa [hac] using hmul
      have ht_pos : 0 < t := lt_trans hc_pos htIoo.1
      exact ⟨ht_pos, by linarith [ht_pos, hy_pos], hyt⟩
    · exact ⟨le_rfl, hcz.le⟩
    · exact ⟨hcz.le, le_rfl⟩
    · exact hderiv_c
  simpa [c, auxFunction1_eq_vGeTwo p hp' z y hcl_z,
    auxFunction1_eq_vGeTwo p hp' (y / a p) y hboundary.2] using h_v

private lemma auxFunction1_tangent_x_on_QuarterPlaneOpen_segment
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hx_pos : 0 < x) (hyx : y < x) (hneg_x : -x < y)
    (hz_pos : 0 < z) (hyz : y < z) (hneg_z : -z < y) :
    auxFunction1 p z y ≤
      auxFunction1 p x y + DxauxFunction1 p x y * (z - x) := by
  have hp' : 2 ≤ p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  by_cases hxA1 : (a p) * x < y
  · by_cases hzA1 : (a p) * z < y
    · exact auxFunction1_tangent_x_on_A1_segment p hp'
        hx_pos hxA1 hyx hz_pos hzA1 hyz
    · by_cases hzA2 : y < (a p) * z
      · exact auxFunction1_tangent_x_forward_cross_A1_A2 p hp
          hx_pos hxA1 hyx hzA2
      · have hz_eq : y = (a p) * z := le_antisymm (not_lt.mp hzA1) (not_lt.mp hzA2)
        have hz_div : z = y / a p := by
          rw [hz_eq]
          field_simp [ha_pos.ne']
        rw [hz_div]
        exact auxFunction1_tangent_x_A1_to_boundary p hp hx_pos hxA1 hyx
  · by_cases hxA2 : y < (a p) * x
    · by_cases hzA1 : (a p) * z < y
      · have hy_pos : 0 < y := by
          have haz_pos : 0 < (a p) * z := mul_pos ha_pos hz_pos
          exact lt_trans haz_pos hzA1
        exact auxFunction1_tangent_x_backward_cross_A2_A1 p hp
          hx_pos hy_pos hxA2 hzA1 hyz
      · by_cases hzA2 : y < (a p) * z
        · exact auxFunction1_tangent_x_on_A2_segment p hp'
            hx_pos hneg_x hxA2 hz_pos hneg_z hzA2
        · have hz_eq : y = (a p) * z := le_antisymm (not_lt.mp hzA1) (not_lt.mp hzA2)
          have hy_pos : 0 < y := by
            rw [hz_eq]
            exact mul_pos ha_pos hz_pos
          have hz_div : z = y / a p := by
            rw [hz_eq]
            field_simp [ha_pos.ne']
          rw [hz_div]
          exact auxFunction1_tangent_x_A2_to_boundary p hp hx_pos hy_pos hxA2
    · have hx_eq : y = (a p) * x := le_antisymm (not_lt.mp hxA1) (not_lt.mp hxA2)
      have hy_pos : 0 < y := by
        rw [hx_eq]
        exact mul_pos ha_pos hx_pos
      have hx_div : x = y / a p := by
        rw [hx_eq]
        field_simp [ha_pos.ne']
      by_cases hzA1 : (a p) * z < y
      · rw [hx_div]
        exact auxFunction1_tangent_x_boundary_to_A1 p hp hy_pos hzA1 hyz
      · by_cases hzA2 : y < (a p) * z
        · rw [hx_div]
          exact auxFunction1_tangent_x_boundary_to_A2 p hp hy_pos hzA2
        · have hz_eq : y = (a p) * z := le_antisymm (not_lt.mp hzA1) (not_lt.mp hzA2)
          have hz_div : z = y / a p := by
            rw [hz_eq]
            field_simp [ha_pos.ne']
          rw [hx_div, hz_div]
          simp

/-! ## 9. Boundary-to-boundary tangent estimates for `uCandidate` -/

/-
The following private lemmas lift the first-quadrant estimates to the four-quadrant
candidate.  They also add the closed endpoint estimates needed when a horizontal
segment hits the diagonal `x = y` or antidiagonal `x = -y`.

The most important pattern is:

* prove a tangent estimate up to a boundary point;
* prove a tangent estimate starting from that boundary point;
* compare the derivatives at the boundary;
* glue the two estimates with `tangent_glue_two_forward` or
  `tangent_glue_two_backward`.
-/

private lemma DxauxFunction1_internal_boundary_le_diag
    (p : ℝ) (hp : 2 < p) {y : ℝ} (hy : 0 < y) :
    DxauxFunction1 p (y / a p) y ≤ DxauxFunction1 p y y := by
  have hp' : 2 ≤ p := by linarith
  have hp1 : 1 < p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  have ha_lt : a p < 1 := a_lt_one_of_two_le p hp'
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hyc : y < c := by
    have hlt_inv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    have hmul := mul_lt_mul_of_pos_left hlt_inv hy
    simpa [c, div_eq_mul_inv] using hmul
  have hboundary := horizontal_boundary_closureA1_closureA2 p y hp hy
  have hdiag : closureA1 p y y := by
    refine ⟨hy.le, ?_, le_rfl⟩
    have hmul : a p * y < 1 * y := mul_lt_mul_of_pos_right ha_lt hy
    simpa using hmul.le
  have hanti :
      AntitoneOn (fun t : ℝ => DxuA1Fun p (t, y)) (Set.Icc y c) := by
    have hcont : ContinuousOn (fun t : ℝ => DxuA1Fun p (t, y)) (Set.Icc y c) := by
      have hpair : ContinuousOn (fun t : ℝ => (t, y)) (Set.Icc y c) :=
        (by continuity : Continuous (fun t : ℝ => (t, y))).continuousOn
      exact (continuousOn_DxuA1_closureA1 p hp1).comp hpair (by
        intro t ht
        have htc : t ≤ c := ht.2
        have hyt : y ≤ t := ht.1
        have h_at : a p * t ≤ y := by
          have hmul : a p * t ≤ a p * c :=
            mul_le_mul_of_nonneg_left htc ha_pos.le
          simpa [hac] using hmul
        exact ⟨le_trans hy.le hyt, h_at, hyt⟩)
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc y c)
      (f := fun t : ℝ => DxuA1Fun p (t, y))
      (f' := fun t : ℝ => deriv (fun s => DxuA1Fun p (s, y)) t)
      (convex_Icc y c) hcont ?_ ?_
    · intro t ht
      have htIoo : t ∈ Set.Ioo y c := by
        simpa [interior_Icc] using ht
      exact (differentiableAt_DxuA1Fun_x_of_pos p t y
        (lt_trans hy htIoo.1)).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htIoo : t ∈ Set.Ioo y c := by
        simpa [interior_Icc] using ht
      have h_at : a p * t < y := by
        have hmul : a p * t < a p * c :=
          mul_lt_mul_of_pos_left htIoo.2 ha_pos
        simpa [hac] using hmul
      exact deriv_DxuA1Fun_x_nonpos_on_A1 p hp' t y
        ⟨lt_trans hy htIoo.1, h_at, htIoo.1⟩
  have hy_mem : y ∈ Set.Icc y c := ⟨le_rfl, hyc.le⟩
  have hc_mem : c ∈ Set.Icc y c := ⟨hyc.le, le_rfl⟩
  have hle : DxuA1Fun p (c, y) ≤ DxuA1Fun p (y, y) :=
    hanti hy_mem hc_mem hyc.le
  simpa [c, auxFunction1_Dx_eq_DxuA1 p (y / a p) y hboundary.1,
    auxFunction1_Dx_eq_DxuA1 p y y hdiag, DxuA1Fun] using hle

private lemma auxFunction1_tangent_x_diag_to_QuarterPlaneOpen_segment
    (p : ℝ) (hp : 2 < p) {z y : ℝ}
    (hy : 0 < y) (hyz : y < z) :
    auxFunction1 p z y ≤
      auxFunction1 p y y + DxauxFunction1 p y y * (z - y) := by
  have hp' : 2 ≤ p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  have ha_lt : a p < 1 := a_lt_one_of_two_le p hp'
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hyc : y < c := by
    have hlt_inv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    have hmul := mul_lt_mul_of_pos_left hlt_inv hy
    simpa [c, div_eq_mul_inv] using hmul
  have hdiag : closureA1 p y y := by
    refine ⟨hy.le, ?_, le_rfl⟩
    have hmul : a p * y < 1 * y := mul_lt_mul_of_pos_right ha_lt hy
    simpa using hmul.le
  have hboundary := horizontal_boundary_closureA1_closureA2 p y hp hy
  have hderiv_y :
      HasDerivAt (fun t => uA1 p t y) (DxauxFunction1 p y y) y := by
    refine (hasDerivAt_uA1_x_of_pos p hp' y y hy).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxuA1 p y y hdiag).symm
  by_cases hzc : z ≤ c
  · have hcl_z : closureA1 p z y := by
      refine ⟨(lt_trans hy hyz).le, ?_, hyz.le⟩
      have hmul : a p * z ≤ a p * c :=
        mul_le_mul_of_nonneg_left hzc ha_pos.le
      simpa [hac] using hmul
    have h_u :
        uA1 p z y ≤ uA1 p y y + DxauxFunction1 p y y * (z - y) := by
      apply uA1_tangent_x_on_Icc_of_A1
        (p := p) (hp := hp') (a := y) (b := z) (x := y) (z := z) (y := y)
      · intro t ht
        exact le_trans hy.le ht.1
      · intro t ht
        have htIoo : t ∈ Set.Ioo y z := by
          simpa [interior_Icc] using ht
        have h_at : a p * t < y := by
          have htc : t < c := lt_of_lt_of_le htIoo.2 hzc
          have hmul : a p * t < a p * c :=
            mul_lt_mul_of_pos_left htc ha_pos
          simpa [hac] using hmul
        exact ⟨lt_trans hy htIoo.1, h_at, htIoo.1⟩
      · exact ⟨le_rfl, hyz.le⟩
      · exact ⟨hyz.le, le_rfl⟩
      · exact hderiv_y
    simpa [auxFunction1_eq_uA1 p z y hcl_z,
      auxFunction1_eq_uA1 p y y hdiag] using h_u
  · have hcz : c < z := lt_of_not_ge hzc
    have hz_pos : 0 < z := lt_trans (lt_trans hy hyc) hcz
    have hcl_z : closureA2 p z y :=
      ⟨hz_pos.le, by linarith [hz_pos, hy], by
        have hmul : a p * c < a p * z :=
          mul_lt_mul_of_pos_left hcz ha_pos
        exact le_of_lt (by simpa [hac] using hmul)⟩
    have hderiv_c :
        HasDerivAt (fun t => vGeTwo p t y) (DxauxFunction1 p c y) c := by
      have hsum : 0 < (c + y) / 2 := by
        have hc_pos : 0 < c := div_pos hy ha_pos
        linarith
      have hdiff : 0 < (c - y) / 2 := by linarith
      refine (hasDerivAt_vGeTwo_x_of_pos p hp' c y hsum hdiff).congr_deriv ?_
      exact (auxFunction1_Dx_eq_DxvGeTwo p hp' c y hboundary.2).symm
    have h_yc_u :
        uA1 p c y ≤ uA1 p y y + DxauxFunction1 p y y * (c - y) := by
      apply uA1_tangent_x_on_Icc_of_A1
        (p := p) (hp := hp') (a := y) (b := c) (x := y) (z := c) (y := y)
      · intro t ht
        exact le_trans hy.le ht.1
      · intro t ht
        have htIoo : t ∈ Set.Ioo y c := by
          simpa [interior_Icc] using ht
        have h_at : a p * t < y := by
          have hmul : a p * t < a p * c :=
            mul_lt_mul_of_pos_left htIoo.2 ha_pos
          simpa [hac] using hmul
        exact ⟨lt_trans hy htIoo.1, h_at, htIoo.1⟩
      · exact ⟨le_rfl, hyc.le⟩
      · exact ⟨hyc.le, le_rfl⟩
      · exact hderiv_y
    have h_cz_v :
        vGeTwo p z y ≤ vGeTwo p c y + DxauxFunction1 p c y * (z - c) := by
      apply vGeTwo_tangent_x_on_Icc_of_A2
        (p := p) (hp := hp') (lo := c) (hi := z) (x := c) (z := z) (y := y)
      · intro t ht
        have htIoo : t ∈ Set.Ioo c z := by
          simpa [interior_Icc] using ht
        have hc_pos : 0 < c := div_pos hy ha_pos
        have hyt : y < a p * t := by
          have hmul : a p * c < a p * t :=
            mul_lt_mul_of_pos_left htIoo.1 ha_pos
          simpa [hac] using hmul
        have ht_pos : 0 < t := lt_trans hc_pos htIoo.1
        exact ⟨ht_pos, by linarith [ht_pos, hy], hyt⟩
      · exact ⟨le_rfl, hcz.le⟩
      · exact ⟨hcz.le, le_rfl⟩
      · exact hderiv_c
    have h_yc :
        auxFunction1 p c y ≤ auxFunction1 p y y + DxauxFunction1 p y y * (c - y) := by
      simpa [auxFunction1_eq_uA1 p c y hboundary.1,
        auxFunction1_eq_uA1 p y y hdiag] using h_yc_u
    have h_cz :
        auxFunction1 p z y ≤ auxFunction1 p c y + DxauxFunction1 p c y * (z - c) := by
      simpa [auxFunction1_eq_vGeTwo p hp' z y hcl_z,
        auxFunction1_eq_vGeTwo p hp' c y hboundary.2] using h_cz_v
    have hd : DxauxFunction1 p c y ≤ DxauxFunction1 p y y := by
      simpa [c] using DxauxFunction1_internal_boundary_le_diag p hp hy
    exact tangent_glue_two_forward
      (fun t => auxFunction1 p t y) (fun t => DxauxFunction1 p t y)
      hyc.le hcz.le h_yc h_cz hd

private lemma uCandidate_tangent_x_on_QuarterPlaneOpen_segment
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hx_pos : 0 < x) (hyx : y < x) (hneg_x : -x < y)
    (hz_pos : 0 < z) (hyz : y < z) (hneg_z : -z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hQx : QuarterPlane x y := ⟨hx_pos.le, hyx.le, hneg_x.le⟩
  have hQz : QuarterPlane z y := ⟨hz_pos.le, hyz.le, hneg_z.le⟩
  have haux := auxFunction1_tangent_x_on_QuarterPlaneOpen_segment
    p hp hx_pos hyx hneg_x hz_pos hyz hneg_z
  simpa [uCandidate, DxuCandidate, hQx, hQz] using haux

private lemma uCandidate_tangent_x_diag_to_QuarterPlaneOpen_segment
    (p : ℝ) (hp : 2 < p) {z y : ℝ}
    (hy : 0 < y) (hyz : y < z) :
    uCandidate p z y ≤
      uCandidate p y y + DxuCandidate p y y * (z - y) := by
  have hQy : QuarterPlane y y := ⟨hy.le, le_rfl, by linarith⟩
  have hQz : QuarterPlane z y := ⟨(lt_trans hy hyz).le, hyz.le, by linarith⟩
  have haux := auxFunction1_tangent_x_diag_to_QuarterPlaneOpen_segment
    p hp hy hyz
  simpa [uCandidate, DxuCandidate, hQy, hQz] using haux

private lemma auxFunction1_tangent_x_QuarterPlaneOpen_to_diag_segment
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hy : 0 < y) (hyx : y < x) :
    auxFunction1 p y y ≤
      auxFunction1 p x y + DxauxFunction1 p x y * (y - x) := by
  have hp' : 2 ≤ p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  have ha_lt : a p < 1 := a_lt_one_of_two_le p hp'
  let c : ℝ := y / a p
  have hac : a p * c = y := by
    dsimp [c]
    field_simp [ha_pos.ne']
  have hyc : y < c := by
    have hlt_inv : 1 < (a p)⁻¹ := by
      rw [one_lt_inv₀ ha_pos]
      exact ha_lt
    have hmul := mul_lt_mul_of_pos_left hlt_inv hy
    simpa [c, div_eq_mul_inv] using hmul
  have hdiag : closureA1 p y y := by
    refine ⟨hy.le, ?_, le_rfl⟩
    have hmul : a p * y < 1 * y := mul_lt_mul_of_pos_right ha_lt hy
    simpa using hmul.le
  have hboundary := horizontal_boundary_closureA1_closureA2 p y hp hy
  by_cases hxc : x ≤ c
  · have hcl_x : closureA1 p x y := by
      refine ⟨(lt_trans hy hyx).le, ?_, hyx.le⟩
      have hmul : a p * x ≤ a p * c :=
        mul_le_mul_of_nonneg_left hxc ha_pos.le
      simpa [hac] using hmul
    have hderiv_x :
        HasDerivAt (fun t => uA1 p t y) (DxauxFunction1 p x y) x := by
      refine (hasDerivAt_uA1_x_of_pos p hp' x y (lt_trans hy hyx)).congr_deriv ?_
      exact (auxFunction1_Dx_eq_DxuA1 p x y hcl_x).symm
    have h_u :
        uA1 p y y ≤ uA1 p x y + DxauxFunction1 p x y * (y - x) := by
      apply uA1_tangent_x_on_Icc_of_A1
        (p := p) (hp := hp') (a := y) (b := x) (x := x) (z := y) (y := y)
      · intro t ht
        exact le_trans hy.le ht.1
      · intro t ht
        have htIoo : t ∈ Set.Ioo y x := by
          simpa [interior_Icc] using ht
        have htc : t < c := lt_of_lt_of_le htIoo.2 hxc
        have h_at : a p * t < y := by
          have hmul : a p * t < a p * c :=
            mul_lt_mul_of_pos_left htc ha_pos
          simpa [hac] using hmul
        exact ⟨lt_trans hy htIoo.1, h_at, htIoo.1⟩
      · exact ⟨hyx.le, le_rfl⟩
      · exact ⟨le_rfl, hyx.le⟩
      · exact hderiv_x
    simpa [auxFunction1_eq_uA1 p y y hdiag,
      auxFunction1_eq_uA1 p x y hcl_x] using h_u
  · have hcx : c < x := lt_of_not_ge hxc
    have hx_pos : 0 < x := lt_trans (lt_trans hy hyc) hcx
    have hcl_x : closureA2 p x y :=
      ⟨hx_pos.le, by linarith [hx_pos, hy], by
        have hmul : a p * c < a p * x :=
          mul_lt_mul_of_pos_left hcx ha_pos
        exact le_of_lt (by simpa [hac] using hmul)⟩
    have hderiv_x :
        HasDerivAt (fun t => vGeTwo p t y) (DxauxFunction1 p x y) x := by
      have hsum : 0 < (x + y) / 2 := by linarith
      have hdiff : 0 < (x - y) / 2 := by linarith
      refine (hasDerivAt_vGeTwo_x_of_pos p hp' x y hsum hdiff).congr_deriv ?_
      exact (auxFunction1_Dx_eq_DxvGeTwo p hp' x y hcl_x).symm
    have hderiv_c :
        HasDerivAt (fun t => uA1 p t y) (DxauxFunction1 p c y) c := by
      have hc_pos : 0 < c := div_pos hy ha_pos
      refine (hasDerivAt_uA1_x_of_pos p hp' c y hc_pos).congr_deriv ?_
      exact (auxFunction1_Dx_eq_DxuA1 p c y hboundary.1).symm
    have h_xc_v :
        vGeTwo p c y ≤ vGeTwo p x y + DxauxFunction1 p x y * (c - x) := by
      apply vGeTwo_tangent_x_on_Icc_of_A2
        (p := p) (hp := hp') (lo := c) (hi := x) (x := x) (z := c) (y := y)
      · intro t ht
        have htIoo : t ∈ Set.Ioo c x := by
          simpa [interior_Icc] using ht
        have hc_pos : 0 < c := div_pos hy ha_pos
        have hyt : y < a p * t := by
          have hmul : a p * c < a p * t :=
            mul_lt_mul_of_pos_left htIoo.1 ha_pos
          simpa [hac] using hmul
        have ht_pos : 0 < t := lt_trans hc_pos htIoo.1
        exact ⟨ht_pos, by linarith [ht_pos, hy], hyt⟩
      · exact ⟨hcx.le, le_rfl⟩
      · exact ⟨le_rfl, hcx.le⟩
      · exact hderiv_x
    have h_cy_u :
        uA1 p y y ≤ uA1 p c y + DxauxFunction1 p c y * (y - c) := by
      apply uA1_tangent_x_on_Icc_of_A1
        (p := p) (hp := hp') (a := y) (b := c) (x := c) (z := y) (y := y)
      · intro t ht
        exact le_trans hy.le ht.1
      · intro t ht
        have htIoo : t ∈ Set.Ioo y c := by
          simpa [interior_Icc] using ht
        have h_at : a p * t < y := by
          have hmul : a p * t < a p * c :=
            mul_lt_mul_of_pos_left htIoo.2 ha_pos
          simpa [hac] using hmul
        exact ⟨lt_trans hy htIoo.1, h_at, htIoo.1⟩
      · exact ⟨hyc.le, le_rfl⟩
      · exact ⟨le_rfl, hyc.le⟩
      · exact hderiv_c
    have h_xc :
        auxFunction1 p c y ≤ auxFunction1 p x y + DxauxFunction1 p x y * (c - x) := by
      simpa [auxFunction1_eq_vGeTwo p hp' c y hboundary.2,
        auxFunction1_eq_vGeTwo p hp' x y hcl_x] using h_xc_v
    have h_cy :
        auxFunction1 p y y ≤ auxFunction1 p c y + DxauxFunction1 p c y * (y - c) := by
      simpa [auxFunction1_eq_uA1 p y y hdiag,
        auxFunction1_eq_uA1 p c y hboundary.1] using h_cy_u
    have hd : DxauxFunction1 p x y ≤ DxauxFunction1 p c y := by
      have hay : y < a p * x := by
        have hmul : a p * c < a p * x :=
          mul_lt_mul_of_pos_left hcx ha_pos
        simpa [hac] using hmul
      simpa [c] using DxauxFunction1_A2_le_boundary p hp hx_pos hy hay
    exact tangent_glue_two_backward
      (fun t => auxFunction1 p t y) (fun t => DxauxFunction1 p t y)
      hyc.le hcx.le h_xc h_cy hd

private lemma uCandidate_tangent_x_QuarterPlaneOpen_to_diag_segment
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hy : 0 < y) (hyx : y < x) :
    uCandidate p y y ≤
      uCandidate p x y + DxuCandidate p x y * (y - x) := by
  have hQx : QuarterPlane x y := ⟨(lt_trans hy hyx).le, hyx.le, by linarith⟩
  have hQy : QuarterPlane y y := ⟨hy.le, le_rfl, by linarith⟩
  have haux := auxFunction1_tangent_x_QuarterPlaneOpen_to_diag_segment
    p hp hy hyx
  simpa [uCandidate, DxuCandidate, hQx, hQy] using haux

private lemma uCandidate_tangent_y_on_QuarterPlaneOpen_segment
    (p : ℝ) (hp : 2 < p) {x y z : ℝ}
    (hx_pos : 0 < x) (hy_lower : -x < y) (hy_upper : y < x)
    (hz_lower : -x < z) (hz_upper : z < x) :
    uCandidate p x z ≤
      uCandidate p x y + DyuCandidate p x y * (z - y) := by
  have hQy : QuarterPlane x y := ⟨hx_pos.le, hy_upper.le, hy_lower.le⟩
  have hQz : QuarterPlane x z := ⟨hx_pos.le, hz_upper.le, hz_lower.le⟩
  have haux := auxFunction1_tangent_y_on_QuarterPlaneOpen_segment
    p (by linarith : 2 ≤ p) hx_pos hy_lower hy_upper hz_lower hz_upper
  simpa [uCandidate, DyuCandidate, hQy, hQz] using haux

private lemma uCandidate_tangent_x_on_QuarterPlane2Open_segment
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hx_neg : x < 0) (hynegx : y < -x) (hxy : x < y)
    (hz_neg : z < 0) (hynegz : y < -z) (hzy : z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hQx : QuarterPlane2 x y := ⟨le_of_lt hx_neg, le_of_lt hynegx, le_of_lt hxy⟩
  have hQz : QuarterPlane2 z y := ⟨le_of_lt hz_neg, le_of_lt hynegz, le_of_lt hzy⟩
  have hnotQx : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hx_neg hq.1
  have hnotQz : ¬ QuarterPlane z y := by
    intro hq
    exact not_le_of_gt hz_neg hq.1
  have haux := auxFunction1_tangent_x_on_QuarterPlaneOpen_segment
    p hp
    (by linarith : 0 < -x)
    (by linarith : -y < -x)
    (by linarith : -(-x) < -y)
    (by linarith : 0 < -z)
    (by linarith : -y < -z)
    (by linarith : -(-z) < -y)
  have haux' :
      auxFunction1 p (-z) (-y) ≤
        auxFunction1 p (-x) (-y) + DxauxFunction1 p (-x) (-y) * ((-z) - (-x)) := haux
  have hdx : DxuCandidate p x y = -DxauxFunction1 p (-x) (-y) := by
    simp [DxuCandidate, hnotQx, hQx]
  calc
    uCandidate p z y = auxFunction1 p (-z) (-y) := by
      simp [uCandidate, hnotQz, hQz]
    _ ≤ auxFunction1 p (-x) (-y) + DxauxFunction1 p (-x) (-y) * ((-z) - (-x)) := haux'
    _ = uCandidate p x y + DxuCandidate p x y * (z - x) := by
      simp [uCandidate, hnotQx, hQx, hdx]
      ring

private lemma uCandidate_tangent_y_on_QuarterPlane2Open_segment
    (p : ℝ) (hp : 2 < p) {x y z : ℝ}
    (hx_neg : x < 0) (hynegx : y < -x) (hxy : x < y)
    (hznegx : z < -x) (hxz : x < z) :
    uCandidate p x z ≤
      uCandidate p x y + DyuCandidate p x y * (z - y) := by
  have hQy : QuarterPlane2 x y := ⟨le_of_lt hx_neg, le_of_lt hynegx, le_of_lt hxy⟩
  have hQz : QuarterPlane2 x z := ⟨le_of_lt hx_neg, le_of_lt hznegx, le_of_lt hxz⟩
  have hnotQy : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hx_neg hq.1
  have hnotQz : ¬ QuarterPlane x z := by
    intro hq
    exact not_le_of_gt hx_neg hq.1
  have haux := auxFunction1_tangent_y_on_QuarterPlaneOpen_segment
    p (by linarith : 2 ≤ p)
    (by linarith : 0 < -x)
    (by linarith : -(-x) < -y)
    (by linarith : -y < -x)
    (by linarith : -(-x) < -z)
    (by linarith : -z < -x)
  have hdy : DyuCandidate p x y = -DyauxFunction1 p (-x) (-y) := by
    simp [DyuCandidate, hnotQy, hQy]
  calc
    uCandidate p x z = auxFunction1 p (-x) (-z) := by
      simp [uCandidate, hnotQz, hQz]
    _ ≤ auxFunction1 p (-x) (-y) + DyauxFunction1 p (-x) (-y) * ((-z) - (-y)) := haux
    _ = uCandidate p x y + DyuCandidate p x y * (z - y) := by
      simp [uCandidate, hnotQy, hQy, hdy]
      ring

private lemma uCandidate_tangent_x_on_QuarterPlane3Open_segment
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hneg_x : -y < x) (hxy : x < y)
    (hneg_z : -y < z) (hzy : z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hneg_x, le_of_lt hxy⟩
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, le_of_lt hneg_z, le_of_lt hzy⟩
  have hnotQx : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hxy hq.2.1
  have hnotQ2x : ¬ QuarterPlane2 x y := by
    intro hq
    have hlt : -x < y := by linarith
    exact not_le_of_gt hlt hq.2.1
  have hnotQz : ¬ QuarterPlane z y := by
    intro hq
    exact not_le_of_gt hzy hq.2.1
  have hnotQ2z : ¬ QuarterPlane2 z y := by
    intro hq
    have hlt : -z < y := by linarith
    exact not_le_of_gt hlt hq.2.1
  have haux := auxFunction1_tangent_y_on_QuarterPlaneOpen_segment
    p (by linarith : 2 ≤ p)
    hy_pos hneg_x hxy hneg_z hzy
  have hdx : DxuCandidate p x y = DyauxFunction1 p y x := by
    simp [DxuCandidate, hnotQx, hnotQ2x, hQx]
  calc
    uCandidate p z y = auxFunction1 p y z := by
      simp [uCandidate, hnotQz, hnotQ2z, hQz]
    _ ≤ auxFunction1 p y x + DyauxFunction1 p y x * (z - x) := haux
    _ = uCandidate p x y + DxuCandidate p x y * (z - x) := by
      simp [uCandidate, hnotQx, hnotQ2x, hQx, hdx]

private lemma uCandidate_tangent_x_QuarterPlane3Open_to_diag_segment
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hy_pos : 0 < y) (hneg_x : -y < x) (hxy : x < y) :
    uCandidate p y y ≤
      uCandidate p x y + DxuCandidate p x y * (y - x) := by
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hneg_x, le_of_lt hxy⟩
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hnotQx : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hxy hq.2.1
  have hnotQ2x : ¬ QuarterPlane2 x y := by
    intro hq
    have hlt : -x < y := by linarith
    exact not_le_of_gt hlt hq.2.1
  have haux := auxFunction1_tangent_y_to_diag_from_QuarterPlaneOpen_segment
    p (by linarith : 2 ≤ p) hy_pos hneg_x hxy
  have hdx : DxuCandidate p x y = DyauxFunction1 p y x := by
    simp [DxuCandidate, hnotQx, hnotQ2x, hQx]
  calc
    uCandidate p y y = auxFunction1 p y y := by
      simp [uCandidate, hQy]
    _ ≤ auxFunction1 p y x + DyauxFunction1 p y x * (y - x) := haux
    _ = uCandidate p x y + DxuCandidate p x y * (y - x) := by
      simp [uCandidate, hnotQx, hnotQ2x, hQx, hdx]

private lemma auxFunction1_tangent_y_diag_to_QuarterPlaneOpen_segment
    (p : ℝ) (hp : 2 < p) {x z : ℝ}
    (hx : 0 < x) (hz_lower : -x ≤ z) (hz_upper : z < x) :
    auxFunction1 p x z ≤
      auxFunction1 p x x + DyauxFunction1 p x x * (z - x) := by
  have hp' : 2 ≤ p := by linarith
  let c : ℝ := (a p) * x
  have hc_lt_x : c < x := by
    have hlt : a p < 1 := a_lt_one_of_two_le p hp'
    simpa [c] using mul_lt_mul_of_pos_right hlt hx
  have hneg_c : -x < c := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
    nlinarith [mul_nonneg ha_nonneg hx.le]
  have hdiag : closureA1 p x x := ⟨hx.le, le_of_lt hc_lt_x, le_rfl⟩
  have hcl_c_A1 : closureA1 p x c := ⟨hx.le, le_rfl, le_of_lt hc_lt_x⟩
  have hcl_c_A2 : closureA2 p x c := ⟨hx.le, le_of_lt hneg_c, le_rfl⟩
  have hderiv_x :
      HasDerivAt (fun t => uA1 p x t) (DyauxFunction1 p x x) x := by
    refine (hasDerivAt_uA1_y_of_pos p hp' x x hx).congr_deriv ?_
    exact (auxFunction1_Dy_eq_DyuA1 p x x hdiag).symm
  by_cases hcz : c ≤ z
  · have hcl_z : closureA1 p x z := ⟨hx.le, hcz, le_of_lt hz_upper⟩
    have h_u :
        uA1 p x z ≤ uA1 p x x + DyauxFunction1 p x x * (z - x) := by
      apply uA1_tangent_y_on_Icc_of_A1
        (p := p) (hp := hp') (lo := z) (hi := x) (x := x) (y := x) (z := z)
      · exact hx
      · intro t ht
        have htIoo : t ∈ Set.Ioo z x := by
          simpa [interior_Icc] using ht
        exact ⟨hx, lt_of_le_of_lt hcz htIoo.1, htIoo.2⟩
      · exact ⟨hz_upper.le, le_rfl⟩
      · exact ⟨le_rfl, hz_upper.le⟩
      · exact hderiv_x
    simpa [auxFunction1_eq_uA1 p x z hcl_z,
      auxFunction1_eq_uA1 p x x hdiag] using h_u
  · have hzc : z < c := lt_of_not_ge hcz
    have hcl_z : closureA2 p x z := ⟨hx.le, hz_lower, le_of_lt hzc⟩
    have hderiv_c :
        HasDerivAt (fun t => vGeTwo p x t) (DyauxFunction1 p x c) c := by
      have hsum : 0 < (x + c) / 2 := by linarith [hneg_c]
      have hdiff : 0 < (x - c) / 2 := by linarith [hc_lt_x]
      refine (hasDerivAt_vGeTwo_y_of_pos p hp' x c hsum hdiff).congr_deriv ?_
      exact (auxFunction1_Dy_eq_DyvGeTwo p hp' x c hcl_c_A2).symm
    have h_xc_u :
        uA1 p x c ≤ uA1 p x x + DyauxFunction1 p x x * (c - x) := by
      apply uA1_tangent_y_on_Icc_of_A1
        (p := p) (hp := hp') (lo := c) (hi := x) (x := x) (y := x) (z := c)
      · exact hx
      · intro t ht
        have htIoo : t ∈ Set.Ioo c x := by
          simpa [interior_Icc] using ht
        exact ⟨hx, htIoo.1, htIoo.2⟩
      · exact ⟨hc_lt_x.le, le_rfl⟩
      · exact ⟨le_rfl, hc_lt_x.le⟩
      · exact hderiv_x
    have h_cz_v :
        vGeTwo p x z ≤ vGeTwo p x c + DyauxFunction1 p x c * (z - c) := by
      apply vGeTwo_tangent_y_on_Icc_of_A2
        (p := p) (hp := hp') (lo := z) (hi := c) (x := x) (y := c) (z := z)
      · intro t ht
        have htIoo : t ∈ Set.Ioo z c := by
          simpa [interior_Icc] using ht
        exact ⟨hx, by linarith [htIoo.1], htIoo.2⟩
      · exact ⟨le_of_lt hzc, le_rfl⟩
      · exact ⟨le_rfl, le_of_lt hzc⟩
      · exact hderiv_c
    have h_xc :
        auxFunction1 p x c ≤ auxFunction1 p x x + DyauxFunction1 p x x * (c - x) := by
      simpa [auxFunction1_eq_uA1 p x c hcl_c_A1,
        auxFunction1_eq_uA1 p x x hdiag] using h_xc_u
    have h_cz :
        auxFunction1 p x z ≤ auxFunction1 p x c + DyauxFunction1 p x c * (z - c) := by
      simpa [auxFunction1_eq_vGeTwo p hp' x z hcl_z,
        auxFunction1_eq_vGeTwo p hp' x c hcl_c_A2] using h_cz_v
    have hd : DyauxFunction1 p x x ≤ DyauxFunction1 p x c := by
      rw [auxFunction1_Dy_eq_DyuA1 p x x hdiag,
        auxFunction1_Dy_eq_DyuA1 p x c hcl_c_A1]
      simp [DyuA1]
    exact tangent_glue_two_backward
      (fun t => auxFunction1 p x t) (fun t => DyauxFunction1 p x t)
      hzc.le hc_lt_x.le h_xc h_cz hd

private lemma uCandidate_tangent_x_diag_to_QuarterPlane3Open_segment
    (p : ℝ) (hp : 2 < p) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : -y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p y y + DxuCandidate p y y * (z - y) := by
  have hQd : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt hz_upper⟩
  have hnotQz : ¬ QuarterPlane z y := by
    intro hq
    exact not_le_of_gt hz_upper hq.2.1
  have hnotQ2z : ¬ QuarterPlane2 z y := by
    intro hq
    have hlt : -z < y := by linarith
    exact not_le_of_gt hlt hq.2.1
  have haux := auxFunction1_tangent_y_diag_to_QuarterPlaneOpen_segment
    p hp hy_pos hz_lower.le hz_upper
  have hdx : DxuCandidate p y y = DyauxFunction1 p y y := by
    have h := DxauxFunction1_eq_DyauxFunction1_on_diag p hp y hy_pos.le
    simp [DxuCandidate, hQd, h]
  calc
    uCandidate p z y = auxFunction1 p y z := by
      simp [uCandidate, hnotQz, hnotQ2z, hQz]
    _ ≤ auxFunction1 p y y + DyauxFunction1 p y y * (z - y) := haux
    _ = uCandidate p y y + DxuCandidate p y y * (z - y) := by
      simp [uCandidate, hQd, hdx]

private lemma DxuCandidate_QuarterPlaneOpen_le_diag
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hy_pos : 0 < y) (hyx : y < x) :
    DxuCandidate p x y ≤ DxuCandidate p y y := by
  have hQx : QuarterPlane x y := ⟨(lt_trans hy_pos hyx).le, hyx.le, by linarith⟩
  have hQd : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  by_cases hxc : x ≤ y / a p
  · have ha_pos : 0 < a p := a_pos_of_two_lt p hp
    have hcl_x : closureA1 p x y := by
      refine ⟨(lt_trans hy_pos hyx).le, ?_, hyx.le⟩
      have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
      have hmul : a p * x ≤ a p * (y / a p) :=
        mul_le_mul_of_nonneg_left hxc ha_pos.le
      simpa [hac] using hmul
    have hdiag : closureA1 p y y := by
      have hp' : 2 ≤ p := by linarith
      have hlt := a_lt_one_of_two_le p hp'
      refine ⟨hy_pos.le, ?_, le_rfl⟩
      have hmul : a p * y < 1 * y := mul_lt_mul_of_pos_right hlt hy_pos
      simpa using hmul.le
    have hx_eq : DxuCandidate p x y = DxuA1 p x y := by
      simp [DxuCandidate, hQx, auxFunction1_Dx_eq_DxuA1 p x y hcl_x]
    have hd_eq : DxuCandidate p y y = DxuA1 p y y := by
      simp [DxuCandidate, hQd, auxFunction1_Dx_eq_DxuA1 p y y hdiag]
    rw [hx_eq, hd_eq]
    -- In A1 this is one-dimensional concavity of DxuA1 from the diagonal to x.
    have hle := DxauxFunction1_internal_boundary_le_diag p hp hy_pos
    have hboundary := horizontal_boundary_closureA1_closureA2 p y hp hy_pos
    have hxc_boundary : DxuA1 p x y ≤ DxuA1 p y y := by
      have hp' : 2 ≤ p := by linarith
      have ha_pos : 0 < a p := a_pos_of_two_lt p hp
      let c : ℝ := y / a p
      have hac : a p * c = y := by
        dsimp [c]; field_simp [ha_pos.ne']
      have hyc : y < c := by
        have hlt : a p < 1 := a_lt_one_of_two_le p hp'
        have hlt_inv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact hlt
        have hmul := mul_lt_mul_of_pos_left hlt_inv hy_pos
        simpa [c, div_eq_mul_inv] using hmul
      have hanti :
          AntitoneOn (fun t : ℝ => DxuA1Fun p (t, y)) (Set.Icc y x) := by
        have hcont : ContinuousOn (fun t : ℝ => DxuA1Fun p (t, y)) (Set.Icc y x) := by
          have hpair : ContinuousOn (fun t : ℝ => (t, y)) (Set.Icc y x) :=
            (by continuity : Continuous (fun t : ℝ => (t, y))).continuousOn
          exact (continuousOn_DxuA1_closureA1 p (by linarith : 1 < p)).comp hpair (by
            intro t ht
            have htc : t ≤ c := le_trans ht.2 hxc
            have h_at : a p * t ≤ y := by
              have hmul : a p * t ≤ a p * c :=
                mul_le_mul_of_nonneg_left htc ha_pos.le
              simpa [hac] using hmul
            exact ⟨le_trans hy_pos.le ht.1, h_at, ht.1⟩)
        refine antitoneOn_of_hasDerivWithinAt_nonpos
          (D := Set.Icc y x)
          (f := fun t : ℝ => DxuA1Fun p (t, y))
          (f' := fun t : ℝ => deriv (fun s => DxuA1Fun p (s, y)) t)
          (convex_Icc y x) hcont ?_ ?_
        · intro t ht
          have htIoo : t ∈ Set.Ioo y x := by
            simpa [interior_Icc] using ht
          exact (differentiableAt_DxuA1Fun_x_of_pos p t y
            (lt_trans hy_pos htIoo.1)).hasDerivAt.hasDerivWithinAt
        · intro t ht
          have htIoo : t ∈ Set.Ioo y x := by
            simpa [interior_Icc] using ht
          have htc : t < c := lt_of_lt_of_le htIoo.2 hxc
          have h_at : a p * t < y := by
            have hmul : a p * t < a p * c :=
              mul_lt_mul_of_pos_left htc ha_pos
            simpa [hac] using hmul
          exact deriv_DxuA1Fun_x_nonpos_on_A1 p hp' t y
            ⟨lt_trans hy_pos htIoo.1, h_at, htIoo.1⟩
      have hy_mem : y ∈ Set.Icc y x := ⟨le_rfl, hyx.le⟩
      have hx_mem : x ∈ Set.Icc y x := ⟨hyx.le, le_rfl⟩
      have hle' : DxuA1Fun p (x, y) ≤ DxuA1Fun p (y, y) := hanti hy_mem hx_mem hyx.le
      simpa [DxuA1Fun] using hle'
    exact hxc_boundary
  · have hcx : y / a p < x := lt_of_not_ge hxc
    have hle_boundary : DxauxFunction1 p x y ≤ DxauxFunction1 p (y / a p) y := by
      have ha_pos : 0 < a p := a_pos_of_two_lt p hp
      have hay : y < a p * x := by
        have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
        have hmul : a p * (y / a p) < a p * x :=
          mul_lt_mul_of_pos_left hcx ha_pos
        simpa [hac] using hmul
      exact DxauxFunction1_A2_le_boundary p hp (lt_trans (div_pos hy_pos ha_pos) hcx) hy_pos hay
    have hle_diag := DxauxFunction1_internal_boundary_le_diag p hp hy_pos
    have hx_aux : DxuCandidate p x y = DxauxFunction1 p x y := by simp [DxuCandidate, hQx]
    have hd_aux : DxuCandidate p y y = DxauxFunction1 p y y := by simp [DxuCandidate, hQd]
    rw [hx_aux, hd_aux]
    linarith

private lemma uCandidate_tangent_x_cross_QuarterPlaneOpen_to_QuarterPlane3Open
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hyx : y < x)
    (hz_lower : -y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have h_x_d := uCandidate_tangent_x_QuarterPlaneOpen_to_diag_segment
    p hp hy_pos hyx
  have h_d_z := uCandidate_tangent_x_diag_to_QuarterPlane3Open_segment
    p hp hy_pos hz_lower hz_upper
  have hd := DxuCandidate_QuarterPlaneOpen_le_diag p hp hy_pos hyx
  exact tangent_glue_two_backward
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    hz_upper.le hyx.le h_x_d h_d_z hd

private lemma DxuCandidate_diag_le_QuarterPlane3Open
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hy_pos : 0 < y) (hneg_x : -y < x) (hxy : x < y) :
    DxuCandidate p y y ≤ DxuCandidate p x y := by
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hneg_x, le_of_lt hxy⟩
  have hQy : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hnotQx : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hxy hq.2.1
  have hnotQ2x : ¬ QuarterPlane2 x y := by
    intro hq
    have hlt : -x < y := by linarith
    exact not_le_of_gt hlt hq.2.1
  have hdiag :
      DxuCandidate p y y = DyauxFunction1 p y y := by
    have h := DxauxFunction1_eq_DyauxFunction1_on_diag p hp y hy_pos.le
    simp [DxuCandidate, hQy, h]
  have hstart :
      DxuCandidate p x y = DyauxFunction1 p y x := by
    simp [DxuCandidate, hnotQx, hnotQ2x, hQx]
  calc
    DxuCandidate p y y = DyauxFunction1 p y y := hdiag
    _ ≤ DyauxFunction1 p y x :=
      DyauxFunction1_diag_le_of_QuarterPlaneOpen
        p (by linarith : 2 ≤ p) hy_pos hneg_x hxy
    _ = DxuCandidate p x y := hstart.symm

private lemma uCandidate_tangent_x_cross_QuarterPlane3Open_to_QuarterPlaneOpen
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hneg_x : -y < x) (hxy : x < y)
    (hyz : y < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have h_x_diag := uCandidate_tangent_x_QuarterPlane3Open_to_diag_segment
    p hp hy_pos hneg_x hxy
  have h_diag_z := uCandidate_tangent_x_diag_to_QuarterPlaneOpen_segment
    p hp hy_pos hyz
  have hd := DxuCandidate_diag_le_QuarterPlane3Open
    p hp hy_pos hneg_x hxy
  exact tangent_glue_two_forward
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    hxy.le hyz.le h_x_diag h_diag_z hd

private lemma auxFunction1_tangent_x_to_antidiag_from_QuarterPlaneOpen_segment
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ}
    (hx_pos : 0 < x) (hy_neg : y < 0) (_hyx : y < x) (hneg_x : -x < y) :
    auxFunction1 p (-y) y ≤
      auxFunction1 p x y + DxauxFunction1 p x y * ((-y) - x) := by
  have hcl_x : closureA2 p x y := ⟨hx_pos.le, le_of_lt hneg_x, by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
    have haxy_nonneg : 0 ≤ a p * x := mul_nonneg ha_nonneg hx_pos.le
    linarith⟩
  have hcl_a : closureA2 p (-y) y := by
    refine ⟨(neg_pos.mpr hy_neg).le, by linarith, ?_⟩
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
    have hnonneg : 0 ≤ a p * (-y) := mul_nonneg ha_nonneg (neg_nonneg.mpr hy_neg.le)
    linarith
  have hderiv_x :
      HasDerivAt (fun t => vGeTwo p t y) (DxauxFunction1 p x y) x := by
    have hsum : 0 < (x + y) / 2 := by linarith
    have hdiff : 0 < (x - y) / 2 := by linarith
    refine (hasDerivAt_vGeTwo_x_of_pos p hp x y hsum hdiff).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxvGeTwo p hp x y hcl_x).symm
  have h_v :
      vGeTwo p (-y) y ≤ vGeTwo p x y + DxauxFunction1 p x y * ((-y) - x) := by
    apply vGeTwo_tangent_x_on_Icc_of_A2
      (p := p) (hp := hp) (lo := -y) (hi := x) (x := x) (z := -y) (y := y)
    · intro t ht
      have htIoo : t ∈ Set.Ioo (-y) x := by
        simpa [interior_Icc] using ht
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
      have ht_pos : 0 < t := lt_trans (neg_pos.mpr hy_neg) htIoo.1
      exact ⟨ht_pos, by linarith [htIoo.1], lt_of_lt_of_le hy_neg
        (mul_nonneg ha_nonneg ht_pos.le)⟩
    · exact ⟨(by linarith : -y ≤ x), le_rfl⟩
    · exact ⟨le_rfl, by linarith⟩
    · exact hderiv_x
  simpa [auxFunction1_eq_vGeTwo p hp (-y) y hcl_a,
    auxFunction1_eq_vGeTwo p hp x y hcl_x] using h_v

private lemma DxauxFunction1_QuarterPlaneOpen_le_antidiag
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ}
    (hx_pos : 0 < x) (hy_neg : y < 0) (hneg_x : -x < y) :
    DxauxFunction1 p x y ≤ DxauxFunction1 p (-y) y := by
  have hcl_x : closureA2 p x y := ⟨hx_pos.le, le_of_lt hneg_x, by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
    have haxy_nonneg : 0 ≤ a p * x := mul_nonneg ha_nonneg hx_pos.le
    linarith⟩
  have hcl_a : closureA2 p (-y) y := by
    refine ⟨(neg_pos.mpr hy_neg).le, by linarith, ?_⟩
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
    have hnonneg : 0 ≤ a p * (-y) := mul_nonneg ha_nonneg (neg_nonneg.mpr hy_neg.le)
    linarith
  have hanti :
      AntitoneOn (fun t : ℝ => DxvGeTwo p t y) (Set.Icc (-y) x) := by
    have hcont : ContinuousOn (fun t : ℝ => DxvGeTwo p t y) (Set.Icc (-y) x) := by
      have hpair : ContinuousOn (fun t : ℝ => (t, y)) (Set.Icc (-y) x) :=
        (by continuity : Continuous (fun t : ℝ => (t, y))).continuousOn
      exact (continuousOn_DxvGeTwo_closureA2 p hp).comp hpair (by
        intro t ht
        have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
        have ht_pos : 0 ≤ t := le_trans (neg_nonneg.mpr hy_neg.le) ht.1
        exact ⟨ht_pos, by linarith [ht.1], le_trans (le_of_lt hy_neg)
          (mul_nonneg ha_nonneg ht_pos)⟩)
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc (-y) x)
      (f := fun t : ℝ => DxvGeTwo p t y)
      (f' := fun t : ℝ => deriv (fun s => DxvGeTwo p s y) t)
      (convex_Icc (-y) x) hcont ?_ ?_
    · intro t ht
      have htIoo : t ∈ Set.Ioo (-y) x := by
        simpa [interior_Icc] using ht
      have hsum : 0 < (t + y) / 2 := by linarith [htIoo.1]
      have hdiff : 0 < (t - y) / 2 := by linarith [hy_neg, htIoo.1]
      exact (differentiableAt_DxvGeTwo_x_of_pos p t y hsum hdiff).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htIoo : t ∈ Set.Ioo (-y) x := by
        simpa [interior_Icc] using ht
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
      have ht_pos : 0 < t := lt_trans (neg_pos.mpr hy_neg) htIoo.1
      exact deriv_DxvGeTwo_x_nonpos_on_A2 p hp t y
        ⟨ht_pos, by linarith [htIoo.1], lt_of_lt_of_le hy_neg
          (mul_nonneg ha_nonneg ht_pos.le)⟩
  have ha_mem : (-y) ∈ Set.Icc (-y) x := ⟨le_rfl, by linarith⟩
  have hx_mem : x ∈ Set.Icc (-y) x := ⟨by linarith, le_rfl⟩
  have hle : DxvGeTwo p x y ≤ DxvGeTwo p (-y) y :=
    hanti ha_mem hx_mem (by linarith)
  simpa [auxFunction1_Dx_eq_DxvGeTwo p hp x y hcl_x,
    auxFunction1_Dx_eq_DxvGeTwo p hp (-y) y hcl_a] using hle

private lemma uCandidate_tangent_x_QuarterPlane2Open_to_antidiag_segment
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    uCandidate p (-y) y ≤
      uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
  have hx_neg : x < 0 := by linarith
  have hQx : QuarterPlane2 x y :=
    ⟨le_of_lt hx_neg, le_of_lt (by linarith : y < -x), le_of_lt (by linarith : x < y)⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hnotQx : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hx_neg hq.1
  have hnotQa : ¬ QuarterPlane (-y) y := by
    intro hq
    exact not_le_of_gt (by linarith : -y < 0) hq.1
  have haux := auxFunction1_tangent_x_to_antidiag_from_QuarterPlaneOpen_segment
    p (by linarith : 2 ≤ p)
    (by linarith : 0 < -x)
    (by linarith : -y < 0)
    (by linarith : -y < -x)
    (by linarith : -(-x) < -y)
  have hdx : DxuCandidate p x y = -DxauxFunction1 p (-x) (-y) := by
    simp [DxuCandidate, hnotQx, hQx]
  calc
    uCandidate p (-y) y = auxFunction1 p y (-y) := by
      simp [uCandidate, hnotQa, hQa]
    _ ≤ auxFunction1 p (-x) (-y) + DxauxFunction1 p (-x) (-y) * (y - (-x)) := by
      simpa using haux
    _ = uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
      simp [uCandidate, hnotQx, hQx, hdx]
      ring

private lemma DyauxFunction1_internal_boundary_le_antidiag
    (p : ℝ) (hp : 2 < p) {x : ℝ} (hx : 0 < x) :
    DyauxFunction1 p x ((a p) * x) ≤ DyauxFunction1 p x (-x) := by
  have hp' : 2 ≤ p := by linarith
  let c : ℝ := (a p) * x
  have hc_lt_x : c < x := by
    have hlt : a p < 1 := a_lt_one_of_two_le p hp'
    simpa [c] using mul_lt_mul_of_pos_right hlt hx
  have hneg_c : -x < c := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
    nlinarith [mul_nonneg ha_nonneg hx.le]
  have hcl_a : closureA2 p x (-x) := by
    refine ⟨hx.le, le_rfl, ?_⟩
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
    exact le_trans (neg_nonpos.mpr hx.le) (mul_nonneg ha_nonneg hx.le)
  have hcl_c : closureA2 p x c := ⟨hx.le, le_of_lt hneg_c, le_rfl⟩
  have hanti :
      AntitoneOn (fun t : ℝ => DyvGeTwo p x t) (Set.Icc (-x) c) := by
    have hcont : ContinuousOn (fun t : ℝ => DyvGeTwo p x t) (Set.Icc (-x) c) := by
      have hpair : ContinuousOn (fun t : ℝ => (x, t)) (Set.Icc (-x) c) :=
        (by continuity : Continuous (fun t : ℝ => (x, t))).continuousOn
      exact (continuousOn_DyvGeTwo_closureA2 p hp').comp hpair (by
        intro t ht
        exact ⟨hx.le, ht.1, ht.2⟩)
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc (-x) c)
      (f := fun t : ℝ => DyvGeTwo p x t)
      (f' := fun t : ℝ => deriv (fun s => DyvGeTwo p x s) t)
      (convex_Icc (-x) c) hcont ?_ ?_
    · intro t ht
      have htIoo : t ∈ Set.Ioo (-x) c := by
        simpa [interior_Icc] using ht
      have hsum : 0 < (x + t) / 2 := by linarith [htIoo.1]
      have hdiff : 0 < (x - t) / 2 := by linarith [htIoo.2, hc_lt_x]
      exact (differentiableAt_DyvGeTwo_y_of_pos p x t hsum hdiff).hasDerivAt.hasDerivWithinAt
    · intro t ht
      have htIoo : t ∈ Set.Ioo (-x) c := by
        simpa [interior_Icc] using ht
      exact deriv_DyvGeTwo_y_nonpos_on_A2 p hp' x t ⟨hx, htIoo.1, htIoo.2⟩
  have ha_mem : (-x) ∈ Set.Icc (-x) c := ⟨le_rfl, le_of_lt hneg_c⟩
  have hc_mem : c ∈ Set.Icc (-x) c := ⟨le_of_lt hneg_c, le_rfl⟩
  have hle : DyvGeTwo p x c ≤ DyvGeTwo p x (-x) :=
    hanti ha_mem hc_mem (le_of_lt hneg_c)
  simpa [c, auxFunction1_Dy_eq_DyvGeTwo p hp' x ((a p) * x) hcl_c,
    auxFunction1_Dy_eq_DyvGeTwo p hp' x (-x) hcl_a] using hle

private lemma auxFunction1_tangent_y_antidiag_to_QuarterPlaneOpen_segment
    (p : ℝ) (hp : 2 < p) {x z : ℝ}
    (hx : 0 < x) (hz_lower : -x < z) (hz_upper : z ≤ x) :
    auxFunction1 p x z ≤
      auxFunction1 p x (-x) + DyauxFunction1 p x (-x) * (z - (-x)) := by
  have hp' : 2 ≤ p := by linarith
  let c : ℝ := (a p) * x
  have hc_lt_x : c < x := by
    have hlt : a p < 1 := a_lt_one_of_two_le p hp'
    simpa [c] using mul_lt_mul_of_pos_right hlt hx
  have hneg_c : -x < c := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
    nlinarith [mul_nonneg ha_nonneg hx.le]
  have hcl_a_A2 : closureA2 p x (-x) := by
    refine ⟨hx.le, le_rfl, ?_⟩
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
    exact le_trans (neg_nonpos.mpr hx.le) (mul_nonneg ha_nonneg hx.le)
  have hcl_c_A2 : closureA2 p x c := ⟨hx.le, le_of_lt hneg_c, le_rfl⟩
  have hcl_c_A1 : closureA1 p x c := ⟨hx.le, le_rfl, le_of_lt hc_lt_x⟩
  have hderiv_a :
      HasDerivAt (fun t => vGeTwo p x t) (DyauxFunction1 p x (-x)) (-x) := by
    refine (hasDerivAt_vGeTwo_y_on_antidiag_pos p hp x hx).congr_deriv ?_
    exact (auxFunction1_Dy_eq_DyvGeTwo p hp' x (-x) hcl_a_A2).symm
  by_cases hzc : z ≤ c
  · have hcl_z : closureA2 p x z := ⟨hx.le, le_of_lt hz_lower, hzc⟩
    have h_v :
        vGeTwo p x z ≤ vGeTwo p x (-x) + DyauxFunction1 p x (-x) * (z - (-x)) := by
      apply vGeTwo_tangent_y_on_Icc_of_A2
        (p := p) (hp := hp') (lo := -x) (hi := z) (x := x) (y := -x) (z := z)
      · intro t ht
        have htIoo : t ∈ Set.Ioo (-x) z := by
          simpa [interior_Icc] using ht
        exact ⟨hx, htIoo.1, lt_of_lt_of_le htIoo.2 hzc⟩
      · exact ⟨le_rfl, hz_lower.le⟩
      · exact ⟨hz_lower.le, le_rfl⟩
      · exact hderiv_a
    simpa [auxFunction1_eq_vGeTwo p hp' x z hcl_z,
      auxFunction1_eq_vGeTwo p hp' x (-x) hcl_a_A2] using h_v
  · have hcz : c < z := lt_of_not_ge hzc
    have hcl_z : closureA1 p x z := ⟨hx.le, le_of_lt hcz, hz_upper⟩
    have hderiv_c :
        HasDerivAt (fun t => uA1 p x t) (DyauxFunction1 p x c) c := by
      refine (hasDerivAt_uA1_y_of_pos p hp' x c hx).congr_deriv ?_
      exact (auxFunction1_Dy_eq_DyuA1 p x c hcl_c_A1).symm
    have h_ac_v :
        vGeTwo p x c ≤ vGeTwo p x (-x) + DyauxFunction1 p x (-x) * (c - (-x)) := by
      apply vGeTwo_tangent_y_on_Icc_of_A2
        (p := p) (hp := hp') (lo := -x) (hi := c) (x := x) (y := -x) (z := c)
      · intro t ht
        have htIoo : t ∈ Set.Ioo (-x) c := by
          simpa [interior_Icc] using ht
        exact ⟨hx, htIoo.1, htIoo.2⟩
      · exact ⟨le_rfl, le_of_lt hneg_c⟩
      · exact ⟨le_of_lt hneg_c, le_rfl⟩
      · exact hderiv_a
    have h_cz_u :
        uA1 p x z ≤ uA1 p x c + DyauxFunction1 p x c * (z - c) := by
      apply uA1_tangent_y_on_Icc_of_A1
        (p := p) (hp := hp') (lo := c) (hi := z) (x := x) (y := c) (z := z)
      · exact hx
      · intro t ht
        have htIoo : t ∈ Set.Ioo c z := by
          simpa [interior_Icc] using ht
        exact ⟨hx, htIoo.1, lt_of_lt_of_le htIoo.2 hz_upper⟩
      · exact ⟨le_rfl, hcz.le⟩
      · exact ⟨hcz.le, le_rfl⟩
      · exact hderiv_c
    have h_ac :
        auxFunction1 p x c ≤ auxFunction1 p x (-x) +
          DyauxFunction1 p x (-x) * (c - (-x)) := by
      simpa [auxFunction1_eq_vGeTwo p hp' x c hcl_c_A2,
        auxFunction1_eq_vGeTwo p hp' x (-x) hcl_a_A2] using h_ac_v
    have h_cz :
        auxFunction1 p x z ≤ auxFunction1 p x c + DyauxFunction1 p x c * (z - c) := by
      simpa [auxFunction1_eq_uA1 p x z hcl_z,
        auxFunction1_eq_uA1 p x c hcl_c_A1] using h_cz_u
    have hd : DyauxFunction1 p x c ≤ DyauxFunction1 p x (-x) := by
      simpa [c] using DyauxFunction1_internal_boundary_le_antidiag p hp hx
    exact tangent_glue_two_forward
      (fun t => auxFunction1 p x t) (fun t => DyauxFunction1 p x t)
      (le_of_lt hneg_c) hcz.le h_ac h_cz hd

/--
Tangent estimate from an interior first-quadrant point down to the antidiagonal.

This is the reverse-direction companion to
`auxFunction1_tangent_y_antidiag_to_QuarterPlaneOpen_segment`.  The segment
may lie entirely in A2, or it may first move through A1 and then cross the
internal A1/A2 boundary before reaching the antidiagonal.
-/
private lemma auxFunction1_tangent_y_QuarterPlaneOpen_to_antidiag_segment
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hx : 0 < x) (hy_lower : -x < y) (hy_upper : y < x) :
    auxFunction1 p x (-x) ≤
      auxFunction1 p x y + DyauxFunction1 p x y * ((-x) - y) := by
  have hp' : 2 ≤ p := by linarith
  let c : ℝ := (a p) * x
  have hc_lt_x : c < x := by
    have hlt : a p < 1 := a_lt_one_of_two_le p hp'
    simpa [c] using mul_lt_mul_of_pos_right hlt hx
  have hneg_c : -x < c := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
    nlinarith [mul_nonneg ha_nonneg hx.le]
  have hcl_a_A2 : closureA2 p x (-x) := by
    refine ⟨hx.le, le_rfl, ?_⟩
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
    exact le_trans (neg_nonpos.mpr hx.le) (mul_nonneg ha_nonneg hx.le)
  have hcl_c_A2 : closureA2 p x c := ⟨hx.le, le_of_lt hneg_c, le_rfl⟩
  have hcl_c_A1 : closureA1 p x c := ⟨hx.le, le_rfl, le_of_lt hc_lt_x⟩
  by_cases hyc : y ≤ c
  · have hcl_y : closureA2 p x y := ⟨hx.le, le_of_lt hy_lower, hyc⟩
    have hderiv_y :
        HasDerivAt (fun t => vGeTwo p x t) (DyauxFunction1 p x y) y := by
      have hsum : 0 < (x + y) / 2 := by linarith
      have hdiff : 0 < (x - y) / 2 := by linarith
      refine (hasDerivAt_vGeTwo_y_of_pos p hp' x y hsum hdiff).congr_deriv ?_
      exact (auxFunction1_Dy_eq_DyvGeTwo p hp' x y hcl_y).symm
    have h_v :
        vGeTwo p x (-x) ≤
          vGeTwo p x y + DyauxFunction1 p x y * ((-x) - y) := by
      apply vGeTwo_tangent_y_on_Icc_of_A2
        (p := p) (hp := hp') (lo := -x) (hi := y)
        (x := x) (y := y) (z := -x)
      · intro t ht
        have htIoo : t ∈ Set.Ioo (-x) y := by
          simpa [interior_Icc] using ht
        exact ⟨hx, htIoo.1, lt_of_lt_of_le htIoo.2 hyc⟩
      · exact ⟨hy_lower.le, le_rfl⟩
      · exact ⟨le_rfl, hy_lower.le⟩
      · exact hderiv_y
    simpa [auxFunction1_eq_vGeTwo p hp' x (-x) hcl_a_A2,
      auxFunction1_eq_vGeTwo p hp' x y hcl_y] using h_v
  · have hcy : c < y := lt_of_not_ge hyc
    have hcl_y : closureA1 p x y := ⟨hx.le, le_of_lt hcy, le_of_lt hy_upper⟩
    have hderiv_y :
        HasDerivAt (fun t => uA1 p x t) (DyauxFunction1 p x y) y := by
      refine (hasDerivAt_uA1_y_of_pos p hp' x y hx).congr_deriv ?_
      exact (auxFunction1_Dy_eq_DyuA1 p x y hcl_y).symm
    have hderiv_c :
        HasDerivAt (fun t => vGeTwo p x t) (DyauxFunction1 p x c) c := by
      have hsum : 0 < (x + c) / 2 := by linarith [hneg_c]
      have hdiff : 0 < (x - c) / 2 := by linarith [hc_lt_x]
      refine (hasDerivAt_vGeTwo_y_of_pos p hp' x c hsum hdiff).congr_deriv ?_
      exact (auxFunction1_Dy_eq_DyvGeTwo p hp' x c hcl_c_A2).symm
    have h_yc_u :
        uA1 p x c ≤ uA1 p x y + DyauxFunction1 p x y * (c - y) := by
      apply uA1_tangent_y_on_Icc_of_A1
        (p := p) (hp := hp') (lo := c) (hi := y)
        (x := x) (y := y) (z := c)
      · exact hx
      · intro t ht
        have htIoo : t ∈ Set.Ioo c y := by
          simpa [interior_Icc] using ht
        exact ⟨hx, htIoo.1, lt_trans htIoo.2 hy_upper⟩
      · exact ⟨hcy.le, le_rfl⟩
      · exact ⟨le_rfl, hcy.le⟩
      · exact hderiv_y
    have h_cz_v :
        vGeTwo p x (-x) ≤
          vGeTwo p x c + DyauxFunction1 p x c * ((-x) - c) := by
      apply vGeTwo_tangent_y_on_Icc_of_A2
        (p := p) (hp := hp') (lo := -x) (hi := c)
        (x := x) (y := c) (z := -x)
      · intro t ht
        have htIoo : t ∈ Set.Ioo (-x) c := by
          simpa [interior_Icc] using ht
        exact ⟨hx, htIoo.1, htIoo.2⟩
      · exact ⟨le_of_lt hneg_c, le_rfl⟩
      · exact ⟨le_rfl, le_of_lt hneg_c⟩
      · exact hderiv_c
    have h_yc :
        auxFunction1 p x c ≤
          auxFunction1 p x y + DyauxFunction1 p x y * (c - y) := by
      simpa [auxFunction1_eq_uA1 p x c hcl_c_A1,
        auxFunction1_eq_uA1 p x y hcl_y] using h_yc_u
    have h_cz :
        auxFunction1 p x (-x) ≤
          auxFunction1 p x c + DyauxFunction1 p x c * ((-x) - c) := by
      simpa [auxFunction1_eq_vGeTwo p hp' x (-x) hcl_a_A2,
        auxFunction1_eq_vGeTwo p hp' x c hcl_c_A2] using h_cz_v
    have hd : DyauxFunction1 p x y ≤ DyauxFunction1 p x c := by
      rw [auxFunction1_Dy_eq_DyuA1 p x y hcl_y,
        auxFunction1_Dy_eq_DyuA1 p x c hcl_c_A1]
      simp [DyuA1]
    exact tangent_glue_two_backward
      (fun t => auxFunction1 p x t) (fun t => DyauxFunction1 p x t)
      (le_of_lt hneg_c) hcy.le h_yc h_cz hd

private lemma uCandidate_tangent_x_antidiag_to_QuarterPlane3Open_segment
    (p : ℝ) (hp : 2 < p) {z y : ℝ}
    (hy_pos : 0 < y) (hz_lower : -y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, le_of_lt hz_lower, le_of_lt hz_upper⟩
  have hnotQa : ¬ QuarterPlane (-y) y := by
    intro hq
    exact not_le_of_gt (by linarith : -y < 0) hq.1
  have hnotQz : ¬ QuarterPlane z y := by
    intro hq
    exact not_le_of_gt hz_upper hq.2.1
  have hnotQ2z : ¬ QuarterPlane2 z y := by
    intro hq
    have hlt : -z < y := by linarith
    exact not_le_of_gt hlt hq.2.1
  have haux := auxFunction1_tangent_y_antidiag_to_QuarterPlaneOpen_segment
    p hp hy_pos hz_lower hz_upper.le
  have hdx : DxuCandidate p (-y) y = DyauxFunction1 p y (-y) := by
    have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp y hy_pos.le
    simp [DxuCandidate, hnotQa, hQa, hrel]
  calc
    uCandidate p z y = auxFunction1 p y z := by
      simp [uCandidate, hnotQz, hnotQ2z, hQz]
    _ ≤ auxFunction1 p y (-y) + DyauxFunction1 p y (-y) * (z - (-y)) := haux
    _ = uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
      simp [uCandidate, hnotQa, hQa, hdx]

/--
Horizontal tangent estimate from Q3 down to the antidiagonal.

Under the Q3 reflection `uCandidate p x y = auxFunction1 p y x`, this is the
auxiliary vertical estimate from an interior point to `-y`.
-/
private lemma uCandidate_tangent_x_QuarterPlane3Open_to_antidiag_segment
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hy_pos : 0 < y) (hneg_x : -y < x) (hxy : x < y) :
    uCandidate p (-y) y ≤
      uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hneg_x, le_of_lt hxy⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hnotQx : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hxy hq.2.1
  have hnotQ2x : ¬ QuarterPlane2 x y := by
    intro hq
    have hlt : -x < y := by linarith
    exact not_le_of_gt hlt hq.2.1
  have hnotQa : ¬ QuarterPlane (-y) y := by
    intro hq
    exact not_le_of_gt (by linarith : -y < 0) hq.1
  have haux := auxFunction1_tangent_y_QuarterPlaneOpen_to_antidiag_segment
    p hp hy_pos hneg_x hxy
  have hdx : DxuCandidate p x y = DyauxFunction1 p y x := by
    simp [DxuCandidate, hnotQx, hnotQ2x, hQx]
  calc
    uCandidate p (-y) y = auxFunction1 p y (-y) := by
      simp [uCandidate, hnotQa, hQa]
    _ ≤ auxFunction1 p y x + DyauxFunction1 p y x * ((-y) - x) := haux
    _ = uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
      simp [uCandidate, hnotQx, hnotQ2x, hQx, hdx]

/--
First-quadrant estimate from the antidiagonal to the right, along A2.

This is the auxiliary form of moving left from the antidiagonal into Q2 in the
original coordinates.  The whole open segment lies in A2; only the starting
point is on the antidiagonal boundary.
-/
private lemma auxFunction1_tangent_x_antidiag_to_right_segment
    (p : ℝ) (hp : 2 < p) {x z : ℝ}
    (hx : 0 < x) (hxz : x < z) :
    auxFunction1 p z (-x) ≤
      auxFunction1 p x (-x) + DxauxFunction1 p x (-x) * (z - x) := by
  have hp' : 2 ≤ p := by linarith
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
  have hcl_x : closureA2 p x (-x) := by
    refine ⟨hx.le, le_rfl, ?_⟩
    exact le_trans (neg_nonpos.mpr hx.le) (mul_nonneg ha_nonneg hx.le)
  have hz_pos : 0 < z := lt_trans hx hxz
  have hcl_z : closureA2 p z (-x) := by
    refine ⟨hz_pos.le, ?_, ?_⟩
    · linarith
    · exact le_trans (by linarith : -x ≤ 0) (mul_nonneg ha_nonneg hz_pos.le)
  have hderiv_x :
      HasDerivAt (fun t => vGeTwo p t (-x)) (DxauxFunction1 p x (-x)) x := by
    refine (hasDerivAt_vGeTwo_x_on_antidiag_pos p hp x hx).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxvGeTwo p hp' x (-x) hcl_x).symm
  have h_v :
      vGeTwo p z (-x) ≤
        vGeTwo p x (-x) + DxauxFunction1 p x (-x) * (z - x) := by
    apply vGeTwo_tangent_x_on_Icc_of_A2
      (p := p) (hp := hp') (lo := x) (hi := z)
      (x := x) (z := z) (y := -x)
    · intro t ht
      have htIoo : t ∈ Set.Ioo x z := by
        simpa [interior_Icc] using ht
      have ht_pos : 0 < t := lt_trans hx htIoo.1
      refine ⟨ht_pos, by linarith [htIoo.1], ?_⟩
      exact lt_of_lt_of_le (by linarith : -x < 0)
        (mul_nonneg ha_nonneg ht_pos.le)
    · exact ⟨le_rfl, hxz.le⟩
    · exact ⟨hxz.le, le_rfl⟩
    · exact hderiv_x
  simpa [auxFunction1_eq_vGeTwo p hp' z (-x) hcl_z,
    auxFunction1_eq_vGeTwo p hp' x (-x) hcl_x] using h_v

/--
Horizontal tangent estimate from the antidiagonal into Q2.

This is the original-coordinate wrapper for
`auxFunction1_tangent_x_antidiag_to_right_segment`.
-/
private lemma uCandidate_tangent_x_antidiag_to_QuarterPlane2Open_segment
    (p : ℝ) (hp : 2 < p) {z y : ℝ}
    (hy_pos : 0 < y) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hz_neg : z < 0 := by linarith
  have hQz : QuarterPlane2 z y :=
    ⟨le_of_lt hz_neg, le_of_lt (by linarith : y < -z),
      le_of_lt (by linarith : z < y)⟩
  have hnotQa : ¬ QuarterPlane (-y) y := by
    intro hq
    exact not_le_of_gt (by linarith : -y < 0) hq.1
  have hnotQz : ¬ QuarterPlane z y := by
    intro hq
    exact not_le_of_gt hz_neg hq.1
  have haux := auxFunction1_tangent_x_antidiag_to_right_segment
    p hp hy_pos (by linarith : y < -z)
  have hdx : DxuCandidate p (-y) y = -DxauxFunction1 p y (-y) := by
    simp [DxuCandidate, hnotQa, hQa]
  calc
    uCandidate p z y = auxFunction1 p (-z) (-y) := by
      simp [uCandidate, hnotQz, hQz]
    _ ≤ auxFunction1 p y (-y) + DxauxFunction1 p y (-y) * ((-z) - y) := haux
    _ = uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
      simp [uCandidate, hnotQa, hQa, hdx]
      ring

/--
Derivative comparison from an interior first-quadrant point down to the
antidiagonal.

This is the derivative monotonicity input for the backward glue across the
antidiagonal.
-/
private lemma DyauxFunction1_QuarterPlaneOpen_le_antidiag
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hx : 0 < x) (hy_lower : -x < y) (hy_upper : y < x) :
    DyauxFunction1 p x y ≤ DyauxFunction1 p x (-x) := by
  have hp' : 2 ≤ p := by linarith
  let c : ℝ := (a p) * x
  have hc_lt_x : c < x := by
    have hlt : a p < 1 := a_lt_one_of_two_le p hp'
    simpa [c] using mul_lt_mul_of_pos_right hlt hx
  have hneg_c : -x < c := by
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
    nlinarith [mul_nonneg ha_nonneg hx.le]
  by_cases hyc : y ≤ c
  · have hcl_y : closureA2 p x y := ⟨hx.le, le_of_lt hy_lower, hyc⟩
    have hcl_a : closureA2 p x (-x) := by
      have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
      exact ⟨hx.le, le_rfl,
        le_trans (neg_nonpos.mpr hx.le) (mul_nonneg ha_nonneg hx.le)⟩
    have hanti :
        AntitoneOn (fun t : ℝ => DyvGeTwo p x t) (Set.Icc (-x) y) := by
      have hcont : ContinuousOn (fun t : ℝ => DyvGeTwo p x t) (Set.Icc (-x) y) := by
        have hpair : ContinuousOn (fun t : ℝ => (x, t)) (Set.Icc (-x) y) :=
          (by continuity : Continuous (fun t : ℝ => (x, t))).continuousOn
        exact (continuousOn_DyvGeTwo_closureA2 p hp').comp hpair (by
          intro t ht
          exact ⟨hx.le, ht.1, le_trans ht.2 hyc⟩)
      refine antitoneOn_of_hasDerivWithinAt_nonpos
        (D := Set.Icc (-x) y)
        (f := fun t : ℝ => DyvGeTwo p x t)
        (f' := fun t : ℝ => deriv (fun s => DyvGeTwo p x s) t)
        (convex_Icc (-x) y) hcont ?_ ?_
      · intro t ht
        have htIoo : t ∈ Set.Ioo (-x) y := by
          simpa [interior_Icc] using ht
        have hsum : 0 < (x + t) / 2 := by linarith [htIoo.1]
        have hdiff : 0 < (x - t) / 2 := by linarith [htIoo.2, hy_upper]
        exact (differentiableAt_DyvGeTwo_y_of_pos p x t hsum hdiff).hasDerivAt.hasDerivWithinAt
      · intro t ht
        have htIoo : t ∈ Set.Ioo (-x) y := by
          simpa [interior_Icc] using ht
        exact deriv_DyvGeTwo_y_nonpos_on_A2 p hp' x t
          ⟨hx, htIoo.1, lt_of_lt_of_le htIoo.2 hyc⟩
    have ha_mem : (-x) ∈ Set.Icc (-x) y := ⟨le_rfl, hy_lower.le⟩
    have hy_mem : y ∈ Set.Icc (-x) y := ⟨hy_lower.le, le_rfl⟩
    have hle : DyvGeTwo p x y ≤ DyvGeTwo p x (-x) :=
      hanti ha_mem hy_mem hy_lower.le
    simpa [auxFunction1_Dy_eq_DyvGeTwo p hp' x y hcl_y,
      auxFunction1_Dy_eq_DyvGeTwo p hp' x (-x) hcl_a] using hle
  · have hcy : c < y := lt_of_not_ge hyc
    have hcl_y : closureA1 p x y := ⟨hx.le, le_of_lt hcy, le_of_lt hy_upper⟩
    have hcl_c : closureA1 p x c := ⟨hx.le, le_rfl, le_of_lt hc_lt_x⟩
    have h_eq : DyauxFunction1 p x y = DyauxFunction1 p x c := by
      rw [auxFunction1_Dy_eq_DyuA1 p x y hcl_y,
        auxFunction1_Dy_eq_DyuA1 p x c hcl_c]
      simp [DyuA1]
    calc
      DyauxFunction1 p x y = DyauxFunction1 p x c := h_eq
      _ ≤ DyauxFunction1 p x (-x) := by
        simpa [c] using DyauxFunction1_internal_boundary_le_antidiag p hp hx

private lemma DxuCandidate_QuarterPlane3Open_le_antidiag
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hy_pos : 0 < y) (hneg_x : -y < x) (hxy : x < y) :
    DxuCandidate p x y ≤ DxuCandidate p (-y) y := by
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hneg_x, le_of_lt hxy⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hnotQx : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hxy hq.2.1
  have hnotQ2x : ¬ QuarterPlane2 x y := by
    intro hq
    have hlt : -x < y := by linarith
    exact not_le_of_gt hlt hq.2.1
  have hnotQa : ¬ QuarterPlane (-y) y := by
    intro hq
    exact not_le_of_gt (by linarith : -y < 0) hq.1
  have hstart : DxuCandidate p x y = DyauxFunction1 p y x := by
    simp [DxuCandidate, hnotQx, hnotQ2x, hQx]
  have hbreak : DxuCandidate p (-y) y = DyauxFunction1 p y (-y) := by
    have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp y hy_pos.le
    simp [DxuCandidate, hnotQa, hQa, hrel]
  rw [hstart, hbreak]
  exact DyauxFunction1_QuarterPlaneOpen_le_antidiag p hp hy_pos hneg_x hxy

private lemma uCandidate_tangent_x_cross_QuarterPlane3Open_to_QuarterPlane2Open
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hneg_x : -y < x) (hxy : x < y)
    (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have h_x_a := uCandidate_tangent_x_QuarterPlane3Open_to_antidiag_segment
    p hp hy_pos hneg_x hxy
  have h_a_z := uCandidate_tangent_x_antidiag_to_QuarterPlane2Open_segment
    p hp hy_pos hz_left
  have hd := DxuCandidate_QuarterPlane3Open_le_antidiag
    p hp hy_pos hneg_x hxy
  exact tangent_glue_two_backward
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    hz_left.le hneg_x.le h_x_a h_a_z hd

private lemma uCandidate_tangent_x_antidiag_to_diag_segment
    (p : ℝ) (hp : 2 < p) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p y y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (y - (-y)) := by
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hQd : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hnotQa : ¬ QuarterPlane (-y) y := by
    intro hq
    exact not_le_of_gt (by linarith : -y < 0) hq.1
  have haux := auxFunction1_tangent_y_antidiag_to_QuarterPlaneOpen_segment
    p hp hy_pos (by linarith : -y < y) le_rfl
  have hdx : DxuCandidate p (-y) y = DyauxFunction1 p y (-y) := by
    have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp y hy_pos.le
    simp [DxuCandidate, hnotQa, hQa, hrel]
  calc
    uCandidate p y y = auxFunction1 p y y := by
      simp [uCandidate, hQd]
    _ ≤ auxFunction1 p y (-y) + DyauxFunction1 p y (-y) * (y - (-y)) := haux
    _ = uCandidate p (-y) y + DxuCandidate p (-y) y * (y - (-y)) := by
      simp [uCandidate, hnotQa, hQa, hdx]

private lemma DxuCandidate_diag_le_antidiag_pos
    (p : ℝ) (hp : 2 < p) {y : ℝ} (hy_pos : 0 < y) :
    DxuCandidate p y y ≤ DxuCandidate p (-y) y := by
  have hp' : 2 ≤ p := by linarith
  let c : ℝ := (a p) * y
  have hc_lt_y : c < y := by
    have hlt : a p < 1 := a_lt_one_of_two_le p hp'
    simpa [c] using mul_lt_mul_of_pos_right hlt hy_pos
  have hdiag : closureA1 p y y := ⟨hy_pos.le, le_of_lt hc_lt_y, le_rfl⟩
  have hcl_c_A1 : closureA1 p y c := ⟨hy_pos.le, le_rfl, le_of_lt hc_lt_y⟩
  have hQd : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hnotQa : ¬ QuarterPlane (-y) y := by
    intro hq
    exact not_le_of_gt (by linarith : -y < 0) hq.1
  have hdiag_eq : DxuCandidate p y y = DyauxFunction1 p y y := by
    have h := DxauxFunction1_eq_DyauxFunction1_on_diag p hp y hy_pos.le
    simp [DxuCandidate, hQd, h]
  have hant_eq : DxuCandidate p (-y) y = DyauxFunction1 p y (-y) := by
    have h := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp y hy_pos.le
    simp [DxuCandidate, hnotQa, hQa, h]
  have hdiag_c : DyauxFunction1 p y y = DyauxFunction1 p y c := by
    rw [auxFunction1_Dy_eq_DyuA1 p y y hdiag,
      auxFunction1_Dy_eq_DyuA1 p y c hcl_c_A1]
    simp [DyuA1]
  calc
    DxuCandidate p y y = DyauxFunction1 p y y := hdiag_eq
    _ = DyauxFunction1 p y c := hdiag_c
    _ ≤ DyauxFunction1 p y (-y) := by
      simpa [c] using DyauxFunction1_internal_boundary_le_antidiag p hp hy_pos
    _ = DxuCandidate p (-y) y := hant_eq.symm

/--
Horizontal tangent estimate from the diagonal down to the antidiagonal.

This is the endpoint case of the first-quadrant vertical estimate after the
Q3 reflection.  The auxiliary private lemma allows the closed endpoint `z = -y`.
-/
private lemma uCandidate_tangent_x_diag_to_antidiag_segment
    (p : ℝ) (hp : 2 < p) {y : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (-y) y ≤
      uCandidate p y y + DxuCandidate p y y * ((-y) - y) := by
  have hQd : QuarterPlane y y := ⟨hy_pos.le, le_rfl, by linarith⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hnotQa : ¬ QuarterPlane (-y) y := by
    intro hq
    exact not_le_of_gt (by linarith : -y < 0) hq.1
  have haux := auxFunction1_tangent_y_diag_to_QuarterPlaneOpen_segment
    p hp hy_pos le_rfl (by linarith : -y < y)
  have hdx : DxuCandidate p y y = DyauxFunction1 p y y := by
    have h := DxauxFunction1_eq_DyauxFunction1_on_diag p hp y hy_pos.le
    simp [DxuCandidate, hQd, h]
  calc
    uCandidate p (-y) y = auxFunction1 p y (-y) := by
      simp [uCandidate, hnotQa, hQa]
    _ ≤ auxFunction1 p y y + DyauxFunction1 p y y * ((-y) - y) := haux
    _ = uCandidate p y y + DxuCandidate p y y * ((-y) - y) := by
      simp [uCandidate, hQd, hdx]

/--
Derivative comparison from Q1 all the way to the antidiagonal.

It is just the already proved Q1-to-diagonal comparison followed by the
diagonal-to-antidiagonal comparison.
-/
private lemma DxuCandidate_QuarterPlaneOpen_le_antidiag
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hy_pos : 0 < y) (hyx : y < x) :
    DxuCandidate p x y ≤ DxuCandidate p (-y) y := by
  have hxd := DxuCandidate_QuarterPlaneOpen_le_diag p hp hy_pos hyx
  have hda := DxuCandidate_diag_le_antidiag_pos p hp hy_pos
  linarith

/--
Horizontal tangent estimate from Q1 down to the antidiagonal.

The path is glued at the diagonal.  This is one of the closed endpoint pieces
needed for the backward horizontal dispatcher.
-/
private lemma uCandidate_tangent_x_cross_QuarterPlaneOpen_to_antidiag
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hy_pos : 0 < y) (hyx : y < x) :
    uCandidate p (-y) y ≤
      uCandidate p x y + DxuCandidate p x y * ((-y) - x) := by
  have h_x_d := uCandidate_tangent_x_QuarterPlaneOpen_to_diag_segment
    p hp hy_pos hyx
  have h_d_a := uCandidate_tangent_x_diag_to_antidiag_segment
    p hp hy_pos
  have hd := DxuCandidate_QuarterPlaneOpen_le_diag p hp hy_pos hyx
  exact tangent_glue_two_backward
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by linarith : -y ≤ y) hyx.le h_x_d h_d_a hd

/--
Horizontal tangent estimate from the diagonal into Q2.

This glues the closed diagonal-to-antidiagonal piece with the Q2 reflected
first-quadrant estimate.
-/
private lemma uCandidate_tangent_x_diag_to_QuarterPlane2Open_segment
    (p : ℝ) (hp : 2 < p) {z y : ℝ}
    (hy_pos : 0 < y) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p y y + DxuCandidate p y y * (z - y) := by
  have h_d_a := uCandidate_tangent_x_diag_to_antidiag_segment
    p hp hy_pos
  have h_a_z := uCandidate_tangent_x_antidiag_to_QuarterPlane2Open_segment
    p hp hy_pos hz_left
  have hd := DxuCandidate_diag_le_antidiag_pos p hp hy_pos
  exact tangent_glue_two_backward
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    hz_left.le (by linarith : -y ≤ y) h_d_a h_a_z hd

/--
Horizontal tangent estimate from Q1 into Q2.

The full segment crosses both special lines, so we glue at the diagonal and
the antidiagonal.  The derivative comparisons are always made against the
starting point in Q1, as required by `tangent_glue_three_backward`.
-/
private lemma uCandidate_tangent_x_cross_QuarterPlaneOpen_to_QuarterPlane2Open
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hyx : y < x) (hz_left : z < -y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have h_x_d := uCandidate_tangent_x_QuarterPlaneOpen_to_diag_segment
    p hp hy_pos hyx
  have h_d_a := uCandidate_tangent_x_diag_to_antidiag_segment
    p hp hy_pos
  have h_a_z := uCandidate_tangent_x_antidiag_to_QuarterPlane2Open_segment
    p hp hy_pos hz_left
  have hd_xd := DxuCandidate_QuarterPlaneOpen_le_diag p hp hy_pos hyx
  have hd_xa := DxuCandidate_QuarterPlaneOpen_le_antidiag p hp hy_pos hyx
  exact tangent_glue_three_backward
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    hz_left.le (by linarith : -y ≤ y) hyx.le
    h_x_d h_d_a h_a_z hd_xd hd_xa

private lemma DxuCandidate_antidiag_le_QuarterPlane2Open
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    DxuCandidate p (-y) y ≤ DxuCandidate p x y := by
  have hx_neg : x < 0 := by linarith
  have hQx : QuarterPlane2 x y :=
    ⟨le_of_lt hx_neg, le_of_lt (by linarith : y < -x), le_of_lt (by linarith : x < y)⟩
  have hQa : QuarterPlane2 (-y) y := ⟨by linarith, by linarith, by linarith⟩
  have hnotQx : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hx_neg hq.1
  have hnotQa : ¬ QuarterPlane (-y) y := by
    intro hq
    exact not_le_of_gt (by linarith : -y < 0) hq.1
  have hle :
      DxauxFunction1 p (-x) (-y) ≤ DxauxFunction1 p y (-y) := by
    simpa using DxauxFunction1_QuarterPlaneOpen_le_antidiag
      p (by linarith : 2 ≤ p)
      (by linarith : 0 < -x)
      (by linarith : -y < 0)
      (by linarith : -(-x) < -y)
  have hstart : DxuCandidate p x y = -DxauxFunction1 p (-x) (-y) := by
    simp [DxuCandidate, hnotQx, hQx]
  have hbreak : DxuCandidate p (-y) y = -DxauxFunction1 p y (-y) := by
    simp [DxuCandidate, hnotQa, hQa]
  rw [hstart, hbreak]
  linarith

private lemma uCandidate_tangent_x_cross_QuarterPlane2Open_to_QuarterPlane3Open
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y)
    (hz_lower : -y < z) (hz_upper : z < y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have h_x_a := uCandidate_tangent_x_QuarterPlane2Open_to_antidiag_segment
    p hp hy_pos hx_left
  have h_a_z := uCandidate_tangent_x_antidiag_to_QuarterPlane3Open_segment
    p hp hy_pos hz_lower hz_upper
  have hd := DxuCandidate_antidiag_le_QuarterPlane2Open
    p hp hy_pos hx_left
  exact tangent_glue_two_forward
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    hx_left.le hz_lower.le h_x_a h_a_z hd

private lemma uCandidate_tangent_x_cross_QuarterPlane2Open_to_diag
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) :
    uCandidate p y y ≤
      uCandidate p x y + DxuCandidate p x y * (y - x) := by
  have h_x_a := uCandidate_tangent_x_QuarterPlane2Open_to_antidiag_segment
    p hp hy_pos hx_left
  have h_a_d := uCandidate_tangent_x_antidiag_to_diag_segment
    p hp hy_pos
  have hd := DxuCandidate_antidiag_le_QuarterPlane2Open
    p hp hy_pos hx_left
  exact tangent_glue_two_forward
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    hx_left.le (by linarith : -y ≤ y) h_x_a h_a_d hd

private lemma uCandidate_tangent_x_antidiag_to_QuarterPlaneOpen_segment
    (p : ℝ) (hp : 2 < p) {z y : ℝ}
    (hy_pos : 0 < y) (hyz : y < z) :
    uCandidate p z y ≤
      uCandidate p (-y) y + DxuCandidate p (-y) y * (z - (-y)) := by
  have h_a_d := uCandidate_tangent_x_antidiag_to_diag_segment
    p hp hy_pos
  have h_d_z := uCandidate_tangent_x_diag_to_QuarterPlaneOpen_segment
    p hp hy_pos hyz
  have hd := DxuCandidate_diag_le_antidiag_pos p hp hy_pos
  exact tangent_glue_two_forward
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    (by linarith : -y ≤ y) hyz.le h_a_d h_d_z hd

private lemma uCandidate_tangent_x_cross_QuarterPlane2Open_to_QuarterPlaneOpen
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_left : x < -y) (hyz : y < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have h_x_a := uCandidate_tangent_x_QuarterPlane2Open_to_antidiag_segment
    p hp hy_pos hx_left
  have h_a_d := uCandidate_tangent_x_antidiag_to_diag_segment
    p hp hy_pos
  have h_d_z := uCandidate_tangent_x_diag_to_QuarterPlaneOpen_segment
    p hp hy_pos hyz
  have hd_a_x := DxuCandidate_antidiag_le_QuarterPlane2Open
    p hp hy_pos hx_left
  have hd_d_x : DxuCandidate p y y ≤ DxuCandidate p x y := by
    have hda := DxuCandidate_diag_le_antidiag_pos p hp hy_pos
    linarith
  exact tangent_glue_three_forward
    (fun t => uCandidate p t y) (fun t => DxuCandidate p t y)
    hx_left.le (by linarith : -y ≤ y) hyz.le
    h_x_a h_a_d h_d_z hd_a_x hd_d_x

private lemma uCandidate_tangent_x_forward_of_y_pos
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hxz : x < z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  by_cases hx_left : x < -y
  · by_cases hz_left : z < -y
    · exact uCandidate_tangent_x_on_QuarterPlane2Open_segment p hp
        (by linarith : x < 0)
        (by linarith : y < -x)
        (by linarith : x < y)
        (by linarith : z < 0)
        (by linarith : y < -z)
        (by linarith : z < y)
    · have hza_le : -y ≤ z := le_of_not_gt hz_left
      by_cases hza_eq : z = -y
      · subst z
        exact uCandidate_tangent_x_QuarterPlane2Open_to_antidiag_segment
          p hp hy_pos hx_left
      · have hza : -y < z := lt_of_le_of_ne hza_le (by
          intro h
          exact hza_eq h.symm)
        by_cases hz_mid : z < y
        · exact uCandidate_tangent_x_cross_QuarterPlane2Open_to_QuarterPlane3Open
            p hp hy_pos hx_left hza hz_mid
        · have hyz_le : y ≤ z := le_of_not_gt hz_mid
          by_cases hzy_eq : z = y
          · subst z
            exact uCandidate_tangent_x_cross_QuarterPlane2Open_to_diag
              p hp hy_pos hx_left
          · have hyz : y < z := lt_of_le_of_ne hyz_le (by
              intro h
              exact hzy_eq h.symm)
            exact uCandidate_tangent_x_cross_QuarterPlane2Open_to_QuarterPlaneOpen
              p hp hy_pos hx_left hyz
  · have hxa_le : -y ≤ x := le_of_not_gt hx_left
    by_cases hxa_eq : x = -y
    · subst x
      by_cases hz_mid : z < y
      · exact uCandidate_tangent_x_antidiag_to_QuarterPlane3Open_segment
          p hp hy_pos hxz hz_mid
      · have hyz_le : y ≤ z := le_of_not_gt hz_mid
        by_cases hzy_eq : z = y
        · subst z
          exact uCandidate_tangent_x_antidiag_to_diag_segment p hp hy_pos
        · have hyz : y < z := lt_of_le_of_ne hyz_le (by
            intro h
            exact hzy_eq h.symm)
          exact uCandidate_tangent_x_antidiag_to_QuarterPlaneOpen_segment
            p hp hy_pos hyz
    · have hxa : -y < x := lt_of_le_of_ne hxa_le (by
        intro h
        exact hxa_eq h.symm)
      by_cases hx_mid : x < y
      · by_cases hz_mid : z < y
        · exact uCandidate_tangent_x_on_QuarterPlane3Open_segment p hp
            hy_pos hxa hx_mid
            (lt_trans hxa hxz) hz_mid
        · have hyz_le : y ≤ z := le_of_not_gt hz_mid
          by_cases hzy_eq : z = y
          · subst z
            exact uCandidate_tangent_x_QuarterPlane3Open_to_diag_segment
              p hp hy_pos hxa hx_mid
          · have hyz : y < z := lt_of_le_of_ne hyz_le (by
              intro h
              exact hzy_eq h.symm)
            exact uCandidate_tangent_x_cross_QuarterPlane3Open_to_QuarterPlaneOpen
              p hp hy_pos hxa hx_mid hyz
      · have hyx_le : y ≤ x := le_of_not_gt hx_mid
        by_cases hxy_eq : x = y
        · subst x
          exact uCandidate_tangent_x_diag_to_QuarterPlaneOpen_segment
            p hp hy_pos hxz
        · have hyx : y < x := lt_of_le_of_ne hyx_le (by
            intro h
            exact hxy_eq h.symm)
          exact uCandidate_tangent_x_on_QuarterPlaneOpen_segment p hp
            (lt_trans hy_pos hyx) hyx (by linarith)
            (lt_trans hy_pos (lt_trans hyx hxz)) (lt_trans hyx hxz) (by linarith)

private lemma uCandidate_tangent_x_forward_of_y_pos_le
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hxz : x ≤ z) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  rcases hxz.lt_or_eq with hxz_lt | rfl
  · exact uCandidate_tangent_x_forward_of_y_pos p hp hy_pos hxz_lt
  · simp

/--
Horizontal tangent dispatcher for targets to the left, with `y > 0`.

The proof follows the geometry of the horizontal segment.  The only possible
breakpoints are the diagonal `x = y` and the antidiagonal `x = -y`; every case
below either stays in one open sector or uses one of the glued estimates above.
-/
private lemma uCandidate_tangent_x_backward_of_y_pos
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hzx : z < x) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  by_cases hx_right : y < x
  · by_cases hz_right : y < z
    · exact uCandidate_tangent_x_on_QuarterPlaneOpen_segment p hp
        (lt_trans hy_pos hx_right) hx_right (by linarith)
        (lt_trans hy_pos hz_right) hz_right (by linarith)
    · have hzy_le : z ≤ y := le_of_not_gt hz_right
      by_cases hzy_eq : z = y
      · subst z
        exact uCandidate_tangent_x_QuarterPlaneOpen_to_diag_segment
          p hp hy_pos hx_right
      · have hzy : z < y := lt_of_le_of_ne hzy_le hzy_eq
        by_cases hz_mid : -y < z
        · exact uCandidate_tangent_x_cross_QuarterPlaneOpen_to_QuarterPlane3Open
            p hp hy_pos hx_right hz_mid hzy
        · have hza_le : z ≤ -y := le_of_not_gt hz_mid
          by_cases hza_eq : z = -y
          · subst z
            exact uCandidate_tangent_x_cross_QuarterPlaneOpen_to_antidiag
              p hp hy_pos hx_right
          · have hz_left : z < -y := lt_of_le_of_ne hza_le hza_eq
            exact uCandidate_tangent_x_cross_QuarterPlaneOpen_to_QuarterPlane2Open
              p hp hy_pos hx_right hz_left
  · have hxy_le : x ≤ y := le_of_not_gt hx_right
    by_cases hxy_eq : x = y
    · subst x
      by_cases hz_mid : -y < z
      · exact uCandidate_tangent_x_diag_to_QuarterPlane3Open_segment
          p hp hy_pos hz_mid hzx
      · have hza_le : z ≤ -y := le_of_not_gt hz_mid
        by_cases hza_eq : z = -y
        · subst z
          exact uCandidate_tangent_x_diag_to_antidiag_segment p hp hy_pos
        · have hz_left : z < -y := lt_of_le_of_ne hza_le hza_eq
          exact uCandidate_tangent_x_diag_to_QuarterPlane2Open_segment
            p hp hy_pos hz_left
    · have hxy : x < y := lt_of_le_of_ne hxy_le hxy_eq
      by_cases hx_mid : -y < x
      · by_cases hz_mid : -y < z
        · exact uCandidate_tangent_x_on_QuarterPlane3Open_segment p hp
            hy_pos hx_mid hxy hz_mid (lt_trans hzx hxy)
        · have hza_le : z ≤ -y := le_of_not_gt hz_mid
          by_cases hza_eq : z = -y
          · subst z
            exact uCandidate_tangent_x_QuarterPlane3Open_to_antidiag_segment
              p hp hy_pos hx_mid hxy
          · have hz_left : z < -y := lt_of_le_of_ne hza_le hza_eq
            exact uCandidate_tangent_x_cross_QuarterPlane3Open_to_QuarterPlane2Open
              p hp hy_pos hx_mid hxy hz_left
      · have hxa_le : x ≤ -y := le_of_not_gt hx_mid
        by_cases hxa_eq : x = -y
        · subst x
          exact uCandidate_tangent_x_antidiag_to_QuarterPlane2Open_segment
            p hp hy_pos hzx
        · have hx_left : x < -y := lt_of_le_of_ne hxa_le hxa_eq
          exact uCandidate_tangent_x_on_QuarterPlane2Open_segment p hp
            (by linarith : x < 0)
            (by linarith : y < -x)
            (by linarith : x < y)
            (by linarith : z < 0)
            (by linarith : y < -z)
            (by linarith : z < y)

/-- Closed-form version of the left-target horizontal dispatcher. -/
private lemma uCandidate_tangent_x_backward_of_y_pos_le
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hzx : z ≤ x) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  rcases hzx.lt_or_eq with hzx_lt | rfl
  · exact uCandidate_tangent_x_backward_of_y_pos p hp hy_pos hzx_lt
  · simp

private lemma uCandidate_tangent_x_nonneg_increment_of_y_pos
    (p : ℝ) (hp : 2 < p) {x y h : ℝ}
    (hy_pos : 0 < y) (hh : 0 ≤ h) :
    uCandidate p (x + h) y ≤
      uCandidate p x y + DxuCandidate p x y * h := by
  have hxz : x ≤ x + h := by linarith
  have hmain := uCandidate_tangent_x_forward_of_y_pos_le
    p hp hy_pos hxz
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmain

/-- Horizontal tangent inequality for nonpositive increments, still with `y > 0`. -/
private lemma uCandidate_tangent_x_nonpos_increment_of_y_pos
    (p : ℝ) (hp : 2 < p) {x y h : ℝ}
    (hy_pos : 0 < y) (hh : h ≤ 0) :
    uCandidate p (x + h) y ≤
      uCandidate p x y + DxuCandidate p x y * h := by
  have hxz : x + h ≤ x := by linarith
  have hmain := uCandidate_tangent_x_backward_of_y_pos_le
    p hp hy_pos hxz
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmain

/--
Horizontal tangent inequality for every increment, with `y > 0`.

This is the one-dimensional form of the desired axis estimate.  The proof only
chooses the correct dispatcher according to the sign of the increment.
-/
private lemma uCandidate_tangent_x_increment_of_y_pos
    (p : ℝ) (hp : 2 < p) {x y h : ℝ}
    (hy_pos : 0 < y) :
    uCandidate p (x + h) y ≤
      uCandidate p x y + DxuCandidate p x y * h := by
  rcases le_total 0 h with hh | hh
  · exact uCandidate_tangent_x_nonneg_increment_of_y_pos
      p hp hy_pos hh
  · exact uCandidate_tangent_x_nonpos_increment_of_y_pos
      p hp hy_pos hh

private lemma uCandidate_axis_tangent_horizontal_nonneg_of_y_pos
    (p : ℝ) (hp : 2 < p) {x y h k : ℝ}
    (hy_pos : 0 < y) (hh : 0 ≤ h) (hk0 : k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  subst k
  have hx := uCandidate_tangent_x_nonneg_increment_of_y_pos
    (p := p) (hp := hp) (x := x) (y := y) (h := h) hy_pos hh
  simpa using hx

/--
The horizontal part of the target tangent inequality for `y > 0`.

When `k = 0`, the `DyuCandidate` term vanishes and the estimate reduces to the
one-dimensional horizontal tangent inequality above.
-/
private lemma uCandidate_axis_tangent_horizontal_of_y_pos
    (p : ℝ) (hp : 2 < p) {x y h k : ℝ}
    (hy_pos : 0 < y) (hk0 : k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  subst k
  have hx := uCandidate_tangent_x_increment_of_y_pos
    (p := p) (hp := hp) (x := x) (y := y) (h := h) hy_pos
  simpa using hx

/--
Central symmetry of the candidate on horizontal lines below the origin.

For `y < 0`, the reflected point `(-x, -y)` lies on the corresponding
horizontal line with positive second coordinate.  The proof only dispatches the
three possible regions cut out by `x = y` and `x = -y`.
-/
private lemma uCandidate_neg_neg_of_y_neg
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

/--
The x-partial changes sign under the same central reflection.

This is the derivative counterpart of `uCandidate_neg_neg_of_y_neg`, used to
transport the positive-`y` horizontal tangent inequality to `y < 0`.
-/
private lemma DxuCandidate_neg_neg_of_y_neg
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

/-- Horizontal tangent inequality for every increment, with `y < 0`. -/
private lemma uCandidate_tangent_x_increment_of_y_neg
    (p : ℝ) (hp : 2 < p) {x y h : ℝ}
    (hy_neg : y < 0) :
    uCandidate p (x + h) y ≤
      uCandidate p x y + DxuCandidate p x y * h := by
  have hpos : 0 < -y := by linarith
  have hmain := uCandidate_tangent_x_increment_of_y_pos
    (p := p) (hp := hp) (x := -x) (y := -y) (h := -h) hpos
  have hstart := uCandidate_neg_neg_of_y_neg (p := p) (x := x) (y := y) hy_neg
  have hend := uCandidate_neg_neg_of_y_neg (p := p) (x := x + h) (y := y) hy_neg
  have hdx := DxuCandidate_neg_neg_of_y_neg (p := p) (x := x) (y := y) hy_neg
  calc
    uCandidate p (x + h) y = uCandidate p (-(x + h)) (-y) := hend
    _ = uCandidate p ((-x) + (-h)) (-y) := by ring
    _ ≤ uCandidate p (-x) (-y) + DxuCandidate p (-x) (-y) * (-h) := hmain
    _ = uCandidate p x y + DxuCandidate p x y * h := by
      rw [← hstart, hdx]
      ring

/--
The horizontal part of the target tangent inequality for `y < 0`.

The proof is the reflected version of the positive-`y` estimate.
-/
private lemma uCandidate_axis_tangent_horizontal_of_y_neg
    (p : ℝ) (hp : 2 < p) {x y h k : ℝ}
    (hy_neg : y < 0) (hk0 : k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  subst k
  have hx := uCandidate_tangent_x_increment_of_y_neg
    (p := p) (hp := hp) (x := x) (y := y) (h := h) hy_neg
  simpa using hx

/--
Horizontal tangent inequality away from the x-axis.

The positive half-plane is proved by sector decomposition; the negative
half-plane is its central reflection.
-/
private lemma uCandidate_axis_tangent_horizontal_of_y_ne_zero
    (p : ℝ) (hp : 2 < p) {x y h k : ℝ}
    (hy_ne : y ≠ 0) (hk0 : k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  rcases lt_or_gt_of_ne hy_ne with hy_neg | hy_pos
  · exact uCandidate_axis_tangent_horizontal_of_y_neg p hp hy_neg hk0
  · exact uCandidate_axis_tangent_horizontal_of_y_pos p hp hy_pos hk0

/--
Horizontal tangent inequality on the x-axis.

Instead of redoing the collapsed sector geometry at `y = 0`, we approach the
axis from the upper half-plane.  The inequality is known for every `yy > 0`,
and the global continuity of `uCandidate` and `DxuCandidate` lets us pass to
the one-sided limit `yy → 0+`.
-/
private lemma uCandidate_tangent_x_increment_of_y_zero
    (p : ℝ) (hp : 2 < p) {x h : ℝ} :
    uCandidate p (x + h) 0 ≤
      uCandidate p x 0 + DxuCandidate p x 0 * h := by
  have hp' : 2 ≤ p := by linarith
  have hcontU : Continuous (fun z : ℝ × ℝ => uCandidate p z.1 z.2) :=
    continuousOn_univ.mp (continuousuCandidate p hp')
  have hcontDx : Continuous (fun z : ℝ × ℝ => DxuCandidate p z.1 z.2) :=
    continuousOn_univ.mp (continuousDxuCandidate p hp)
  have htend_lhs :
      Filter.Tendsto (fun yy : ℝ => uCandidate p (x + h) yy)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (uCandidate p (x + h) 0)) := by
    have hline : Continuous (fun yy : ℝ => ((x + h), yy)) := by continuity
    have hcomp : Continuous (fun yy : ℝ => uCandidate p (x + h) yy) := by
      simpa [Function.comp_def] using hcontU.comp hline
    exact (hcomp.tendsto 0).mono_left nhdsWithin_le_nhds
  have htend_rhs :
      Filter.Tendsto
        (fun yy : ℝ => uCandidate p x yy + DxuCandidate p x yy * h)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (uCandidate p x 0 + DxuCandidate p x 0 * h)) := by
    have hline : Continuous (fun yy : ℝ => (x, yy)) := by continuity
    have hUx : Continuous (fun yy : ℝ => uCandidate p x yy) := by
      simpa [Function.comp_def] using hcontU.comp hline
    have hDxx : Continuous (fun yy : ℝ => DxuCandidate p x yy) := by
      simpa [Function.comp_def] using hcontDx.comp hline
    have htotal :
        Continuous (fun yy : ℝ => uCandidate p x yy + DxuCandidate p x yy * h) :=
      hUx.add (hDxx.mul continuous_const)
    exact (htotal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hineq :
      (fun yy : ℝ => uCandidate p (x + h) yy) ≤ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        fun yy : ℝ => uCandidate p x yy + DxuCandidate p x yy * h := by
    exact eventually_nhdsWithin_of_forall fun yy hyy =>
      uCandidate_tangent_x_increment_of_y_pos
        (p := p) (hp := hp) (x := x) (y := yy) (h := h) hyy
  exact le_of_tendsto_of_tendsto htend_lhs htend_rhs hineq

/-- The horizontal part of the target tangent inequality on the x-axis. -/
private lemma uCandidate_axis_tangent_horizontal_of_y_zero
    (p : ℝ) (hp : 2 < p) {x y h k : ℝ}
    (hy0 : y = 0) (hk0 : k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  subst y
  subst k
  have hx := uCandidate_tangent_x_increment_of_y_zero
    (p := p) (hp := hp) (x := x) (h := h)
  simpa using hx

/--
Horizontal tangent inequality for every horizontal line.

This is the complete `k = 0` case of the displayed inequality for `p > 2`.
-/
private lemma uCandidate_axis_tangent_horizontal
    (p : ℝ) (hp : 2 < p) {x y h k : ℝ}
    (hk0 : k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  rcases lt_trichotomy y 0 with hy_neg | hy0 | hy_pos
  · exact uCandidate_axis_tangent_horizontal_of_y_neg p hp hy_neg hk0
  · exact uCandidate_axis_tangent_horizontal_of_y_zero p hp hy0 hk0
  · exact uCandidate_axis_tangent_horizontal_of_y_pos p hp hy_pos hk0

/-! ### Swap symmetry for the vertical axis case -/

/--
Formula selected by `uCandidate` on Q1.

Q1 is the first branch in the definition, so no boundary correction is needed.
-/
private lemma uCandidate_eq_Q1
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane x y) :
    uCandidate p x y = auxFunction1 p x y := by
  simp [uCandidate, hQ]

/--
Formula selected by `uCandidate` on Q2.

If Q1 also holds, the point is the origin and the two formulas agree.
-/
private lemma uCandidate_eq_Q2
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

/--
Formula selected by `uCandidate` on Q3.

On overlaps with earlier branches the diagonal or antidiagonal compatibility
private lemmas make the displayed formula agree with the branch chosen by the `if`.
-/
private lemma uCandidate_eq_Q3
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane3 x y) :
    uCandidate p x y = auxFunction1 p y x := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := uCandidate_eq_Q1 p (hQ := hQ1)
    obtain ⟨_, hyx, _⟩ := hQ1
    obtain ⟨_, _, hxy⟩ := hQ
    have hxy' : x = y := le_antisymm hxy hyx
    calc
      uCandidate p x y = auxFunction1 p x y := hbranch
      _ = auxFunction1 p y x := by rw [hxy']
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := uCandidate_eq_Q2 p (hQ := hQ2)
      obtain ⟨_, hynegx, _⟩ := hQ2
      obtain ⟨_, hnegyx, _⟩ := hQ
      have hx : x = -y := le_antisymm (by linarith [hynegx]) hnegyx
      calc
        uCandidate p x y = auxFunction1 p (-x) (-y) := hbranch
        _ = auxFunction1 p y x := by rw [hx]; simp
    · simp [uCandidate, hQ1, hQ2, hQ]

/--
Formula selected by `uCandidate` on Q4.

This is the last branch, with boundary corrections for all earlier overlaps.
-/
private lemma uCandidate_eq_Q4
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane4 x y) :
    uCandidate p x y = auxFunction1 p (-y) (-x) := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := uCandidate_eq_Q1 p (hQ := hQ1)
    obtain ⟨_, _, hnegxy⟩ := hQ1
    obtain ⟨_, _, hxnegy⟩ := hQ
    have hy : y = -x := by linarith
    calc
      uCandidate p x y = auxFunction1 p x y := hbranch
      _ = auxFunction1 p (-y) (-x) := by rw [hy]; simp
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := uCandidate_eq_Q2 p (hQ := hQ2)
      obtain ⟨_, _, hxy⟩ := hQ2
      obtain ⟨_, hyx, _⟩ := hQ
      have hxy' : x = y := le_antisymm hxy hyx
      calc
        uCandidate p x y = auxFunction1 p (-x) (-y) := hbranch
        _ = auxFunction1 p (-y) (-x) := by rw [hxy']
    · by_cases hQ3 : QuarterPlane3 x y
      · have hbranch := uCandidate_eq_Q3 p (hQ := hQ3)
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

/--
The sector decomposition covers the plane.

This is a reusable version of the cover argument used by the continuity proofs.
-/
private lemma mem_some_QuarterPlane (x y : ℝ) :
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

/-- `uCandidate` is symmetric under swapping the coordinates. -/
private lemma uCandidate_swap
    (p : ℝ) (x y : ℝ) :
    uCandidate p x y = uCandidate p y x := by
  rcases mem_some_QuarterPlane x y with hQ1 | hrest
  · have hswap : QuarterPlane3 y x := ⟨hQ1.1, hQ1.2.2, hQ1.2.1⟩
    rw [uCandidate_eq_Q1 p hQ1, uCandidate_eq_Q3 p hswap]
  rcases hrest with hQ2 | hrest
  · have hswap : QuarterPlane4 y x := ⟨hQ2.1, hQ2.2.2, hQ2.2.1⟩
    rw [uCandidate_eq_Q2 p hQ2, uCandidate_eq_Q4 p hswap]
  rcases hrest with hQ3 | hQ4
  · have hswap : QuarterPlane y x := ⟨hQ3.1, hQ3.2.2, hQ3.2.1⟩
    rw [uCandidate_eq_Q3 p hQ3, uCandidate_eq_Q1 p hswap]
  · have hswap : QuarterPlane2 y x := ⟨hQ4.1, hQ4.2.2, hQ4.2.1⟩
    rw [uCandidate_eq_Q4 p hQ4, uCandidate_eq_Q2 p hswap]

/-- Formula selected by `DxuCandidate` on Q1. -/
private lemma DxuCandidate_eq_Q1
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane x y) :
    DxuCandidate p x y = DxauxFunction1 p x y := by
  simp [DxuCandidate, hQ]

/-- Formula selected by `DxuCandidate` on Q2, with boundary compatibility. -/
private lemma DxuCandidate_eq_Q2
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

/-- Formula selected by `DxuCandidate` on Q3, with boundary compatibility. -/
private lemma DxuCandidate_eq_Q3
    (p : ℝ) (hp : 2 < p) {x y : ℝ} (hQ : QuarterPlane3 x y) :
    DxuCandidate p x y = DyauxFunction1 p y x := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := DxuCandidate_eq_Q1 p (hQ := hQ1)
    obtain ⟨_, hyx, _⟩ := hQ1
    obtain ⟨hy0, _, hxy⟩ := hQ
    have hxy' : x = y := le_antisymm hxy hyx
    subst x
    calc
      DxuCandidate p y y = DxauxFunction1 p y y := hbranch
      _ = DyauxFunction1 p y y := DxauxFunction1_eq_DyauxFunction1_on_diag p hp y hy0
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := DxuCandidate_eq_Q2 p (hQ := hQ2)
      obtain ⟨_, hynegx, _⟩ := hQ2
      obtain ⟨hy0, hnegyx, _⟩ := hQ
      have hx : x = -y := le_antisymm (by linarith [hynegx]) hnegyx
      subst x
      have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp y hy0
      have h' : -DxauxFunction1 p y (-y) = DyauxFunction1 p y (-y) := by
        linarith
      calc
        DxuCandidate p (-y) y = -DxauxFunction1 p (-(-y)) (-y) := hbranch
        _ = -DxauxFunction1 p y (-y) := by simp
        _ = DyauxFunction1 p y (-y) := h'
    · simp [DxuCandidate, hQ1, hQ2, hQ]

/-- Formula selected by `DxuCandidate` on Q4, with boundary compatibility. -/
private lemma DxuCandidate_eq_Q4
    (p : ℝ) (hp : 2 < p) {x y : ℝ} (hQ : QuarterPlane4 x y) :
    DxuCandidate p x y = -DyauxFunction1 p (-y) (-x) := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := DxuCandidate_eq_Q1 p (hQ := hQ1)
    obtain ⟨hx0, _, hnegxy⟩ := hQ1
    obtain ⟨_, _, hxnegy⟩ := hQ
    have hy : y = -x := by linarith
    subst y
    calc
      DxuCandidate p x (-x) = DxauxFunction1 p x (-x) := hbranch
      _ = -DyauxFunction1 p x (-x) :=
        DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp x hx0
      _ = -DyauxFunction1 p (-(-x)) (-x) := by simp
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := DxuCandidate_eq_Q2 p (hQ := hQ2)
      obtain ⟨hx0, _, hxy⟩ := hQ2
      obtain ⟨_, hyx, _⟩ := hQ
      have hxy' : x = y := le_antisymm hxy hyx
      subst x
      have hnonneg : 0 ≤ -y := by linarith
      have hdiag := DxauxFunction1_eq_DyauxFunction1_on_diag p hp (-y) hnonneg
      calc
        DxuCandidate p y y = -DxauxFunction1 p (-y) (-y) := hbranch
        _ = -DyauxFunction1 p (-y) (-y) := by rw [hdiag]
    · by_cases hQ3 : QuarterPlane3 x y
      · have hbranch := DxuCandidate_eq_Q3 p hp (hQ := hQ3)
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

/-- Formula selected by `DyuCandidate` on Q1. -/
private lemma DyuCandidate_eq_Q1
    (p : ℝ) {x y : ℝ} (hQ : QuarterPlane x y) :
    DyuCandidate p x y = DyauxFunction1 p x y := by
  simp [DyuCandidate, hQ]

/-- Formula selected by `DyuCandidate` on Q2, with boundary compatibility. -/
private lemma DyuCandidate_eq_Q2
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

/-- Formula selected by `DyuCandidate` on Q3, with boundary compatibility. -/
private lemma DyuCandidate_eq_Q3
    (p : ℝ) (hp : 2 < p) {x y : ℝ} (hQ : QuarterPlane3 x y) :
    DyuCandidate p x y = DxauxFunction1 p y x := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := DyuCandidate_eq_Q1 p (hQ := hQ1)
    obtain ⟨_, hyx, _⟩ := hQ1
    obtain ⟨hy0, _, hxy⟩ := hQ
    have hxy' : x = y := le_antisymm hxy hyx
    subst x
    calc
      DyuCandidate p y y = DyauxFunction1 p y y := hbranch
      _ = DxauxFunction1 p y y := (DxauxFunction1_eq_DyauxFunction1_on_diag p hp y hy0).symm
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := DyuCandidate_eq_Q2 p (hQ := hQ2)
      obtain ⟨_, hynegx, _⟩ := hQ2
      obtain ⟨hy0, hnegyx, _⟩ := hQ
      have hx : x = -y := le_antisymm (by linarith [hynegx]) hnegyx
      subst x
      have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp y hy0
      calc
        DyuCandidate p (-y) y = -DyauxFunction1 p (-(-y)) (-y) := hbranch
        _ = -DyauxFunction1 p y (-y) := by simp
        _ = DxauxFunction1 p y (-y) := hrel.symm
    · simp [DyuCandidate, hQ1, hQ2, hQ]

/-- Formula selected by `DyuCandidate` on Q4, with boundary compatibility. -/
private lemma DyuCandidate_eq_Q4
    (p : ℝ) (hp : 2 < p) {x y : ℝ} (hQ : QuarterPlane4 x y) :
    DyuCandidate p x y = -DxauxFunction1 p (-y) (-x) := by
  by_cases hQ1 : QuarterPlane x y
  · have hbranch := DyuCandidate_eq_Q1 p (hQ := hQ1)
    obtain ⟨hx0, _, hnegxy⟩ := hQ1
    obtain ⟨_, _, hxnegy⟩ := hQ
    have hy : y = -x := by linarith
    subst y
    have hrel := DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp x hx0
    have h' : DyauxFunction1 p x (-x) = -DxauxFunction1 p x (-x) := by
      linarith
    calc
      DyuCandidate p x (-x) = DyauxFunction1 p x (-x) := hbranch
      _ = -DxauxFunction1 p x (-x) := h'
      _ = -DxauxFunction1 p (-(-x)) (-x) := by simp
  · by_cases hQ2 : QuarterPlane2 x y
    · have hbranch := DyuCandidate_eq_Q2 p (hQ := hQ2)
      obtain ⟨hx0, _, hxy⟩ := hQ2
      obtain ⟨_, hyx, _⟩ := hQ
      have hxy' : x = y := le_antisymm hxy hyx
      subst x
      have hnonneg : 0 ≤ -y := by linarith
      have hdiag := DxauxFunction1_eq_DyauxFunction1_on_diag p hp (-y) hnonneg
      calc
        DyuCandidate p y y = -DyauxFunction1 p (-y) (-y) := hbranch
        _ = -DxauxFunction1 p (-y) (-y) := by rw [hdiag]
    · by_cases hQ3 : QuarterPlane3 x y
      · have hbranch := DyuCandidate_eq_Q3 p hp (hQ := hQ3)
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

/-- The first partials are exchanged by coordinate swap. -/
private lemma DyuCandidate_eq_DxuCandidate_swap
    (p : ℝ) (hp : 2 < p) (x y : ℝ) :
    DyuCandidate p x y = DxuCandidate p y x := by
  rcases mem_some_QuarterPlane x y with hQ1 | hrest
  · have hswap : QuarterPlane3 y x := ⟨hQ1.1, hQ1.2.2, hQ1.2.1⟩
    rw [DyuCandidate_eq_Q1 p hQ1, DxuCandidate_eq_Q3 p hp hswap]
  rcases hrest with hQ2 | hrest
  · have hswap : QuarterPlane4 y x := ⟨hQ2.1, hQ2.2.2, hQ2.2.1⟩
    rw [DyuCandidate_eq_Q2 p hQ2, DxuCandidate_eq_Q4 p hp hswap]
  rcases hrest with hQ3 | hQ4
  · have hswap : QuarterPlane y x := ⟨hQ3.1, hQ3.2.2, hQ3.2.1⟩
    rw [DyuCandidate_eq_Q3 p hp hQ3, DxuCandidate_eq_Q1 p hswap]
  · have hswap : QuarterPlane2 y x := ⟨hQ4.1, hQ4.2.2, hQ4.2.1⟩
    rw [DyuCandidate_eq_Q4 p hp hQ4, DxuCandidate_eq_Q2 p hswap]

/-! ## Polynomial growth of the candidate -/

private def uA1GrowthConst (p : ℝ) : ℝ :=
  |alpha p| * (1 + |pStar p| * (1 + max 1 |a p|) / 2)

private def vGeTwoGrowthConst (p : ℝ) : ℝ :=
  1 + |Real.rpow (p - 1) p|

private def auxGrowthConst (p : ℝ) : ℝ :=
  max (uA1GrowthConst p) (vGeTwoGrowthConst p)

private def uCandidateGrowthConst (p : ℝ) : ℝ :=
  max 0 (auxGrowthConst p)

private lemma uA1GrowthConst_nonneg (p : ℝ) :
    0 ≤ uA1GrowthConst p := by
  unfold uA1GrowthConst
  positivity

private lemma vGeTwoGrowthConst_nonneg (p : ℝ) :
    0 ≤ vGeTwoGrowthConst p := by
  unfold vGeTwoGrowthConst
  positivity

private lemma auxGrowthConst_nonneg (p : ℝ) :
    0 ≤ auxGrowthConst p := by
  unfold auxGrowthConst
  exact le_trans (uA1GrowthConst_nonneg p) (le_max_left _ _)

private lemma uCandidateGrowthConst_nonneg (p : ℝ) :
    0 ≤ uCandidateGrowthConst p := by
  unfold uCandidateGrowthConst
  exact le_max_left _ _

private lemma closureA2_abs_y_le_x
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ} (h : closureA2 p x y) :
    |y| ≤ x := by
  rcases h with ⟨hx, hlow, hup⟩
  have ha_le_one : a p ≤ 1 := (a_lt_one_of_two_le p hp).le
  have hy_upper : y ≤ x := by
    calc
      y ≤ a p * x := hup
      _ ≤ 1 * x := mul_le_mul_of_nonneg_right ha_le_one hx
      _ = x := one_mul x
  exact abs_le.mpr ⟨hlow, hy_upper⟩

private lemma abs_uA1_le_growth
    (p : ℝ) (_hp : 2 ≤ p) {x y : ℝ} (h : closureA1 p x y) :
    |uA1 p x y| ≤ uA1GrowthConst p * Real.rpow x p := by
  rcases h with ⟨hx, hlow, hup⟩
  by_cases hxpos : 0 < x
  · have hyabs : |y| ≤ (max 1 |a p|) * x :=
      abs_y_le_const_mul_x p x y ⟨hx, hlow, hup⟩
    have hx_abs : |x| = x := abs_of_nonneg hx
    have hxmy :
        |x - y| ≤ (1 + max 1 |a p|) * x := by
      have htmp : |x - y| ≤ |x| + |y| := by
        simpa [sub_eq_add_neg] using abs_add_le x (-y)
      calc
        |x - y| ≤ |x| + |y| := htmp
        _ = x + |y| := by rw [hx_abs]
        _ ≤ x + max 1 |a p| * x := by
          gcongr
        _ = (1 + max 1 |a p|) * x := by ring
    have hlin :
        |x - pStar p * (x - y) / 2|
          ≤ (1 + |pStar p| * (1 + max 1 |a p|) / 2) * x := by
      have htmp :
          |x - pStar p * (x - y) / 2|
            ≤ |x| + |pStar p * (x - y) / 2| := by
        simpa [sub_eq_add_neg] using abs_add_le x (-(pStar p * (x - y) / 2))
      have hdiv :
          |pStar p * (x - y) / 2| = |pStar p| * |x - y| / 2 := by
        rw [abs_div, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      rw [hx_abs, hdiv] at htmp
      calc
        |x - pStar p * (x - y) / 2|
            ≤ x + |pStar p| * |x - y| / 2 := htmp
        _ ≤ x + |pStar p| * ((1 + max 1 |a p|) * x) / 2 := by
          gcongr
        _ = (1 + |pStar p| * (1 + max 1 |a p|) / 2) * x := by ring
    have hpow :
        Real.rpow x (p - 1) * x = Real.rpow x p := by
      have hexp : (p - 1) + 1 = p := by ring
      nth_rewrite 2 [show x = Real.rpow x (1 : ℝ) by simp]
      calc
        Real.rpow x (p - 1) * Real.rpow x (1 : ℝ)
            = Real.rpow x ((p - 1) + 1) := by
                simpa using (Real.rpow_add hxpos (p - 1) 1).symm
        _ = Real.rpow x p := by simp [hexp]
    have hpow_nonneg : 0 ≤ Real.rpow x (p - 1) :=
      Real.rpow_nonneg hx _
    calc
      |uA1 p x y|
          = |alpha p| * Real.rpow x (p - 1) *
              |x - pStar p * (x - y) / 2| := by
            simp only [uA1, hxpos, if_true]
            calc
              |alpha p * Real.rpow x (p - 1) *
                  (x - pStar p * (x - y) / 2)|
                  = |alpha p * Real.rpow x (p - 1)| *
                      |x - pStar p * (x - y) / 2| := by rw [abs_mul]
              _ = |alpha p| * |Real.rpow x (p - 1)| *
                      |x - pStar p * (x - y) / 2| := by rw [abs_mul]
              _ = |alpha p| * Real.rpow x (p - 1) *
                      |x - pStar p * (x - y) / 2| := by
                    rw [abs_of_nonneg hpow_nonneg]
      _ ≤ |alpha p| * Real.rpow x (p - 1) *
            ((1 + |pStar p| * (1 + max 1 |a p|) / 2) * x) := by
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

private lemma abs_vGeTwo_le_growth_on_closureA2
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ} (h : closureA2 p x y) :
    |vGeTwo p x y| ≤ vGeTwoGrowthConst p * Real.rpow x p := by
  rcases h with ⟨hx, hlow, hup⟩
  have hyabs : |y| ≤ x := closureA2_abs_y_le_x p hp ⟨hx, hlow, hup⟩
  have hx_abs : |x| = x := abs_of_nonneg hx
  have hsum : |(x + y) / 2| ≤ x := by
    have htmp : |x + y| ≤ |x| + |y| := abs_add_le x y
    have hdiv := div_le_div_of_nonneg_right htmp (by norm_num : (0 : ℝ) ≤ 2)
    have habs_div : |(x + y) / 2| = |x + y| / 2 := by
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    calc
      |(x + y) / 2| = |x + y| / 2 := habs_div
      _ ≤ (|x| + |y|) / 2 := hdiv
      _ = (x + |y|) / 2 := by rw [hx_abs]
      _ ≤ (x + x) / 2 := by
        gcongr
      _ = x := by ring
  have hdiff : |(x - y) / 2| ≤ x := by
    have htmp : |x - y| ≤ |x| + |y| := by
      simpa [sub_eq_add_neg] using abs_add_le x (-y)
    have hdiv := div_le_div_of_nonneg_right htmp (by norm_num : (0 : ℝ) ≤ 2)
    have habs_div : |(x - y) / 2| = |x - y| / 2 := by
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    calc
      |(x - y) / 2| = |x - y| / 2 := habs_div
      _ ≤ (|x| + |y|) / 2 := hdiv
      _ = (x + |y|) / 2 := by rw [hx_abs]
      _ ≤ (x + x) / 2 := by
        gcongr
      _ = x := by ring
  have hp_nonneg : 0 ≤ p := by linarith
  have hsum_pow :
      Real.rpow |(x + y) / 2| p ≤ Real.rpow x p :=
    Real.rpow_le_rpow (abs_nonneg _) hsum hp_nonneg
  have hdiff_pow :
      Real.rpow |(x - y) / 2| p ≤ Real.rpow x p :=
    Real.rpow_le_rpow (abs_nonneg _) hdiff hp_nonneg
  calc
    |vGeTwo p x y|
        ≤ Real.rpow |(x + y) / 2| p +
            |Real.rpow (p - 1) p| * Real.rpow |(x - y) / 2| p := by
          unfold vGeTwo
          calc
            |Real.rpow |(x + y) / 2| p -
                Real.rpow (p - 1) p * Real.rpow |(x - y) / 2| p|
                ≤ |Real.rpow |(x + y) / 2| p| +
                    |Real.rpow (p - 1) p * Real.rpow |(x - y) / 2| p| := by
                    simpa [sub_eq_add_neg] using
                      abs_add_le (Real.rpow |(x + y) / 2| p)
                        (-(Real.rpow (p - 1) p * Real.rpow |(x - y) / 2| p))
            _ = Real.rpow |(x + y) / 2| p +
                    |Real.rpow (p - 1) p| * Real.rpow |(x - y) / 2| p := by
                    have hA :
                        |Real.rpow |(x + y) / 2| p| =
                          Real.rpow |(x + y) / 2| p :=
                      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
                    have hB :
                        |Real.rpow (p - 1) p * Real.rpow |(x - y) / 2| p| =
                          |Real.rpow (p - 1) p| * Real.rpow |(x - y) / 2| p := by
                      have hD :
                          |Real.rpow |(x - y) / 2| p| =
                            Real.rpow |(x - y) / 2| p :=
                        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
                      rw [abs_mul, hD]
                    rw [hA, hB]
    _ ≤ Real.rpow x p + |Real.rpow (p - 1) p| * Real.rpow x p := by
          gcongr
    _ = vGeTwoGrowthConst p * Real.rpow x p := by
          unfold vGeTwoGrowthConst
          ring

private lemma abs_auxFunction1_le_growth
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ} :
    |auxFunction1 p x y| ≤ auxGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by
  by_cases h1 : closureA1 p x y
  · have hx : 0 ≤ x := h1.1
    have hx_abs : |x| = x := abs_of_nonneg hx
    have hlocal := abs_uA1_le_growth p hp h1
    calc
      |auxFunction1 p x y| = |uA1 p x y| := by rw [auxFunction1_eq_uA1 p x y h1]
      _ ≤ uA1GrowthConst p * Real.rpow x p := hlocal
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
      have hlocal := abs_vGeTwo_le_growth_on_closureA2 p hp h2
      calc
        |auxFunction1 p x y| = |vGeTwo p x y| := by
          rw [auxFunction1_eq_vGeTwo p hp x y h2]
        _ ≤ vGeTwoGrowthConst p * Real.rpow x p := hlocal
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

/--
Polynomial growth of the glued Burkholder candidate in the `p ≥ 2` regime.

The constant is deliberately coarse; its role is to give an integrability
majorant, not a sharp estimate.
-/
private lemma abs_uCandidate_le_growth
    (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) :
    |uCandidate p x y|
      ≤ uCandidateGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by
  have hCaux : auxGrowthConst p ≤ uCandidateGrowthConst p := by
    unfold uCandidateGrowthConst
    exact le_max_right _ _
  have hsum_nonneg : 0 ≤ Real.rpow |x| p + Real.rpow |y| p :=
    add_nonneg (Real.rpow_nonneg (abs_nonneg x) _)
      (Real.rpow_nonneg (abs_nonneg y) _)
  by_cases hQ1 : QuarterPlane x y
  · have haux := abs_auxFunction1_le_growth p hp (x := x) (y := y)
    calc
      |uCandidate p x y| = |auxFunction1 p x y| := by rw [uCandidate_eq_Q1 p hQ1]
      _ ≤ auxGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := haux
      _ ≤ uCandidateGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by
        exact mul_le_mul_of_nonneg_right hCaux hsum_nonneg
  · by_cases hQ2 : QuarterPlane2 x y
    · have haux := abs_auxFunction1_le_growth p hp (x := -x) (y := -y)
      calc
        |uCandidate p x y| = |auxFunction1 p (-x) (-y)| := by rw [uCandidate_eq_Q2 p hQ2]
        _ ≤ auxGrowthConst p * (Real.rpow |(-x)| p + Real.rpow |(-y)| p) := haux
        _ = auxGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by simp
        _ ≤ uCandidateGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by
          exact mul_le_mul_of_nonneg_right hCaux hsum_nonneg
    · by_cases hQ3 : QuarterPlane3 x y
      · have haux := abs_auxFunction1_le_growth p hp (x := y) (y := x)
        calc
          |uCandidate p x y| = |auxFunction1 p y x| := by rw [uCandidate_eq_Q3 p hQ3]
          _ ≤ auxGrowthConst p * (Real.rpow |y| p + Real.rpow |x| p) := haux
          _ = auxGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by ring
          _ ≤ uCandidateGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by
            exact mul_le_mul_of_nonneg_right hCaux hsum_nonneg
      · by_cases hQ4 : QuarterPlane4 x y
        · have haux := abs_auxFunction1_le_growth p hp (x := -y) (y := -x)
          calc
            |uCandidate p x y| = |auxFunction1 p (-y) (-x)| := by rw [uCandidate_eq_Q4 p hQ4]
            _ ≤ auxGrowthConst p * (Real.rpow |(-y)| p + Real.rpow |(-x)| p) := haux
            _ = auxGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by simp [add_comm]
            _ ≤ uCandidateGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by
              exact mul_le_mul_of_nonneg_right hCaux hsum_nonneg
        · have hnonneg :
              0 ≤ uCandidateGrowthConst p * (Real.rpow |x| p + Real.rpow |y| p) := by
            exact mul_nonneg (uCandidateGrowthConst_nonneg p) hsum_nonneg
          simpa [uCandidate, hQ1, hQ2, hQ3, hQ4] using hnonneg

private lemma uCandidate_growth_bound
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      |uCandidate p x y| ≤ C * (Real.rpow |x| p + Real.rpow |y| p) := by
  refine ⟨uCandidateGrowthConst p, uCandidateGrowthConst_nonneg p, ?_⟩
  intro x y
  exact abs_uCandidate_le_growth p hp x y

/-! ## Polynomial growth of the first partials -/

private def DxuA1GrowthConst (p : ℝ) : ℝ :=
  |alpha p| * (|p| / 2) * (|2 - p| + |p - 1| * max 1 |a p|)

private def DyuA1GrowthConst (p : ℝ) : ℝ :=
  |alpha p| * (|pStar p| / 2)

private def DvGeTwoGrowthConst (p : ℝ) : ℝ :=
  |p| / 2 * (1 + |Real.rpow (p - 1) p|)

private def auxDerivativeGrowthConst (p : ℝ) : ℝ :=
  max (max (DxuA1GrowthConst p) (DyuA1GrowthConst p)) (DvGeTwoGrowthConst p)

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

private lemma DvGeTwoGrowthConst_nonneg (p : ℝ) :
    0 ≤ DvGeTwoGrowthConst p := by
  unfold DvGeTwoGrowthConst
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

private lemma DvGeTwoGrowthConst_le_auxDerivativeGrowthConst (p : ℝ) :
    DvGeTwoGrowthConst p ≤ auxDerivativeGrowthConst p := by
  unfold auxDerivativeGrowthConst
  exact le_max_right _ _

private lemma auxDerivativeGrowthConst_le_uCandidateDerivativeGrowthConst (p : ℝ) :
    auxDerivativeGrowthConst p ≤ uCandidateDerivativeGrowthConst p := by
  unfold uCandidateDerivativeGrowthConst
  exact le_max_right _ _

private lemma closureA2_abs_add_div_two_le_x
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ} (h : closureA2 p x y) :
    |(x + y) / 2| ≤ x := by
  rcases h with ⟨hx, hlow, hup⟩
  have hyabs : |y| ≤ x := closureA2_abs_y_le_x p hp ⟨hx, hlow, hup⟩
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
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ} (h : closureA2 p x y) :
    |(x - y) / 2| ≤ x := by
  rcases h with ⟨hx, hlow, hup⟩
  have hyabs : |y| ≤ x := closureA2_abs_y_le_x p hp ⟨hx, hlow, hup⟩
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

private lemma abs_DxuA1_le_growth
    (p : ℝ) {x y : ℝ} (h : closureA1 p x y) :
    |DxuA1 p x y| ≤ DxuA1GrowthConst p * Real.rpow x (p - 1) := by
  simpa [DxuA1GrowthConst] using abs_DxuA1_le p x y h

private lemma abs_DyuA1_le_growth
    (p : ℝ) {x y : ℝ} (h : closureA1 p x y) :
    |DyuA1 p x y| ≤ DyuA1GrowthConst p * Real.rpow x (p - 1) := by
  rcases h with ⟨hx, hlow, hup⟩
  by_cases hxpos : 0 < x
  · have hxpow_nonneg : 0 ≤ Real.rpow x (p - 1) := Real.rpow_nonneg hx _
    calc
      |DyuA1 p x y|
          = |alpha p| * Real.rpow x (p - 1) * (|pStar p| / 2) := by
            simp only [DyuA1, hxpos, if_true]
            calc
              |alpha p * Real.rpow x (p - 1) * (pStar p / 2)|
                  = |alpha p| * |Real.rpow x (p - 1)| * |pStar p / 2| := by
                    rw [abs_mul, abs_mul]
              _ = |alpha p| * Real.rpow x (p - 1) * (|pStar p| / 2) := by
                    rw [abs_of_nonneg hxpow_nonneg, abs_div,
                      abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      _ ≤ DyuA1GrowthConst p * Real.rpow x (p - 1) := by
            unfold DyuA1GrowthConst
            ring_nf
            exact le_rfl
  · have h00 : x = 0 ∧ y = 0 := closureA1_x0_y0 p x y ⟨hx, hlow, hup⟩ hxpos
    rcases h00 with ⟨rfl, rfl⟩
    have hnonneg : 0 ≤ DyuA1GrowthConst p * Real.rpow 0 (p - 1) :=
      mul_nonneg (DyuA1GrowthConst_nonneg p) (Real.rpow_nonneg le_rfl _)
    simpa [DyuA1] using hnonneg

private lemma abs_DxvGeTwo_le_growth_on_closureA2
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ} (h : closureA2 p x y) :
    |DxvGeTwo p x y| ≤ DvGeTwoGrowthConst p * Real.rpow x (p - 1) := by
  rcases h with ⟨hx, hlow, hup⟩
  by_cases hxpos : 0 < x
  · have hsum : |(x + y) / 2| ≤ x :=
      closureA2_abs_add_div_two_le_x p hp ⟨hx, hlow, hup⟩
    have hdiff : |(x - y) / 2| ≤ x :=
      closureA2_abs_sub_div_two_le_x p hp ⟨hx, hlow, hup⟩
    have hp1_nonneg : 0 ≤ p - 1 := by linarith
    have hsum_pow :
        Real.rpow |(x + y) / 2| (p - 1) ≤ Real.rpow x (p - 1) :=
      Real.rpow_le_rpow (abs_nonneg _) hsum hp1_nonneg
    have hdiff_pow :
        Real.rpow |(x - y) / 2| (p - 1) ≤ Real.rpow x (p - 1) :=
      Real.rpow_le_rpow (abs_nonneg _) hdiff hp1_nonneg
    calc
      |DxvGeTwo p x y|
          ≤ |p| / 2 * Real.rpow |(x + y) / 2| (p - 1) +
              |Real.rpow (p - 1) p| * (|p| / 2) *
                Real.rpow |(x - y) / 2| (p - 1) := by
            unfold DxvGeTwo
            simp only [hxpos, if_true]
            calc
              |Real.rpow |(x + y) / 2| (p - 1) * (p / 2) -
                  Real.rpow (p - 1) p * Real.rpow |(x - y) / 2| (p - 1) *
                    (p / 2)|
                  ≤ |Real.rpow |(x + y) / 2| (p - 1) * (p / 2)| +
                      |Real.rpow (p - 1) p *
                        Real.rpow |(x - y) / 2| (p - 1) * (p / 2)| := by
                    simpa [sub_eq_add_neg] using
                      abs_add_le
                        (Real.rpow |(x + y) / 2| (p - 1) * (p / 2))
                        (-(Real.rpow (p - 1) p *
                          Real.rpow |(x - y) / 2| (p - 1) * (p / 2)))
              _ = |p| / 2 * Real.rpow |(x + y) / 2| (p - 1) +
                    |Real.rpow (p - 1) p| * (|p| / 2) *
                      Real.rpow |(x - y) / 2| (p - 1) := by
                    have hA :
                        |Real.rpow |(x + y) / 2| (p - 1) * (p / 2)| =
                          |p| / 2 * Real.rpow |(x + y) / 2| (p - 1) := by
                      calc
                        |Real.rpow |(x + y) / 2| (p - 1) * (p / 2)|
                            = |Real.rpow |(x + y) / 2| (p - 1)| * |p / 2| := by
                              rw [abs_mul]
                        _ = Real.rpow |(x + y) / 2| (p - 1) * (|p| / 2) := by
                              have hnon :
                                  0 ≤ Real.rpow |(x + y) / 2| (p - 1) :=
                                Real.rpow_nonneg (abs_nonneg _) _
                              have hpdiv : |p / 2| = |p| / 2 := by
                                rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
                              rw [abs_of_nonneg hnon, hpdiv]
                        _ = |p| / 2 * Real.rpow |(x + y) / 2| (p - 1) := by ring
                    have hB :
                        |Real.rpow (p - 1) p *
                          Real.rpow |(x - y) / 2| (p - 1) * (p / 2)| =
                          |Real.rpow (p - 1) p| * (|p| / 2) *
                            Real.rpow |(x - y) / 2| (p - 1) := by
                      calc
                        |Real.rpow (p - 1) p *
                          Real.rpow |(x - y) / 2| (p - 1) * (p / 2)|
                            = |Real.rpow (p - 1) p| *
                              |Real.rpow |(x - y) / 2| (p - 1)| * |p / 2| := by
                                rw [abs_mul, abs_mul]
                        _ = |Real.rpow (p - 1) p| *
                              Real.rpow |(x - y) / 2| (p - 1) * (|p| / 2) := by
                                have hnon :
                                    0 ≤ Real.rpow |(x - y) / 2| (p - 1) :=
                                  Real.rpow_nonneg (abs_nonneg _) _
                                have hpdiv : |p / 2| = |p| / 2 := by
                                  rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
                                rw [abs_of_nonneg hnon, hpdiv]
                        _ = |Real.rpow (p - 1) p| * (|p| / 2) *
                              Real.rpow |(x - y) / 2| (p - 1) := by ring
                    rw [hA, hB]
      _ ≤ |p| / 2 * Real.rpow x (p - 1) +
              |Real.rpow (p - 1) p| * (|p| / 2) * Real.rpow x (p - 1) := by
            gcongr
      _ = DvGeTwoGrowthConst p * Real.rpow x (p - 1) := by
            unfold DvGeTwoGrowthConst
            ring
  · have h00 : x = 0 ∧ y = 0 := closureA2_x0_y0 p x y ⟨hx, hlow, hup⟩ hxpos
    rcases h00 with ⟨rfl, rfl⟩
    have hnonneg : 0 ≤ DvGeTwoGrowthConst p * Real.rpow 0 (p - 1) :=
      mul_nonneg (DvGeTwoGrowthConst_nonneg p) (Real.rpow_nonneg le_rfl _)
    simpa [DxvGeTwo] using hnonneg

private lemma abs_DyvGeTwo_le_growth_on_closureA2
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ} (h : closureA2 p x y) :
    |DyvGeTwo p x y| ≤ DvGeTwoGrowthConst p * Real.rpow x (p - 1) := by
  rcases h with ⟨hx, hlow, hup⟩
  by_cases hxpos : 0 < x
  · have hsum : |(x + y) / 2| ≤ x :=
      closureA2_abs_add_div_two_le_x p hp ⟨hx, hlow, hup⟩
    have hdiff : |(x - y) / 2| ≤ x :=
      closureA2_abs_sub_div_two_le_x p hp ⟨hx, hlow, hup⟩
    have hp1_nonneg : 0 ≤ p - 1 := by linarith
    have hsum_pow :
        Real.rpow |(x + y) / 2| (p - 1) ≤ Real.rpow x (p - 1) :=
      Real.rpow_le_rpow (abs_nonneg _) hsum hp1_nonneg
    have hdiff_pow :
        Real.rpow |(x - y) / 2| (p - 1) ≤ Real.rpow x (p - 1) :=
      Real.rpow_le_rpow (abs_nonneg _) hdiff hp1_nonneg
    calc
      |DyvGeTwo p x y|
          ≤ |p| / 2 * Real.rpow |(x + y) / 2| (p - 1) +
              |Real.rpow (p - 1) p| * (|p| / 2) *
                Real.rpow |(x - y) / 2| (p - 1) := by
            unfold DyvGeTwo
            simp only [hxpos, if_true]
            calc
              |Real.rpow |(x + y) / 2| (p - 1) * (p / 2) +
                  Real.rpow (p - 1) p * Real.rpow |(x - y) / 2| (p - 1) *
                    (p / 2)|
                  ≤ |Real.rpow |(x + y) / 2| (p - 1) * (p / 2)| +
                      |Real.rpow (p - 1) p *
                        Real.rpow |(x - y) / 2| (p - 1) * (p / 2)| :=
                    abs_add_le _ _
              _ = |p| / 2 * Real.rpow |(x + y) / 2| (p - 1) +
                    |Real.rpow (p - 1) p| * (|p| / 2) *
                      Real.rpow |(x - y) / 2| (p - 1) := by
                    have hA :
                        |Real.rpow |(x + y) / 2| (p - 1) * (p / 2)| =
                          |p| / 2 * Real.rpow |(x + y) / 2| (p - 1) := by
                      calc
                        |Real.rpow |(x + y) / 2| (p - 1) * (p / 2)|
                            = |Real.rpow |(x + y) / 2| (p - 1)| * |p / 2| := by
                              rw [abs_mul]
                        _ = Real.rpow |(x + y) / 2| (p - 1) * (|p| / 2) := by
                              have hnon :
                                  0 ≤ Real.rpow |(x + y) / 2| (p - 1) :=
                                Real.rpow_nonneg (abs_nonneg _) _
                              have hpdiv : |p / 2| = |p| / 2 := by
                                rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
                              rw [abs_of_nonneg hnon, hpdiv]
                        _ = |p| / 2 * Real.rpow |(x + y) / 2| (p - 1) := by ring
                    have hB :
                        |Real.rpow (p - 1) p *
                          Real.rpow |(x - y) / 2| (p - 1) * (p / 2)| =
                          |Real.rpow (p - 1) p| * (|p| / 2) *
                            Real.rpow |(x - y) / 2| (p - 1) := by
                      calc
                        |Real.rpow (p - 1) p *
                          Real.rpow |(x - y) / 2| (p - 1) * (p / 2)|
                            = |Real.rpow (p - 1) p| *
                              |Real.rpow |(x - y) / 2| (p - 1)| * |p / 2| := by
                                rw [abs_mul, abs_mul]
                        _ = |Real.rpow (p - 1) p| *
                              Real.rpow |(x - y) / 2| (p - 1) * (|p| / 2) := by
                                have hnon :
                                    0 ≤ Real.rpow |(x - y) / 2| (p - 1) :=
                                  Real.rpow_nonneg (abs_nonneg _) _
                                have hpdiv : |p / 2| = |p| / 2 := by
                                  rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
                                rw [abs_of_nonneg hnon, hpdiv]
                        _ = |Real.rpow (p - 1) p| * (|p| / 2) *
                              Real.rpow |(x - y) / 2| (p - 1) := by ring
                    rw [hA, hB]
      _ ≤ |p| / 2 * Real.rpow x (p - 1) +
              |Real.rpow (p - 1) p| * (|p| / 2) * Real.rpow x (p - 1) := by
            gcongr
      _ = DvGeTwoGrowthConst p * Real.rpow x (p - 1) := by
            unfold DvGeTwoGrowthConst
            ring
  · have h00 : x = 0 ∧ y = 0 := closureA2_x0_y0 p x y ⟨hx, hlow, hup⟩ hxpos
    rcases h00 with ⟨rfl, rfl⟩
    have hnonneg : 0 ≤ DvGeTwoGrowthConst p * Real.rpow 0 (p - 1) :=
      mul_nonneg (DvGeTwoGrowthConst_nonneg p) (Real.rpow_nonneg le_rfl _)
    simpa [DyvGeTwo] using hnonneg

private lemma abs_DxauxFunction1_le_growth
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ} :
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
        abs_DxuA1_le_growth p h1
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
        |DxauxFunction1 p x y| = |DxvGeTwo p x y| := by
          rw [auxFunction1_Dx_eq_DxvGeTwo p hp x y h2]
        _ ≤ DvGeTwoGrowthConst p * Real.rpow x (p - 1) :=
          abs_DxvGeTwo_le_growth_on_closureA2 p hp h2
        _ ≤ auxDerivativeGrowthConst p * Real.rpow |x| (p - 1) := by
          rw [hx_abs]
          exact mul_le_mul_of_nonneg_right
            (DvGeTwoGrowthConst_le_auxDerivativeGrowthConst p)
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
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ} :
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
        |DyauxFunction1 p x y| = |DyvGeTwo p x y| := by
          rw [auxFunction1_Dy_eq_DyvGeTwo p hp x y h2]
        _ ≤ DvGeTwoGrowthConst p * Real.rpow x (p - 1) :=
          abs_DyvGeTwo_le_growth_on_closureA2 p hp h2
        _ ≤ auxDerivativeGrowthConst p * Real.rpow |x| (p - 1) := by
          rw [hx_abs]
          exact mul_le_mul_of_nonneg_right
            (DvGeTwoGrowthConst_le_auxDerivativeGrowthConst p)
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
    (p : ℝ) (hp : 2 < p) (x y : ℝ) :
    |DxuCandidate p x y|
      ≤ uCandidateDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by
  have hp' : 2 ≤ p := le_of_lt hp
  have hC : auxDerivativeGrowthConst p ≤ uCandidateDerivativeGrowthConst p :=
    auxDerivativeGrowthConst_le_uCandidateDerivativeGrowthConst p
  have hsum_nonneg :
      0 ≤ Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1) :=
    add_nonneg (Real.rpow_nonneg (abs_nonneg x) _)
      (Real.rpow_nonneg (abs_nonneg y) _)
  rcases mem_some_QuarterPlane x y with hQ1 | hrest
  · have haux := abs_DxauxFunction1_le_growth p hp' (x := x) (y := y)
    calc
      |DxuCandidate p x y| = |DxauxFunction1 p x y| := by
        rw [DxuCandidate_eq_Q1 p hQ1]
      _ ≤ auxDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := haux
      _ ≤ uCandidateDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) :=
        mul_le_mul_of_nonneg_right hC hsum_nonneg
  rcases hrest with hQ2 | hrest
  · have haux := abs_DxauxFunction1_le_growth p hp' (x := -x) (y := -y)
    calc
      |DxuCandidate p x y| = |DxauxFunction1 p (-x) (-y)| := by
        rw [DxuCandidate_eq_Q2 p hQ2, abs_neg]
      _ ≤ auxDerivativeGrowthConst p *
          (Real.rpow |(-x)| (p - 1) + Real.rpow |(-y)| (p - 1)) := haux
      _ = auxDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by simp
      _ ≤ uCandidateDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) :=
        mul_le_mul_of_nonneg_right hC hsum_nonneg
  rcases hrest with hQ3 | hQ4
  · have haux := abs_DyauxFunction1_le_growth p hp' (x := y) (y := x)
    calc
      |DxuCandidate p x y| = |DyauxFunction1 p y x| := by
        rw [DxuCandidate_eq_Q3 p hp hQ3]
      _ ≤ auxDerivativeGrowthConst p *
          (Real.rpow |y| (p - 1) + Real.rpow |x| (p - 1)) := haux
      _ = auxDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by ring
      _ ≤ uCandidateDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) :=
        mul_le_mul_of_nonneg_right hC hsum_nonneg
  · have haux := abs_DyauxFunction1_le_growth p hp' (x := -y) (y := -x)
    calc
      |DxuCandidate p x y| = |DyauxFunction1 p (-y) (-x)| := by
        rw [DxuCandidate_eq_Q4 p hp hQ4, abs_neg]
      _ ≤ auxDerivativeGrowthConst p *
          (Real.rpow |(-y)| (p - 1) + Real.rpow |(-x)| (p - 1)) := haux
      _ = auxDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by simp [add_comm]
      _ ≤ uCandidateDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) :=
        mul_le_mul_of_nonneg_right hC hsum_nonneg

private lemma abs_DyuCandidate_le_growth
    (p : ℝ) (hp : 2 < p) (x y : ℝ) :
    |DyuCandidate p x y|
      ≤ uCandidateDerivativeGrowthConst p *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by
  have h := abs_DxuCandidate_le_growth p hp y x
  rw [DyuCandidate_eq_DxuCandidate_swap p hp x y]
  simpa [add_comm] using h

private lemma uCandidate_derivative_growth_bound
    (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x y,
        |DxuCandidate p x y| ≤
          C * (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1))) ∧
      (∀ x y,
        |DyuCandidate p x y| ≤
          C * (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1))) := by
  refine ⟨uCandidateDerivativeGrowthConst p, uCandidateDerivativeGrowthConst_nonneg p, ?_, ?_⟩
  · intro x y
    exact abs_DxuCandidate_le_growth p hp x y
  · intro x y
    exact abs_DyuCandidate_le_growth p hp x y

/--
The vertical axis case follows from the horizontal one by swapping
coordinates.

The value symmetry transports the left and base terms, while the derivative
symmetry identifies the horizontal derivative at the swapped point with
`DyuCandidate` at the original point.
-/
private lemma uCandidate_axis_tangent_vertical
    (p : ℝ) (hp : 2 < p) {x y h k : ℝ}
    (hh0 : h = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  subst h
  have hhor := uCandidate_axis_tangent_horizontal
    (p := p) (hp := hp) (x := y) (y := x) (h := k) (k := 0) rfl
  have hswap_target :
      uCandidate p (x + 0) (y + k) =
        uCandidate p (y + k) (x + 0) := by
    exact uCandidate_swap p (x + 0) (y + k)
  have hswap_base : uCandidate p y x = uCandidate p x y :=
    (uCandidate_swap p x y).symm
  have hderiv : DxuCandidate p y x = DyuCandidate p x y :=
    (DyuCandidate_eq_DxuCandidate_swap p hp x y).symm
  calc
    uCandidate p (x + 0) (y + k) =
        uCandidate p (y + k) (x + 0) := hswap_target
    _ ≤ uCandidate p y x + DxuCandidate p y x * k + DyuCandidate p y x * 0 := hhor
    _ = uCandidate p x y + DxuCandidate p x y * 0 + DyuCandidate p x y * k := by
      rw [hswap_base, hderiv]
      ring

/--
The displayed tangent inequality whenever one coordinate increment is zero.

This is the final axis-supported statement: the `k = 0` branch is the
horizontal theorem proved by sector splitting, and the `h = 0` branch is its
coordinate-swapped version.
-/
private lemma uCandidate_axis_tangent
    (p : ℝ) (hp : 2 < p) {x y h k : ℝ}
    (hk : h * k = 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  rcases mul_eq_zero.mp hk with hh0 | hk0
  · exact uCandidate_axis_tangent_vertical p hp hh0
  · exact uCandidate_axis_tangent_horizontal p hp hk0

/-! ## 10. Other quadrant wrappers and pointwise differentiability -/

/-
The earlier horizontal dispatcher currently covers a substantial part of the
target tangent inequality.  The remaining wrappers below translate local
first-quadrant differentiability through the four quadrant reflections and
prove differentiability on open sectors and on the diagonal/antidiagonal.
-/

private lemma uCandidate_tangent_y_on_QuarterPlane3Open_segment
    (p : ℝ) (hp : 2 < p) {x y z : ℝ}
    (hy_pos : 0 < y) (hneg_x : -y < x) (hxy : x < y)
    (hz_pos : 0 < z) (hneg_z : -z < x) (hxz : x < z) :
    uCandidate p x z ≤
      uCandidate p x y + DyuCandidate p x y * (z - y) := by
  have hQy : QuarterPlane3 x y := ⟨hy_pos.le, le_of_lt hneg_x, le_of_lt hxy⟩
  have hQz : QuarterPlane3 x z := ⟨hz_pos.le, le_of_lt hneg_z, le_of_lt hxz⟩
  have hnotQy : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hxy hq.2.1
  have hnotQ2y : ¬ QuarterPlane2 x y := by
    intro hq
    have hlt : -x < y := by linarith
    exact not_le_of_gt hlt hq.2.1
  have hnotQz : ¬ QuarterPlane x z := by
    intro hq
    exact not_le_of_gt hxz hq.2.1
  have hnotQ2z : ¬ QuarterPlane2 x z := by
    intro hq
    have hlt : -x < z := by linarith
    exact not_le_of_gt hlt hq.2.1
  have haux := auxFunction1_tangent_x_on_QuarterPlaneOpen_segment
    p hp
    hy_pos hxy hneg_x
    hz_pos hxz hneg_z
  have hdy : DyuCandidate p x y = DxauxFunction1 p y x := by
    simp [DyuCandidate, hnotQy, hnotQ2y, hQy]
  calc
    uCandidate p x z = auxFunction1 p z x := by
      simp [uCandidate, hnotQz, hnotQ2z, hQz]
    _ ≤ auxFunction1 p y x + DxauxFunction1 p y x * (z - y) := haux
    _ = uCandidate p x y + DyuCandidate p x y * (z - y) := by
      simp [uCandidate, hnotQy, hnotQ2y, hQy, hdy]

private lemma uCandidate_tangent_x_on_QuarterPlane4Open_segment
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_neg : y < 0) (hyx : y < x) (hxnegy : x < -y)
    (hyz : y < z) (hznegy : z < -y) :
    uCandidate p z y ≤
      uCandidate p x y + DxuCandidate p x y * (z - x) := by
  have hQx : QuarterPlane4 x y := ⟨le_of_lt hy_neg, le_of_lt hyx, le_of_lt hxnegy⟩
  have hQz : QuarterPlane4 z y := ⟨le_of_lt hy_neg, le_of_lt hyz, le_of_lt hznegy⟩
  have hnotQx : ¬ QuarterPlane x y := by
    intro hq
    have hy_negx : y < -x := by linarith
    exact not_le_of_gt hy_negx hq.2.2
  have hnotQ2x : ¬ QuarterPlane2 x y := by
    intro hq
    linarith [hq.2.2]
  have hnotQ3x : ¬ QuarterPlane3 x y := by
    intro hq
    exact not_le_of_gt hy_neg hq.1
  have hnotQz : ¬ QuarterPlane z y := by
    intro hq
    have hy_negz : y < -z := by linarith
    exact not_le_of_gt hy_negz hq.2.2
  have hnotQ2z : ¬ QuarterPlane2 z y := by
    intro hq
    linarith [hq.2.2]
  have hnotQ3z : ¬ QuarterPlane3 z y := by
    intro hq
    exact not_le_of_gt hy_neg hq.1
  have haux := auxFunction1_tangent_y_on_QuarterPlaneOpen_segment
    p (by linarith : 2 ≤ p)
    (by linarith : 0 < -y)
    (by linarith : -(-y) < -x)
    (by linarith : -x < -y)
    (by linarith : -(-y) < -z)
    (by linarith : -z < -y)
  have hdx : DxuCandidate p x y = -DyauxFunction1 p (-y) (-x) := by
    simp [DxuCandidate, hnotQx, hnotQ2x, hnotQ3x, hQx]
  calc
    uCandidate p z y = auxFunction1 p (-y) (-z) := by
      simp [uCandidate, hnotQz, hnotQ2z, hnotQ3z, hQz]
    _ ≤ auxFunction1 p (-y) (-x) + DyauxFunction1 p (-y) (-x) * ((-z) - (-x)) := haux
    _ = uCandidate p x y + DxuCandidate p x y * (z - x) := by
      simp [uCandidate, hnotQx, hnotQ2x, hnotQ3x, hQx, hdx]
      ring

private lemma uCandidate_tangent_y_on_QuarterPlane4Open_segment
    (p : ℝ) (hp : 2 < p) {x y z : ℝ}
    (hy_neg : y < 0) (hyx : y < x) (hxnegy : x < -y)
    (hz_neg : z < 0) (hzx : z < x) (hxnegz : x < -z) :
    uCandidate p x z ≤
      uCandidate p x y + DyuCandidate p x y * (z - y) := by
  have hQy : QuarterPlane4 x y := ⟨le_of_lt hy_neg, le_of_lt hyx, le_of_lt hxnegy⟩
  have hQz : QuarterPlane4 x z := ⟨le_of_lt hz_neg, le_of_lt hzx, le_of_lt hxnegz⟩
  have hnotQy : ¬ QuarterPlane x y := by
    intro hq
    have hy_negx : y < -x := by linarith
    exact not_le_of_gt hy_negx hq.2.2
  have hnotQ2y : ¬ QuarterPlane2 x y := by
    intro hq
    linarith [hq.2.2]
  have hnotQ3y : ¬ QuarterPlane3 x y := by
    intro hq
    exact not_le_of_gt hy_neg hq.1
  have hnotQz : ¬ QuarterPlane x z := by
    intro hq
    have hz_negx : z < -x := by linarith
    exact not_le_of_gt hz_negx hq.2.2
  have hnotQ2z : ¬ QuarterPlane2 x z := by
    intro hq
    linarith [hq.2.2]
  have hnotQ3z : ¬ QuarterPlane3 x z := by
    intro hq
    exact not_le_of_gt hz_neg hq.1
  have haux := auxFunction1_tangent_x_on_QuarterPlaneOpen_segment
    p hp
    (by linarith : 0 < -y)
    (by linarith : -x < -y)
    (by linarith : -(-y) < -x)
    (by linarith : 0 < -z)
    (by linarith : -x < -z)
    (by linarith : -(-z) < -x)
  have hdy : DyuCandidate p x y = -DxauxFunction1 p (-y) (-x) := by
    simp [DyuCandidate, hnotQy, hnotQ2y, hnotQ3y, hQy]
  calc
    uCandidate p x z = auxFunction1 p (-z) (-x) := by
      simp [uCandidate, hnotQz, hnotQ2z, hnotQ3z, hQz]
    _ ≤ auxFunction1 p (-y) (-x) + DxauxFunction1 p (-y) (-x) * ((-z) - (-y)) := haux
    _ = uCandidate p x y + DyuCandidate p x y * (z - y) := by
      simp [uCandidate, hnotQy, hnotQ2y, hnotQ3y, hQy, hdy]
      ring

private lemma deriv_auxFunction1_eq_DxauxFunction1_on_QuarterPlaneOpen (p : ℝ) (hp : 2 ≤ p)
    (x y : ℝ) (hQ : QuarterPlaneOpen x y) :
    deriv (fun t => auxFunction1 p t y) x = DxauxFunction1 p x y := by
  rcases hQ with ⟨hx, hyx, hneg⟩
  by_cases h1 : a p * x < y
  · exact deriv_auxFunction1_eq_DxauxFunction1_on_A1 p hp x y ⟨hx, h1, hyx⟩
  · by_cases h2 : y < a p * x
    · exact deriv_auxFunction1_eq_DxauxFunction1_on_A2 p hp x y ⟨hx, hneg, h2⟩
    · have hy : y = a p * x := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      rw [hy]
      exact (hasDerivAt_auxFunction1_x_on_boundary p x hp hx).deriv

private lemma hasDerivAt_auxFunction1_x_on_QuarterPlaneOpen (p : ℝ) (hp : 2 ≤ p)
    (x y : ℝ) (hQ : QuarterPlaneOpen x y) :
    HasDerivAt (fun t => auxFunction1 p t y) (DxauxFunction1 p x y) x := by
  rcases hQ with ⟨hx, hyx, hneg⟩
  by_cases h1 : a p * x < y
  · have hEq : (fun t => auxFunction1 p t y) =ᶠ[nhds x] fun t => uA1 p t y := by
      have h0 : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
      have hA : {t : ℝ | a p * t < y} ∈ nhds x := by
        have hcont : ContinuousAt (fun t : ℝ => y - a p * t) x :=
          (continuous_const.sub (continuous_const.mul continuous_id')).continuousAt
        have hpos : 0 < y - a p * x := sub_pos.mpr h1
        simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hpos)
      have hY : {t : ℝ | y < t} ∈ nhds x := Ioi_mem_nhds hyx
      filter_upwards [h0, hA, hY] with t ht0 htA htY
      exact auxFunction1_eq_uA1 p t y ⟨le_of_lt ht0, le_of_lt htA, le_of_lt htY⟩
    have hbase : HasDerivAt (fun t => uA1 p t y) (DxuA1Fun p (x, y)) x :=
      hasDerivAt_uA1_x_of_pos p hp x y hx
    refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
    exact (auxFunction1_Dx_eq_DxuA1 p x y ⟨hx.le, le_of_lt h1, le_of_lt hyx⟩).symm
  · by_cases h2 : y < a p * x
    · have hEq : (fun t => auxFunction1 p t y) =ᶠ[nhds x] fun t => vGeTwo p t y := by
        have h0 : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
        have hN : {t : ℝ | -t < y} ∈ nhds x := by
          have hxy : -y < x := by linarith
          have hset : {t : ℝ | -t < y} = Set.Ioi (-y) := by
            ext t; simp [neg_lt]
          rw [hset]
          exact Ioi_mem_nhds hxy
        have hA : {t : ℝ | y < a p * t} ∈ nhds x := by
          have hcont : ContinuousAt (fun t : ℝ => a p * t - y) x :=
            ((continuous_const.mul continuous_id').sub continuous_const).continuousAt
          have hpos : 0 < a p * x - y := sub_pos.mpr h2
          simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hpos)
        filter_upwards [h0, hN, hA] with t ht0 htN htA
        exact auxFunction1_eq_vGeTwo p hp t y ⟨le_of_lt ht0, le_of_lt htN, le_of_lt htA⟩
      have hsum : 0 < (x + y) / 2 := by linarith
      have hdiff : 0 < (x - y) / 2 := by linarith
      have hbase : HasDerivAt (fun t => vGeTwo p t y) (DxvGeTwo p x y) x :=
        hasDerivAt_vGeTwo_x_of_pos p hp x y hsum hdiff
      refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
      exact (auxFunction1_Dx_eq_DxvGeTwo p hp x y ⟨hx.le, le_of_lt hneg, le_of_lt h2⟩).symm
    · have hy : y = a p * x := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      rw [hy]
      exact hasDerivAt_auxFunction1_x_on_boundary p x hp hx

private lemma deriv_auxFunction1_eq_DyauxFunction1_on_QuarterPlaneOpen (p : ℝ) (hp : 2 < p)
    (x y : ℝ) (hQ : QuarterPlaneOpen x y) :
    deriv (fun s => auxFunction1 p x s) y = DyauxFunction1 p x y := by
  rcases hQ with ⟨hx, hyx, hneg⟩
  have hp' : 2 ≤ p := by linarith
  by_cases h1 : a p * x < y
  · exact deriv_auxFunction1_eq_DyauxFunction1_on_A1 p hp x y ⟨hx, h1, hyx⟩
  · by_cases h2 : y < a p * x
    · exact deriv_auxFunction1_eq_DyauxFunction1_on_A2 p hp' x y ⟨hx, hneg, h2⟩
    · have hy : y = a p * x := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      rw [hy]
      exact (hasDerivAt_auxFunction1_y_on_boundary p x hp hx).deriv

private lemma hasDerivAt_auxFunction1_y_on_QuarterPlaneOpen (p : ℝ) (hp : 2 < p)
    (x y : ℝ) (hQ : QuarterPlaneOpen x y) :
    HasDerivAt (fun s => auxFunction1 p x s) (DyauxFunction1 p x y) y := by
  rcases hQ with ⟨hx, hyx, hneg⟩
  have hp' : 2 ≤ p := by linarith
  by_cases h1 : a p * x < y
  · have hEq : (fun s => auxFunction1 p x s) =ᶠ[nhds y] fun s => uA1 p x s := by
      have hA : {s : ℝ | a p * x < s} ∈ nhds y := Ioi_mem_nhds h1
      have hY : {s : ℝ | s < x} ∈ nhds y := Iio_mem_nhds hyx
      filter_upwards [hA, hY] with s hsA hsY
      exact auxFunction1_eq_uA1 p x s ⟨le_of_lt hx, le_of_lt hsA, le_of_lt hsY⟩
    have hbase : HasDerivAt (fun s => uA1 p x s) (DyuA1Fun p (x, y)) y :=
      hasDerivAt_uA1_y_of_pos p hp' x y hx
    refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
    exact (auxFunction1_Dy_eq_DyuA1 p x y ⟨hx.le, le_of_lt h1, le_of_lt hyx⟩).symm
  · by_cases h2 : y < a p * x
    · have hEq : (fun s => auxFunction1 p x s) =ᶠ[nhds y] fun s => vGeTwo p x s := by
        have hN : {s : ℝ | -x < s} ∈ nhds y := Ioi_mem_nhds hneg
        have hA : {s : ℝ | s < a p * x} ∈ nhds y := Iio_mem_nhds h2
        filter_upwards [hN, hA] with s hsN hsA
        exact auxFunction1_eq_vGeTwo p hp' x s ⟨le_of_lt hx, le_of_lt hsN, le_of_lt hsA⟩
      have hsum : 0 < (x + y) / 2 := by linarith
      have hdiff : 0 < (x - y) / 2 := by linarith
      have hbase : HasDerivAt (fun s => vGeTwo p x s) (DyvGeTwo p x y) y :=
        hasDerivAt_vGeTwo_y_of_pos p hp' x y hsum hdiff
      refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
      exact (auxFunction1_Dy_eq_DyvGeTwo p hp' x y ⟨hx.le, le_of_lt hneg, le_of_lt h2⟩).symm
    · have hy : y = a p * x := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
      rw [hy]
      exact hasDerivAt_auxFunction1_y_on_boundary p x hp hx

private lemma hasDerivAt_uCandidate_x_on_QuarterPlaneOpen (p : ℝ) (hp : 2 ≤ p)
    (x y : ℝ) (hQ : QuarterPlaneOpen x y) :
    HasDerivAt (fun t => uCandidate p t y) (DxuCandidate p x y) x := by
  rcases hQ with ⟨hx, hyx, hneg⟩
  have hEq : (fun t => uCandidate p t y) =ᶠ[nhds x] fun t => auxFunction1 p t y := by
    have h0 : {t : ℝ | 0 < t} ∈ nhds x := Ioi_mem_nhds hx
    have hY : {t : ℝ | y < t} ∈ nhds x := Ioi_mem_nhds hyx
    have hN : {t : ℝ | -t < y} ∈ nhds x := by
      have hxy : -y < x := by linarith
      have hset : {t : ℝ | -t < y} = Set.Ioi (-y) := by
        ext t; simp [neg_lt]
      rw [hset]
      exact Ioi_mem_nhds hxy
    filter_upwards [h0, hY, hN] with t ht0 htY htN
    have hq : QuarterPlane t y := ⟨le_of_lt ht0, le_of_lt htY, le_of_lt htN⟩
    simp [uCandidate, hq]
  have hbase :
      HasDerivAt (fun t => auxFunction1 p t y) (DxauxFunction1 p x y) x :=
    hasDerivAt_auxFunction1_x_on_QuarterPlaneOpen p hp x y ⟨hx, hyx, hneg⟩
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DxuCandidate, QuarterPlane, hx.le, hyx.le, hneg.le]

private lemma hasDerivAt_uCandidate_y_on_QuarterPlaneOpen (p : ℝ) (hp : 2 < p)
    (x y : ℝ) (hQ : QuarterPlaneOpen x y) :
    HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x y) y := by
  rcases hQ with ⟨hx, hyx, hneg⟩
  have hEq : (fun s => uCandidate p x s) =ᶠ[nhds y] fun s => auxFunction1 p x s := by
    have hY : {s : ℝ | s < x} ∈ nhds y := Iio_mem_nhds hyx
    have hN : {s : ℝ | -x < s} ∈ nhds y := Ioi_mem_nhds hneg
    filter_upwards [hY, hN] with s hsY hsN
    have hq : QuarterPlane x s := ⟨hx.le, le_of_lt hsY, le_of_lt hsN⟩
    simp [uCandidate, hq]
  have hbase :
      HasDerivAt (fun s => auxFunction1 p x s) (DyauxFunction1 p x y) y :=
    hasDerivAt_auxFunction1_y_on_QuarterPlaneOpen p hp x y ⟨hx, hyx, hneg⟩
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DyuCandidate, QuarterPlane, hx.le, hyx.le, hneg.le]

private lemma hasDerivAt_uCandidate_x_on_QuarterPlane2Open (p : ℝ) (hp : 2 ≤ p)
    (x y : ℝ) (hQ : QuarterPlane2Open x y) :
    HasDerivAt (fun t => uCandidate p t y) (DxuCandidate p x y) x := by
  rcases hQ with ⟨hx, hynegx, hxy⟩
  have hQaux : QuarterPlaneOpen (-x) (-y) := by
    exact ⟨by linarith, by linarith, by linarith⟩
  have hEq : (fun t => uCandidate p t y) =ᶠ[nhds x]
      fun t => auxFunction1 p (-t) (-y) := by
    have hX : {t : ℝ | t < 0} ∈ nhds x := Iio_mem_nhds hx
    have hY : {t : ℝ | y < -t} ∈ nhds x := by
      have hcont : ContinuousAt (fun t : ℝ => -t - y) x :=
        (continuous_id'.neg.sub continuous_const).continuousAt
      have hpos : 0 < -x - y := by linarith
      simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hpos)
    have hXY : {t : ℝ | t < y} ∈ nhds x := Iio_mem_nhds hxy
    filter_upwards [hX, hY, hXY] with t htX htY htXY
    have hq1 : ¬ QuarterPlane t y := by
      intro hq
      exact not_le_of_gt htX hq.1
    have hq2 : QuarterPlane2 t y := ⟨le_of_lt htX, le_of_lt htY, le_of_lt htXY⟩
    simp [uCandidate, hq1, hq2]
  have haux :
      HasDerivAt (fun r => auxFunction1 p r (-y))
        (DxauxFunction1 p (-x) (-y)) (-x) :=
    hasDerivAt_auxFunction1_x_on_QuarterPlaneOpen p hp (-x) (-y) hQaux
  have hbase :
      HasDerivAt (fun t => auxFunction1 p (-t) (-y))
        (-(DxauxFunction1 p (-x) (-y))) x := by
    have hcomp := haux.comp x (hasDerivAt_neg x)
    simp only [Function.comp_def] at hcomp
    refine hcomp.congr_deriv ?_
    ring
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [DxuCandidate, QuarterPlane, QuarterPlane2, hx.le, hynegx.le, hxy.le,
    not_le_of_gt hx]

private lemma hasDerivAt_uCandidate_x_on_QuarterPlane3Open (p : ℝ) (hp : 2 < p)
    (x y : ℝ) (hQ : QuarterPlane3Open x y) :
    HasDerivAt (fun t => uCandidate p t y) (DxuCandidate p x y) x := by
  rcases hQ with ⟨hy, hneg, hxy⟩
  have hQaux : QuarterPlaneOpen y x := ⟨hy, hxy, hneg⟩
  have hEq : (fun t => uCandidate p t y) =ᶠ[nhds x]
      fun t => auxFunction1 p y t := by
    have hN : {t : ℝ | -y < t} ∈ nhds x := Ioi_mem_nhds hneg
    have hY : {t : ℝ | t < y} ∈ nhds x := Iio_mem_nhds hxy
    filter_upwards [hN, hY] with t htN htY
    have hq1 : ¬ QuarterPlane t y := by
      intro hq
      exact not_le_of_gt htY hq.2.1
    have hq2 : ¬ QuarterPlane2 t y := by
      intro hq
      have hlt : -t < y := by linarith
      exact not_le_of_gt hlt hq.2.1
    have hq3 : QuarterPlane3 t y := ⟨hy.le, le_of_lt htN, le_of_lt htY⟩
    simp [uCandidate, hq1, hq2, hq3]
  have hbase :
      HasDerivAt (fun t => auxFunction1 p y t) (DyauxFunction1 p y x) x :=
    hasDerivAt_auxFunction1_y_on_QuarterPlaneOpen p hp y x hQaux
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  have hq1 : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hxy hq.2.1
  have hq2 : ¬ QuarterPlane2 x y := by
    intro hq
    have hlt : -x < y := by linarith
    exact not_le_of_gt hlt hq.2.1
  have hq3 : QuarterPlane3 x y := ⟨hy.le, hneg.le, hxy.le⟩
  simp [DxuCandidate, hq1, hq2, hq3]

private lemma hasDerivAt_uCandidate_x_on_QuarterPlane4Open (p : ℝ) (hp : 2 < p)
    (x y : ℝ) (hQ : QuarterPlane4Open x y) :
    HasDerivAt (fun t => uCandidate p t y) (DxuCandidate p x y) x := by
  rcases hQ with ⟨hy, hyx, hxnegy⟩
  have hQaux : QuarterPlaneOpen (-y) (-x) := by
    exact ⟨by linarith, by linarith, by linarith⟩
  have hEq : (fun t => uCandidate p t y) =ᶠ[nhds x]
      fun t => auxFunction1 p (-y) (-t) := by
    have hY : {t : ℝ | y < t} ∈ nhds x := Ioi_mem_nhds hyx
    have hX : {t : ℝ | t < -y} ∈ nhds x := Iio_mem_nhds hxnegy
    filter_upwards [hY, hX] with t htY htX
    have hq1 : ¬ QuarterPlane t y := by
      intro hq
      have hlt : y < -t := by linarith
      exact not_le_of_gt hlt hq.2.2
    have hq2 : ¬ QuarterPlane2 t y := by
      intro hq
      exact not_le_of_gt htY hq.2.2
    have hq3 : ¬ QuarterPlane3 t y := by
      intro hq
      exact not_le_of_gt hy hq.1
    have hq4 : QuarterPlane4 t y := ⟨le_of_lt hy, le_of_lt htY, le_of_lt htX⟩
    simp [uCandidate, hq1, hq2, hq3, hq4]
  have haux :
      HasDerivAt (fun s => auxFunction1 p (-y) s)
        (DyauxFunction1 p (-y) (-x)) (-x) :=
    hasDerivAt_auxFunction1_y_on_QuarterPlaneOpen p hp (-y) (-x) hQaux
  have hbase :
      HasDerivAt (fun t => auxFunction1 p (-y) (-t))
        (-(DyauxFunction1 p (-y) (-x))) x := by
    have hcomp := haux.comp x (hasDerivAt_neg x)
    simp only [Function.comp_def] at hcomp
    refine hcomp.congr_deriv ?_
    ring
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  have hq1 : ¬ QuarterPlane x y := by
    intro hq
    have hlt : y < -x := by linarith
    exact not_le_of_gt hlt hq.2.2
  have hq2 : ¬ QuarterPlane2 x y := by
    intro hq
    exact not_le_of_gt hyx hq.2.2
  have hq3 : ¬ QuarterPlane3 x y := by
    intro hq
    exact not_le_of_gt hy hq.1
  have hq4 : QuarterPlane4 x y := ⟨hy.le, hyx.le, hxnegy.le⟩
  simp [DxuCandidate, hq1, hq2, hq3, hq4]

private lemma hasDerivAt_uCandidate_y_on_QuarterPlane2Open (p : ℝ) (hp : 2 < p)
    (x y : ℝ) (hQ : QuarterPlane2Open x y) :
    HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x y) y := by
  rcases hQ with ⟨hx, hynegx, hxy⟩
  have hQaux : QuarterPlaneOpen (-x) (-y) := by
    exact ⟨by linarith, by linarith, by linarith⟩
  have hEq : (fun s => uCandidate p x s) =ᶠ[nhds y]
      fun s => auxFunction1 p (-x) (-s) := by
    have hY : {s : ℝ | s < -x} ∈ nhds y := Iio_mem_nhds hynegx
    have hX : {s : ℝ | x < s} ∈ nhds y := Ioi_mem_nhds hxy
    filter_upwards [hY, hX] with s hsY hsX
    have hq1 : ¬ QuarterPlane x s := by
      intro hq
      exact not_le_of_gt hx hq.1
    have hq2 : QuarterPlane2 x s := ⟨le_of_lt hx, le_of_lt hsY, le_of_lt hsX⟩
    simp [uCandidate, hq1, hq2]
  have haux :
      HasDerivAt (fun r => auxFunction1 p (-x) r)
        (DyauxFunction1 p (-x) (-y)) (-y) :=
    hasDerivAt_auxFunction1_y_on_QuarterPlaneOpen p hp (-x) (-y) hQaux
  have hbase :
      HasDerivAt (fun s => auxFunction1 p (-x) (-s))
        (-(DyauxFunction1 p (-x) (-y))) y := by
    have hcomp := haux.comp y (hasDerivAt_neg y)
    simp only [Function.comp_def] at hcomp
    refine hcomp.congr_deriv ?_
    ring
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  have hq1 : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hx hq.1
  have hq2 : QuarterPlane2 x y := ⟨hx.le, hynegx.le, hxy.le⟩
  simp [DyuCandidate, hq1, hq2]

private lemma hasDerivAt_uCandidate_y_on_QuarterPlane3Open (p : ℝ) (hp : 2 ≤ p)
    (x y : ℝ) (hQ : QuarterPlane3Open x y) :
    HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x y) y := by
  rcases hQ with ⟨hy, hneg, hxy⟩
  have hQaux : QuarterPlaneOpen y x := ⟨hy, hxy, hneg⟩
  have hEq : (fun s => uCandidate p x s) =ᶠ[nhds y]
      fun s => auxFunction1 p s x := by
    have hY : {s : ℝ | 0 < s} ∈ nhds y := Ioi_mem_nhds hy
    have hN : {s : ℝ | 0 < x + s} ∈ nhds y := by
      have hcont : ContinuousAt (fun s : ℝ => x + s) y :=
        (continuous_const.add continuous_id').continuousAt
      have hpos : 0 < x + y := by linarith
      simpa [Set.preimage] using hcont.preimage_mem_nhds (Ioi_mem_nhds hpos)
    have hX : {s : ℝ | x < s} ∈ nhds y := Ioi_mem_nhds hxy
    filter_upwards [hY, hN, hX] with s hsY hsN hsX
    have hq1 : ¬ QuarterPlane x s := by
      intro hq
      exact not_le_of_gt hsX hq.2.1
    have hq2 : ¬ QuarterPlane2 x s := by
      intro hq
      have hlt : -x < s := by linarith
      exact not_le_of_gt hlt hq.2.1
    have hsN' : -s < x := by linarith
    have hq3 : QuarterPlane3 x s := ⟨le_of_lt hsY, le_of_lt hsN', le_of_lt hsX⟩
    simp [uCandidate, hq1, hq2, hq3]
  have hbase :
      HasDerivAt (fun s => auxFunction1 p s x) (DxauxFunction1 p y x) y :=
    hasDerivAt_auxFunction1_x_on_QuarterPlaneOpen p hp y x hQaux
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  have hq1 : ¬ QuarterPlane x y := by
    intro hq
    exact not_le_of_gt hxy hq.2.1
  have hq2 : ¬ QuarterPlane2 x y := by
    intro hq
    have hlt : -x < y := by linarith
    exact not_le_of_gt hlt hq.2.1
  have hq3 : QuarterPlane3 x y := ⟨hy.le, hneg.le, hxy.le⟩
  simp [DyuCandidate, hq1, hq2, hq3]

private lemma hasDerivAt_uCandidate_y_on_QuarterPlane4Open (p : ℝ) (hp : 2 ≤ p)
    (x y : ℝ) (hQ : QuarterPlane4Open x y) :
    HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x y) y := by
  rcases hQ with ⟨hy, hyx, hxnegy⟩
  have hQaux : QuarterPlaneOpen (-y) (-x) := by
    exact ⟨by linarith, by linarith, by linarith⟩
  have hEq : (fun s => uCandidate p x s) =ᶠ[nhds y]
      fun s => auxFunction1 p (-s) (-x) := by
    have hY : {s : ℝ | s < 0} ∈ nhds y := Iio_mem_nhds hy
    have hYX : {s : ℝ | s < x} ∈ nhds y := Iio_mem_nhds hyx
    have hX : {s : ℝ | x < -s} ∈ nhds y := by
      have hcont : ContinuousAt (fun s : ℝ => -s - x) y :=
        (continuous_id'.neg.sub continuous_const).continuousAt
      have hpos : 0 < -y - x := by linarith
      simpa [Set.preimage, sub_pos] using hcont.preimage_mem_nhds (Ioi_mem_nhds hpos)
    filter_upwards [hY, hYX, hX] with s hsY hsYX hsX
    have hq1 : ¬ QuarterPlane x s := by
      intro hq
      have hlt : s < -x := by linarith
      exact not_le_of_gt hlt hq.2.2
    have hq2 : ¬ QuarterPlane2 x s := by
      intro hq
      exact not_le_of_gt hsYX hq.2.2
    have hq3 : ¬ QuarterPlane3 x s := by
      intro hq
      exact not_le_of_gt hsY hq.1
    have hq4 : QuarterPlane4 x s := ⟨le_of_lt hsY, le_of_lt hsYX, le_of_lt hsX⟩
    simp [uCandidate, hq1, hq2, hq3, hq4]
  have haux :
      HasDerivAt (fun r => auxFunction1 p r (-x))
        (DxauxFunction1 p (-y) (-x)) (-y) :=
    hasDerivAt_auxFunction1_x_on_QuarterPlaneOpen p hp (-y) (-x) hQaux
  have hbase :
      HasDerivAt (fun s => auxFunction1 p (-s) (-x))
        (-(DxauxFunction1 p (-y) (-x))) y := by
    have hcomp := haux.comp y (hasDerivAt_neg y)
    simp only [Function.comp_def] at hcomp
    refine hcomp.congr_deriv ?_
    ring
  refine (hbase.congr_of_eventuallyEq hEq).congr_deriv ?_
  have hq1 : ¬ QuarterPlane x y := by
    intro hq
    have hlt : y < -x := by linarith
    exact not_le_of_gt hlt hq.2.2
  have hq2 : ¬ QuarterPlane2 x y := by
    intro hq
    exact not_le_of_gt hyx hq.2.2
  have hq3 : ¬ QuarterPlane3 x y := by
    intro hq
    exact not_le_of_gt hy hq.1
  have hq4 : QuarterPlane4 x y := ⟨hy.le, hyx.le, hxnegy.le⟩
  simp [DyuCandidate, hq1, hq2, hq3, hq4]

private lemma hasDerivAt_uCandidate_x_on_diag_pos (p : ℝ) (hp : 2 < p)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => uCandidate p t x) (DxuCandidate p x x) x := by
  have hp' : 2 ≤ p := by linarith
  have hleftEq :
      (fun t => uCandidate p t x) =ᶠ[𝓝[Set.Iic x] x]
        fun t => auxFunction1 p x t := by
    have hmem : {t : ℝ | -x < t ∧ t ≤ x} ∈ 𝓝[Set.Iic x] x := by
      exact Filter.inter_mem
        (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith)))
        self_mem_nhdsWithin
    filter_upwards [hmem] with t ht
    rcases ht with ⟨hneg, htx⟩
    by_cases ht_eq : t = x
    · subst t
      have hq : QuarterPlane x x := ⟨hx.le, le_rfl, by linarith⟩
      simp [uCandidate, hq]
    · have htx_lt : t < x := lt_of_le_of_ne htx ht_eq
      have hq1' : ¬ QuarterPlane t x := by
        intro hq
        exact not_le_of_gt htx_lt hq.2.1
      have hq2 : ¬ QuarterPlane2 t x := by
        intro hq
        have hlt : -t < x := by linarith
        exact not_le_of_gt hlt hq.2.1
      have hq3 : QuarterPlane3 t x := ⟨hx.le, le_of_lt hneg, htx⟩
      simp [uCandidate, hq1', hq2, hq3]
  have hrightEq :
      (fun t => uCandidate p t x) =ᶠ[𝓝[Set.Ici x] x]
        fun t => auxFunction1 p t x := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := lt_of_lt_of_le hx ht
    have hq : QuarterPlane t x := ⟨le_of_lt htpos, ht, by linarith⟩
    simp [uCandidate, hq]
  have hleft :
      HasDerivWithinAt (fun t => uCandidate p t x)
        (DxuCandidate p x x) (Set.Iic x) x := by
    have hbase :
        HasDerivWithinAt (fun t => auxFunction1 p x t)
          (DyauxFunction1 p x x) (Set.Iic x) x :=
      by
        have ha_lt : a p * x < x := by
          have hlt : a p < 1 := a_lt_one_of_two_le p hp'
          simpa using mul_lt_mul_of_pos_right hlt hx
        have hEq :
            (fun t => auxFunction1 p x t) =ᶠ[𝓝[Set.Iic x] x]
              fun t => uA1 p x t := by
          have hmem : {t : ℝ | a p * x < t ∧ t ≤ x} ∈ 𝓝[Set.Iic x] x := by
            exact Filter.inter_mem
              (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ha_lt))
              self_mem_nhdsWithin
          filter_upwards [hmem] with t ht
          rcases ht with ⟨hat, htx⟩
          exact auxFunction1_eq_uA1 p x t ⟨hx.le, le_of_lt hat, htx⟩
        have hu :
            HasDerivWithinAt (fun t => uA1 p x t)
              (DyuA1Fun p (x, x)) (Set.Iic x) x :=
          (hasDerivAt_uA1_y_of_pos p hp' x x hx).hasDerivWithinAt
        refine (hu.congr_of_eventuallyEq_of_mem hEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
        exact (auxFunction1_Dy_eq_DyuA1 p x x ⟨hx.le, le_of_lt ha_lt, le_rfl⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hleftEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
    have hD : DxuCandidate p x x = DxauxFunction1 p x x := by
      simp [DxuCandidate, QuarterPlane, hx.le]
    rw [hD]
    exact (DxauxFunction1_eq_DyauxFunction1_on_diag p hp x hx.le).symm
  have hright :
      HasDerivWithinAt (fun t => uCandidate p t x)
        (DxuCandidate p x x) (Set.Ici x) x := by
    have hbase :
        HasDerivWithinAt (fun t => auxFunction1 p t x)
          (DxauxFunction1 p x x) (Set.Ici x) x :=
      by
        have ha_lt : a p * x < x := by
          have hlt : a p < 1 := a_lt_one_of_two_le p hp'
          simpa using mul_lt_mul_of_pos_right hlt hx
        have hEq :
            (fun t => auxFunction1 p t x) =ᶠ[𝓝[Set.Ici x] x]
              fun t => uA1 p t x := by
          have ha_pos : 0 < a p := by
            have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
            have hp_pos : 0 < p := by linarith
            rw [a, hpStar]
            field_simp [hp_pos.ne]
            nlinarith
          have hx_lt_div : x < x / a p := by
            rw [div_eq_mul_inv]
            have ha_lt : a p < 1 := a_lt_one_of_two_le p hp'
            have hlt_inv : 1 < (a p)⁻¹ := by
              rw [one_lt_inv₀ ha_pos]
              exact ha_lt
            nlinarith
          have hmem : {t : ℝ | x ≤ t ∧ t < x / a p} ∈ 𝓝[Set.Ici x] x := by
            have hset : {t : ℝ | x ≤ t ∧ t < x / a p} = Set.Ici x ∩ Set.Iio (x / a p) := by
              ext t; simp [Set.mem_Ici, Set.mem_Iio]
            rw [hset]
            exact inter_mem_nhdsWithin (Set.Ici x) (Iio_mem_nhds hx_lt_div)
          filter_upwards [hmem] with t ht
          rcases ht with ⟨ht, ht_div⟩
          have htpos : 0 < t := lt_of_lt_of_le hx ht
          have hat : a p * t < x := by
            have hmul := mul_lt_mul_of_pos_left ht_div ha_pos
            field_simp [ha_pos.ne'] at hmul
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
          exact auxFunction1_eq_uA1 p t x ⟨le_of_lt htpos, le_of_lt hat, ht⟩
        have hu :
            HasDerivWithinAt (fun t => uA1 p t x)
              (DxuA1Fun p (x, x)) (Set.Ici x) x :=
          (hasDerivAt_uA1_x_of_pos p hp' x x hx).hasDerivWithinAt
        refine (hu.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
        exact (auxFunction1_Dx_eq_DxuA1 p x x ⟨hx.le, le_of_lt ha_lt, le_rfl⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hrightEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
    simp [DxuCandidate, QuarterPlane, hx.le]
  simpa [Set.Iic_union_Ici] using hleft.union hright

private lemma hasDerivAt_uCandidate_y_on_diag_pos (p : ℝ) (hp : 2 < p)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x x) x := by
  have hp' : 2 ≤ p := by linarith
  have hleftEq :
      (fun s => uCandidate p x s) =ᶠ[𝓝[Set.Iic x] x]
        fun s => auxFunction1 p x s := by
    have hmem : {s : ℝ | -x < s ∧ s ≤ x} ∈ 𝓝[Set.Iic x] x := by
      exact Filter.inter_mem
        (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith)))
        self_mem_nhdsWithin
    filter_upwards [hmem] with s hs
    rcases hs with ⟨hneg, hsx⟩
    have hq : QuarterPlane x s := ⟨hx.le, hsx, le_of_lt hneg⟩
    simp [uCandidate, hq]
  have hrightEq :
      (fun s => uCandidate p x s) =ᶠ[𝓝[Set.Ici x] x]
        fun s => auxFunction1 p s x := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    by_cases hs_eq : s = x
    · subst s
      have hq : QuarterPlane x x := ⟨hx.le, le_rfl, by linarith⟩
      simp [uCandidate, hq]
    · have hxs_lt : x < s := lt_of_le_of_ne hs (Ne.symm hs_eq)
      have hq1 : ¬ QuarterPlane x s := by
        intro hq
        exact not_le_of_gt hxs_lt hq.2.1
      have hq2 : ¬ QuarterPlane2 x s := by
        intro hq
        exact not_le_of_gt hx hq.1
      have hq3 : QuarterPlane3 x s := ⟨le_trans hx.le hs, by linarith, le_of_lt hxs_lt⟩
      simp [uCandidate, hq1, hq2, hq3]
  have hleft :
      HasDerivWithinAt (fun s => uCandidate p x s)
        (DyuCandidate p x x) (Set.Iic x) x := by
    have hbase :
        HasDerivWithinAt (fun s => auxFunction1 p x s)
          (DyauxFunction1 p x x) (Set.Iic x) x :=
      by
        have ha_lt : a p * x < x := by
          have hlt : a p < 1 := a_lt_one_of_two_le p hp'
          simpa using mul_lt_mul_of_pos_right hlt hx
        have hEq :
            (fun s => auxFunction1 p x s) =ᶠ[𝓝[Set.Iic x] x]
              fun s => uA1 p x s := by
          have hmem : {s : ℝ | a p * x < s ∧ s ≤ x} ∈ 𝓝[Set.Iic x] x := by
            exact Filter.inter_mem
              (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ha_lt))
              self_mem_nhdsWithin
          filter_upwards [hmem] with s hs
          rcases hs with ⟨has, hsx⟩
          exact auxFunction1_eq_uA1 p x s ⟨hx.le, le_of_lt has, hsx⟩
        have hu :
            HasDerivWithinAt (fun s => uA1 p x s)
              (DyuA1Fun p (x, x)) (Set.Iic x) x :=
          (hasDerivAt_uA1_y_of_pos p hp' x x hx).hasDerivWithinAt
        refine (hu.congr_of_eventuallyEq_of_mem hEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
        exact (auxFunction1_Dy_eq_DyuA1 p x x ⟨hx.le, le_of_lt ha_lt, le_rfl⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hleftEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
    simp [DyuCandidate, QuarterPlane, hx.le]
  have hright :
      HasDerivWithinAt (fun s => uCandidate p x s)
        (DyuCandidate p x x) (Set.Ici x) x := by
    have hbase :
        HasDerivWithinAt (fun s => auxFunction1 p s x)
          (DxauxFunction1 p x x) (Set.Ici x) x :=
      by
        have ha_lt : a p * x < x := by
          have hlt : a p < 1 := a_lt_one_of_two_le p hp'
          simpa using mul_lt_mul_of_pos_right hlt hx
        have hEq :
            (fun s => auxFunction1 p s x) =ᶠ[𝓝[Set.Ici x] x]
              fun s => uA1 p s x := by
          have ha_pos : 0 < a p := by
            have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
            have hp_pos : 0 < p := by linarith
            rw [a, hpStar]
            field_simp [hp_pos.ne]
            nlinarith
          have hx_lt_div : x < x / a p := by
            rw [div_eq_mul_inv]
            have ha_lt_one : a p < 1 := a_lt_one_of_two_le p hp'
            have hlt_inv : 1 < (a p)⁻¹ := by
              rw [one_lt_inv₀ ha_pos]
              exact ha_lt_one
            nlinarith
          have hmem : {s : ℝ | x ≤ s ∧ s < x / a p} ∈ 𝓝[Set.Ici x] x := by
            have hset : {s : ℝ | x ≤ s ∧ s < x / a p} = Set.Ici x ∩ Set.Iio (x / a p) := by
              ext s; simp [Set.mem_Ici, Set.mem_Iio]
            rw [hset]
            exact inter_mem_nhdsWithin (Set.Ici x) (Iio_mem_nhds hx_lt_div)
          filter_upwards [hmem] with s hs
          rcases hs with ⟨hxs, hsdiv⟩
          have hspos : 0 < s := lt_of_lt_of_le hx hxs
          have has : a p * s < x := by
            have hmul := mul_lt_mul_of_pos_left hsdiv ha_pos
            field_simp [ha_pos.ne'] at hmul
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
          exact auxFunction1_eq_uA1 p s x ⟨le_of_lt hspos, le_of_lt has, hxs⟩
        have hu :
            HasDerivWithinAt (fun s => uA1 p s x)
              (DxuA1Fun p (x, x)) (Set.Ici x) x :=
          (hasDerivAt_uA1_x_of_pos p hp' x x hx).hasDerivWithinAt
        refine (hu.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
        exact (auxFunction1_Dx_eq_DxuA1 p x x ⟨hx.le, le_of_lt ha_lt, le_rfl⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hrightEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
    have hD : DyuCandidate p x x = DyauxFunction1 p x x := by
      simp [DyuCandidate, QuarterPlane, hx.le]
    rw [hD]
    exact DxauxFunction1_eq_DyauxFunction1_on_diag p hp x hx.le
  simpa [Set.Iic_union_Ici] using hleft.union hright

private lemma hasDerivAt_uCandidate_x_on_antidiag_pos (p : ℝ) (hp : 2 < p)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => uCandidate p t (-x)) (DxuCandidate p x (-x)) x := by
  have hp' : 2 ≤ p := by linarith
  have ha_nonneg : 0 ≤ a p := by
    have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
    have hp_pos : 0 < p := by linarith
    rw [a, hpStar]
    field_simp [hp_pos.ne]
    nlinarith
  have hleftEq :
      (fun t => uCandidate p t (-x)) =ᶠ[𝓝[Set.Iic x] x]
        fun t => auxFunction1 p x (-t) := by
    have hmem : {t : ℝ | -x < t ∧ t ≤ x} ∈ 𝓝[Set.Iic x] x := by
      exact Filter.inter_mem
        (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith)))
        self_mem_nhdsWithin
    filter_upwards [hmem] with t ht
    rcases ht with ⟨hneg, htx⟩
    by_cases ht_eq : t = x
    · subst t
      have hq : QuarterPlane x (-x) := ⟨hx.le, by linarith, le_rfl⟩
      simp [uCandidate, hq]
    · have htx_lt : t < x := lt_of_le_of_ne htx ht_eq
      have hq1 : ¬ QuarterPlane t (-x) := by
        intro hq
        have hxt : x ≤ t := by linarith [hq.2.2]
        linarith
      have hq2 : ¬ QuarterPlane2 t (-x) := by
        intro hq
        linarith [hq.2.2]
      have hq3 : ¬ QuarterPlane3 t (-x) := by
        intro hq
        exact not_le_of_gt (neg_neg_of_pos hx) hq.1
      have hq4 : QuarterPlane4 t (-x) := ⟨by linarith, by linarith, by linarith⟩
      simp [uCandidate, hq1, hq2, hq3, hq4]
  have hrightEq :
      (fun t => uCandidate p t (-x)) =ᶠ[𝓝[Set.Ici x] x]
        fun t => auxFunction1 p t (-x) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := lt_of_lt_of_le hx ht
    have hq : QuarterPlane t (-x) :=
      ⟨htpos.le, le_trans (neg_nonpos.mpr hx.le) htpos.le, neg_le_neg ht⟩
    simp [uCandidate, hq]
  have hleft :
      HasDerivWithinAt (fun t => uCandidate p t (-x))
        (DxuCandidate p x (-x)) (Set.Iic x) x := by
    have hbase :
        HasDerivWithinAt (fun t => auxFunction1 p x (-t))
          (-(DyauxFunction1 p x (-x))) (Set.Iic x) x := by
      have hEq :
          (fun t => auxFunction1 p x (-t)) =ᶠ[𝓝[Set.Iic x] x]
            fun t => vGeTwo p x (-t) := by
        have hmem : {t : ℝ | t ≤ x ∧ -t < a p * x} ∈ 𝓝[Set.Iic x] x := by
          have hlt : -x < a p * x := by
            have hmul : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
            linarith
          exact Filter.inter_mem self_mem_nhdsWithin
            (mem_nhdsWithin_of_mem_nhds
              ((continuous_id'.neg).continuousAt.preimage_mem_nhds
                (Iio_mem_nhds hlt)))
        filter_upwards [hmem] with t ht
        rcases ht with ⟨htx, htax⟩
        exact auxFunction1_eq_vGeTwo p hp' x (-t) ⟨hx.le, by linarith, le_of_lt htax⟩
      have hv :
          HasDerivWithinAt (fun t => vGeTwo p x (-t))
            (-(DyvGeTwo p x (-x))) (Set.Iic x) x := by
        have h0 :
            HasDerivAt (fun s => vGeTwo p x s)
              (DyvGeTwo p x (-x)) (-x) :=
          hasDerivAt_vGeTwo_y_on_antidiag_pos p hp x hx
        have hcomp :
            HasDerivAt (fun t => vGeTwo p x (-t))
              (-(DyvGeTwo p x (-x))) x := by
          have hcomp := h0.comp x (hasDerivAt_neg x)
          simp only [Function.comp_def] at hcomp
          refine hcomp.congr_deriv ?_
          ring
        exact hcomp.hasDerivWithinAt
      refine (hv.congr_of_eventuallyEq_of_mem hEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
      exact congrArg Neg.neg (auxFunction1_Dy_eq_DyvGeTwo p hp' x (-x)
        ⟨hx.le, le_rfl, by
          have hmul : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
          linarith⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hleftEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
    have hD : DxuCandidate p x (-x) = DxauxFunction1 p x (-x) := by
      simp [DxuCandidate, QuarterPlane, hx.le]
    rw [hD]
    exact (DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp x hx.le).symm
  have hright :
      HasDerivWithinAt (fun t => uCandidate p t (-x))
        (DxuCandidate p x (-x)) (Set.Ici x) x := by
    have hbase :
        HasDerivWithinAt (fun t => auxFunction1 p t (-x))
          (DxauxFunction1 p x (-x)) (Set.Ici x) x := by
      have hEq :
          (fun t => auxFunction1 p t (-x)) =ᶠ[𝓝[Set.Ici x] x]
            fun t => vGeTwo p t (-x) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have htpos : 0 ≤ t := le_trans hx.le ht
        exact auxFunction1_eq_vGeTwo p hp' t (-x) ⟨htpos, neg_le_neg ht, by
          exact le_trans (neg_nonpos.mpr hx.le) (mul_nonneg ha_nonneg htpos)⟩
      have hv :
          HasDerivWithinAt (fun t => vGeTwo p t (-x))
            (DxvGeTwo p x (-x)) (Set.Ici x) x :=
        (hasDerivAt_vGeTwo_x_on_antidiag_pos p hp x hx).hasDerivWithinAt
      refine (hv.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
      exact (auxFunction1_Dx_eq_DxvGeTwo p hp' x (-x)
        ⟨hx.le, le_rfl, by
          have hmul : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
          linarith⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hrightEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
    simp [DxuCandidate, QuarterPlane, hx.le]
  simpa [Set.Iic_union_Ici] using hleft.union hright

private lemma hasDerivAt_uCandidate_y_on_antidiag_pos (p : ℝ) (hp : 2 < p)
    (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun s => uCandidate p x s) (DyuCandidate p x (-x)) (-x) := by
  have hp' : 2 ≤ p := by linarith
  have ha_nonneg : 0 ≤ a p := by
    have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp'
    have hp_pos : 0 < p := by linarith
    rw [a, hpStar]
    field_simp [hp_pos.ne]
    nlinarith
  have hleftEq :
      (fun s => uCandidate p x s) =ᶠ[𝓝[Set.Iic (-x)] (-x)]
        fun s => auxFunction1 p (-s) (-x) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    by_cases hs_eq : s = -x
    · subst s
      have hq : QuarterPlane x (-x) := ⟨hx.le, by linarith, le_rfl⟩
      simp [uCandidate, hq]
    · have hs_lt : s < -x := lt_of_le_of_ne hs hs_eq
      have hq1 : ¬ QuarterPlane x s := by
        intro hq
        exact not_le_of_gt hs_lt hq.2.2
      have hq2 : ¬ QuarterPlane2 x s := by
        intro hq
        exact not_le_of_gt hx hq.1
      have hq3 : ¬ QuarterPlane3 x s := by
        intro hq
        linarith [hq.2.2]
      have hq4 : QuarterPlane4 x s := ⟨by linarith, by linarith, by linarith⟩
      simp [uCandidate, hq1, hq2, hq3, hq4]
  have hrightEq :
      (fun s => uCandidate p x s) =ᶠ[𝓝[Set.Ici (-x)] (-x)]
        fun s => auxFunction1 p x s := by
    have hmem : {s : ℝ | s ≤ x ∧ -x ≤ s} ∈ 𝓝[Set.Ici (-x)] (-x) := by
      exact Filter.inter_mem
        (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith)))
        self_mem_nhdsWithin
    filter_upwards [hmem] with s hs
    rcases hs with ⟨hsx, hnegs⟩
    have hq : QuarterPlane x s := ⟨hx.le, hsx, hnegs⟩
    simp [uCandidate, hq]
  have hleft :
      HasDerivWithinAt (fun s => uCandidate p x s)
        (DyuCandidate p x (-x)) (Set.Iic (-x)) (-x) := by
    have hbase :
        HasDerivWithinAt (fun s => auxFunction1 p (-s) (-x))
          (-(DxauxFunction1 p x (-x))) (Set.Iic (-x)) (-x) := by
      have hEq :
          (fun s => auxFunction1 p (-s) (-x)) =ᶠ[𝓝[Set.Iic (-x)] (-x)]
            fun s => vGeTwo p (-s) (-x) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hspos : 0 ≤ -s := by
          have hs0 : s ≤ 0 := le_trans hs (neg_nonpos.mpr hx.le)
          linarith
        exact auxFunction1_eq_vGeTwo p hp' (-s) (-x) ⟨hspos, by simpa using hs, by
          exact le_trans (neg_nonpos.mpr hx.le) (mul_nonneg ha_nonneg hspos)⟩
      have hv :
          HasDerivWithinAt (fun s => vGeTwo p (-s) (-x))
            (-(DxvGeTwo p x (-x))) (Set.Iic (-x)) (-x) := by
        have h0 :
            HasDerivAt (fun t => vGeTwo p t (-x))
              (DxvGeTwo p x (-x)) x :=
          hasDerivAt_vGeTwo_x_on_antidiag_pos p hp x hx
        have hcomp :
            HasDerivAt (fun s => vGeTwo p (-s) (-x))
              (-(DxvGeTwo p x (-x))) (-x) := by
          have h0' :
              HasDerivAt (fun t => vGeTwo p t (-x))
                (DxvGeTwo p x (-x)) (- -x) := by
            simpa using h0
          have hneg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) (-x) := by
            simpa using (hasDerivAt_neg (-x))
          have hc := h0'.comp (-x) hneg
          simp only [Function.comp_def] at hc
          refine hc.congr_deriv ?_
          ring
        exact hcomp.hasDerivWithinAt
      refine (hv.congr_of_eventuallyEq_of_mem hEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
      exact congrArg Neg.neg (auxFunction1_Dx_eq_DxvGeTwo p hp' x (-x)
        ⟨hx.le, le_rfl, by
          have hmul : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
          linarith⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hleftEq (Set.mem_Iic.mpr le_rfl)).congr_deriv ?_
    have hD : DyuCandidate p x (-x) = DyauxFunction1 p x (-x) := by
      simp [DyuCandidate, QuarterPlane, hx.le]
    rw [hD]
    rw [DxauxFunction1_eq_neg_DyauxFunction1_on_antidiag p hp x hx.le]
    simp
  have hright :
      HasDerivWithinAt (fun s => uCandidate p x s)
        (DyuCandidate p x (-x)) (Set.Ici (-x)) (-x) := by
    have hbase :
        HasDerivWithinAt (fun s => auxFunction1 p x s)
          (DyauxFunction1 p x (-x)) (Set.Ici (-x)) (-x) := by
      have hEq :
          (fun s => auxFunction1 p x s) =ᶠ[𝓝[Set.Ici (-x)] (-x)]
            fun s => vGeTwo p x s := by
        have hmem : {s : ℝ | -x ≤ s ∧ s < a p * x} ∈ 𝓝[Set.Ici (-x)] (-x) := by
          have hlt : -x < a p * x := by
            have hmul : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
            linarith
          exact Filter.inter_mem self_mem_nhdsWithin
            (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt))
        filter_upwards [hmem] with s hs
        exact auxFunction1_eq_vGeTwo p hp' x s ⟨hx.le, hs.1, le_of_lt hs.2⟩
      have hv :
          HasDerivWithinAt (fun s => vGeTwo p x s)
            (DyvGeTwo p x (-x)) (Set.Ici (-x)) (-x) :=
        (hasDerivAt_vGeTwo_y_on_antidiag_pos p hp x hx).hasDerivWithinAt
      refine (hv.congr_of_eventuallyEq_of_mem hEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
      exact (auxFunction1_Dy_eq_DyvGeTwo p hp' x (-x)
        ⟨hx.le, le_rfl, by
          have hmul : 0 ≤ a p * x := mul_nonneg ha_nonneg hx.le
          linarith⟩).symm
    refine (hbase.congr_of_eventuallyEq_of_mem hrightEq (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
    simp [DyuCandidate, QuarterPlane, hx.le]
  simpa [Set.Iic_union_Ici] using hleft.union hright

private lemma continuousOn_DxauxFunction1_on_QuarterPlaneOpen (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (fun z : ℝ × ℝ => DxauxFunction1 p z.1 z.2)
      {z | QuarterPlaneOpen z.1 z.2} := by
  exact (continuousOn_DxauxFunction1 p hp).mono (by
    intro z hz
    rcases hz with ⟨hz1, hz2, hz3⟩
    exact ⟨le_of_lt hz1, le_of_lt hz2, le_of_lt hz3⟩)

private lemma continuousOn_DyauxFunction1_on_QuarterPlaneOpen (p : ℝ) (hp : 2 < p) :
    ContinuousOn (fun z : ℝ × ℝ => DyauxFunction1 p z.1 z.2)
      {z | QuarterPlaneOpen z.1 z.2} := by
  exact (continuousOn_DyauxFunction1 p hp).mono (by
    intro z hz
    rcases hz with ⟨hz1, hz2, hz3⟩
    exact ⟨le_of_lt hz1, le_of_lt hz2, le_of_lt hz3⟩)

private lemma continuousOn_DxauxFunction1_on_QuarterPlane (p : ℝ) (hp : 2 ≤ p) :
    ContinuousOn (fun z : ℝ × ℝ => DxauxFunction1 p z.1 z.2)
      {z | QuarterPlane z.1 z.2} := by
  exact continuousOn_DxauxFunction1 p hp

private lemma continuousOn_DyauxFunction1_on_QuarterPlane (p : ℝ) (hp : 2 < p) :
    ContinuousOn (fun z : ℝ × ℝ => DyauxFunction1 p z.1 z.2)
      {z | QuarterPlane z.1 z.2} := by
  exact continuousOn_DyauxFunction1 p hp


/-! ## 11. Pointwise majorization -/

/-
The pointwise estimate `vGeTwo ≤ uCandidate` is local in the first quadrant
and then transported by the symmetries used in the definition of
`uCandidate`.  The only genuinely analytic part is the scalar inequality on
the `A1` sector; the `A2` sector is equality by construction.
-/

/-- A convexity bound for the derivative of the normalized scalar difference. -/
private lemma burkholder_scalar_deriv_nonpos
    (p t : ℝ) (hp : 2 < p) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / p) :
    (1 - t) ^ (p - 1) + (p - 1) ^ p * t ^ (p - 1) ≤ alpha p := by
  let lam : ℝ := 1 - p * t
  let mu : ℝ := p * t
  have hp_ge : 2 ≤ p := by linarith
  have hp_pos : 0 < p := by linarith
  have hp1_ge_one : 1 ≤ p - 1 := by linarith
  have hp1_pos : 0 < p - 1 := by linarith
  have hbase_nonneg : 0 ≤ (p - 1) / p := by positivity
  have hbase_le_one : (p - 1) / p ≤ 1 := by
    field_simp [hp_pos.ne']
    linarith
  have h_inv_nonneg : 0 ≤ 1 / p := by positivity
  have hlam_nonneg : 0 ≤ lam := by
    dsimp [lam]
    have hmul := mul_le_mul_of_nonneg_left ht1 (by linarith : 0 ≤ p)
    field_simp [hp_pos.ne'] at hmul
    linarith
  have hmu_nonneg : 0 ≤ mu := by
    dsimp [mu]
    positivity
  have hsum : lam + mu = 1 := by
    dsimp [lam, mu]
    ring
  have hone :
      lam • (1 : ℝ) + mu • ((p - 1) / p) = 1 - t := by
    dsimp [lam, mu]
    field_simp [hp_pos.ne']
    ring
  have ht_as_combo :
      lam • (0 : ℝ) + mu • (1 / p) = t := by
    dsimp [lam, mu]
    field_simp [hp_pos.ne']
    ring
  have hone' : lam + mu * ((p - 1) / p) = 1 - t := by
    simpa [smul_eq_mul] using hone
  have ht_as_combo' : mu * p⁻¹ = t := by
    simpa [smul_eq_mul, one_div] using ht_as_combo
  have hconv := convexOn_rpow (p := p - 1) hp1_ge_one
  have hfirst :
      (1 - t) ^ (p - 1) ≤
        lam * (1 : ℝ) ^ (p - 1) + mu * (((p - 1) / p) ^ (p - 1)) := by
    have h :=
      hconv.2 (by simp : (1 : ℝ) ∈ Set.Ici 0) hbase_nonneg
        hlam_nonneg hmu_nonneg hsum
    simpa [smul_eq_mul, hone'] using h
  have hsecond :
      t ^ (p - 1) ≤
        lam * (0 : ℝ) ^ (p - 1) + mu * ((1 / p) ^ (p - 1)) := by
    have h :=
      hconv.2 (by simp : (0 : ℝ) ∈ Set.Ici 0) h_inv_nonneg
        hlam_nonneg hmu_nonneg hsum
    simpa [smul_eq_mul, one_div, ht_as_combo'] using h
  have hzero : (0 : ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
  have hsecond' :
      (p - 1) ^ p * t ^ (p - 1) ≤
        (p - 1) ^ p * (mu * ((1 / p) ^ (p - 1))) := by
    have hcoef_nonneg : 0 ≤ (p - 1) ^ p :=
      Real.rpow_nonneg (by linarith : 0 ≤ p - 1) p
    have h2 : t ^ (p - 1) ≤ mu * ((1 / p) ^ (p - 1)) := by
      simpa [hzero] using hsecond
    exact mul_le_mul_of_nonneg_left h2 hcoef_nonneg
  have halpha : alpha p = p * (((p - 1) / p) ^ (p - 1)) :=
    alpha_eq_boundary_coeff p hp_ge
  have hsum_bound :
      (1 - t) ^ (p - 1) + (p - 1) ^ p * t ^ (p - 1) ≤
        lam + mu * (p * (((p - 1) / p) ^ (p - 1))) := by
    calc
      (1 - t) ^ (p - 1) + (p - 1) ^ p * t ^ (p - 1)
          ≤ (lam * (1 : ℝ) ^ (p - 1) + mu * (((p - 1) / p) ^ (p - 1))) +
              (p - 1) ^ p * (mu * ((1 / p) ^ (p - 1))) := by
                exact add_le_add hfirst hsecond'
      _ = lam + mu * (p * (((p - 1) / p) ^ (p - 1))) := by
          rw [Real.one_rpow]
          have hpow_split : (p - 1) ^ p = (p - 1) * (p - 1) ^ (p - 1) := by
            calc
              (p - 1) ^ p = (p - 1) ^ (1 + (p - 1)) := by
                congr 1
                ring
              _ = (p - 1) * (p - 1) ^ (p - 1) := by
                rw [Real.rpow_one_add' (by linarith : 0 ≤ p - 1)
                  (by linarith : (1 : ℝ) + (p - 1) ≠ 0)]
          rw [hpow_split]
          have hinv_pow : (1 / p) ^ (p - 1) = (p ^ (p - 1))⁻¹ := by
            rw [one_div, Real.inv_rpow hp_pos.le]
          have hbase_pow :
              ((p - 1) / p) ^ (p - 1) =
                (p - 1) ^ (p - 1) * (p ^ (p - 1))⁻¹ := by
            rw [Real.div_rpow (by linarith : 0 ≤ p - 1) hp_pos.le]
            ring
          rw [hinv_pow, hbase_pow]
          ring
  have hmix_le_alpha :
      lam + mu * (p * (((p - 1) / p) ^ (p - 1))) ≤ alpha p := by
    rw [halpha]
    have hone_le : 1 ≤ p * (((p - 1) / p) ^ (p - 1)) := by
      simpa [halpha] using one_le_alpha p hp_ge
    have hlam_le :
        lam ≤ lam * (p * (((p - 1) / p) ^ (p - 1))) := by
      have h := mul_le_mul_of_nonneg_left hone_le hlam_nonneg
      simpa using h
    calc
      lam + mu * (p * (((p - 1) / p) ^ (p - 1)))
          ≤ lam * (p * (((p - 1) / p) ^ (p - 1))) +
              mu * (p * (((p - 1) / p) ^ (p - 1))) := by
                exact add_le_add hlam_le le_rfl
      _ = (lam + mu) * (p * (((p - 1) / p) ^ (p - 1))) := by ring
      _ = p * (((p - 1) / p) ^ (p - 1)) := by rw [hsum]; ring
  exact hsum_bound.trans hmix_le_alpha

private lemma burkholder_scalar_A1
    (p t : ℝ) (hp : 2 < p) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / p) :
    (1 - t) ^ p - (p - 1) ^ p * t ^ p ≤ alpha p * (1 - p * t) := by
  let H : ℝ → ℝ := fun s =>
    (1 - s) ^ p - (p - 1) ^ p * s ^ p - alpha p * (1 - p * s)
  have hp_ge : 2 ≤ p := by linarith
  have hp_pos : 0 < p := by linarith
  have hp1_ge_one : 1 ≤ p - 1 := by linarith
  have hcont : ContinuousOn H (Set.Icc 0 (1 / p)) := by
    unfold H
    apply ContinuousOn.sub
    · apply ContinuousOn.sub
      · exact ((continuousOn_const.sub continuousOn_id).rpow_const
          (by intro s hs; exact Or.inr (by linarith : 0 ≤ p)))
      · exact continuousOn_const.mul
          (continuousOn_id.rpow_const (by intro s hs; exact Or.inr (by linarith : 0 ≤ p)))
    · exact continuousOn_const.mul
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
  have hderiv_at :
      ∀ s ∈ interior (Set.Icc 0 (1 / p)),
        HasDerivAt H
          (p * (alpha p -
            ((1 - s) ^ (p - 1) + (p - 1) ^ p * s ^ (p - 1)))) s := by
    intro s hs
    have hsI : s ∈ Set.Ioo 0 (1 / p) := by simpa [interior_Icc] using hs
    have hspos : 0 < s := hsI.1
    have hslt : s < 1 / p := hsI.2
    have h1spos : 0 < 1 - s := by
      have hhalf : 1 / p ≤ 1 := by
        field_simp [hp_pos.ne']
        linarith
      linarith
    have h_one_sub :
        HasDerivAt (fun r : ℝ => 1 - r) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub (1 : ℝ)
    have hpow1 :
        HasDerivAt (fun r : ℝ => (1 - r) ^ p)
          (p * (1 - s) ^ (p - 1) * (-1)) s := by
      have hr := (Real.hasDerivAt_rpow_const (Or.inr (by linarith : 1 ≤ p)) :
        HasDerivAt (fun u : ℝ => u ^ p) (p * (1 - s) ^ (p - 1)) (1 - s))
      exact hr.comp s h_one_sub
    have hpow2 :
        HasDerivAt (fun r : ℝ => r ^ p)
          (p * s ^ (p - 1)) s := by
      exact (Real.hasDerivAt_rpow_const (Or.inr (by linarith : 1 ≤ p)) :
        HasDerivAt (fun r : ℝ => r ^ p) (p * s ^ (p - 1)) s)
    have hlinear :
        HasDerivAt (fun r : ℝ => alpha p * (1 - p * r))
          (alpha p * (-p)) s := by
      have hbase : HasDerivAt (fun r : ℝ => 1 - p * r) (-p) s := by
        simpa using ((hasDerivAt_id s).const_mul p).const_sub (1 : ℝ)
      exact hbase.const_mul (alpha p)
    have hmain :
        HasDerivAt H
          ((p * (1 - s) ^ (p - 1) * (-1)) -
            (p - 1) ^ p * (p * s ^ (p - 1)) -
            alpha p * (-p)) s := by
      unfold H
      exact (hpow1.sub (hpow2.const_mul ((p - 1) ^ p))).sub hlinear
    refine hmain.congr_deriv ?_
    ring
  have hdiff : DifferentiableOn ℝ H (interior (Set.Icc 0 (1 / p))) := by
    intro s hs
    exact (hderiv_at s hs).differentiableAt.differentiableWithinAt
  have hderiv_nonneg :
      ∀ s ∈ interior (Set.Icc 0 (1 / p)), 0 ≤ deriv H s := by
    intro s hs
    have hsI : s ∈ Set.Ioo 0 (1 / p) := by simpa [interior_Icc] using hs
    have hspos : 0 < s := hsI.1
    have hslt : s < 1 / p := hsI.2
    have hsle : s ≤ 1 / p := le_of_lt hsI.2
    have hs_nonneg : 0 ≤ s := le_of_lt hspos
    have hderiv := hderiv_at s hs
    rw [hderiv.deriv]
    have hA :=
      burkholder_scalar_deriv_nonpos p s hp hs_nonneg hsle
    have hnonneg : 0 ≤ alpha p -
        ((1 - s) ^ (p - 1) + (p - 1) ^ p * s ^ (p - 1)) := by
      linarith
    exact mul_nonneg hp_pos.le hnonneg
  have hmono : MonotoneOn H (Set.Icc 0 (1 / p)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / p)) hcont hdiff ?_
    exact hderiv_nonneg
  have ht_mem : t ∈ Set.Icc 0 (1 / p) := ⟨ht0, ht1⟩
  have hb_mem : (1 / p) ∈ Set.Icc 0 (1 / p) := ⟨by positivity, le_rfl⟩
  have hle := hmono ht_mem hb_mem ht1
  have hHb : H (1 / p) = 0 := by
    unfold H
    have hbase1 : 1 - 1 / p = (p - 1) / p := by
      field_simp [hp_pos.ne']
    have hzero : 1 - p * (1 / p) = 0 := by
      field_simp [hp_pos.ne']
      norm_num
    rw [hbase1, hzero, mul_zero, sub_zero]
    have hpow :
        (p - 1) ^ p * (1 / p) ^ p = ((p - 1) / p) ^ p := by
      rw [Real.div_rpow (by linarith : 0 ≤ p - 1) hp_pos.le]
      rw [one_div, Real.inv_rpow hp_pos.le]
      ring
    rw [← hpow]
    ring
  have hHt : H t ≤ 0 := by
    rw [hHb] at hle
    exact hle
  unfold H at hHt
  linarith

/-- On the closed `A1` sector, the scalar inequality gives `vGeTwo ≤ uA1`. -/
private lemma vGeTwo_le_uA1_on_closureA1
    (p : ℝ) (hp : 2 < p) {x y : ℝ}
    (hA1 : closureA1 p x y) :
    vGeTwo p x y ≤ uA1 p x y := by
  rcases hA1 with ⟨hx_nonneg, hlow, hyx⟩
  rcases hx_nonneg.eq_or_lt with rfl | hxpos
  · have hy0 : y = 0 := by linarith
    subst hy0
    simp [vGeTwo, uA1, Real.zero_rpow (by linarith : p ≠ 0)]
  · have hx_nonneg' : 0 ≤ x := le_of_lt hxpos
    have hp_nonneg : 0 ≤ p := by linarith
    have hp_pos : 0 < p := by linarith
    have hp_ne : p ≠ 0 := by linarith
    have hpStar : pStar p = p := pStar_eq_self_of_two_le p (by linarith)
    have ha_eq : a p = 1 - 2 / p := by simp [a, hpStar]
    have ha_nonneg : 0 ≤ a p := by
      rw [ha_eq]
      have hdiv : 2 / p ≤ 1 := by
        field_simp [hp_pos.ne']
        linarith
      linarith
    have hy_nonneg : 0 ≤ y := by
      exact le_trans (mul_nonneg ha_nonneg hx_nonneg') hlow
    let t : ℝ := (x - y) / (2 * x)
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg (sub_nonneg.mpr hyx) (mul_nonneg (by norm_num) hx_nonneg')
    have ht1 : t ≤ 1 / p := by
      dsimp [t]
      rw [ha_eq] at hlow
      have hxy : x - y ≤ 2 * x / p := by
        have htmp : x - (1 - 2 / p) * x = 2 * x / p := by
          field_simp [hp_pos.ne']
          ring
        nlinarith
      have hden_pos : 0 < 2 * x := mul_pos (by norm_num) hxpos
      have h := div_le_div_of_nonneg_right hxy hden_pos.le
      calc
        (x - y) / (2 * x) ≤ (2 * x / p) / (2 * x) := h
        _ = 1 / p := by field_simp [hp_pos.ne', hxpos.ne']
    have ht_le_half : t ≤ 1 / 2 := by
      exact ht1.trans (by
        field_simp [hp_pos.ne']
        linarith)
    have h1mt_nonneg : 0 ≤ 1 - t := by linarith
    have hpt_nonneg : 0 ≤ 1 - p * t := by
      have hmul := mul_le_mul_of_nonneg_left ht1 hp_nonneg
      field_simp [hp_pos.ne'] at hmul
      linarith
    -- Normalize the two coordinates by `x`.
    have hsum_norm : (x + y) / 2 = x * (1 - t) := by
      dsimp [t]
      field_simp [hxpos.ne']
      ring
    have hdiff_norm : (x - y) / 2 = x * t := by
      dsimp [t]
      field_simp [hxpos.ne']
    have hlinear_norm :
        x - p * (x - y) / 2 = x * (1 - p * t) := by
      dsimp [t]
      field_simp [hxpos.ne']
    -- Rewrite `vGeTwo` as `x^p` times the normalized scalar expression.
    have hv_norm :
        vGeTwo p x y =
          x ^ p * ((1 - t) ^ p - (p - 1) ^ p * t ^ p) := by
      have hsum_nonneg : 0 ≤ (x + y) / 2 := by
        rw [hsum_norm]
        exact mul_nonneg hx_nonneg' h1mt_nonneg
      have hdiff_nonneg : 0 ≤ (x - y) / 2 := by
        rw [hdiff_norm]
        exact mul_nonneg hx_nonneg' ht0
      calc
        vGeTwo p x y =
            ((x + y) / 2) ^ p -
              (p - 1) ^ p * ((x - y) / 2) ^ p := by
                simp [vGeTwo, abs_of_nonneg hsum_nonneg, abs_of_nonneg hdiff_nonneg]
        _ = (x * (1 - t)) ^ p - (p - 1) ^ p * (x * t) ^ p := by
                rw [hsum_norm, hdiff_norm]
        _ = x ^ p * (1 - t) ^ p - (p - 1) ^ p * (x ^ p * t ^ p) := by
                rw [Real.mul_rpow hx_nonneg' h1mt_nonneg,
                  Real.mul_rpow hx_nonneg' ht0]
        _ = x ^ p * ((1 - t) ^ p - (p - 1) ^ p * t ^ p) := by ring
    -- Rewrite `uA1` in the same normalization.
    have hu_norm :
        uA1 p x y = x ^ p * (alpha p * (1 - p * t)) := by
      have hxpow : x ^ (p - 1) * x = x ^ p := by
        have h := Real.rpow_one_add' hx_nonneg'
          (by linarith : (1 : ℝ) + (p - 1) ≠ 0)
        have h' : x ^ p = x * x ^ (p - 1) := by
          simpa [show (1 : ℝ) + (p - 1) = p by ring] using h
        rw [h']
        ring
      calc
        uA1 p x y =
            alpha p * x ^ (p - 1) * (x - p * (x - y) / 2) := by
              simp [uA1, hxpos, hpStar]
        _ = alpha p * x ^ (p - 1) * (x * (1 - p * t)) := by
              rw [hlinear_norm]
        _ = x ^ p * (alpha p * (1 - p * t)) := by
              rw [← hxpow]
              ring
    have hscalar := burkholder_scalar_A1 p t hp ht0 ht1
    have hxpow_nonneg : 0 ≤ x ^ p := Real.rpow_nonneg hx_nonneg' p
    calc
      vGeTwo p x y =
          x ^ p * ((1 - t) ^ p - (p - 1) ^ p * t ^ p) := hv_norm
      _ ≤ x ^ p * (alpha p * (1 - p * t)) :=
          mul_le_mul_of_nonneg_left hscalar hxpow_nonneg
      _ = uA1 p x y := hu_norm.symm

/-- `vGeTwo` is invariant under the central symmetry `(x, y) ↦ (-x, -y)`. -/
private lemma vGeTwo_neg_neg (p x y : ℝ) :
    vGeTwo p (-x) (-y) = vGeTwo p x y := by
  have hsum : ((-x + -y) / 2 : ℝ) = -((x + y) / 2) := by ring
  have hdiff : ((-x + y) / 2 : ℝ) = -((x - y) / 2) := by ring
  simp [vGeTwo, hsum, hdiff]

/-- `vGeTwo` is invariant under swapping the two coordinates. -/
private lemma vGeTwo_swap (p x y : ℝ) :
    vGeTwo p y x = vGeTwo p x y := by
  have hsum : ((y + x) / 2 : ℝ) = (x + y) / 2 := by ring
  have hdiff : ((y - x) / 2 : ℝ) = -((x - y) / 2) := by ring
  simp [vGeTwo, hsum, hdiff]

/-- On the `A2` branch the pointwise majorization is equality by construction. -/
private lemma vGeTwo_le_auxFunction1_on_closureA2
    (p : ℝ) (hp : 2 ≤ p) {x y : ℝ} (h2 : closureA2 p x y) :
    vGeTwo p x y ≤ auxFunction1 p x y := by
  rw [auxFunction1_eq_vGeTwo p hp x y h2]

/--
First-quadrant reduction for the pointwise majorization.

Inside the first quadrant cone, every point is either in the closed `A2`
sector, where `auxFunction1 = vGeTwo`, or in the complementary closed `A1`
sector, where the remaining scalar Burkholder inequality must be supplied by
`hA1`.
-/
private lemma vGeTwo_le_auxFunction1_on_QuarterPlane_of_A1
    (p : ℝ) (hp : 2 ≤ p)
    (hA1 : ∀ ⦃x y : ℝ⦄, closureA1 p x y → vGeTwo p x y ≤ uA1 p x y)
    {x y : ℝ} (hQ : QuarterPlane x y) :
    vGeTwo p x y ≤ auxFunction1 p x y := by
  by_cases h1 : closureA1 p x y
  · exact (hA1 h1).trans_eq (auxFunction1_eq_uA1 p x y h1).symm
  · have h2 : closureA2 p x y := by
      rcases hQ with ⟨hx, hyx, hnegx_y⟩
      have hy_le_ax : y ≤ a p * x := by
        by_contra hy_not
        have hax_le_y : a p * x ≤ y := le_of_not_ge hy_not
        exact h1 ⟨hx, hax_le_y, hyx⟩
      exact ⟨hx, hnegx_y, hy_le_ax⟩
    exact vGeTwo_le_auxFunction1_on_closureA2 p hp h2

/--
Global reduction for `vGeTwo ≤ uCandidate`.

The four quadrant branches of `uCandidate` are reflected copies of
`auxFunction1`.  Since `vGeTwo` is invariant under the same reflections, a
first-quadrant proof gives the whole-plane proof.
-/
private lemma vGeTwo_le_uCandidate_of_A1
    (p : ℝ) (hp : 2 ≤ p)
    (hA1 : ∀ ⦃x y : ℝ⦄, closureA1 p x y → vGeTwo p x y ≤ uA1 p x y)
    (x y : ℝ) :
    vGeTwo p x y ≤ uCandidate p x y := by
  rcases mem_some_QuarterPlane x y with hQ1 | hrest
  · rw [uCandidate_eq_Q1 p hQ1]
    exact vGeTwo_le_auxFunction1_on_QuarterPlane_of_A1 p hp hA1 hQ1
  rcases hrest with hQ2 | hrest
  · have hQ : QuarterPlane (-x) (-y) := ⟨by linarith [hQ2.1], by linarith [hQ2.2.2],
      by linarith [hQ2.2.1]⟩
    rw [uCandidate_eq_Q2 p hQ2, ← vGeTwo_neg_neg p x y]
    exact vGeTwo_le_auxFunction1_on_QuarterPlane_of_A1 p hp hA1 hQ
  rcases hrest with hQ3 | hQ4
  · have hQ : QuarterPlane y x := ⟨hQ3.1, hQ3.2.2, hQ3.2.1⟩
    rw [uCandidate_eq_Q3 p hQ3, ← vGeTwo_swap p x y]
    exact vGeTwo_le_auxFunction1_on_QuarterPlane_of_A1 p hp hA1 hQ
  · have hQ : QuarterPlane (-y) (-x) := ⟨by linarith [hQ4.1], by linarith [hQ4.2.1],
      by linarith [hQ4.2.2]⟩
    have hv : vGeTwo p (-y) (-x) = vGeTwo p x y := by
      rw [vGeTwo_neg_neg p y x, vGeTwo_swap p y x]
    rw [uCandidate_eq_Q4 p hQ4, ← hv]
    exact vGeTwo_le_auxFunction1_on_QuarterPlane_of_A1 p hp hA1 hQ

/--
The candidate dominates the Burkholder expression on the whole plane.

The proof is now purely geometric: the first-quadrant `A2` sector is equality,
the first-quadrant `A1` sector is handled by the normalized scalar inequality,
and all other quadrants follow from the symmetries in `uCandidate`.
-/
private lemma vGeTwo_le_uCandidate
    (p : ℝ) (hp : 2 < p) (x y : ℝ) :
    vGeTwo p x y ≤ uCandidate p x y := by
  exact vGeTwo_le_uCandidate_of_A1 p (by linarith)
    (fun {x y} hA1 => vGeTwo_le_uA1_on_closureA1 p hp hA1) x y


/-! ## 12. uCandidate(p,x,y) <0 If  xy=0 e (x,y) ≠ (0,0)  -/

private lemma uCandidate_le_zero_of_xy_zero
    (p x y : ℝ) (hp : 2 ≤ p)
    (hxy : x * y = 0) :
    uCandidate p x y ≤ 0 := by
  have hv_axis : ∀ t : ℝ, vGeTwo p t 0 ≤ 0 := by
    intro t
    have hp_nonneg : 0 ≤ p := by linarith
    have hbase : (1 : ℝ) ≤ p - 1 := by linarith
    have hpow : (1 : ℝ) ≤ Real.rpow (p - 1) p := by
      simpa [Real.one_rpow] using
        (Real.rpow_le_rpow
          (by norm_num : (0 : ℝ) ≤ 1) hbase hp_nonneg)
    have hA_nonneg : 0 ≤ Real.rpow (|t / 2|) p :=
      Real.rpow_nonneg (abs_nonneg (t / 2)) p
    have hle :
        Real.rpow (|t / 2|) p ≤
          Real.rpow (p - 1) p * Real.rpow (|t / 2|) p := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hpow hA_nonneg
    have hsum : ((t + 0) / 2 : ℝ) = t / 2 := by ring
    have hdiff : ((t - 0) / 2 : ℝ) = t / 2 := by ring
    simpa [vGeTwo, hsum, hdiff] using sub_nonpos.mpr hle
  have haux_axis : ∀ t : ℝ, 0 ≤ t → auxFunction1 p t 0 ≤ 0 := by
    intro t ht
    have h2 : closureA2 p t 0 := by
      refine ⟨ht, by linarith, ?_⟩
      exact mul_nonneg (a_nonneg_of_two_le p hp) ht
    rw [auxFunction1_eq_vGeTwo p hp t 0 h2]
    exact hv_axis t
  rcases mem_some_QuarterPlane x y with hQ1 | hrest
  · rw [uCandidate_eq_Q1 p hQ1]
    have hy0 : y = 0 := by
      rcases mul_eq_zero.mp hxy with hx0 | hy0
      · have hy_le : y ≤ 0 := by simpa [hx0] using hQ1.2.1
        have hy_ge : 0 ≤ y := by simpa [hx0] using hQ1.2.2
        exact le_antisymm hy_le hy_ge
      · exact hy0
    subst y
    exact haux_axis x hQ1.1
  rcases hrest with hQ2 | hrest
  · rw [uCandidate_eq_Q2 p hQ2]
    have hy0 : y = 0 := by
      rcases mul_eq_zero.mp hxy with hx0 | hy0
      · have hy_le : y ≤ 0 := by simpa [hx0] using hQ2.2.1
        have hy_ge : 0 ≤ y := by simpa [hx0] using hQ2.2.2
        exact le_antisymm hy_le hy_ge
      · exact hy0
    subst y
    have ht : 0 ≤ -x := by linarith [hQ2.1]
    simpa using haux_axis (-x) ht
  rcases hrest with hQ3 | hQ4
  · rw [uCandidate_eq_Q3 p hQ3]
    have hx0 : x = 0 := by
      rcases mul_eq_zero.mp hxy with hx0 | hy0
      · exact hx0
      · have hx_ge : 0 ≤ x := by simpa [hy0] using hQ3.2.1
        have hx_le : x ≤ 0 := by simpa [hy0] using hQ3.2.2
        exact le_antisymm hx_le hx_ge
    subst x
    exact haux_axis y hQ3.1
  · rw [uCandidate_eq_Q4 p hQ4]
    have hx0 : x = 0 := by
      rcases mul_eq_zero.mp hxy with hx0 | hy0
      · exact hx0
      · have hx_ge : 0 ≤ x := by simpa [hy0] using hQ4.2.1
        have hx_le : x ≤ 0 := by simpa [hy0] using hQ4.2.2
        exact le_antisymm hx_le hx_ge
    subst x
    have ht : 0 ≤ -y := by linarith [hQ4.1]
    simpa using haux_axis (-y) ht

private lemma vGeTwo_le_zero_of_mul_nonpos
    (p x y : ℝ) (hp : 2 ≤ p) (hxy : x * y ≤ 0) :
    vGeTwo p x y ≤ 0 := by
  have hp_nonneg : 0 ≤ p := by linarith
  have hp1_nonneg : 0 ≤ p - 1 := by linarith
  have hp1_one : (1 : ℝ) ≤ p - 1 := by linarith
  have hsq : ((x + y) / 2) ^ 2 ≤ ((x - y) / 2) ^ 2 := by
    nlinarith
  have habs : |(x + y) / 2| ≤ |(x - y) / 2| := sq_le_sq.mp hsq
  have hpow :
      Real.rpow (|(x + y) / 2|) p ≤ Real.rpow (|(x - y) / 2|) p :=
    Real.rpow_le_rpow (abs_nonneg _) habs hp_nonneg
  have hcoef_ge_one : (1 : ℝ) ≤ Real.rpow (p - 1) p := by
    simpa [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hp1_one hp_nonneg
  have hdiff_nonneg : 0 ≤ Real.rpow (|(x - y) / 2|) p :=
    Real.rpow_nonneg (abs_nonneg _) _
  have hmul :
      Real.rpow (|(x - y) / 2|) p ≤
        Real.rpow (p - 1) p * Real.rpow (|(x - y) / 2|) p := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hcoef_ge_one hdiff_nonneg
  exact sub_nonpos.mpr (hpow.trans hmul)

private lemma auxFunction1_le_zero_of_QuarterPlane_mul_nonpos
    (p x y : ℝ) (hp : 2 ≤ p) (hQ : QuarterPlane x y) (hxy : x * y ≤ 0) :
    auxFunction1 p x y ≤ 0 := by
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp
  have hy_nonpos : y ≤ 0 := by
    by_contra hy_not
    have hy_pos : 0 < y := lt_of_not_ge hy_not
    have hx_pos : 0 < x := lt_of_lt_of_le hy_pos hQ.2.1
    have hprod_pos : 0 < x * y := mul_pos hx_pos hy_pos
    linarith
  have hA2 : closureA2 p x y := by
    refine ⟨hQ.1, hQ.2.2, ?_⟩
    exact le_trans hy_nonpos (mul_nonneg ha_nonneg hQ.1)
  rw [auxFunction1_eq_vGeTwo p hp x y hA2]
  exact vGeTwo_le_zero_of_mul_nonpos p x y hp hxy

private lemma uCandidate_le_zero_of_mul_nonpos
    (p x y : ℝ) (hp : 2 ≤ p) (hxy : x * y ≤ 0) :
    uCandidate p x y ≤ 0 := by
  rcases mem_some_QuarterPlane x y with hQ1 | hrest
  · rw [uCandidate_eq_Q1 p hQ1]
    exact auxFunction1_le_zero_of_QuarterPlane_mul_nonpos p x y hp hQ1 hxy
  rcases hrest with hQ2 | hrest
  · have hQ : QuarterPlane (-x) (-y) := ⟨by linarith [hQ2.1], by linarith [hQ2.2.2],
      by linarith [hQ2.2.1]⟩
    have hxy' : (-x) * (-y) ≤ 0 := by nlinarith
    rw [uCandidate_eq_Q2 p hQ2]
    exact auxFunction1_le_zero_of_QuarterPlane_mul_nonpos p (-x) (-y) hp hQ hxy'
  rcases hrest with hQ3 | hQ4
  · have hQ : QuarterPlane y x := ⟨hQ3.1, hQ3.2.2, hQ3.2.1⟩
    have hxy' : y * x ≤ 0 := by nlinarith
    rw [uCandidate_eq_Q3 p hQ3]
    exact auxFunction1_le_zero_of_QuarterPlane_mul_nonpos p y x hp hQ hxy'
  · have hQ : QuarterPlane (-y) (-x) := ⟨by linarith [hQ4.1], by linarith [hQ4.2.1],
      by linarith [hQ4.2.2]⟩
    have hxy' : (-y) * (-x) ≤ 0 := by nlinarith
    rw [uCandidate_eq_Q4 p hQ4]
    exact auxFunction1_le_zero_of_QuarterPlane_mul_nonpos p (-y) (-x) hp hQ hxy'


private lemma uCandidate_le_zero_of_mul_neg
    (p x y : ℝ) (hp : 2 < p) (hxy : x * y = 0) (hnzero : (x, y) ≠ (0, 0)) :
    uCandidate p x y < 0 := by
  have hp' : 2 ≤ p := by linarith
  have hv_axis : ∀ t : ℝ, t ≠ 0 → vGeTwo p t 0 < 0 := by
    intro t htne
    have hp_pos : 0 < p := by linarith
    have hcoef_gt_one : (1 : ℝ) < Real.rpow (p - 1) p := by
      exact Real.one_lt_rpow (by linarith : (1 : ℝ) < p - 1) hp_pos
    have hbase_pos : 0 < |t / 2| := by
      exact abs_pos.mpr (by
        intro hdiv
        apply htne
        nlinarith)
    have hA_pos : 0 < Real.rpow (|t / 2|) p :=
      Real.rpow_pos_of_pos hbase_pos p
    have hlt :
        Real.rpow (|t / 2|) p <
          Real.rpow (p - 1) p * Real.rpow (|t / 2|) p := by
      simpa [one_mul] using mul_lt_mul_of_pos_right hcoef_gt_one hA_pos
    have hsum : ((t + 0) / 2 : ℝ) = t / 2 := by ring
    have hdiff : ((t - 0) / 2 : ℝ) = t / 2 := by ring
    simpa [vGeTwo, hsum, hdiff] using sub_neg.mpr hlt
  have haux_axis : ∀ t : ℝ, 0 ≤ t → t ≠ 0 → auxFunction1 p t 0 < 0 := by
    intro t ht htne
    have h2 : closureA2 p t 0 := by
      refine ⟨ht, by linarith, ?_⟩
      exact mul_nonneg (a_nonneg_of_two_le p hp') ht
    rw [auxFunction1_eq_vGeTwo p hp' t 0 h2]
    exact hv_axis t htne
  rcases mem_some_QuarterPlane x y with hQ1 | hrest
  · rw [uCandidate_eq_Q1 p hQ1]
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
  · rw [uCandidate_eq_Q2 p hQ2]
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
  · rw [uCandidate_eq_Q3 p hQ3]
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
  · rw [uCandidate_eq_Q4 p hQ4]
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

private lemma DyuCandidate_neg_neg
    (p : ℝ) (hp : 2 < p) (x y : ℝ) :
    DyuCandidate p x y = -DyuCandidate p (-x) (-y) := by
  rcases mem_some_QuarterPlane x y with hQ1 | hrest
  · have hQ2 : QuarterPlane2 (-x) (-y) := ⟨by linarith [hQ1.1],
      by linarith [hQ1.2.2], by linarith [hQ1.2.1]⟩
    rw [DyuCandidate_eq_Q1 p hQ1, DyuCandidate_eq_Q2 p hQ2]
    simp
  rcases hrest with hQ2 | hrest
  · have hQ1 : QuarterPlane (-x) (-y) := ⟨by linarith [hQ2.1],
      by linarith [hQ2.2.2], by linarith [hQ2.2.1]⟩
    rw [DyuCandidate_eq_Q2 p hQ2, DyuCandidate_eq_Q1 p hQ1]
  rcases hrest with hQ3 | hQ4
  · have hQ4 : QuarterPlane4 (-x) (-y) := ⟨by linarith [hQ3.1],
      by linarith [hQ3.2.2], by linarith [hQ3.2.1]⟩
    rw [DyuCandidate_eq_Q3 p hp hQ3, DyuCandidate_eq_Q4 p hp hQ4]
    simp
  · have hQ3 : QuarterPlane3 (-x) (-y) := ⟨by linarith [hQ4.1],
      by linarith [hQ4.2.2], by linarith [hQ4.2.1]⟩
    rw [DyuCandidate_eq_Q4 p hp hQ4, DyuCandidate_eq_Q3 p hp hQ3]

private lemma alpha_nonneg_of_two_le (p : ℝ) (hp : 2 ≤ p) : 0 ≤ alpha p := by
  exact le_trans zero_le_one (one_le_alpha p hp)

private lemma DyuA1_mono_x_of_pos
    (p : ℝ) (hp : 2 ≤ p) {x z y : ℝ}
    (hx : 0 < x) (hxz : x ≤ z) :
    DyuA1 p x y ≤ DyuA1 p z y := by
  have hz : 0 < z := lt_of_lt_of_le hx hxz
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hpow : x ^ (p - 1) ≤ z ^ (p - 1) :=
    Real.rpow_le_rpow hx.le hxz (by linarith : 0 ≤ p - 1)
  have hcoef : 0 ≤ alpha p * (p / 2) := by
    exact mul_nonneg (alpha_nonneg_of_two_le p hp) (by linarith : 0 ≤ p / 2)
  simp [DyuA1, hx, hz, hpStar]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left hpow hcoef

private lemma DxuA1_mono_y_of_pos
    (p : ℝ) (hp : 2 ≤ p) {x y z : ℝ}
    (hx : 0 < x) (hyz : y ≤ z) :
    DxuA1 p x y ≤ DxuA1 p x z := by
  have hpStar : pStar p = p := pStar_eq_self_of_two_le p hp
  have hcoef :
      0 ≤ alpha p * (p / 2) * x ^ (p - 2) := by
    exact mul_nonneg
      (mul_nonneg (alpha_nonneg_of_two_le p hp) (by linarith : 0 ≤ p / 2))
      (Real.rpow_nonneg hx.le _)
  have hlin :
      (2 - p) * x + (p - 1) * y ≤
        (2 - p) * x + (p - 1) * z := by
    linarith [mul_le_mul_of_nonneg_left hyz (by linarith : 0 ≤ p - 1)]
  simp only [DxuA1, gt_iff_lt, hx, ↓reduceIte, Real.rpow_eq_pow, ge_iff_le]
  exact mul_le_mul_of_nonneg_left hlin hcoef

private lemma DyvGeTwo_mono_x_of_pos
    (p : ℝ) (hp : 2 ≤ p) {x z y : ℝ}
    (hxpos : 0 < x)
    (hsum_x : 0 ≤ (x + y) / 2) (hdiff_x : 0 ≤ (x - y) / 2)
    (hxz : x ≤ z) :
    DyvGeTwo p x y ≤ DyvGeTwo p z y := by
  have hp_exp : 0 ≤ p - 1 := by linarith
  have hsum_le : (x + y) / 2 ≤ (z + y) / 2 := by linarith
  have hdiff_le : (x - y) / 2 ≤ (z - y) / 2 := by linarith
  have hsum_z : 0 ≤ (z + y) / 2 := le_trans hsum_x hsum_le
  have hdiff_z : 0 ≤ (z - y) / 2 := le_trans hdiff_x hdiff_le
  have hA := Real.rpow_le_rpow hsum_x hsum_le hp_exp
  have hB := Real.rpow_le_rpow hdiff_x hdiff_le hp_exp
  have hcoef : 0 ≤ (p - 1) ^ p := Real.rpow_nonneg (by linarith : 0 ≤ p - 1) _
  have hhalf : 0 ≤ p / 2 := by linarith
  have hzpos : 0 < z := lt_of_lt_of_le hxpos hxz
  simp [DyvGeTwo, hxpos, hzpos, abs_of_nonneg hsum_x, abs_of_nonneg hsum_z,
    abs_of_nonneg hdiff_x, abs_of_nonneg hdiff_z]
  nlinarith [mul_le_mul_of_nonneg_right hA hhalf,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hcoef) hhalf]

private lemma DxvGeTwo_mono_y_of_pos
    (p : ℝ) (hp : 2 ≤ p) {x y z : ℝ}
    (hxpos : 0 < x)
    (hsum_y : 0 ≤ (x + y) / 2) (hdiff_z : 0 ≤ (x - z) / 2)
    (hyz : y ≤ z) :
    DxvGeTwo p x y ≤ DxvGeTwo p x z := by
  have hp_exp : 0 ≤ p - 1 := by linarith
  have hsum_le : (x + y) / 2 ≤ (x + z) / 2 := by linarith
  have hdiff_le : (x - z) / 2 ≤ (x - y) / 2 := by linarith
  have hsum_z : 0 ≤ (x + z) / 2 := le_trans hsum_y hsum_le
  have hdiff_y : 0 ≤ (x - y) / 2 := le_trans hdiff_z hdiff_le
  have hA := Real.rpow_le_rpow hsum_y hsum_le hp_exp
  have hB := Real.rpow_le_rpow hdiff_z hdiff_le hp_exp
  have hcoef : 0 ≤ (p - 1) ^ p := Real.rpow_nonneg (by linarith : 0 ≤ p - 1) _
  have hhalf : 0 ≤ p / 2 := by linarith
  simp [DxvGeTwo, hxpos, abs_of_nonneg hsum_y, abs_of_nonneg hsum_z,
    abs_of_nonneg hdiff_y, abs_of_nonneg hdiff_z]
  nlinarith [mul_le_mul_of_nonneg_right hA hhalf,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hcoef) hhalf]

private lemma DyuCandidate_mono_x_on_Q2
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hz_upper : z ≤ -y) (hxz : x ≤ z) :
    DyuCandidate p x y ≤ DyuCandidate p z y := by
  have hp' : 2 ≤ p := by linarith
  have hQx : QuarterPlane2 x y := ⟨by linarith, by linarith, by linarith⟩
  have hQz : QuarterPlane2 z y := ⟨by linarith, by linarith, by linarith⟩
  have hclx : closureA2 p (-x) (-y) := by
    refine ⟨by linarith, by linarith, ?_⟩
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
    exact le_trans (by linarith : -y ≤ 0) (mul_nonneg ha_nonneg (by linarith : 0 ≤ -x))
  have hclz : closureA2 p (-z) (-y) := by
    refine ⟨by linarith, by linarith, ?_⟩
    have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
    exact le_trans (by linarith : -y ≤ 0) (mul_nonneg ha_nonneg (by linarith : 0 ≤ -z))
  have hx_eq : DyuCandidate p x y = -DyvGeTwo p (-x) (-y) := by
    rw [DyuCandidate_eq_Q2 p hQx]
    exact congrArg Neg.neg (auxFunction1_Dy_eq_DyvGeTwo p hp' (-x) (-y) hclx)
  have hz_eq : DyuCandidate p z y = -DyvGeTwo p (-z) (-y) := by
    rw [DyuCandidate_eq_Q2 p hQz]
    exact congrArg Neg.neg (auxFunction1_Dy_eq_DyvGeTwo p hp' (-z) (-y) hclz)
  have hmono :
      DyvGeTwo p (-z) (-y) ≤ DyvGeTwo p (-x) (-y) := by
    exact DyvGeTwo_mono_x_of_pos p hp'
      (by linarith) (by linarith) (by linarith) (by linarith)
  rw [hx_eq, hz_eq]
  linarith

private lemma DyuCandidate_mono_x_on_Q3_A2
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : -y ≤ x) (hz_upper : z ≤ a p * y)
    (hxz : x ≤ z) :
    DyuCandidate p x y ≤ DyuCandidate p z y := by
  have hp' : 2 ≤ p := by linarith
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
  have ha_le_y : a p * y ≤ y :=
    (mul_le_mul_of_nonneg_right (a_lt_one_of_two_le p hp').le hy_pos.le).trans_eq
      (one_mul y)
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, hx_lower,
    le_trans (le_trans hxz hz_upper)
      ((mul_le_mul_of_nonneg_right (a_lt_one_of_two_le p hp').le hy_pos.le).trans_eq
        (one_mul y))⟩
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, le_trans hx_lower hxz,
    le_trans hz_upper
      ((mul_le_mul_of_nonneg_right (a_lt_one_of_two_le p hp').le hy_pos.le).trans_eq
        (one_mul y))⟩
  have hclx : closureA2 p y x := ⟨hy_pos.le, hx_lower, hz_upper.trans' hxz⟩
  have hclz : closureA2 p y z := ⟨hy_pos.le, le_trans hx_lower hxz, hz_upper⟩
  have hx_eq : DyuCandidate p x y = DxvGeTwo p y x := by
    rw [DyuCandidate_eq_Q3 p hp hQx]
    exact auxFunction1_Dx_eq_DxvGeTwo p hp' y x hclx
  have hz_eq : DyuCandidate p z y = DxvGeTwo p y z := by
    rw [DyuCandidate_eq_Q3 p hp hQz]
    exact auxFunction1_Dx_eq_DxvGeTwo p hp' y z hclz
  rw [hx_eq, hz_eq]
  exact DxvGeTwo_mono_y_of_pos p hp' hy_pos (by linarith) (by
    have haz_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    have hz_le_y : z ≤ y := le_trans hz_upper ha_le_y
    linarith) hxz

private lemma DyuCandidate_mono_x_on_Q3_A1
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : a p * y ≤ x) (hz_upper : z ≤ y)
    (hxz : x ≤ z) :
    DyuCandidate p x y ≤ DyuCandidate p z y := by
  have hp' : 2 ≤ p := by linarith
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
  have hQx : QuarterPlane3 x y := ⟨hy_pos.le, by
      have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith, le_trans hxz hz_upper⟩
  have hQz : QuarterPlane3 z y := ⟨hy_pos.le, by
      have haxy_nonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
      linarith, hz_upper⟩
  have hclx : closureA1 p y x := ⟨hy_pos.le, hx_lower, le_trans hxz hz_upper⟩
  have hclz : closureA1 p y z := ⟨hy_pos.le, le_trans hx_lower hxz, hz_upper⟩
  have hx_eq : DyuCandidate p x y = DxuA1 p y x := by
    rw [DyuCandidate_eq_Q3 p hp hQx]
    exact auxFunction1_Dx_eq_DxuA1 p y x hclx
  have hz_eq : DyuCandidate p z y = DxuA1 p y z := by
    rw [DyuCandidate_eq_Q3 p hp hQz]
    exact auxFunction1_Dx_eq_DxuA1 p y z hclz
  rw [hx_eq, hz_eq]
  exact DxuA1_mono_y_of_pos p hp' hy_pos hxz

private lemma DyuCandidate_mono_x_on_Q1_A1
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hyx : y ≤ x) (hz_upper : z ≤ y / a p)
    (hxz : x ≤ z) :
    DyuCandidate p x y ≤ DyuCandidate p z y := by
  have hp' : 2 ≤ p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  have hQx : QuarterPlane x y := ⟨(lt_of_lt_of_le hy_pos hyx).le, hyx, by linarith⟩
  have hQz : QuarterPlane z y := ⟨(lt_of_lt_of_le hy_pos (le_trans hyx hxz)).le,
    le_trans hyx hxz, by linarith⟩
  have hclx : closureA1 p x y := by
    refine ⟨(lt_of_lt_of_le hy_pos hyx).le, ?_, hyx⟩
    have hmul := mul_le_mul_of_nonneg_left (le_trans hxz hz_upper) ha_pos.le
    have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
    simpa [hac] using hmul
  have hclz : closureA1 p z y := by
    refine ⟨(lt_of_lt_of_le hy_pos (le_trans hyx hxz)).le, ?_, le_trans hyx hxz⟩
    have hmul := mul_le_mul_of_nonneg_left hz_upper ha_pos.le
    have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
    simpa [hac] using hmul
  have hx_eq : DyuCandidate p x y = DyuA1 p x y := by
    rw [DyuCandidate_eq_Q1 p hQx]
    exact auxFunction1_Dy_eq_DyuA1 p x y hclx
  have hz_eq : DyuCandidate p z y = DyuA1 p z y := by
    rw [DyuCandidate_eq_Q1 p hQz]
    exact auxFunction1_Dy_eq_DyuA1 p z y hclz
  rw [hx_eq, hz_eq]
  exact DyuA1_mono_x_of_pos p hp' (lt_of_lt_of_le hy_pos hyx) hxz

private lemma DyuCandidate_mono_x_on_Q1_A2
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hx_lower : y / a p ≤ x) (hxz : x ≤ z) :
    DyuCandidate p x y ≤ DyuCandidate p z y := by
  have hp' : 2 ≤ p := by linarith
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  have hx_pos : 0 < x := by
    exact lt_of_lt_of_le (div_pos hy_pos ha_pos) hx_lower
  have hz_pos : 0 < z := lt_of_lt_of_le hx_pos hxz
  have hQx : QuarterPlane x y := ⟨hx_pos.le, by
      have ha_lt : a p < 1 := a_lt_one_of_two_le p hp'
      have hy_lt_div : y < y / a p := by
        rw [div_eq_mul_inv]
        have hlt_inv : 1 < (a p)⁻¹ := by
          rw [one_lt_inv₀ ha_pos]
          exact ha_lt
        nlinarith
      exact le_trans hy_lt_div.le hx_lower, by linarith⟩
  have hQz : QuarterPlane z y := ⟨hz_pos.le, le_trans hQx.2.1 hxz, by linarith⟩
  have hclx : closureA2 p x y := by
    refine ⟨hx_pos.le, by linarith, ?_⟩
    have hmul := mul_le_mul_of_nonneg_left hx_lower ha_pos.le
    have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
    simpa [hac] using hmul
  have hclz : closureA2 p z y := by
    refine ⟨hz_pos.le, by linarith, ?_⟩
    have hmul := mul_le_mul_of_nonneg_left (le_trans hx_lower hxz) ha_pos.le
    have hac : a p * (y / a p) = y := by field_simp [ha_pos.ne']
    simpa [hac] using hmul
  have hx_eq : DyuCandidate p x y = DyvGeTwo p x y := by
    rw [DyuCandidate_eq_Q1 p hQx]
    exact auxFunction1_Dy_eq_DyvGeTwo p hp' x y hclx
  have hz_eq : DyuCandidate p z y = DyvGeTwo p z y := by
    rw [DyuCandidate_eq_Q1 p hQz]
    exact auxFunction1_Dy_eq_DyvGeTwo p hp' z y hclz
  rw [hx_eq, hz_eq]
  exact DyvGeTwo_mono_x_of_pos p hp' hx_pos (by linarith) (by
    have ha_lt : a p < 1 := a_lt_one_of_two_le p hp'
    have hy_lt_div : y < y / a p := by
      rw [div_eq_mul_inv]
      have hlt_inv : 1 < (a p)⁻¹ := by
        rw [one_lt_inv₀ ha_pos]
        exact ha_lt
      nlinarith
    linarith) hxz

private lemma DyuCandidate_mono_x_of_y_pos
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hy_pos : 0 < y) (hxz : x ≤ z) :
    DyuCandidate p x y ≤ DyuCandidate p z y := by
  have hp' : 2 ≤ p := by linarith
  have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
  have ha_lt : a p < 1 := a_lt_one_of_two_le p hp'
  have ha_pos : 0 < a p := a_pos_of_two_lt p hp
  have hneg_le_a : -y ≤ a p * y := by
    have hnonneg : 0 ≤ a p * y := mul_nonneg ha_nonneg hy_pos.le
    linarith
  have ha_le_y : a p * y ≤ y :=
    (mul_le_mul_of_nonneg_right ha_lt.le hy_pos.le).trans_eq (one_mul y)
  have hy_le_div : y ≤ y / a p := by
    have hy_lt_div : y < y / a p := by
      rw [div_eq_mul_inv]
      have hlt_inv : 1 < (a p)⁻¹ := by
        rw [one_lt_inv₀ ha_pos]
        exact ha_lt
      nlinarith
    exact hy_lt_div.le
  by_cases hz_q2 : z ≤ -y
  · exact DyuCandidate_mono_x_on_Q2 p hp hy_pos hz_q2 hxz
  have hz_gt_q2 : -y < z := lt_of_not_ge hz_q2
  by_cases hz_q3a2 : z ≤ a p * y
  · by_cases hx_q2 : x ≤ -y
    · exact le_trans (DyuCandidate_mono_x_on_Q2 p hp hy_pos le_rfl hx_q2)
        (DyuCandidate_mono_x_on_Q3_A2 p hp hy_pos le_rfl hz_q3a2 hz_gt_q2.le)
    · exact DyuCandidate_mono_x_on_Q3_A2 p hp hy_pos (le_of_lt (lt_of_not_ge hx_q2))
        hz_q3a2 hxz
  have hz_gt_q3a2 : a p * y < z := lt_of_not_ge hz_q3a2
  have to_q3_boundary_of_x_le_a (hx_a : x ≤ a p * y) :
      DyuCandidate p x y ≤ DyuCandidate p (a p * y) y := by
    by_cases hx_q2 : x ≤ -y
    · exact le_trans (DyuCandidate_mono_x_on_Q2 p hp hy_pos le_rfl hx_q2)
        (DyuCandidate_mono_x_on_Q3_A2 p hp hy_pos le_rfl le_rfl hneg_le_a)
    · exact DyuCandidate_mono_x_on_Q3_A2 p hp hy_pos
        (le_of_lt (lt_of_not_ge hx_q2)) le_rfl hx_a
  by_cases hz_q3a1 : z ≤ y
  · by_cases hx_a : x ≤ a p * y
    · exact le_trans (to_q3_boundary_of_x_le_a hx_a)
        (DyuCandidate_mono_x_on_Q3_A1 p hp hy_pos le_rfl hz_q3a1 (le_of_lt hz_gt_q3a2))
    · exact DyuCandidate_mono_x_on_Q3_A1 p hp hy_pos
        (le_of_lt (lt_of_not_ge hx_a)) hz_q3a1 hxz
  have hz_gt_y : y < z := lt_of_not_ge hz_q3a1
  have to_diag_of_x_le_y (hx_y_bound : x ≤ y) :
      DyuCandidate p x y ≤ DyuCandidate p y y := by
    by_cases hx_a : x ≤ a p * y
    · exact le_trans (to_q3_boundary_of_x_le_a hx_a)
        (DyuCandidate_mono_x_on_Q3_A1 p hp hy_pos le_rfl le_rfl ha_le_y)
    · exact DyuCandidate_mono_x_on_Q3_A1 p hp hy_pos
        (le_of_lt (lt_of_not_ge hx_a)) le_rfl hx_y_bound
  by_cases hz_q1a1 : z ≤ y / a p
  · by_cases hx_y : x ≤ y
    · exact le_trans (to_diag_of_x_le_y hx_y)
        (DyuCandidate_mono_x_on_Q1_A1 p hp hy_pos le_rfl hz_q1a1 hz_gt_y.le)
    · exact DyuCandidate_mono_x_on_Q1_A1 p hp hy_pos
        (le_of_lt (lt_of_not_ge hx_y)) hz_q1a1 hxz
  have hz_gt_div : y / a p < z := lt_of_not_ge hz_q1a1
  have to_q1_boundary_of_x_le_div (hx_div_bound : x ≤ y / a p) :
      DyuCandidate p x y ≤ DyuCandidate p (y / a p) y := by
    by_cases hx_y : x ≤ y
    · exact le_trans (to_diag_of_x_le_y hx_y)
        (DyuCandidate_mono_x_on_Q1_A1 p hp hy_pos le_rfl le_rfl hy_le_div)
    · exact DyuCandidate_mono_x_on_Q1_A1 p hp hy_pos
        (le_of_lt (lt_of_not_ge hx_y)) le_rfl hx_div_bound
  by_cases hx_div : x ≤ y / a p
  · exact le_trans (to_q1_boundary_of_x_le_div hx_div)
      (DyuCandidate_mono_x_on_Q1_A2 p hp hy_pos le_rfl (le_of_lt hz_gt_div))
  · exact DyuCandidate_mono_x_on_Q1_A2 p hp hy_pos
      (le_of_lt (lt_of_not_ge hx_div)) hxz

private lemma DyvGeTwo_axis_nonneg
    (p : ℝ) (hp : 2 ≤ p) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ DyvGeTwo p x 0 := by
  rcases hx.eq_or_lt with rfl | hx_pos
  · simp [DyvGeTwo]
  · have hsum : 0 ≤ (x + 0) / 2 := by linarith
    have hdiff : 0 ≤ (x - 0) / 2 := by linarith
    have hbase : 0 ≤ |x / 2| ^ (p - 1) := Real.rpow_nonneg (abs_nonneg _) _
    have hcoef : 0 ≤ (p - 1) ^ p := Real.rpow_nonneg (by linarith : 0 ≤ p - 1) _
    have hhalf : 0 ≤ p / 2 := by linarith
    simp [DyvGeTwo, hx_pos]
    nlinarith [mul_nonneg hbase hhalf,
      mul_nonneg (mul_nonneg hcoef hbase) hhalf]

private lemma DyuCandidate_axis_mono_x
    (p : ℝ) (hp : 2 < p) {x z : ℝ}
    (hxz : x ≤ z) :
    DyuCandidate p x 0 ≤ DyuCandidate p z 0 := by
  have hp' : 2 ≤ p := by linarith
  by_cases hz_nonpos : z ≤ 0
  · have hx_nonpos : x ≤ 0 := le_trans hxz hz_nonpos
    have hx_eq : DyuCandidate p x 0 = -DyvGeTwo p (-x) 0 := by
      have hQ : QuarterPlane2 x 0 := ⟨hx_nonpos, by linarith, hx_nonpos⟩
      have hcl : closureA2 p (-x) 0 := by
        have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
        exact ⟨by linarith, by linarith,
          mul_nonneg ha_nonneg (by linarith : 0 ≤ -x)⟩
      rw [DyuCandidate_eq_Q2 p hQ]
      simpa using congrArg Neg.neg (auxFunction1_Dy_eq_DyvGeTwo p hp' (-x) 0 hcl)
    by_cases hz0 : z = 0
    · subst z
      have hz_eq : DyuCandidate p 0 0 = 0 := by
        have hQ : QuarterPlane 0 0 := ⟨le_rfl, le_rfl, by norm_num⟩
        simp [DyuCandidate_eq_Q1 p hQ, DyauxFunction1, closureA1, DyuA1]
      rw [hx_eq, hz_eq]
      linarith [DyvGeTwo_axis_nonneg p hp' (by linarith : 0 ≤ -x)]
    · have hz_neg : z < 0 := lt_of_le_of_ne hz_nonpos hz0
      have hz_eq : DyuCandidate p z 0 = -DyvGeTwo p (-z) 0 := by
        have hQ : QuarterPlane2 z 0 := ⟨hz_nonpos, by linarith, hz_nonpos⟩
        have hcl : closureA2 p (-z) 0 := by
          have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
          exact ⟨by linarith, by linarith,
            mul_nonneg ha_nonneg (by linarith : 0 ≤ -z)⟩
        rw [DyuCandidate_eq_Q2 p hQ]
        simpa using congrArg Neg.neg (auxFunction1_Dy_eq_DyvGeTwo p hp' (-z) 0 hcl)
      have hmono : DyvGeTwo p (-z) 0 ≤ DyvGeTwo p (-x) 0 :=
        DyvGeTwo_mono_x_of_pos p hp' (by linarith) (by linarith) (by linarith) (by linarith)
      rw [hx_eq, hz_eq]
      linarith
  · have hz_pos : 0 < z := lt_of_not_ge hz_nonpos
    by_cases hx_nonneg : 0 ≤ x
    · have hx_pos_or : x = 0 ∨ 0 < x := by
        rcases hx_nonneg.eq_or_lt with hx0 | hxpos
        · exact Or.inl hx0.symm
        · exact Or.inr hxpos
      rcases hx_pos_or with rfl | hx_pos
      · have hleft : DyuCandidate p 0 0 = 0 := by
          have hQ : QuarterPlane 0 0 := ⟨le_rfl, le_rfl, by norm_num⟩
          simp [DyuCandidate_eq_Q1 p hQ, DyauxFunction1, closureA1, DyuA1]
        have hright_nonneg : 0 ≤ DyuCandidate p z 0 := by
          have hQ : QuarterPlane z 0 := ⟨hz_pos.le, by linarith, by linarith⟩
          have hcl : closureA2 p z 0 := by
            have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
            exact ⟨hz_pos.le, by linarith, mul_nonneg ha_nonneg hz_pos.le⟩
          rw [DyuCandidate_eq_Q1 p hQ, auxFunction1_Dy_eq_DyvGeTwo p hp' z 0 hcl]
          exact DyvGeTwo_axis_nonneg p hp' hz_pos.le
        linarith
      · have hx_eq : DyuCandidate p x 0 = DyvGeTwo p x 0 := by
          have hQ : QuarterPlane x 0 := ⟨hx_pos.le, by linarith, by linarith⟩
          have hcl : closureA2 p x 0 := by
            have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
            exact ⟨hx_pos.le, by linarith, mul_nonneg ha_nonneg hx_pos.le⟩
          rw [DyuCandidate_eq_Q1 p hQ]
          exact auxFunction1_Dy_eq_DyvGeTwo p hp' x 0 hcl
        have hz_eq : DyuCandidate p z 0 = DyvGeTwo p z 0 := by
          have hQ : QuarterPlane z 0 := ⟨hz_pos.le, by linarith, by linarith⟩
          have hcl : closureA2 p z 0 := by
            have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
            exact ⟨hz_pos.le, by linarith, mul_nonneg ha_nonneg hz_pos.le⟩
          rw [DyuCandidate_eq_Q1 p hQ]
          exact auxFunction1_Dy_eq_DyvGeTwo p hp' z 0 hcl
        rw [hx_eq, hz_eq]
        exact DyvGeTwo_mono_x_of_pos p hp' hx_pos (by linarith) (by linarith) hxz
    · have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
      have hzero : DyuCandidate p 0 0 = 0 := by
        have hQ : QuarterPlane 0 0 := ⟨le_rfl, le_rfl, by norm_num⟩
        simp [DyuCandidate_eq_Q1 p hQ, DyauxFunction1, closureA1, DyuA1]
      have hleft : DyuCandidate p x 0 ≤ 0 := by
        have hQ : QuarterPlane2 x 0 := ⟨hx_neg.le, by linarith, hx_neg.le⟩
        have hcl : closureA2 p (-x) 0 := by
          have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
          exact ⟨by linarith, by linarith,
            mul_nonneg ha_nonneg (by linarith : 0 ≤ -x)⟩
        have hx_eq : DyuCandidate p x 0 = -DyvGeTwo p (-x) 0 := by
          rw [DyuCandidate_eq_Q2 p hQ]
          simpa using congrArg Neg.neg (auxFunction1_Dy_eq_DyvGeTwo p hp' (-x) 0 hcl)
        rw [hx_eq]
        linarith [DyvGeTwo_axis_nonneg p hp' (by linarith : 0 ≤ -x)]
      have hright : 0 ≤ DyuCandidate p z 0 := by
        have hQ : QuarterPlane z 0 := ⟨hz_pos.le, by linarith, by linarith⟩
        have hcl : closureA2 p z 0 := by
          have ha_nonneg : 0 ≤ a p := a_nonneg_of_two_le p hp'
          exact ⟨hz_pos.le, by linarith, mul_nonneg ha_nonneg hz_pos.le⟩
        rw [DyuCandidate_eq_Q1 p hQ, auxFunction1_Dy_eq_DyvGeTwo p hp' z 0 hcl]
        exact DyvGeTwo_axis_nonneg p hp' hz_pos.le
      linarith

private lemma DyuCandidate_mono_x
    (p : ℝ) (hp : 2 < p) {x z y : ℝ}
    (hxz : x ≤ z) :
    DyuCandidate p x y ≤ DyuCandidate p z y := by
  rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
  · have hmono :
        DyuCandidate p (-z) (-y) ≤ DyuCandidate p (-x) (-y) :=
      DyuCandidate_mono_x_of_y_pos p hp (by linarith : 0 < -y) (by linarith)
    rw [DyuCandidate_neg_neg p hp x y, DyuCandidate_neg_neg p hp z y]
    linarith
  · subst y
    exact DyuCandidate_axis_mono_x p hp hxz
  · exact DyuCandidate_mono_x_of_y_pos p hp hy_pos hxz

private lemma DyuCandidate_mixed_mono_mul_le
    (p : ℝ) (hp : 2 < p) {x y h k : ℝ}
    (hk : h * k ≤ 0) :
    DyuCandidate p (x + h) y * k ≤ DyuCandidate p x y * k := by
  rcases lt_trichotomy k 0 with hk_neg | hk_zero | hk_pos
  · have hh_nonneg : 0 ≤ h := by
      by_contra hh
      have hh_neg : h < 0 := lt_of_not_ge hh
      have hprod_pos : 0 < h * k := mul_pos_of_neg_of_neg hh_neg hk_neg
      linarith
    have hmono : DyuCandidate p x y ≤ DyuCandidate p (x + h) y :=
      DyuCandidate_mono_x p hp (by linarith)
    exact mul_le_mul_of_nonpos_right hmono hk_neg.le
  · subst k
    simp
  · have hh_nonpos : h ≤ 0 := by
      by_contra hh
      have hh_pos : 0 < h := lt_of_not_ge hh
      have hprod_pos : 0 < h * k := mul_pos hh_pos hk_pos
      linarith
    have hmono : DyuCandidate p (x + h) y ≤ DyuCandidate p x y :=
      DyuCandidate_mono_x p hp (by linarith)
    exact mul_le_mul_of_nonneg_right hmono hk_pos.le


private lemma uCandidate_hk_negative_geTwo
    (p : ℝ) (hp : 2 < p) {x y h k : ℝ}
    (hk : h * k ≤ 0) :
    uCandidate p (x + h) (y + k) ≤
      uCandidate p x y + DxuCandidate p x y * h + DyuCandidate p x y * k := by
  by_cases hk0 : h * k = 0
  · exact uCandidate_axis_tangent p hp hk0
  have hhor :
      uCandidate p (x + h) y ≤
        uCandidate p x y + DxuCandidate p x y * h := by
    have h := uCandidate_axis_tangent_horizontal
      (p := p) (hp := hp) (x := x) (y := y) (h := h) (k := 0) rfl
    simpa using h
  have hvert :
      uCandidate p (x + h) (y + k) ≤
        uCandidate p (x + h) y + DyuCandidate p (x + h) y * k := by
    have h := uCandidate_axis_tangent_vertical
      (p := p) (hp := hp) (x := x + h) (y := y) (h := 0) (k := k) rfl
    simpa using h
  have hmixed :
      DyuCandidate p (x + h) y * k ≤ DyuCandidate p x y * k := by
    exact DyuCandidate_mixed_mono_mul_le p hp hk
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


end  MajorantPG2

/-! 13. Majorant existence statement -/

/--
Existence of a Burkholder majorant in the regime `p > 2`.

Informally, this theorem says the candidate built in this file really has all
the properties we need: continuity, derivative growth bounds, the tangent-step
inequality for mixed-sign increments, domination of `v`, and strict negativity
on the nontrivial axis points.

So this is the "package everything together" result for the high-exponent case.
-/
theorem exists_majorant_geTwo (p : ℝ) (hp : 2 < p) :
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
      (∀ x y, x*y = 0 ∧ (x,y) ≠ (0,0) → u x y < 0) := by
  use MajorantPG2.uCandidate p
  use MajorantPG2.DxuCandidate p
  use MajorantPG2.DyuCandidate p
  obtain ⟨Cdu, hCdu_nonneg, hDxu_growth, hDyu_growth⟩ :=
    MajorantPG2.uCandidate_derivative_growth_bound p hp
  obtain ⟨Cu, hCu_nonneg, hu_abs_growth⟩ :=
    MajorantPG2.uCandidate_growth_bound p (le_of_lt hp)
  use max Cdu Cu
  have hCdu_le : Cdu ≤ max Cdu Cu := le_max_left _ _
  have hCu_le : Cu ≤ max Cdu Cu := le_max_right _ _
  refine ⟨le_trans hCdu_nonneg hCdu_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact MajorantPG2.continuousuCandidate p (le_of_lt hp)
  · exact MajorantPG2.continuousDxuCandidate p hp
  · exact MajorantPG2.continuousDyuCandidate p hp
  · intro x y
    have hsum_nonneg : 0 ≤ Real.rpow |x| p + Real.rpow |y| p := by
      exact add_nonneg (Real.rpow_nonneg (abs_nonneg x) _)
        (Real.rpow_nonneg (abs_nonneg y) _)
    calc
      |MajorantPG2.uCandidate p x y|
          ≤ Cu * (Real.rpow |x| p + Real.rpow |y| p) := hu_abs_growth x y
      _ ≤ max Cdu Cu * (Real.rpow |x| p + Real.rpow |y| p) :=
        mul_le_mul_of_nonneg_right hCu_le hsum_nonneg
  · intro x y
    have hsum_nonneg :
        0 ≤ Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1) := by
      exact add_nonneg (Real.rpow_nonneg (abs_nonneg x) _)
        (Real.rpow_nonneg (abs_nonneg y) _)
    exact (hDxu_growth x y).trans
      (mul_le_mul_of_nonneg_right hCdu_le hsum_nonneg)
  · intro x y
    have hsum_nonneg :
        0 ≤ Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1) := by
      exact add_nonneg (Real.rpow_nonneg (abs_nonneg x) _)
        (Real.rpow_nonneg (abs_nonneg y) _)
    exact (hDyu_growth x y).trans
      (mul_le_mul_of_nonneg_right hCdu_le hsum_nonneg)
  · intro x y h k hk
    exact MajorantPG2.uCandidate_hk_negative_geTwo p hp hk
  · -- pointwise majorization
    intros x y
    have hv := MajorantPG2.vGeTwo_le_uCandidate p hp x y
    have hp' : 2 ≤ p := by linarith
    simpa [v, MajorantPG2.vGeTwo, MajorantPG2.pStar_eq_self_of_two_le p hp',
      abs_of_nonneg (by linarith : 0 ≤ p - 1)] using hv
  · -- negativity on x*y ≤ 0
    intros x y hxy
    exact MajorantPG2.uCandidate_le_zero_of_mul_nonpos p x y (by linarith) hxy
  · -- negativity on x*y = 0
    intros x y hxy
    rcases hxy with ⟨hxy0, hne⟩
    exact MajorantPG2.uCandidate_le_zero_of_mul_neg p x y hp hxy0 hne



end Majorants
