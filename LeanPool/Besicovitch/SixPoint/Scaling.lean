/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.Score

/-!
# Scaling six-point packing radii

This file shrinks every radius while retaining the same centers and support. Shrinking creates the
strict score gain used when the density parameter is larger than the finite endpoint.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LeanPool.Besicovitch

namespace SixPointPacking

variable {configuration : SixPointConfiguration}

/-- Shrink every packing radius by a factor in `[0, 1]`. -/
def scaleRadii (packing : SixPointPacking configuration) (q : ℝ) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : SixPointPacking configuration where
  support := packing.support
  meets_color := packing.meets_color
  radius i := ⟨q * packing.radius i,
    mul_nonneg hq0 (packing.radius i).property.1,
    calc
      q * (packing.radius i : ℝ) ≤ q * 1 :=
        mul_le_mul_of_nonneg_left (packing.radius i).property.2 hq0
      _ ≤ 1 := by simpa using hq1⟩
  same_color_disjoint i j hij hcolor := by
    have hsum := packing.same_color_disjoint i j hij hcolor
    have hsum_nonneg : 0 ≤ (packing.radius i : ℝ) + packing.radius j :=
      add_nonneg (packing.radius i).property.1 (packing.radius j).property.1
    have hshrink : q * ((packing.radius i : ℝ) + packing.radius j) ≤
        (packing.radius i : ℝ) + packing.radius j := by
      nlinarith
    calc
      q * (packing.radius i : ℝ) + q * packing.radius j =
          q * ((packing.radius i : ℝ) + packing.radius j) := by ring
      _ ≤ (packing.radius i : ℝ) + packing.radius j := hshrink
      _ ≤ _ := hsum

@[simp]
theorem scaleRadii_totalRadius (packing : SixPointPacking configuration) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (packing.scaleRadii q hq0 hq1).totalRadius = q * packing.totalRadius := by
  simp [totalRadius, scaleRadii, Finset.mul_sum]

/-- Shrinking radii cannot increase the virtual diameter. -/
theorem scaleRadii_virtualDiameter_le (packing : SixPointPacking configuration) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (packing.scaleRadii q hq0 hq1).virtualDiameter ≤ packing.virtualDiameter := by
  unfold virtualDiameter
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  have hri : q * (packing.radius i : ℝ) ≤ packing.radius i := by
    nlinarith [(packing.radius i).property.1]
  have hrj : q * (packing.radius j : ℝ) ≤ packing.radius j := by
    nlinarith [(packing.radius j).property.1]
  calc
    dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
          q * packing.radius i + q * packing.radius j ≤
        dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
          packing.radius i + packing.radius j := by gcongr
    _ ≤ packing.virtualDiameter := packing.pair_le_virtualDiameter i j

/-- The score after shrinking has an explicit lower bound from the original diameter. -/
theorem scaleRadii_score_ge (packing : SixPointPacking configuration)
    {s β q lower : ℝ} (hs : 0 < s) (hβ : 0 < β) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hgain : s ≤ β * q) (hscore : 0 ≤ packing.score s)
    (hlower : lower ≤ packing.virtualDiameter) :
    lower * (β * q - s) / (2 * s * β) ≤
      (packing.scaleRadii q hq hq1).score β := by
  have hcoefficient : 0 ≤ (β * q - s) / (2 * s * β) := by positivity
  have hbase : packing.virtualDiameter / (2 * s) ≤ packing.totalRadius := by
    simpa only [score, sub_nonneg] using hscore
  have htotal : q * (packing.virtualDiameter / (2 * s)) ≤
      q * packing.totalRadius := mul_le_mul_of_nonneg_left hbase hq
  have hdiameter :
      (packing.scaleRadii q hq hq1).virtualDiameter / (2 * β) ≤
        packing.virtualDiameter / (2 * β) := by
    exact div_le_div_of_nonneg_right
      (packing.scaleRadii_virtualDiameter_le q hq hq1) (by positivity)
  calc
    lower * (β * q - s) / (2 * s * β) =
        lower * ((β * q - s) / (2 * s * β)) := by ring
    _ ≤ packing.virtualDiameter * ((β * q - s) / (2 * s * β)) :=
      mul_le_mul_of_nonneg_right hlower hcoefficient
    _ = q * (packing.virtualDiameter / (2 * s)) -
        packing.virtualDiameter / (2 * β) := by field_simp
    _ ≤ q * packing.totalRadius -
        (packing.scaleRadii q hq hq1).virtualDiameter / (2 * β) :=
      sub_le_sub htotal hdiameter
    _ = (packing.scaleRadii q hq hq1).score β := by
      rw [score, scaleRadii_totalRadius]

/-- Shrinking by `q` gives positive score at `β` when `s < βq`. -/
theorem scaleRadii_score_pos (packing : SixPointPacking configuration)
    {s β q lower : ℝ} (hs : 0 < s) (hβ : 0 < β) (hq : 0 < q) (hq1 : q ≤ 1)
    (hgain : s < β * q) (hscore : 0 ≤ packing.score s)
    (hlower : lower ≤ packing.virtualDiameter) (hlower_pos : 0 < lower) :
    0 < (packing.scaleRadii q hq.le hq1).score β := by
  have hdiameter_pos : 0 < packing.virtualDiameter := hlower_pos.trans_le hlower
  have hbase : packing.virtualDiameter ≤ packing.totalRadius * (2 * s) := by
    rw [score, sub_nonneg] at hscore
    exact (div_le_iff₀ (by positivity : 0 < 2 * s)).1 hscore
  have htotal_pos : 0 < packing.totalRadius := by
    nlinarith
  have hstrict : packing.virtualDiameter < q * packing.totalRadius * (2 * β) := by
    calc
      packing.virtualDiameter ≤ packing.totalRadius * (2 * s) := hbase
      _ < q * packing.totalRadius * (2 * β) := by nlinarith
  rw [score, scaleRadii_totalRadius, sub_pos]
  apply (div_lt_iff₀ (by positivity : 0 < 2 * β)).2
  exact (packing.scaleRadii_virtualDiameter_le q hq.le hq1).trans_lt hstrict

end SixPointPacking

end LeanPool.Besicovitch
