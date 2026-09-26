/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.Configuration
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Packings on six-point configurations

A support remembers selected zero-radius labels, so its virtual diameter has no degenerate cases.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LeanPool.Besicovitch

/-- A supported radius assignment with disjoint same-color balls. -/
structure SixPointPacking (configuration : SixPointConfiguration) where
  /-- The centers retained by the packing. -/
  support : Finset SixPointIndex
  meets_color : ∀ color, ∃ label, (color, label) ∈ support
  /-- The radius at each retained center. -/
  radius : support → Set.Icc (0 : ℝ) 1
  same_color_disjoint : ∀ i j : support, i ≠ j → i.1.1 = j.1.1 →
    (radius i : ℝ) + radius j ≤ dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2)

namespace SixPointPacking

variable {configuration : SixPointConfiguration} (packing : SixPointPacking configuration)

/-- The support of a six-point packing is nonempty. -/
theorem support_nonempty : packing.support.Nonempty := by
  obtain ⟨label, hlabel⟩ := packing.meets_color .red
  exact ⟨(.red, label), hlabel⟩

/-- The sum of all supported radii. -/
def totalRadius : ℝ :=
  packing.support.attach.sum fun i ↦ (packing.radius i : ℝ)

/-- The maximum pairwise center distance plus the two radii on the explicit support. -/
def virtualDiameter : ℝ :=
  packing.support.attach.sup' packing.support_nonempty.attach fun i ↦
    packing.support.attach.sup' packing.support_nonempty.attach fun j ↦
      dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
        packing.radius i + packing.radius j

/-- The packing score at parameter `s`. -/
def score (s : ℝ) : ℝ :=
  packing.totalRadius - packing.virtualDiameter / (2 * s)

/-- Every supported pair contributes at most the virtual diameter. -/
theorem pair_le_virtualDiameter (i j : packing.support) :
    dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
        packing.radius i + packing.radius j ≤ packing.virtualDiameter := by
  unfold virtualDiameter
  calc
    _ ≤ packing.support.attach.sup' packing.support_nonempty.attach (fun j ↦
        dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
          packing.radius i + packing.radius j) := Finset.le_sup' _ (Finset.mem_attach _ j)
    _ ≤ _ := Finset.le_sup'
      (fun i ↦ packing.support.attach.sup' packing.support_nonempty.attach fun j ↦
        dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
          packing.radius i + packing.radius j) (Finset.mem_attach _ i)

/-- The virtual diameter is nonnegative. -/
theorem virtualDiameter_nonneg : 0 ≤ packing.virtualDiameter := by
  obtain ⟨index, hindex⟩ := packing.support_nonempty
  let i : packing.support := ⟨index, hindex⟩
  exact (add_nonneg (add_nonneg dist_nonneg (packing.radius i).property.1)
    (packing.radius i).property.1).trans (packing.pair_le_virtualDiameter i i)

/-- Every supported center distance is at most the virtual diameter. -/
theorem dist_le_virtualDiameter (i j : packing.support) :
    dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) ≤
      packing.virtualDiameter := by
  calc
    _ ≤ _ + (packing.radius i : ℝ) := le_add_of_nonneg_right (packing.radius i).property.1
    _ ≤ _ + (packing.radius j : ℝ) := le_add_of_nonneg_right (packing.radius j).property.1
    _ ≤ _ := packing.pair_le_virtualDiameter i j

/-- A lower bound between the two colors is inherited by the virtual diameter. -/
theorem crossColor_le_virtualDiameter {lower : ℝ}
    (hcross : ∀ redLabel blueLabel,
      (.red, redLabel) ∈ packing.support → (.blue, blueLabel) ∈ packing.support →
        lower ≤ dist (configuration .red redLabel) (configuration .blue blueLabel)) :
    lower ≤ packing.virtualDiameter := by
  obtain ⟨redLabel, hred⟩ := packing.meets_color .red
  obtain ⟨blueLabel, hblue⟩ := packing.meets_color .blue
  let red : packing.support := ⟨(.red, redLabel), hred⟩
  let blue : packing.support := ⟨(.blue, blueLabel), hblue⟩
  exact (hcross redLabel blueLabel hred hblue).trans (packing.dist_le_virtualDiameter red blue)

/-- Twice any supported radius is at most the virtual diameter. -/
theorem two_mul_radius_le_virtualDiameter (i : packing.support) :
    2 * (packing.radius i : ℝ) ≤ packing.virtualDiameter := by
  simpa [two_mul] using packing.pair_le_virtualDiameter i i

/-- The total radius is nonnegative. -/
theorem totalRadius_nonneg : 0 ≤ packing.totalRadius := by
  exact Finset.sum_nonneg fun i _ ↦ (packing.radius i).property.1

end SixPointPacking

end LeanPool.Besicovitch
