/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Finite unions of metric balls

This file collects the finite-ball estimates used in the packing-to-measure transfer.
-/

@[expose] public section

noncomputable section

open Set

namespace LeanPool.Besicovitch

variable {X ι : Type*} [PseudoMetricSpace X]

/-- The union of open balls indexed by a finite support. -/
def finiteBallUnion (support : Finset ι) (center : support → X) (radius : support → ℝ) :
    Set X :=
  ⋃ i : support, Metric.ball (center i) (radius i)

/-- Membership in a finite ball union is witnessed by one supported ball. -/
@[simp]
theorem mem_finiteBallUnion {support : Finset ι} {center : support → X}
    {radius : support → ℝ} {x : X} :
    x ∈ finiteBallUnion support center radius ↔
      ∃ i : support, x ∈ Metric.ball (center i) (radius i) := by
  simp [finiteBallUnion]

/-- Every supported ball lies in the corresponding finite ball union. -/
theorem ball_subset_finiteBallUnion {support : Finset ι} (center : support → X)
    (radius : support → ℝ) (i : support) :
    Metric.ball (center i) (radius i) ⊆ finiteBallUnion support center radius :=
  subset_iUnion (fun j : support ↦ Metric.ball (center j) (radius j)) i

/-- A finite ball union is open. -/
theorem isOpen_finiteBallUnion {support : Finset ι} (center : support → X)
    (radius : support → ℝ) : IsOpen (finiteBallUnion support center radius) :=
  isOpen_iUnion fun _ ↦ Metric.isOpen_ball

/-- A finite ball union is nonempty exactly when one supported radius is positive. -/
@[simp]
theorem finiteBallUnion_nonempty {support : Finset ι} {center : support → X}
    {radius : support → ℝ} :
    (finiteBallUnion support center radius).Nonempty ↔ ∃ i : support, 0 < radius i := by
  simp [finiteBallUnion]

/-- Open balls satisfying the pairwise separation inequalities are pairwise disjoint. -/
theorem pairwise_disjoint_ball_of_add_le_dist {support : Finset ι}
    (center : support → X) (radius : support → ℝ)
    (hsep : ∀ i j, i ≠ j → radius i + radius j ≤ dist (center i) (center j)) :
    Pairwise fun i j ↦
      Disjoint (Metric.ball (center i) (radius i)) (Metric.ball (center j) (radius j)) :=
  fun i j hij ↦ Metric.ball_disjoint_ball (hsep i j hij)

/-- The extended diameter of a finite ball union is bounded by its center-radius maximum. -/
theorem ediam_finiteBallUnion_le {support : Finset ι} (hsupport : support.Nonempty)
    (center : support → X) (radius : support → ℝ) :
    Metric.ediam (finiteBallUnion support center radius) ≤
      ENNReal.ofReal (support.attach.sup' hsupport.attach fun i ↦
        support.attach.sup' hsupport.attach fun j ↦
          dist (center i) (center j) + radius i + radius j) := by
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  obtain ⟨i, hi⟩ := mem_finiteBallUnion.mp hx
  obtain ⟨j, hj⟩ := mem_finiteBallUnion.mp hy
  calc
    dist x y ≤ dist x (center i) + dist (center i) (center j) + dist (center j) y :=
      dist_triangle4 _ _ _ _
    _ ≤ radius i + dist (center i) (center j) + radius j := by
      exact add_le_add (add_le_add hi.le le_rfl) (Metric.mem_ball'.mp hj).le
    _ = dist (center i) (center j) + radius i + radius j := by ring
    _ ≤ support.attach.sup' hsupport.attach (fun i ↦
        support.attach.sup' hsupport.attach fun j ↦
          dist (center i) (center j) + radius i + radius j) := by
      calc
        _ ≤ support.attach.sup' hsupport.attach (fun j ↦
            dist (center i) (center j) + radius i + radius j) :=
          Finset.le_sup' _ (Finset.mem_attach _ j)
        _ ≤ _ := Finset.le_sup'
          (fun i ↦ support.attach.sup' hsupport.attach fun j ↦
            dist (center i) (center j) + radius i + radius j)
          (Finset.mem_attach _ i)

/-- A finite ball union is measurable in the Borel measurable structure. -/
theorem measurableSet_finiteBallUnion {support : Finset ι} [MeasurableSpace X]
    [OpensMeasurableSpace X] (center : support → X) (radius : support → ℝ) :
    MeasurableSet (finiteBallUnion support center radius) :=
  (isOpen_finiteBallUnion center radius).measurableSet

end LeanPool.Besicovitch
