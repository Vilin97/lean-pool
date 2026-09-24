/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Ball Topology

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal


noncomputable section

namespace CKN

/-- The open Euclidean ball is open in the product topology. -/
theorem isOpen_euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    IsOpen (euclideanBall x₀ R) := by
  change IsOpen {x : Vec d | euclideanSqDist x x₀ < R ^ 2}
  exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const

/-- The open Euclidean ball is a measurable set. -/
theorem measurableSet_euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    MeasurableSet (euclideanBall x₀ R) :=
  (isOpen_euclideanBall x₀ R).measurableSet

/-- The open Euclidean ball is contained in the metric ball with the same radius. -/
theorem euclideanBall_subset_metricBall {d : ℕ} {x₀ : Vec d} {R : ℝ} (hR : 0 < R) :
    euclideanBall x₀ R ⊆ Metric.ball x₀ R := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm]
  have hnorm : ‖x - x₀‖ ≤ vecEuclideanNorm (x - x₀) := by
    rw [Pi.norm_def]
    have hnn : Finset.univ.sup (fun i => ‖(x - x₀) i‖₊) ≤
        ⟨vecEuclideanNorm (x - x₀), vecEuclideanNorm_nonneg _⟩ := by
      apply Finset.sup_le
      intro i _hi
      exact_mod_cast abs_apply_le_vecEuclideanNorm (x - x₀) i
    exact_mod_cast hnn
  exact hnorm.trans_lt ((mem_euclideanBall_iff_vecEuclideanNorm_lt hR).1 hx)

/-- The volume of the open Euclidean ball is finite. -/
theorem volume_euclideanBall_lt_top {d : ℕ} (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    volume (euclideanBall x₀ R) < ⊤ :=
  (measure_mono (euclideanBall_subset_metricBall hR)).trans_lt measure_ball_lt_top

/-- The volume of the open Euclidean ball is not infinite. -/
theorem volume_euclideanBall_ne_top {d : ℕ} (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    volume (euclideanBall x₀ R) ≠ ⊤ :=
  (volume_euclideanBall_lt_top x₀ hR).ne

/-- The volume of the open Euclidean ball is positive. -/
theorem volume_euclideanBall_pos {d : ℕ} (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    0 < volume (euclideanBall x₀ R) :=
  (isOpen_euclideanBall x₀ R).measure_pos volume ⟨x₀, by simp [euclideanBall, hR]⟩

end CKN
