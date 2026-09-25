/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.BallTopology
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Ball Mem Lp

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal


noncomputable section

namespace CKN

/-- A continuous function on `Vec d` is `L^p` with respect to the volume measure
restricted to any open Euclidean ball of positive radius, for every exponent `p`. -/
theorem memLp_euclideanBall_of_continuous {d : ℕ}
    {x₀ : Vec d} {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : Continuous f) (p : ℝ≥0∞) :
    MemLp f p (volume.restrict (euclideanBall x₀ r)) := by
  let B : Set (Vec d) := euclideanBall x₀ r
  let K : Set (Vec d) := euclideanClosedBall x₀ r
  have hK : IsCompact K := isCompact_euclideanClosedBall x₀ hr.le
  have hBK : B ⊆ K := by
    intro x hx
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).2
      ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx).le
  have hBopen : IsOpen B := isOpen_euclideanBall x₀ r
  let _ : IsFiniteMeasure (volume.restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact (measure_mono hBK).trans_lt hK.measure_lt_top
  obtain ⟨M, hM⟩ := hK.bddAbove_image hf.continuousOn
  obtain ⟨m, hm⟩ := hK.bddBelow_image hf.continuousOn
  refine memLp_of_bounded (a := m) (b := M) ?_ ?_ p
  · filter_upwards [ae_restrict_mem hBopen.measurableSet] with x hx
    have hxK : x ∈ K := hBK hx
    have hfx : f x ∈ f '' K := ⟨x, hxK, rfl⟩
    exact ⟨hm hfx, hM hfx⟩
  · exact hf.aestronglyMeasurable.restrict

end CKN
