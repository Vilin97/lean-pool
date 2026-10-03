/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.OverlapCount
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Overlap-counting integral bound (U3)

Summing set-lintegrals over the enlarged cubes of a depth-`j` center family
costs at most the bounded-overlap constant `3^d` times one set-lintegral over
the parent product cube.
-/

@[expose] public section

namespace Homogenization
namespace Gagliardo

open MeasureTheory ScalarOverlap
open scoped ENNReal BigOperators

variable {d : ℕ}

/-- The product `E_S ×ˢ E_S` of an enlarged center cube is measurable. -/
theorem measurableSet_overlap_prod (S : TriadicCube d) :
    MeasurableSet (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S) :=
  (ScalarOverlap.measurableSet_cubeSet S).prod
    (ScalarOverlap.measurableSet_cubeSet S)

open Classical in
/-- Pointwise overlap count on pairs: a pair lies in at most `3^d` of the
products `E_S ×ˢ E_S`, and only when it lies in `Q ×ˢ Q`. -/
theorem sum_indicator_overlap_prod_le (Q : TriadicCube d) (j : ℕ)
    (z : Vec d × Vec d) :
    (∑ S ∈ ScalarOverlap.centersAtDepth Q j,
        (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
          (fun _ => (1 : ℝ≥0∞)) z) ≤
      (3 : ℝ≥0∞) ^ d *
        (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q).indicator
          (fun _ => (1 : ℝ≥0∞)) z := by
  by_cases hzQ : z ∈ Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q
  · -- count the centers whose product cube contains `z`
    have hcount :
        (∑ S ∈ ScalarOverlap.centersAtDepth Q j,
          (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
            (fun _ => (1 : ℝ≥0∞)) z) =
        (((ScalarOverlap.centersAtDepth Q j).filter
            (fun S => z ∈ ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S)).card
          : ℝ≥0∞) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun S _hS => ?_
      by_cases hz : z ∈ ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S
      · simp [hz]
      · simp [hz]
    rw [hcount, Set.indicator_of_mem hzQ, mul_one]
    have hsubset :
        (ScalarOverlap.centersAtDepth Q j).filter
            (fun S => z ∈ ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S) ⊆
          (ScalarOverlap.centersAtDepth Q j).filter
            (fun S => z.1 ∈ ScalarOverlap.cubeSet S) := by
      intro S hS
      rw [Finset.mem_filter] at hS ⊢
      exact ⟨hS.1, hS.2.1⟩
    have hcard := (Finset.card_le_card hsubset).trans
      (card_centersAtDepth_filter_mem_le Q j z.1)
    calc ((((ScalarOverlap.centersAtDepth Q j).filter
            (fun S => z ∈ ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S)).card)
          : ℝ≥0∞)
        ≤ ((3 ^ d : ℕ) : ℝ≥0∞) := by exact_mod_cast hcard
      _ = (3 : ℝ≥0∞) ^ d := by push_cast; ring
  · -- outside `Q ×ˢ Q` every summand vanishes
    have hzero : ∀ S ∈ ScalarOverlap.centersAtDepth Q j,
        (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
          (fun _ => (1 : ℝ≥0∞)) z = 0 := by
      intro S hS
      refine Set.indicator_of_notMem (fun hz => hzQ ?_) _
      have hsub := cubeSet_subset_cubeSet_of_mem_centersAtDepth hS
      exact ⟨hsub hz.1, hsub hz.2⟩
    rw [Finset.sum_congr rfl hzero]
    simp

/-- U3 (overlap-counting integral bound): for any measure `ν` on pairs and any
measurable integrand, the depth-`j` family of product cubes is summable at the
cost of the overlap constant `3^d`. -/
theorem sum_setLIntegral_overlap_prod_le (Q : TriadicCube d) (j : ℕ)
    (ν : Measure (Vec d × Vec d)) {f : Vec d × Vec d → ℝ≥0∞}
    (hf : Measurable f) :
    (∑ S ∈ ScalarOverlap.centersAtDepth Q j,
        ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S, f z ∂ν) ≤
      (3 : ℝ≥0∞) ^ d *
        ∫⁻ z in Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q, f z ∂ν := by
  classical
  have hind : ∀ (A : Set (Vec d × Vec d)), MeasurableSet A →
      (∫⁻ z in A, f z ∂ν) =
        ∫⁻ z, A.indicator (fun _ => (1 : ℝ≥0∞)) z * f z ∂ν := by
    intro A hA
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ A
    · simp [hz]
    · simp [hz]
  have hQQ : MeasurableSet
      (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) :=
    (Homogenization.measurableSet_cubeSet Q).prod
      (Homogenization.measurableSet_cubeSet Q)
  have hrewrite : ∀ S ∈ ScalarOverlap.centersAtDepth Q j,
      (∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S, f z ∂ν) =
        ∫⁻ z, (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
          (fun _ => (1 : ℝ≥0∞)) z * f z ∂ν :=
    fun S _hS => hind _ (measurableSet_overlap_prod S)
  have hsum_eq :
      (∑ S ∈ ScalarOverlap.centersAtDepth Q j,
          ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S, f z ∂ν) =
        ∑ S ∈ ScalarOverlap.centersAtDepth Q j,
          ∫⁻ z, (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
            (fun _ => (1 : ℝ≥0∞)) z * f z ∂ν :=
    Finset.sum_congr rfl hrewrite
  have hlint_eq :
      (∫⁻ z, ∑ S ∈ ScalarOverlap.centersAtDepth Q j,
          (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
            (fun _ => (1 : ℝ≥0∞)) z * f z ∂ν) =
        ∑ S ∈ ScalarOverlap.centersAtDepth Q j,
          ∫⁻ z, (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
            (fun _ => (1 : ℝ≥0∞)) z * f z ∂ν :=
    lintegral_finsetSum _ (fun S _hS =>
      ((measurable_const.indicator (measurableSet_overlap_prod S)).mul hf))
  rw [hsum_eq, ← hlint_eq]
  have hpoint : ∀ z,
      (∑ S ∈ ScalarOverlap.centersAtDepth Q j,
        (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
          (fun _ => (1 : ℝ≥0∞)) z * f z) ≤
      (3 : ℝ≥0∞) ^ d *
        ((Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q).indicator
          (fun _ => (1 : ℝ≥0∞)) z * f z) := by
    intro z
    rw [← Finset.sum_mul, ← mul_assoc]
    exact mul_le_mul' (sum_indicator_overlap_prod_le Q j z) le_rfl
  calc (∫⁻ z, ∑ S ∈ ScalarOverlap.centersAtDepth Q j,
        (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
          (fun _ => (1 : ℝ≥0∞)) z * f z ∂ν)
      ≤ ∫⁻ z, (3 : ℝ≥0∞) ^ d *
          ((Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q).indicator
            (fun _ => (1 : ℝ≥0∞)) z * f z) ∂ν :=
        lintegral_mono hpoint
    _ = (3 : ℝ≥0∞) ^ d *
          ∫⁻ z, (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q).indicator
            (fun _ => (1 : ℝ≥0∞)) z * f z ∂ν :=
        lintegral_const_mul _ ((measurable_const.indicator hQQ).mul hf)
    _ = (3 : ℝ≥0∞) ^ d *
          ∫⁻ z in Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q,
            f z ∂ν := by
        rw [hind _ hQQ]

end Gagliardo
end Homogenization
