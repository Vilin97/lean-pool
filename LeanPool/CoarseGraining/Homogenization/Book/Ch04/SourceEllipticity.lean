/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.LocalEllipticitySlices
import LeanPool.CoarseGraining.Homogenization.Probability.Source.Coarse

/-!
# Deterministic ellipticity slices for the exact coarse source

Every coarse-source carrier field is locally uniformly elliptic on source
Euclidean balls.  This file converts that carrier membership fact into the
countable AEE ellipticity slices used on a fixed triadic cube without invoking
any probabilistic assumptions.
-/

namespace Homogenization.Book.Ch04

open MeasureTheory

private theorem cubeSet_subset_sourceEuclideanBall {d : ℕ} (Q : TriadicCube d) :
    ∃ R : ℝ, 1 ≤ R ∧ cubeSet Q ⊆ Source.Coarse.euclideanBall R := by
  let e : Vec d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin d => ℝ).symm
  obtain ⟨C, hC⟩ := (isBounded_cubeSet Q).exists_norm_le
  refine ⟨max 1 (‖e.toContinuousLinearMap‖ * C + 1), le_max_left _ _, ?_⟩
  intro x hx
  have hxC : euclideanNorm x ≤ ‖e.toContinuousLinearMap‖ * C := by
    calc
      euclideanNorm x = ‖HilbertVec.ofVec x‖ := euclideanNorm_eq_norm_ofVec x
      _ = ‖e x‖ := rfl
      _ ≤ ‖e.toContinuousLinearMap‖ * C :=
        e.toContinuousLinearMap.le_opNorm_of_le (hC x hx)
  change euclideanNorm x < max 1 (‖e.toContinuousLinearMap‖ * C + 1)
  exact hxC.trans_lt ((lt_add_one _).trans_le (le_max_right _ _))

/-- A coarse-source carrier field has positive a.e. ellipticity constants on
every triadic cube.  The only inputs are its coordinate measurability and its
pointwise source-ball ellipticity from carrier membership. -/
theorem exists_source_isAEEllipticFieldOn_cubeSet {d : ℕ}
    (a : Source.Coarse.Carrier d) (Q : TriadicCube d) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      IsAEEllipticFieldOn ε ε⁻¹ (cubeSet Q) a.1 := by
  classical
  obtain ⟨R, hR, hQR⟩ := cubeSet_subset_sourceEuclideanBall Q
  obtain ⟨ε, hε_pos, hε_le_one, hEll⟩ := a.2.2 R hR
  have hmeas :
      Measurable (fun x i j => if x ∈ cubeSet Q then a.1 x i j else 0) := by
    refine (measurable_pi_iff).2 fun i => (measurable_pi_iff).2 fun j => ?_
    have heq : (fun x => if x ∈ cubeSet Q then a.1 x i j else 0) =
        Set.indicator (cubeSet Q) (fun x => a.1 x i j) := by
      funext x
      by_cases hx : x ∈ cubeSet Q <;> simp [hx]
    rw [heq]
    exact (a.2.1 i j).indicator (measurableSet_cubeSet Q)
  have hEll_cube : IsEllipticFieldOn ε ε⁻¹ (cubeSet Q) a.1 :=
    ⟨hmeas, fun x hx => hEll x (hQR hx)⟩
  exact ⟨ε, hε_pos, hε_le_one,
    IsAEEllipticFieldOn.of_isEllipticFieldOn hEll_cube⟩

/-- Every coarse-source carrier field belongs to a countable AEE ellipticity
slice on every triadic cube. -/
theorem exists_source_aeeQuantitativeEllipticSlice_cubeSet {d : ℕ}
    (a : Source.Coarse.Carrier d) (Q : TriadicCube d) :
    ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k a.1 := by
  obtain ⟨ε, hε_pos, -, hEll⟩ := exists_source_isAEEllipticFieldOn_cubeSet a Q
  exact AEEQuantitativeEllipticSlice.exists_of_aeeEllipticOn hε_pos hEll

end Homogenization.Book.Ch04
