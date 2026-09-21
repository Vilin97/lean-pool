/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Multiscale.ProjectionLp
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Basic -/

namespace Homogenization

open scoped BigOperators ENNReal

/-!
Local building blocks for the cube Besov layer.

This file stays intentionally lightweight: it packages the cube-wise oscillation
and scale weights that later positive and negative Besov definitions will
assemble across descendants and scales.
-/

noncomputable def cubeBesovOscillation {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → ℝ) : ℝ :=
  cubeLpNorm Q p (cubeFluctuation Q u)

/-- Explicit disjoint-cube spelling of the legacy scalar cube oscillation. -/
noncomputable abbrev cubeBesovDisjointOscillation {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  cubeBesovOscillation Q p u

noncomputable def cubeBesovScaleWeight {d : ℕ} (s : ℝ) (Q : TriadicCube d) : ℝ :=
  (cubeScaleFactor Q) ^ (-s)

noncomputable def descendantsAverage {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → ℝ) : ℝ := by
  let D := descendantsAtDepth Q j
  exact ((D.card : ℝ)⁻¹) * D.sum F

theorem descendantsAverage_nonneg {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → ℝ)
    (hF : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ F R) :
    0 ≤ descendantsAverage Q j F := by
  classical
  dsimp [descendantsAverage]
  refine mul_nonneg ?_ ?_
  · exact inv_nonneg.mpr (show 0 ≤ ((descendantsAtDepth Q j).card : ℝ) by positivity)
  · exact Finset.sum_nonneg fun R hR => hF R hR

theorem descendantsAverage_mul_left {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : ℝ)
    (F : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => c * F R) = c * descendantsAverage Q j F := by
  calc
    descendantsAverage Q j (fun R => c * F R)
        = ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth Q j, c * F R := by
              rfl
    _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          (c * ∑ R ∈ descendantsAtDepth Q j, F R) := by
            rw [← Finset.mul_sum]
    _ = c * descendantsAverage Q j F := by
          unfold descendantsAverage
          ring

theorem descendantsAverage_le_descendantsAverage {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    {F G : TriadicCube d → ℝ}
    (hFG : ∀ R ∈ descendantsAtDepth Q j, F R ≤ G R) :
    descendantsAverage Q j F ≤ descendantsAverage Q j G := by
  classical
  unfold descendantsAverage
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · exact Finset.sum_le_sum hFG
  · exact inv_nonneg.mpr (by positivity)

theorem descendantsAverage_sum {d : ℕ} {ι : Type*} [DecidableEq ι]
    (Q : TriadicCube d) (j : ℕ) (s : Finset ι) (F : TriadicCube d → ι → ℝ) :
    descendantsAverage Q j (fun R => ∑ i ∈ s, F R i) =
      ∑ i ∈ s, descendantsAverage Q j (fun R => F R i) := by
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  calc
    descendantsAverage Q j (fun R => ∑ i ∈ s, F R i)
        = ((D.card : ℝ)⁻¹) * ∑ R ∈ D, ∑ i ∈ s, F R i := by
            rfl
    _ = ((D.card : ℝ)⁻¹) * ∑ i ∈ s, ∑ R ∈ D, F R i := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ s, ((D.card : ℝ)⁻¹) * ∑ R ∈ D, F R i := by
          rw [Finset.mul_sum]
    _ = ∑ i ∈ s, descendantsAverage Q j (fun R => F R i) := by
          simp [descendantsAverage, D]

theorem sq_rpow_half_eq_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 2) ^ (1 / 2 : ℝ) = x := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  norm_num

theorem descendantsAverage_succ_eq_descendantsAverage_descendantsAverage {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ) :
    descendantsAverage Q (j + 1) F =
      descendantsAverage Q j (fun R => descendantsAverage R 1 F) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hsum :
      ∑ S ∈ descendantsAtDepth Q (j + 1), F S =
        ∑ R ∈ D, ∑ S ∈ childCubes R, F S := by
    rw [descendantsAtDepth_succ, Finset.sum_biUnion]
    intro R hR S hS hRS
    exact disjoint_childCubes_of_ne hRS
  have hcard_ne : (((descendantsAtDepth Q j).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j)
  have hpow_ne : (((3 ^ d : ℕ) : ℕ) : ℝ) ≠ 0 := by positivity
  have hcast :
      (((descendantsAtDepth Q j).card * 3 ^ d : ℕ) : ℝ) =
        ((descendantsAtDepth Q j).card : ℝ) * (((3 ^ d : ℕ) : ℝ)) := by
    norm_num
  have hcoeff :
      ((((descendantsAtDepth Q j).card * 3 ^ d : ℕ) : ℝ)⁻¹) =
        ((descendantsAtDepth Q j).card : ℝ)⁻¹ * (((3 ^ d : ℕ) : ℝ)⁻¹) := by
    rw [hcast]
    field_simp [hcard_ne, hpow_ne]
  calc
    descendantsAverage Q (j + 1) F
        = ((((descendantsAtDepth Q j).card * 3 ^ d : ℕ) : ℝ)⁻¹) *
            ∑ S ∈ descendantsAtDepth Q (j + 1), F S := by
              rw [descendantsAverage, descendantsAtDepth_card_succ]
    _ = ((((descendantsAtDepth Q j).card * 3 ^ d : ℕ) : ℝ)⁻¹) *
          ∑ R ∈ D, ∑ S ∈ childCubes R, F S := by
            rw [hsum]
    _ = (((descendantsAtDepth Q j).card : ℝ)⁻¹ * (((3 ^ d : ℕ) : ℝ)⁻¹)) *
          ∑ R ∈ D, ∑ S ∈ childCubes R, F S := by
            rw [hcoeff]
    _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ((((3 ^ d : ℕ) : ℝ)⁻¹) * ∑ R ∈ D, ∑ S ∈ childCubes R, F S) := by
            ring
    _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑ R ∈ D, ((((3 ^ d : ℕ) : ℝ)⁻¹) * ∑ S ∈ childCubes R, F S) := by
            rw [Finset.mul_sum]
    _ = descendantsAverage Q j (fun R => descendantsAverage R 1 F) := by
          simp [descendantsAverage, D, childCubes_card]

theorem descendantsAverage_mul_le_Lp_mul_Lq_of_nonneg {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (A B : TriadicCube d → ℝ) {p q : ℝ}
    (hpq : Real.HolderConjugate p q)
    (hA : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ A R)
    (hB : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ B R) :
    descendantsAverage Q j (fun R => A R * B R) ≤
      (descendantsAverage Q j (fun R => (A R) ^ p)) ^ (1 / p) *
        (descendantsAverage Q j (fun R => (B R) ^ q)) ^ (1 / q) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hD : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty Q j
  have hcard_pos : 0 < ((D.card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hD
  have hcard_nonneg : 0 ≤ ((D.card : ℕ) : ℝ) := le_of_lt hcard_pos
  have hscaleA_nonneg : 0 ≤ (D.card : ℝ) ^ (-1 / p) :=
    Real.rpow_nonneg hcard_nonneg _
  have hscaleB_nonneg : 0 ≤ (D.card : ℝ) ^ (-1 / q) :=
    Real.rpow_nonneg hcard_nonneg _
  have hscaleA_pow : ((D.card : ℝ) ^ (-1 / p)) ^ p = (D.card : ℝ)⁻¹ := by
    calc
      ((D.card : ℝ) ^ (-1 / p)) ^ p = (D.card : ℝ) ^ ((-1 / p) * p) := by
        rw [← Real.rpow_mul hcard_nonneg]
      _ = (D.card : ℝ) ^ (-1 : ℝ) := by
        congr 1
        field_simp [hpq.ne_zero]
      _ = (D.card : ℝ)⁻¹ := by
        rw [Real.rpow_neg_one]
  have hscaleB_pow : ((D.card : ℝ) ^ (-1 / q)) ^ q = (D.card : ℝ)⁻¹ := by
    calc
      ((D.card : ℝ) ^ (-1 / q)) ^ q = (D.card : ℝ) ^ ((-1 / q) * q) := by
        rw [← Real.rpow_mul hcard_nonneg]
      _ = (D.card : ℝ) ^ (-1 : ℝ) := by
        congr 1
        field_simp [hpq.symm.ne_zero]
      _ = (D.card : ℝ)⁻¹ := by
        rw [Real.rpow_neg_one]
  have hscale : (D.card : ℝ) ^ (-1 / p) * (D.card : ℝ) ^ (-1 / q) = (D.card : ℝ)⁻¹ := by
    have hsum : (-1 / p) + (-1 / q) = (-1 : ℝ) := by
      calc
        (-1 / p) + (-1 / q) = -((1 / p) + (1 / q)) := by ring
        _ = -1 := by
              rw [hpq.one_div_add_one_div]
              norm_num
    calc
      (D.card : ℝ) ^ (-1 / p) * (D.card : ℝ) ^ (-1 / q)
          = (D.card : ℝ) ^ ((-1 / p) + (-1 / q)) := by
              symm
              exact Real.rpow_add hcard_pos _ _
      _ = (D.card : ℝ) ^ (-1 : ℝ) := by
            simpa using congrArg (fun t : ℝ => (D.card : ℝ) ^ t) hsum
      _ = (D.card : ℝ)⁻¹ := by
            rw [Real.rpow_neg_one]
  have hholder :
      ∑ R ∈ D, ((D.card : ℝ) ^ (-1 / p) * A R) * ((D.card : ℝ) ^ (-1 / q) * B R) ≤
        (∑ R ∈ D, ((D.card : ℝ) ^ (-1 / p) * A R) ^ p) ^ (1 / p) *
          (∑ R ∈ D, ((D.card : ℝ) ^ (-1 / q) * B R) ^ q) ^ (1 / q) := by
    exact Real.inner_le_Lp_mul_Lq_of_nonneg
      (s := D)
      (f := fun R => (D.card : ℝ) ^ (-1 / p) * A R)
      (g := fun R => (D.card : ℝ) ^ (-1 / q) * B R)
      hpq
      (by
        intro R hR
        exact mul_nonneg hscaleA_nonneg (hA R (by simpa [D] using hR)))
      (by
        intro R hR
        exact mul_nonneg hscaleB_nonneg (hB R (by simpa [D] using hR)))
  have hleft :
      ∑ R ∈ D, ((D.card : ℝ) ^ (-1 / p) * A R) * ((D.card : ℝ) ^ (-1 / q) * B R) =
        (D.card : ℝ)⁻¹ * ∑ R ∈ D, A R * B R := by
    calc
      ∑ R ∈ D, ((D.card : ℝ) ^ (-1 / p) * A R) * ((D.card : ℝ) ^ (-1 / q) * B R)
          = ∑ R ∈ D, ((D.card : ℝ) ^ (-1 / p) * (D.card : ℝ) ^ (-1 / q)) * (A R * B R) := by
              refine Finset.sum_congr rfl ?_
              intro R hR
              ring
      _ = ∑ R ∈ D, (D.card : ℝ)⁻¹ * (A R * B R) := by
            simp [hscale]
      _ = (D.card : ℝ)⁻¹ * ∑ R ∈ D, A R * B R := by
            rw [Finset.mul_sum]
  have hrightA :
      ∑ R ∈ D, ((D.card : ℝ) ^ (-1 / p) * A R) ^ p =
        (D.card : ℝ)⁻¹ * ∑ R ∈ D, (A R) ^ p := by
    calc
      ∑ R ∈ D, ((D.card : ℝ) ^ (-1 / p) * A R) ^ p
          = ∑ R ∈ D, (((D.card : ℝ) ^ (-1 / p)) ^ p * (A R) ^ p) := by
              refine Finset.sum_congr rfl ?_
              intro R hR
              rw [Real.mul_rpow hscaleA_nonneg (hA R (by simpa [D] using hR))]
      _ = ∑ R ∈ D, (D.card : ℝ)⁻¹ * (A R) ^ p := by
            simp [hscaleA_pow]
      _ = (D.card : ℝ)⁻¹ * ∑ R ∈ D, (A R) ^ p := by
            rw [Finset.mul_sum]
  have hrightB :
      ∑ R ∈ D, ((D.card : ℝ) ^ (-1 / q) * B R) ^ q =
        (D.card : ℝ)⁻¹ * ∑ R ∈ D, (B R) ^ q := by
    calc
      ∑ R ∈ D, ((D.card : ℝ) ^ (-1 / q) * B R) ^ q
          = ∑ R ∈ D, (((D.card : ℝ) ^ (-1 / q)) ^ q * (B R) ^ q) := by
              refine Finset.sum_congr rfl ?_
              intro R hR
              rw [Real.mul_rpow hscaleB_nonneg (hB R (by simpa [D] using hR))]
      _ = ∑ R ∈ D, (D.card : ℝ)⁻¹ * (B R) ^ q := by
            simp [hscaleB_pow]
      _ = (D.card : ℝ)⁻¹ * ∑ R ∈ D, (B R) ^ q := by
            rw [Finset.mul_sum]
  calc
    descendantsAverage Q j (fun R => A R * B R)
        = (D.card : ℝ)⁻¹ * ∑ R ∈ D, A R * B R := by
            simp [descendantsAverage, D]
    _ = ∑ R ∈ D, ((D.card : ℝ) ^ (-1 / p) * A R) * ((D.card : ℝ) ^ (-1 / q) * B R) := by
          rw [hleft]
    _ ≤ (∑ R ∈ D, ((D.card : ℝ) ^ (-1 / p) * A R) ^ p) ^ (1 / p) *
          (∑ R ∈ D, ((D.card : ℝ) ^ (-1 / q) * B R) ^ q) ^ (1 / q) :=
          hholder
    _ = (descendantsAverage Q j (fun R => (A R) ^ p)) ^ (1 / p) *
          (descendantsAverage Q j (fun R => (B R) ^ q)) ^ (1 / q) := by
          simp [descendantsAverage, D, hrightA, hrightB]

theorem cubeBesovOscillation_nonneg {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → ℝ) :
    0 ≤ cubeBesovOscillation Q p u :=
  cubeLpNorm_nonneg Q p (cubeFluctuation Q u)

theorem cubeBesovOscillation_cubeFluctuation_eq_of_memLp_two {d : ℕ}
    (R Q : TriadicCube d) {u : Vec d → ℝ}
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeBesovOscillation R (2 : ℝ≥0∞) (cubeFluctuation Q u) =
      cubeBesovOscillation R (2 : ℝ≥0∞) u := by
  unfold cubeBesovOscillation
  rw [cubeFluctuation_cubeFluctuation_of_memLp_two R Q hu]

@[simp] theorem cubeBesovOscillation_const {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (c : ℝ) :
    cubeBesovOscillation Q p (fun _ => c) = 0 := by
  unfold cubeBesovOscillation
  rw [cubeFluctuation_const]
  change cubeLpNorm Q p (fun _ => (0 : ℝ)) = 0
  simp

@[simp] theorem cubeBesovOscillation_zero {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞) :
    cubeBesovOscillation Q p (fun _ => (0 : ℝ)) = 0 := by
  unfold cubeBesovOscillation
  rw [cubeFluctuation_zero]
  change cubeLpNorm Q p (fun _ => (0 : ℝ)) = 0
  simp

theorem cubeBesovScaleWeight_nonneg {d : ℕ} (s : ℝ) (Q : TriadicCube d) :
    0 ≤ cubeBesovScaleWeight s Q := by
  unfold cubeBesovScaleWeight
  exact Real.rpow_nonneg (le_of_lt (by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))) _

theorem cubeBesovScaleWeight_mul_eq_scaleWeight_add {d : ℕ}
    (r q : ℝ) (Q : TriadicCube d) :
    cubeBesovScaleWeight r Q * cubeBesovScaleWeight q Q =
      cubeBesovScaleWeight (r + q) Q := by
  have hpos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  unfold cubeBesovScaleWeight
  rw [← Real.rpow_add hpos]
  ring_nf

end Homogenization
