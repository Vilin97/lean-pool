/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Positive

/-! # Projection Characterization -/

@[expose] public section

namespace Homogenization

open MeasureTheory.Measure
open scoped ENNReal

/-!
Local projection-characterization lemmas for the positive cube Besov package.

This first checkpoint stays deliberately depth-local. It identifies the
oscillation on each descendant cube with the local projection error against
`cubeProjection Q j`, then packages the resulting depth-average and
depth-seminorm reformulations. It also records the analogous local
`cubeIncrement` identity on descendants one generation deeper.
-/

noncomputable def cubeProjectionResidual {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => u x - cubeProjection Q j u x

noncomputable def cubeProjectionGap {d : ℕ} (Q : TriadicCube d) (j n : ℕ)
    (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => cubeProjection Q (j + n) u x - cubeProjection Q j u x

@[simp] theorem cubeProjectionResidual_apply {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (u : Vec d → ℝ) (x : Vec d) :
    cubeProjectionResidual Q j u x = u x - cubeProjection Q j u x := rfl

@[simp] theorem cubeProjectionGap_apply {d : ℕ} (Q : TriadicCube d) (j n : ℕ)
    (u : Vec d → ℝ) (x : Vec d) :
    cubeProjectionGap Q j n u x = cubeProjection Q (j + n) u x - cubeProjection Q j u x := rfl

theorem cubeFluctuation_ae_eq_sub_cubeProjection_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (u : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeFluctuation R u =ᵐ[normalizedCubeMeasure R] fun x => u x - cubeProjection Q j u x := by
  filter_upwards [cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) u hR] with x hx
  simp [cubeFluctuation, hx]

theorem cubeFluctuation_ae_eq_cubeProjectionResidual_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (u : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeFluctuation R u =ᵐ[normalizedCubeMeasure R] cubeProjectionResidual Q j u := by
  simpa [cubeProjectionResidual] using!
    cubeFluctuation_ae_eq_sub_cubeProjection_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) u hR

theorem cubeBesovOscillation_eq_cubeLpNorm_sub_cubeProjection_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeBesovOscillation R p u = cubeLpNorm R p (fun x => u x - cubeProjection Q j u x) := by
  unfold cubeBesovOscillation cubeLpNorm
  rw [Gagliardo.integralLpSeminorm_congr_ae
    (cubeFluctuation_ae_eq_sub_cubeProjection_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) u hR)]

theorem cubeBesovOscillation_eq_cubeLpNorm_cubeProjectionResidual_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeBesovOscillation R p u = cubeLpNorm R p (cubeProjectionResidual Q j u) := by
  simpa [cubeProjectionResidual] using!
    cubeBesovOscillation_eq_cubeLpNorm_sub_cubeProjection_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (p := p) u hR

theorem cubeBesovDepthAverage_eq_descendantsAverage_projection_error {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) :
    cubeBesovDepthAverage Q p u j =
      descendantsAverage Q j (fun R =>
        (cubeLpNorm R p (fun x => u x - cubeProjection Q j u x)) ^ p.toReal) := by
  classical
  unfold cubeBesovDepthAverage descendantsAverage
  refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro R hR
  rw [cubeBesovOscillation_eq_cubeLpNorm_sub_cubeProjection_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) (p := p) u hR]

theorem cubeBesovDepthAverage_eq_descendantsAverage_projectionResidual {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) :
    cubeBesovDepthAverage Q p u j =
      descendantsAverage Q j (fun R =>
        (cubeLpNorm R p (cubeProjectionResidual Q j u)) ^ p.toReal) := by
  simpa [cubeProjectionResidual] using!
    cubeBesovDepthAverage_eq_descendantsAverage_projection_error
      (Q := Q) (p := p) (u := u) (j := j)

theorem cubeBesovDepthSeminorm_eq_projection_error {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) :
    cubeBesovDepthSeminorm Q s p u j =
      cubeBesovDepthWeight Q s j *
        (descendantsAverage Q j (fun R =>
          (cubeLpNorm R p (fun x => u x - cubeProjection Q j u x)) ^ p.toReal)) ^
          (1 / p.toReal) := by
  simp [cubeBesovDepthSeminorm, cubeBesovDepthAverage_eq_descendantsAverage_projection_error]

theorem cubeBesovDepthSeminorm_eq_projectionResidual {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) (j : ℕ) :
    cubeBesovDepthSeminorm Q s p u j =
      cubeBesovDepthWeight Q s j *
        (descendantsAverage Q j (fun R =>
          (cubeLpNorm R p (cubeProjectionResidual Q j u)) ^ p.toReal)) ^
          (1 / p.toReal) := by
  simpa [cubeProjectionResidual] using!
    cubeBesovDepthSeminorm_eq_projection_error (Q := Q) (s := s) (p := p) (u := u) (j := j)

theorem cubeBesovPartialSeminorm_eq_projection_error {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) :
    cubeBesovPartialSeminorm Q s p q N u =
      (Finset.sum (Finset.range (N + 1)) fun j =>
        (cubeBesovDepthWeight Q s j *
          (descendantsAverage Q j (fun R =>
            (cubeLpNorm R p (fun x => u x - cubeProjection Q j u x)) ^ p.toReal)) ^
            (1 / p.toReal)) ^ q.toReal) ^
          (1 / q.toReal) := by
  unfold cubeBesovPartialSeminorm
  refine congrArg (fun t : ℝ => t ^ (1 / q.toReal)) ?_
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [cubeBesovDepthSeminorm_eq_projection_error]

theorem cubeBesovPartialNorm_eq_projection_error {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) :
    cubeBesovPartialNorm Q s p q N u =
      (Finset.sum (Finset.range (N + 1)) fun j =>
        (cubeBesovDepthWeight Q s j *
          (descendantsAverage Q j (fun R =>
            (cubeLpNorm R p (fun x => u x - cubeProjection Q j u x)) ^ p.toReal)) ^
          (1 / p.toReal)) ^ q.toReal) ^
          (1 / q.toReal) + cubeBesovScaleWeight s Q * ‖cubeAverage Q u‖ := by
  unfold cubeBesovPartialNorm
  rw [cubeBesovPartialSeminorm_eq_projection_error]

theorem sum_cubeIncrement_eq_cubeProjectionGap {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → ℝ) (j n : ℕ) :
    (fun x => Finset.sum (Finset.range n) (fun m => cubeIncrement Q (j + m + 1) u x)) =
      cubeProjectionGap Q j n u := by
  funext x
  induction n with
  | zero =>
      simp [cubeProjectionGap]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hinc :
          cubeIncrement Q (j + n + 1) u x =
            cubeProjection Q (j + n + 1) u x - cubeProjection Q (j + n) u x := by
        simpa [Nat.add_assoc] using
          congrArg (fun f : Vec d → ℝ => f x)
            (cubeIncrement_succ (Q := Q) (n := j + n) (f := u))
      rw [hinc]
      simp [cubeProjectionGap, Nat.add_assoc]

theorem cubeLpNorm_sum_cubeIncrement_eq_cubeProjectionGap {d : ℕ}
    (S Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) (j n : ℕ) :
    cubeLpNorm S p (fun x => Finset.sum (Finset.range n) (fun m => cubeIncrement Q (j + m + 1) u x)) =
      cubeLpNorm S p (cubeProjectionGap Q j n u) := by
  rw [sum_cubeIncrement_eq_cubeProjectionGap]

@[simp] theorem cubeBesovDepthAverage_depth_zero_eq_sub_cubeProjection {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) :
    cubeBesovDepthAverage Q p u 0 =
      (cubeLpNorm Q p (fun x => u x - cubeProjection Q 0 u x)) ^ p.toReal := by
  rw [cubeBesovDepthAverage_depth_zero]
  rw [cubeBesovOscillation_eq_cubeLpNorm_sub_cubeProjection_of_mem_descendantsAtDepth
    (Q := Q) (R := Q) (j := 0) (p := p) u]
  simp

@[simp] theorem cubeBesovDepthAverage_depth_zero_eq_sub_cubeIncrement {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) :
    cubeBesovDepthAverage Q p u 0 =
      (cubeLpNorm Q p (fun x => u x - cubeIncrement Q 0 u x)) ^ p.toReal := by
  simpa [cubeIncrement] using
    cubeBesovDepthAverage_depth_zero_eq_sub_cubeProjection (Q := Q) (p := p) (u := u)

theorem cubeIncrement_ae_eq_sub_cubeProjection_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (u : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q (j + 1)) :
    cubeIncrement Q (j + 1) u =ᵐ[normalizedCubeMeasure R]
      fun x => cubeAverage R u - cubeProjection Q j u x := by
  rw [normalizedCubeMeasure, Filter.EventuallyEq]
  exact ae_smul_measure
    ((MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet R)).2 <|
      Filter.Eventually.of_forall fun x hx =>
        cubeIncrement_eq_sub_cubeProjection_of_mem_descendantsAtDepth u hR hx)
    (ENNReal.ofReal ((cubeVolume R)⁻¹))

theorem cubeLpNorm_cubeIncrement_eq_sub_cubeProjection_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q (j + 1)) :
    cubeLpNorm R p (cubeIncrement Q (j + 1) u) =
      cubeLpNorm R p (fun x => cubeAverage R u - cubeProjection Q j u x) := by
  unfold cubeLpNorm
  rw [Gagliardo.integralLpSeminorm_congr_ae
    (cubeIncrement_ae_eq_sub_cubeProjection_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) u hR)]

theorem cubeProjectionGap_ae_eq_sub_cubeProjection_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} (u : Vec d → ℝ) {j n : ℕ}
    (hR : R ∈ descendantsAtDepth Q (j + n)) :
    cubeProjectionGap Q j n u =ᵐ[normalizedCubeMeasure R]
      (fun x => cubeAverage R u - cubeProjection Q j u x) := by
  filter_upwards [cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j + n) u hR] with x hx
  simp [cubeProjectionGap, hx]

theorem cubeLpNorm_cubeProjectionGap_eq_sub_cubeProjection_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} (p : ℝ≥0∞) (u : Vec d → ℝ) {j n : ℕ}
    (hR : R ∈ descendantsAtDepth Q (j + n)) :
    cubeLpNorm R p (cubeProjectionGap Q j n u) =
      cubeLpNorm R p (fun x => cubeAverage R u - cubeProjection Q j u x) := by
  unfold cubeLpNorm
  rw [Gagliardo.integralLpSeminorm_congr_ae
    (cubeProjectionGap_ae_eq_sub_cubeProjection_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (n := n) u hR)]

theorem sum_cubeIncrement_ae_eq_sub_cubeProjection_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} (u : Vec d → ℝ) {j n : ℕ}
    (hR : R ∈ descendantsAtDepth Q (j + n)) :
    (fun x => Finset.sum (Finset.range n) (fun m => cubeIncrement Q (j + m + 1) u x)) =ᵐ[normalizedCubeMeasure R]
      (fun x => cubeAverage R u - cubeProjection Q j u x) := by
  rw [sum_cubeIncrement_eq_cubeProjectionGap (Q := Q) (u := u) (j := j) (n := n)]
  exact cubeProjectionGap_ae_eq_sub_cubeProjection_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) (n := n) u hR

theorem cubeLpNorm_sum_cubeIncrement_eq_sub_cubeProjection_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} (p : ℝ≥0∞) (u : Vec d → ℝ) {j n : ℕ}
    (hR : R ∈ descendantsAtDepth Q (j + n)) :
    cubeLpNorm R p (fun x => Finset.sum (Finset.range n) (fun m => cubeIncrement Q (j + m + 1) u x)) =
      cubeLpNorm R p (fun x => cubeAverage R u - cubeProjection Q j u x) := by
  rw [cubeLpNorm_sum_cubeIncrement_eq_cubeProjectionGap (S := R) (Q := Q)]
  rw [cubeLpNorm_cubeProjectionGap_eq_sub_cubeProjection_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (p := p) (u := u) (j := j) (n := n) hR]

end Homogenization
