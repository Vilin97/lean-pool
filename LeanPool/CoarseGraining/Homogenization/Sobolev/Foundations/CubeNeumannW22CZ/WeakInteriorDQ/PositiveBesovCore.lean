/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson.DualTestNorm
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesComponentwise

/-! # Positive Besov Core -/

namespace Homogenization

open scoped BigOperators ENNReal Topology

noncomputable section

/-!
# Positive Besov handoff for the cube Neumann `W^{2,2}` route

This file records the algebraic endpoint bridge from the positive vector
Besov seminorms controlled by the Hessian/Poincare part of the C.2 argument
to the downstream `CubePoissonGradientDualTestNormL2CoreEstimate`.

The remaining analytic content is intentionally visible in the hypotheses:
uniform control of the positive vector partial seminorms of the Poisson
gradient, and of the component averages.
-/

/-- Componentwise `B¹_{2,1}` positive dual-test control by the positive vector
partial seminorm, plus the cube-average mode. This is the local form needed by
the Neumann CZ endpoint target. -/
theorem cubeBesovDualTestNorm_two_one_component_le_scaleWeight_mul_posVectorPartial_add_avg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (i : Fin d) (N : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => u x i) ≤
      cubeBesovScaleWeight s Q *
          cubeBesovPositiveVectorPartialSeminormTwo Q s N u +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => u x i)‖ := by
  have hconj :
      cubeBesovConjExponent (1 : ℝ≥0∞) = ∞ := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (1 : ℝ≥0∞)) (q := (∞ : ℝ≥0∞)))
  have hpConj :
      cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s
    (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => u x i) hconj]
  unfold cubeBesovPartialNormTop
  exact add_le_add
    (by
      simpa [hpConj] using
        cubeBesovPartialSeminormTop_two_component_le_scaleWeight_mul_positiveVectorPartialSeminormTwo
          Q s u i N hu)
    le_rfl

/-- Scalar form of the `q = 1` dual-test norm at `p = 2`: the top positive
partial seminorm plus the average mode. -/
theorem cubeBesovDualTestNorm_two_one_eq_partialSeminormTop_add_avg
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ) (g : Vec d → ℝ) :
    cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g =
      cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) N g +
        cubeBesovScaleWeight s Q * ‖cubeAverage Q g‖ := by
  have hconj :
      cubeBesovConjExponent (1 : ℝ≥0∞) = ∞ := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (1 : ℝ≥0∞)) (q := (∞ : ℝ≥0∞)))
  have hpConj :
      cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s
    (2 : ℝ≥0∞) (1 : ℝ≥0∞) N g hconj]
  simp [cubeBesovPartialNormTop, hpConj]

/-- A finite top seminorm is bounded once each depth seminorm in its finite
range is bounded. -/
theorem cubeBesovPartialSeminormTop_le_of_forall_depthSeminorm_le
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞)
    (N : ℕ) (g : Vec d → ℝ) {B : ℝ}
    (hB : ∀ j ∈ Finset.range (N + 1),
      cubeBesovDepthSeminorm Q s p g j ≤ B) :
    cubeBesovPartialSeminormTop Q s p N g ≤ B := by
  unfold cubeBesovPartialSeminormTop
  exact Finset.sup'_le
    (s := Finset.range (N + 1)) (H := ⟨0, by simp⟩)
    (f := fun j => cubeBesovDepthSeminorm Q s p g j) hB

/-- If the scalar oscillation is uniformly bounded on every depth-`j`
descendant, then the depth seminorm is bounded by the depth weight times that
uniform bound. -/
theorem cubeBesovDepthSeminorm_two_le_depthWeight_mul_of_descendant_oscillation_le
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (g : Vec d → ℝ)
    (j : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hosc : ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) g ≤ A) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) g j ≤
      cubeBesovDepthWeight Q s j * A := by
  have hsqAvg :
      descendantsAverage Q j
          (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) g) ^ 2) ≤
        A ^ 2 := by
    calc
      descendantsAverage Q j
          (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) g) ^ 2)
          ≤ descendantsAverage Q j (fun _R => A ^ 2) := by
            refine descendantsAverage_le_descendantsAverage Q j ?_
            intro R hR
            exact pow_le_pow_left₀
              (cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) g)
              (hosc R hR) 2
      _ = A ^ 2 := by simp
  have hAvgNonneg :
      0 ≤ descendantsAverage Q j
        (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) g) ^ 2) := by
    exact descendantsAverage_nonneg Q j _ fun R _hR => sq_nonneg _
  have hroot :
      (descendantsAverage Q j
          (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) g) ^ 2)) ^ (1 / 2 : ℝ)
        ≤ A := by
    calc
      (descendantsAverage Q j
          (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) g) ^ 2)) ^ (1 / 2 : ℝ)
          ≤ (A ^ 2) ^ (1 / 2 : ℝ) := by
            exact Real.rpow_le_rpow hAvgNonneg hsqAvg (by norm_num)
      _ = A := sq_rpow_half_eq_of_nonneg hA
  unfold cubeBesovDepthSeminorm cubeBesovDepthAverage
  simpa using
    mul_le_mul_of_nonneg_left hroot (cubeBesovDepthWeight_nonneg Q s j)

/-- Averaged version of the scalar depth handoff. If the scalar oscillation is
pointwise bounded by a nonnegative descendant-local quantity `A R`, then the
depth seminorm is bounded by the depth weight times the descendant `L²`
average of `A`. This is the form compatible with summing local Hessian energy,
rather than taking a sup over all descendants. -/
theorem cubeBesovDepthSeminorm_two_le_depthWeight_mul_descendantsAverage_sq_rpow_half
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (g : Vec d → ℝ)
    (j : ℕ) (A : TriadicCube d → ℝ)
    (_hA : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ A R)
    (hosc : ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) g ≤ A R) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) g j ≤
      cubeBesovDepthWeight Q s j *
        (descendantsAverage Q j (fun R => (A R) ^ 2)) ^ (1 / 2 : ℝ) := by
  have hsqAvg :
      descendantsAverage Q j
          (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) g) ^ 2) ≤
        descendantsAverage Q j (fun R => (A R) ^ 2) := by
    refine descendantsAverage_le_descendantsAverage Q j ?_
    intro R hR
    exact pow_le_pow_left₀
      (cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) g)
      (hosc R hR) 2
  have hAvgNonneg :
      0 ≤ descendantsAverage Q j
        (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) g) ^ 2) := by
    exact descendantsAverage_nonneg Q j _ fun R _hR => sq_nonneg _
  have hroot :
      (descendantsAverage Q j
          (fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) g) ^ 2)) ^ (1 / 2 : ℝ)
        ≤
      (descendantsAverage Q j (fun R => (A R) ^ 2)) ^ (1 / 2 : ℝ) := by
    exact Real.rpow_le_rpow hAvgNonneg hsqAvg (by norm_num)
  unfold cubeBesovDepthSeminorm cubeBesovDepthAverage
  simpa using
    mul_le_mul_of_nonneg_left hroot (cubeBesovDepthWeight_nonneg Q s j)

/-- If the Poisson gradient has uniform positive-vector Besov seminorm control
and controlled component averages, then it satisfies the exact downstream
`L²` core dual-test estimate.

This is deliberately conditional: proving the two hypotheses from the weak
Hessian witness and local Poincare is the remaining analytic bridge. -/
theorem cubePoissonGradientDualTestNormL2CoreEstimate_of_posVectorPartial_and_average
    {d : ℕ} {Q : TriadicCube d} {Cpos Cavg : ℝ}
    (hCpos : 0 ≤ Cpos) (hCavg : 0 ≤ Cavg)
    (hpos :
      ∀ (F : Vec d → ℝ)
        (_hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
        (_hmean : cubeAverage Q F = 0)
        (W : MeanZeroNeumannPoissonSolution Q F) (N : ℕ),
        cubeBesovScaleWeight 1 Q *
            cubeBesovPositiveVectorPartialSeminormTwo Q 1 N
              (fun x => W.w.toH1Function.grad x) ≤
          Cpos * cubeLpNorm Q (2 : ℝ≥0∞) F)
    (havg :
      ∀ (F : Vec d → ℝ)
        (_hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
        (_hmean : cubeAverage Q F = 0)
        (W : MeanZeroNeumannPoissonSolution Q F) (i : Fin d),
        cubeBesovScaleWeight 1 Q *
            ‖cubeAverage Q (fun x => W.w.toH1Function.grad x i)‖ ≤
          Cavg * cubeLpNorm Q (2 : ℝ≥0∞) F) :
    CubePoissonGradientDualTestNormL2CoreEstimate Q (Cpos + Cavg) := by
  refine ⟨add_nonneg hCpos hCavg, ?_⟩
  intro F hF hmean W
  let G : Vec d → Vec d := fun x => W.w.toH1Function.grad x
  have hGmem :
      MeasureTheory.MemLp G (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact MeasureTheory.MemLp.of_eval
      (fun i : Fin d => W.w.toH1Function.grad_memL2_normalizedCubeMeasure i)
  refine ⟨?_, ?_⟩
  · intro i N
    have hcomponent :=
      cubeBesovDualTestNorm_two_one_component_le_scaleWeight_mul_posVectorPartial_add_avg
        Q 1 G i N hGmem
    have hposN := hpos F hF hmean W N
    have havgi := havg F hF hmean W i
    calc
      cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => W.w.toH1Function.grad x i)
          ≤ cubeBesovScaleWeight 1 Q *
              cubeBesovPositiveVectorPartialSeminormTwo Q 1 N G +
            cubeBesovScaleWeight 1 Q *
              ‖cubeAverage Q (fun x => G x i)‖ := by
              simpa [G] using hcomponent
      _ ≤ Cpos * cubeLpNorm Q (2 : ℝ≥0∞) F +
            Cavg * cubeLpNorm Q (2 : ℝ≥0∞) F := by
              exact add_le_add hposN havgi
      _ = (Cpos + Cavg) * cubeLpNorm Q (2 : ℝ≥0∞) F := by
            ring
  · intro i
    exact cubeBesovDualLocalMemLpGlobal_component_of_memLp Q G i hGmem

/-- Scalar-top-seminorm version of the endpoint handoff. This is the form
fed most directly by descendant Poincare estimates for each gradient
component. -/
theorem cubePoissonGradientDualTestNormL2CoreEstimate_of_partialSeminormTop_and_average
    {d : ℕ} {Q : TriadicCube d} {Csemi Cavg : ℝ}
    (hCsemi : 0 ≤ Csemi) (hCavg : 0 ≤ Cavg)
    (hsemi :
      ∀ (F : Vec d → ℝ)
        (_hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
        (_hmean : cubeAverage Q F = 0)
        (W : MeanZeroNeumannPoissonSolution Q F) (i : Fin d) (N : ℕ),
        cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N
            (fun x => W.w.toH1Function.grad x i) ≤
          Csemi * cubeLpNorm Q (2 : ℝ≥0∞) F)
    (havg :
      ∀ (F : Vec d → ℝ)
        (_hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
        (_hmean : cubeAverage Q F = 0)
        (W : MeanZeroNeumannPoissonSolution Q F) (i : Fin d),
        cubeBesovScaleWeight 1 Q *
            ‖cubeAverage Q (fun x => W.w.toH1Function.grad x i)‖ ≤
          Cavg * cubeLpNorm Q (2 : ℝ≥0∞) F) :
    CubePoissonGradientDualTestNormL2CoreEstimate Q (Csemi + Cavg) := by
  refine ⟨add_nonneg hCsemi hCavg, ?_⟩
  intro F hF hmean W
  let G : Vec d → Vec d := fun x => W.w.toH1Function.grad x
  have hGmem :
      MeasureTheory.MemLp G (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact MeasureTheory.MemLp.of_eval
      (fun i : Fin d => W.w.toH1Function.grad_memL2_normalizedCubeMeasure i)
  refine ⟨?_, ?_⟩
  · intro i N
    have hsemiN := hsemi F hF hmean W i N
    have havgi := havg F hF hmean W i
    calc
      cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
          (fun x => W.w.toH1Function.grad x i)
          =
            cubeBesovPartialSeminormTop Q 1 (2 : ℝ≥0∞) N
                (fun x => W.w.toH1Function.grad x i) +
              cubeBesovScaleWeight 1 Q *
                ‖cubeAverage Q (fun x => W.w.toH1Function.grad x i)‖ := by
              exact cubeBesovDualTestNorm_two_one_eq_partialSeminormTop_add_avg
                Q 1 N (fun x => W.w.toH1Function.grad x i)
      _ ≤ Csemi * cubeLpNorm Q (2 : ℝ≥0∞) F +
            Cavg * cubeLpNorm Q (2 : ℝ≥0∞) F := by
              exact add_le_add hsemiN havgi
      _ = (Csemi + Cavg) * cubeLpNorm Q (2 : ℝ≥0∞) F := by
            ring
  · intro i
    exact cubeBesovDualLocalMemLpGlobal_component_of_memLp Q G i hGmem

/-- Depthwise scalar-seminorm version of the endpoint handoff. This is the
form most directly targeted by descendant Poincare estimates. -/
theorem cubePoissonGradientDualTestNormL2CoreEstimate_of_depthSeminorm_and_average
    {d : ℕ} {Q : TriadicCube d} {Cdepth Cavg : ℝ}
    (hCdepth : 0 ≤ Cdepth) (hCavg : 0 ≤ Cavg)
    (hdepth :
      ∀ (F : Vec d → ℝ)
        (_hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
        (_hmean : cubeAverage Q F = 0)
        (W : MeanZeroNeumannPoissonSolution Q F) (i : Fin d) (N j : ℕ),
        j ∈ Finset.range (N + 1) →
          cubeBesovDepthSeminorm Q 1 (2 : ℝ≥0∞)
              (fun x => W.w.toH1Function.grad x i) j ≤
            Cdepth * cubeLpNorm Q (2 : ℝ≥0∞) F)
    (havg :
      ∀ (F : Vec d → ℝ)
        (_hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
        (_hmean : cubeAverage Q F = 0)
        (W : MeanZeroNeumannPoissonSolution Q F) (i : Fin d),
        cubeBesovScaleWeight 1 Q *
            ‖cubeAverage Q (fun x => W.w.toH1Function.grad x i)‖ ≤
          Cavg * cubeLpNorm Q (2 : ℝ≥0∞) F) :
    CubePoissonGradientDualTestNormL2CoreEstimate Q (Cdepth + Cavg) := by
  refine
    cubePoissonGradientDualTestNormL2CoreEstimate_of_partialSeminormTop_and_average
      hCdepth hCavg ?_ havg
  intro F hF hmean W i N
  exact
    cubeBesovPartialSeminormTop_le_of_forall_depthSeminorm_le
      Q 1 (2 : ℝ≥0∞) N (fun x => W.w.toH1Function.grad x i)
      (fun j hj => hdepth F hF hmean W i N j hj)

end

end Homogenization
