/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Definitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.MultiscalePoincare
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.VectorProduct
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesComponentwise

/-! # Cutoff Product -/

namespace Homogenization
namespace Book
namespace Ch01

open scoped BigOperators ENNReal

noncomputable section

/-!
# Cutoff/product estimate

This file retains the legacy disjoint-positive, totalized-real,
componentwise-circ compatibility surface for the cutoff/product Besov estimate
used later in the coarse Caccioppoli argument. It is not the exact manuscript
overlap/Euclidean statement. It is stated for a general smooth vector cutoff
field `ξ`; in the notes this is applied to `ξ = ∇φ`.
-/

namespace Legacy

/-- Legacy finite-depth cutoff/product compatibility estimate in the
disjoint-positive, totalized-real, componentwise-circ Besov convention; not
an exact manuscript overlap/Euclidean statement.

This is the pure product estimate.  Poincare, full-dual, and circ-budget
inputs belong to downstream corollaries, not to the Chapter 1 product surface. -/
theorem cutoffProductPositiveBesov_partial {d : ℕ}
    (Q : Cube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ)
    (ξ : Vec d → Vec d) {B : ℝ}
    (hB : 0 ≤ B)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (fun x => (u x - normalizedAverage Q u) • ξ x) ≤
      2 * (cubeScaleFactor Q * B *
          cubeL2ScalarPartialSeminormTwo Q (s - 1) N (cubeFluctuation Q u) +
        normalizedLpNorm Q ∞ ξ *
          cubeBesovPositiveScalarPartialSeminormTwo Q s N (cubeFluctuation Q u)) := by
  simpa [normalizedAverage, normalizedLpNorm] using!
    Homogenization.cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
      Q s N u ξ hB hu hξLp hξ hderiv

/-- Depth zero of the scalar positive Besov seminorm of a fluctuation is the
top-scale normalized `L²` norm. -/
private theorem cubeBesovDepthSeminorm_two_depth_zero_fluctuation_eq
    {d : ℕ} (Q : Cube d) (s : ℝ) (u : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (cubeFluctuation Q u) 0 =
      cubeBesovScaleWeight s Q * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) := by
  have hfluct : cubeFluctuation Q (cubeFluctuation Q u) = cubeFluctuation Q u :=
    cubeFluctuation_cubeFluctuation_of_memLp_two Q Q hu
  have hnonneg : 0 ≤ cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) :=
    cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (cubeFluctuation Q u)
  have hsq :
      (cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) =
        cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) := by
    simpa using sq_rpow_half_eq_of_nonneg hnonneg
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (cubeFluctuation Q u) 0
        =
          cubeBesovScaleWeight s Q *
            ((cubeLpNorm Q (2 : ℝ≥0∞)
              (cubeFluctuation Q (cubeFluctuation Q u))) ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) := by
            simp [cubeBesovDepthSeminorm, cubeBesovDepthAverage, descendantsAverage,
              cubeBesovOscillation]
    _ =
          cubeBesovScaleWeight s Q *
            ((cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u)) ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) := by
            rw [hfluct]
    _ = cubeBesovScaleWeight s Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) := by
            rw [hsq]

private theorem cubeBesovDepthSeminorm_le_partialNormTop_of_mem_range
    {d : ℕ} (Q : Cube d) (s : ℝ) (M j : ℕ) (u : Vec d → ℝ)
    (hj : j ∈ Finset.range (M + 1)) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j ≤
      cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M u := by
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j
        ≤ cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M u := by
          unfold cubeBesovPartialSeminormTop
          exact Finset.le_sup' (s := Finset.range (M + 1))
            (f := fun k => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u k) hj
    _ ≤ cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M u := by
          unfold cubeBesovPartialNormTop
          exact le_add_of_nonneg_right
            (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _))

private theorem cubeBesovScaleWeight_mul_cubeLpNorm_fluctuation_le_partialNormTop
    {d : ℕ} (Q : Cube d) (s : ℝ) (M : ℕ) (u : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovScaleWeight s Q * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
      cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (cubeFluctuation Q u) := by
  calc
    cubeBesovScaleWeight s Q * cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u)
        = cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (cubeFluctuation Q u) 0 := by
          rw [cubeBesovDepthSeminorm_two_depth_zero_fluctuation_eq Q s u hu]
    _ ≤ cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (cubeFluctuation Q u) := by
          exact cubeBesovDepthSeminorm_le_partialNormTop_of_mem_range Q s M 0
            (cubeFluctuation Q u) (by simp)

private theorem cubeL2ScalarDepthSeminorm_le_cubeLpNorm_two_of_lt_one
    {d : ℕ} (Q : Cube d) (s : ℝ) (j : ℕ) (v : Vec d → ℝ)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs1 : s < 1) :
    cubeL2ScalarDepthSeminorm Q (s - 1) v j ≤
      cubeLpNorm Q (2 : ℝ≥0∞) v := by
  rw [cubeL2ScalarDepthSeminorm_eq_rpow_mul_cubeLpNorm_two Q (s - 1) v j hv]
  have hweight :
      Real.rpow (3 : ℝ) ((s - 1) * (j : ℝ)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
      have hj : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
      nlinarith)
  exact mul_le_of_le_one_left (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) v) hweight

private theorem cubeBesovScaleWeight_mul_cubeL2ScalarDepthSeminorm_fluctuation_le_partialNormTop
    {d : ℕ} (Q : Cube d) (s : ℝ) (M j : ℕ) (u : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hs1 : s < 1) :
    cubeBesovScaleWeight s Q *
        cubeL2ScalarDepthSeminorm Q (s - 1) (cubeFluctuation Q u) j ≤
      cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (cubeFluctuation Q u) := by
  have hfluct :
      MeasureTheory.MemLp (cubeFluctuation Q u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hu.sub (MeasureTheory.memLp_const (cubeAverage Q u))
  have hL2 :
      cubeL2ScalarDepthSeminorm Q (s - 1) (cubeFluctuation Q u) j ≤
        cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) :=
    cubeL2ScalarDepthSeminorm_le_cubeLpNorm_two_of_lt_one Q s j
      (cubeFluctuation Q u) hfluct hs1
  calc
    cubeBesovScaleWeight s Q *
        cubeL2ScalarDepthSeminorm Q (s - 1) (cubeFluctuation Q u) j
        ≤ cubeBesovScaleWeight s Q *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) := by
          exact mul_le_mul_of_nonneg_left hL2 (cubeBesovScaleWeight_nonneg s Q)
    _ ≤ cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (cubeFluctuation Q u) :=
          cubeBesovScaleWeight_mul_cubeLpNorm_fluctuation_le_partialNormTop Q s M u hu

private theorem cubeBesovScaleWeight_mul_positiveScalarDepthSeminorm_le_partialNormTop
    {d : ℕ} (Q : Cube d) (s : ℝ) (M j : ℕ) (v : Vec d → ℝ)
    (hj : j ∈ Finset.range (M + 1)) :
    cubeBesovScaleWeight s Q *
        cubeBesovPositiveScalarDepthSeminorm Q s v j ≤
      cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M v := by
  calc
    cubeBesovScaleWeight s Q * cubeBesovPositiveScalarDepthSeminorm Q s v j
        =
          (cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q) *
            cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j := by
          rw [cubeBesovPositiveScalarDepthSeminorm_eq_scaleWeight_neg_mul_cubeBesovDepthSeminorm_two]
          ring
    _ = cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) v j := by
          have hmul : cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q = 1 := by
            simpa [mul_comm] using cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight Q s
          rw [hmul]
          ring
    _ ≤ cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M v :=
          cubeBesovDepthSeminorm_le_partialNormTop_of_mem_range Q s M j v hj

private theorem cubeAverage_component_scalar_smul_le_linf_mul_l2
    {d : ℕ} (Q : Cube d) (v : Vec d → ℝ) (ξ : Vec d → Vec d) (i : Fin d)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q)) :
    ‖cubeAverage Q (fun x => (v x • ξ x) i)‖ ≤
      cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) v := by
  have hcoord :
      ‖cubeAverage Q (fun x => (v x • ξ x) i)‖ ≤
        ‖cubeAverageVec Q (fun x => v x • ξ x)‖ := by
    simpa [cubeAverageVec] using
      norm_le_pi_norm (cubeAverageVec Q (fun x => v x • ξ x)) i
  exact hcoord.trans
    (norm_cubeAverageVec_scalar_smul_le_cubeLpNorm_infty_mul_cubeLpNorm_two Q v ξ hv hξLp)

theorem cutoffProduct_component_partialNormTop_le_gradient_rhs
    {d : ℕ} [NeZero d] (Q : Cube d) (s : ℝ) (M : ℕ)
    (u : H1Function (openCubeSet Q)) (ξ : Vec d → Vec d) {B : ℝ}
    (hB : 0 ≤ B)
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : s < 1) (i : Fin d) :
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M
        (fun x => (cubeFluctuation Q (fun y => u y) x • ξ x) i) ≤
      (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
        ((fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ∑ i : Fin d,
            circNegativeBesovNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => u.grad x i)) := by
  let v : Vec d → ℝ := cubeFluctuation Q (fun x => u x)
  let F : Vec d → Vec d := fun x => v x • ξ x
  let P : ℝ :=
    (fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ∑ i : Fin d,
        circNegativeBesovNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x i)
  have hu : MeasureTheory.MemLp (fun x => u x) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure
  have hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    exact hu.sub (MeasureTheory.memLp_const (cubeAverage Q (fun x => u x)))
  have hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
    simpa [F, v] using! hξLp.smul (p := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hv
  have hP :
      cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M v ≤ P := by
    simpa [P, v] using
      h1_fluctuation_partialNormTop_two_le_sum_grad_circNorm Q s M u hs0 hs1
  have hsemi :
      cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M (fun x => F x i) ≤
        2 * (cubeScaleFactor Q * B * P + cubeLpNorm Q ∞ ξ * P) := by
    unfold cubeBesovPartialSeminormTop
    refine Finset.sup'_le
      (s := Finset.range (M + 1))
      (H := ⟨0, by simp⟩)
      (f := fun j => cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j) ?_
    intro j hj
    have hcomponent :
        cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j ≤
          cubeBesovScaleWeight s Q * cubeBesovPositiveVectorDepthSeminorm Q s F j :=
      cubeBesovDepthSeminorm_two_component_le_scaleWeight_mul_positiveVectorDepthSeminorm
        Q s F i j hF
    have hdepth :
        cubeBesovPositiveVectorDepthSeminorm Q s F j ≤
          2 * (cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j +
            cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j) := by
      simpa [F, v] using
        cubeBesovPositiveVectorDepthSeminorm_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
          Q s j v ξ hB hv hξLp hξ hderiv
    have hscaled :
        cubeBesovScaleWeight s Q * cubeBesovPositiveVectorDepthSeminorm Q s F j ≤
          cubeBesovScaleWeight s Q *
            (2 * (cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j +
              cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j)) := by
      exact mul_le_mul_of_nonneg_left hdepth (cubeBesovScaleWeight_nonneg s Q)
    have hterm1 :
        cubeBesovScaleWeight s Q * cubeL2ScalarDepthSeminorm Q (s - 1) v j ≤ P := by
      calc
        cubeBesovScaleWeight s Q * cubeL2ScalarDepthSeminorm Q (s - 1) v j
            ≤ cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M v := by
              simpa [v] using
                cubeBesovScaleWeight_mul_cubeL2ScalarDepthSeminorm_fluctuation_le_partialNormTop
                  Q s M j (fun x => u x) hu hs1
        _ ≤ P := hP
    have hterm2 :
        cubeBesovScaleWeight s Q * cubeBesovPositiveScalarDepthSeminorm Q s v j ≤ P := by
      calc
        cubeBesovScaleWeight s Q * cubeBesovPositiveScalarDepthSeminorm Q s v j
            ≤ cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M v :=
              cubeBesovScaleWeight_mul_positiveScalarDepthSeminorm_le_partialNormTop
                Q s M j v hj
        _ ≤ P := hP
    calc
      cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j
          ≤ cubeBesovScaleWeight s Q * cubeBesovPositiveVectorDepthSeminorm Q s F j :=
            hcomponent
      _ ≤ cubeBesovScaleWeight s Q *
            (2 * (cubeScaleFactor Q * B * cubeL2ScalarDepthSeminorm Q (s - 1) v j +
              cubeLpNorm Q ∞ ξ * cubeBesovPositiveScalarDepthSeminorm Q s v j)) :=
            hscaled
      _ = 2 * (cubeScaleFactor Q * B *
              (cubeBesovScaleWeight s Q * cubeL2ScalarDepthSeminorm Q (s - 1) v j) +
            cubeLpNorm Q ∞ ξ *
              (cubeBesovScaleWeight s Q * cubeBesovPositiveScalarDepthSeminorm Q s v j)) := by
            ring
      _ ≤ 2 * (cubeScaleFactor Q * B * P + cubeLpNorm Q ∞ ξ * P) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact add_le_add
              (mul_le_mul_of_nonneg_left hterm1
                (mul_nonneg (cubeScaleFactor_nonneg Q) hB))
              (mul_le_mul_of_nonneg_left hterm2 (cubeLpNorm_nonneg Q ∞ ξ))
  have hL2top :
      cubeBesovScaleWeight s Q * cubeLpNorm Q (2 : ℝ≥0∞) v ≤ P := by
    calc
      cubeBesovScaleWeight s Q * cubeLpNorm Q (2 : ℝ≥0∞) v
          ≤ cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M v := by
            simpa [v] using
              cubeBesovScaleWeight_mul_cubeLpNorm_fluctuation_le_partialNormTop
                Q s M (fun x => u x) hu
      _ ≤ P := hP
  have havg :
      cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => F x i)‖ ≤
        cubeLpNorm Q ∞ ξ * P := by
    have hraw :
        ‖cubeAverage Q (fun x => F x i)‖ ≤
          cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) v := by
      simpa [F] using cubeAverage_component_scalar_smul_le_linf_mul_l2 Q v ξ i hv hξLp
    calc
      cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => F x i)‖
          ≤ cubeBesovScaleWeight s Q *
              (cubeLpNorm Q ∞ ξ * cubeLpNorm Q (2 : ℝ≥0∞) v) := by
            exact mul_le_mul_of_nonneg_left hraw (cubeBesovScaleWeight_nonneg s Q)
      _ = cubeLpNorm Q ∞ ξ *
            (cubeBesovScaleWeight s Q * cubeLpNorm Q (2 : ℝ≥0∞) v) := by
            ring
      _ ≤ cubeLpNorm Q ∞ ξ * P := by
            exact mul_le_mul_of_nonneg_left hL2top (cubeLpNorm_nonneg Q ∞ ξ)
  calc
    cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (fun x => F x i)
        =
          cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M (fun x => F x i) +
            cubeBesovScaleWeight s Q * ‖cubeAverage Q (fun x => F x i)‖ := by
          rfl
    _ ≤ 2 * (cubeScaleFactor Q * B * P + cubeLpNorm Q ∞ ξ * P) +
          cubeLpNorm Q ∞ ξ * P := by
          exact add_le_add hsemi havg
    _ = (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) * P := by
          ring

private theorem cutoffProduct_component_positiveBesovNormTop_le_gradient_rhs
    {d : ℕ} [NeZero d] (Q : Cube d) (s : ℝ)
    (u : H1Function (openCubeSet Q)) (ξ : Vec d → Vec d) {B : ℝ}
    (hB : 0 ≤ B)
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : s < 1) (i : Fin d) :
    positiveBesovNormTop Q s (2 : ℝ≥0∞)
        (fun x => ((u x - normalizedAverage Q (fun y => u y)) • ξ x) i) ≤
      (2 * cubeScaleFactor Q * B + 3 * normalizedLpNorm Q ∞ ξ) *
        ((fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ∑ i : Fin d,
            circNegativeBesovNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => u.grad x i)) := by
  unfold positiveBesovNormTop
  refine csSup_le ?_ ?_
  · exact
      ⟨cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) 1
        (fun x => ((u x - normalizedAverage Q (fun y => u y)) • ξ x) i), ⟨0, by simp⟩⟩
  · intro r hr
    rcases hr with ⟨N, rfl⟩
    simpa [normalizedAverage, normalizedLpNorm, cubeFluctuation] using
      cutoffProduct_component_partialNormTop_le_gradient_rhs
        Q s (N + 1) u ξ hB hξLp hξ hderiv hs0 hs1 i

/-- Legacy infinite-depth cutoff/product compatibility estimate with the
disjoint-positive, totalized-real, componentwise-circ H1-facing right-hand
side; not an exact manuscript overlap/Euclidean statement.

The vector Besov norm is the componentwise public convention
`positiveBesovVectorNormTop`.  The estimate has no finite-depth parameter and
no local-multiscale or projected-Poincare contract hypotheses; all function-side
control is supplied by the already-proved `H¹` gradient-to-function corridor. -/
theorem cutoffProductPositiveBesov_infinite_from_h1 {d : ℕ} [NeZero d]
    (Q : Cube d) (s : ℝ) (u : H1Function (openCubeSet Q))
    (ξ : Vec d → Vec d) {B : ℝ}
    (hB : 0 ≤ B)
    (hξLp : MeasureTheory.MemLp ξ ∞ (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : s < 1) :
    positiveBesovVectorNormTop Q s (2 : ℝ≥0∞)
        (fun x => (u x - normalizedAverage Q (fun y => u y)) • ξ x) ≤
      (d : ℝ) *
        (2 * cubeScaleFactor Q * B + 3 * normalizedLpNorm Q ∞ ξ) *
          ((fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ∑ i : Fin d,
              circNegativeBesovNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => u.grad x i)) := by
  let K : ℝ :=
    (2 * cubeScaleFactor Q * B + 3 * normalizedLpNorm Q ∞ ξ) *
      ((fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ∑ i : Fin d,
          circNegativeBesovNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i))
  have hcomponent :
      ∀ i : Fin d,
        positiveBesovNormTop Q s (2 : ℝ≥0∞)
            (fun x => (((u x - normalizedAverage Q (fun y => u y)) • ξ x) i)) ≤ K := by
    intro i
    simpa [K] using
      cutoffProduct_component_positiveBesovNormTop_le_gradient_rhs
        Q s u ξ hB hξLp hξ hderiv hs0 hs1 i
  calc
    positiveBesovVectorNormTop Q s (2 : ℝ≥0∞)
        (fun x => (u x - normalizedAverage Q (fun y => u y)) • ξ x)
        ≤ ∑ _i : Fin d, K := by
          unfold positiveBesovVectorNormTop
          exact Finset.sum_le_sum fun i _hi => hcomponent i
    _ = (d : ℝ) * K := by
          simp [K, Fintype.card_fin, mul_assoc]
    _ =
      (d : ℝ) *
        (2 * cubeScaleFactor Q * B + 3 * normalizedLpNorm Q ∞ ξ) *
          ((fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ∑ i : Fin d,
              circNegativeBesovNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => u.grad x i)) := by
          simp [K, mul_assoc]

end Legacy

end

end Ch01
end Book
end Homogenization
