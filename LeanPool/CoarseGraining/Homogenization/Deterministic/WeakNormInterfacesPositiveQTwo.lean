/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesQTwo

/-! # Weak Norm Interfaces Positive QTwo -/

namespace Homogenization

noncomputable section

open MeasureTheory.Measure
open scoped BigOperators ENNReal

/-!
# Note-normalized positive `q = 2` vector weak norms

This file packages the minimal positive-order vector Besov surface needed on the
right-hand-side branch of the deterministic Chapter-3 argument. The
normalization is the note-facing one: when `Q` has scale `m`, the quantity here
corresponds to `3^(s m) [u]_{\underline{B}^{s}_{2,2}(Q)}`.
-/

theorem cubeLpNorm_congr_on_cubeSet_generic {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d) (p : ℝ≥0∞)
    {u v : Vec d → E} (h : ∀ x ∈ cubeSet Q, u x = v x) :
    cubeLpNorm Q p u = cubeLpNorm Q p v := by
  unfold cubeLpNorm
  rw [MeasureTheory.eLpNorm_congr_ae]
  rw [normalizedCubeMeasure, Filter.EventuallyEq]
  exact ae_smul_measure
    ((MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
      Filter.Eventually.of_forall h)
    (ENNReal.ofReal ((cubeVolume Q)⁻¹))

@[simp] theorem cubeAverageVec_const {d : ℕ} (Q : TriadicCube d) (c : Vec d) :
    cubeAverageVec Q (fun _ => c) = c := by
  funext i
  simp [cubeAverageVec, cubeAverage_const]

theorem cubeAverageVec_sub_const {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) (c : Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeAverageVec Q (fun x => u x - c) = cubeAverageVec Q u - c := by
  funext i
  have hui : MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
  have hui_int : MeasureTheory.Integrable (fun x => u x i) (normalizedCubeMeasure Q) :=
    hui.integrable (by norm_num)
  have hc_int : MeasureTheory.Integrable (fun _ : Vec d => c i) (normalizedCubeMeasure Q) :=
    MeasureTheory.integrable_const _
  calc
    cubeAverage Q (fun x => u x i - c i)
        = ∫ x, (u x i - c i) ∂ normalizedCubeMeasure Q := by
            rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    _ = ∫ x, u x i ∂ normalizedCubeMeasure Q - ∫ x, c i ∂ normalizedCubeMeasure Q := by
          rw [MeasureTheory.integral_sub hui_int hc_int]
    _ = cubeAverage Q (fun x => u x i) - cubeAverage Q (fun _ => c i) := by
          rw [cubeAverage_eq_integral_normalizedCubeMeasure,
            cubeAverage_eq_integral_normalizedCubeMeasure]
    _ = cubeAverage Q (fun x => u x i) - c i := by
          rw [cubeAverage_const]

theorem cubeAverageVec_sub_memLp {d : ℕ} (Q : TriadicCube d)
    (u v : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeAverageVec Q (fun x => u x - v x) = cubeAverageVec Q u - cubeAverageVec Q v := by
  funext i
  have hui : MeasureTheory.MemLp (fun x => u x i) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
  have hvi : MeasureTheory.MemLp (fun x => v x i) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hv
  have hui_int : MeasureTheory.Integrable (fun x => u x i)
      (normalizedCubeMeasure Q) :=
    hui.integrable (by norm_num)
  have hvi_int : MeasureTheory.Integrable (fun x => v x i)
      (normalizedCubeMeasure Q) :=
    hvi.integrable (by norm_num)
  calc
    cubeAverage Q (fun x => (u x - v x) i)
        = cubeAverage Q (fun x => u x i - v x i) := by
            rfl
    _ = ∫ x, (u x i - v x i) ∂ normalizedCubeMeasure Q := by
            rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    _ = ∫ x, u x i ∂ normalizedCubeMeasure Q -
          ∫ x, v x i ∂ normalizedCubeMeasure Q := by
          rw [MeasureTheory.integral_sub hui_int hvi_int]
    _ = cubeAverage Q (fun x => u x i) - cubeAverage Q (fun x => v x i) := by
          rw [cubeAverage_eq_integral_normalizedCubeMeasure,
            cubeAverage_eq_integral_normalizedCubeMeasure]

/-- Vector-valued fluctuation on a cube. -/
noncomputable def cubeFluctuationVec {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d) :
    Vec d → Vec d :=
  fun x => u x - cubeAverageVec Q u

@[simp] theorem cubeFluctuationVec_apply {d : ℕ} (Q : TriadicCube d) (u : Vec d → Vec d)
    (x : Vec d) :
    cubeFluctuationVec Q u x = u x - cubeAverageVec Q u :=
  rfl

@[simp] theorem cubeFluctuationVec_zero {d : ℕ} (Q : TriadicCube d) :
    cubeFluctuationVec Q (0 : Vec d → Vec d) = 0 := by
  have hmean : cubeAverageVec Q (0 : Vec d → Vec d) = 0 :=
    cubeAverageVec_const Q (0 : Vec d)
  funext x
  simp [cubeFluctuationVec, hmean]

@[simp] theorem cubeFluctuationVec_sub_const {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → Vec d) (c : Vec d)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeFluctuationVec Q (fun x => u x - c) = cubeFluctuationVec Q u := by
  funext x
  ext i
  calc
    cubeFluctuationVec Q (fun y => u y - c) x i
        = (u x i - c i) - cubeAverageVec Q (fun y => u y - c) i := by
            rfl
    _ = (u x i - c i) - (cubeAverageVec Q u i - c i) := by
          rw [cubeAverageVec_sub_const Q u c hu]
          simp
    _ = cubeFluctuationVec Q u x i := by
          simp [cubeFluctuationVec]

/-- The depth-`j` positive `q = 2` square average for a vector field on a parent cube `Q`. -/
noncomputable def cubeBesovPositiveVectorDepthAverage {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ) : ℝ :=
  descendantsAverage Q j fun R => (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R u)) ^ 2

/-- Note-normalized positive depth seminorm. For a parent cube of scale `m`, this is the
depth-`j` contribution to `3^(s m) [u]_{\underline{B}^{s}_{2,2}(Q)}`. -/
noncomputable def cubeBesovPositiveVectorDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) : ℝ :=
  Real.rpow (3 : ℝ) (s * (j : ℝ)) *
    Real.sqrt (cubeBesovPositiveVectorDepthAverage Q u j)

/-- Finite-depth note-normalized positive `q = 2` seminorm for vector fields. -/
noncomputable def cubeBesovPositiveVectorPartialSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) : ℝ :=
  Real.sqrt <|
    Finset.sum (Finset.range (N + 1)) fun j =>
      (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2

/-- Full note-normalized positive `q = 2` seminorm for vector fields. -/
noncomputable def cubeBesovPositiveVectorSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) : ℝ :=
  sSup (Set.range fun N : ℕ => cubeBesovPositiveVectorPartialSeminormTwo Q s N u)

theorem cubeBesovPositiveVectorDepthAverage_nonneg {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ) :
    0 ≤ cubeBesovPositiveVectorDepthAverage Q u j := by
  unfold cubeBesovPositiveVectorDepthAverage
  exact descendantsAverage_nonneg Q j _ fun R hR => sq_nonneg _

theorem cubeBesovPositiveVectorDepthSeminorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) :
    0 ≤ cubeBesovPositiveVectorDepthSeminorm Q s u j := by
  unfold cubeBesovPositiveVectorDepthSeminorm
  refine mul_nonneg ?_ ?_
  · exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  · exact Real.sqrt_nonneg _

theorem cubeBesovPositiveVectorPartialSeminormTwo_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) :
    0 ≤ cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
  unfold cubeBesovPositiveVectorPartialSeminormTwo
  exact Real.sqrt_nonneg _

@[simp] theorem cubeBesovPositiveVectorDepthAverage_zero {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    cubeBesovPositiveVectorDepthAverage Q (0 : Vec d → Vec d) j = 0 := by
  unfold cubeBesovPositiveVectorDepthAverage
  let D := descendantsAtDepth Q j
  change ((D.card : ℝ)⁻¹) *
      D.sum
        (fun R => cubeLpNorm R (2 : ℝ≥0∞)
          (cubeFluctuationVec R (0 : Vec d → Vec d)) ^ 2) =
    0
  have hsum :
      D.sum
        (fun R => cubeLpNorm R (2 : ℝ≥0∞)
          (cubeFluctuationVec R (0 : Vec d → Vec d)) ^ 2) =
        0 := by
    exact Finset.sum_eq_zero fun R hR => by
      have hnorm : cubeLpNorm R (2 : ℝ≥0∞) (0 : Vec d → Vec d) = 0 :=
        cubeLpNorm_zero R (2 : ℝ≥0∞)
      simp [hnorm]
  rw [hsum]
  simp

@[simp] theorem cubeBesovPositiveVectorDepthSeminorm_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    cubeBesovPositiveVectorDepthSeminorm Q s (0 : Vec d → Vec d) j = 0 := by
  simp [cubeBesovPositiveVectorDepthSeminorm]

@[simp] theorem cubeBesovPositiveVectorPartialSeminormTwo_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (0 : Vec d → Vec d) = 0 := by
  simp [cubeBesovPositiveVectorPartialSeminormTwo]

theorem cubeBesovPositiveVectorPartialSeminormTwo_zero_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
        (0 : Vec d → Vec d)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨N, rfl⟩
  simp

@[simp] theorem cubeBesovPositiveVectorSeminormTwo_zero {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) :
    cubeBesovPositiveVectorSeminormTwo Q s (0 : Vec d → Vec d) = 0 := by
  unfold cubeBesovPositiveVectorSeminormTwo
  rw [show Set.range
      (fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (0 : Vec d → Vec d)) =
        ({0} : Set ℝ) by
    ext x
    constructor
    · rintro ⟨N, rfl⟩
      simp
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨0, by simp [hx]⟩]
  simp

@[simp] theorem cubeBesovPositiveVectorDepthAverage_depth_zero {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) :
    cubeBesovPositiveVectorDepthAverage Q u 0 =
      (cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q u)) ^ 2 := by
  unfold cubeBesovPositiveVectorDepthAverage descendantsAverage
  simp

theorem sq_cubeBesovPositiveVectorDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j : ℕ) :
    (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2 =
      (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
        cubeBesovPositiveVectorDepthAverage Q u j := by
  have hA : 0 ≤ cubeBesovPositiveVectorDepthAverage Q u j :=
    cubeBesovPositiveVectorDepthAverage_nonneg Q u j
  calc
    (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2
        =
          (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (cubeBesovPositiveVectorDepthAverage Q u j)) ^ 2 := by
              rfl
    _ =
        (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
          (Real.sqrt (cubeBesovPositiveVectorDepthAverage Q u j)) ^ 2 := by
            ring
    _ =
        (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
          cubeBesovPositiveVectorDepthAverage Q u j := by
            rw [Real.sq_sqrt hA]

theorem sq_cubeBesovPositiveVectorPartialSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) :
    (cubeBesovPositiveVectorPartialSeminormTwo Q s N u) ^ 2 =
      Finset.sum (Finset.range (N + 1)) fun j =>
        (cubeBesovPositiveVectorDepthSeminorm Q s u j) ^ 2 := by
  unfold cubeBesovPositiveVectorPartialSeminormTwo
  simpa [pow_two] using
    Real.sq_sqrt
      (Finset.sum_nonneg fun j _ => sq_nonneg (cubeBesovPositiveVectorDepthSeminorm Q s u j))

theorem cubeBesovPositiveVectorDepthAverage_add_eq_descendantsAverage {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (j n : ℕ) :
    cubeBesovPositiveVectorDepthAverage Q u (j + n) =
      descendantsAverage Q j (fun R => cubeBesovPositiveVectorDepthAverage R u n) := by
  simpa [cubeBesovPositiveVectorDepthAverage] using
    (descendantsAverage_add_eq_descendantsAverage_descendantsAverage
      (Q := Q) (j := j) (n := n)
      (F := fun R => (cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuationVec R u)) ^ 2))

theorem descendantsAverage_sq_cubeBesovPositiveVectorDepthSeminorm_eq_shifted {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j n : ℕ) :
    (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
      descendantsAverage Q j (fun R => (cubeBesovPositiveVectorDepthSeminorm R s u n) ^ 2) =
        (cubeBesovPositiveVectorDepthSeminorm Q s u (j + n)) ^ 2 := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hshift :
      Real.rpow (3 : ℝ) (s * (j : ℝ)) * Real.rpow (3 : ℝ) (s * (n : ℝ)) =
        Real.rpow (3 : ℝ) (s * ((j + n : ℕ) : ℝ)) := by
    calc
      Real.rpow (3 : ℝ) (s * (j : ℝ)) * Real.rpow (3 : ℝ) (s * (n : ℝ))
          = Real.rpow (3 : ℝ) (s * (j : ℝ) + s * (n : ℝ)) := by
              symm
              exact Real.rpow_add h3 _ _
      _ = Real.rpow (3 : ℝ) (s * ((j + n : ℕ) : ℝ)) := by
            rw [Nat.cast_add]
            ring_nf
  calc
    (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
        descendantsAverage Q j (fun R => (cubeBesovPositiveVectorDepthSeminorm R s u n) ^ 2)
        =
          (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
            descendantsAverage Q j
              (fun R =>
                (Real.rpow (3 : ℝ) (s * (n : ℝ))) ^ 2 *
                  cubeBesovPositiveVectorDepthAverage R u n) := by
            congr 1
            refine congrArg (descendantsAverage Q j) ?_
            funext R
            rw [sq_cubeBesovPositiveVectorDepthSeminorm]
    _ =
        (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
          ((Real.rpow (3 : ℝ) (s * (n : ℝ))) ^ 2 *
            descendantsAverage Q j (fun R => cubeBesovPositiveVectorDepthAverage R u n)) := by
            rw [descendantsAverage_mul_left Q j
              ((Real.rpow (3 : ℝ) (s * (n : ℝ))) ^ 2)
              (fun R => cubeBesovPositiveVectorDepthAverage R u n)]
    _ =
        ((Real.rpow (3 : ℝ) (s * (j : ℝ))) * Real.rpow (3 : ℝ) (s * (n : ℝ))) ^ 2 *
          descendantsAverage Q j (fun R => cubeBesovPositiveVectorDepthAverage R u n) := by
            ring
    _ =
        (Real.rpow (3 : ℝ) (s * ((j + n : ℕ) : ℝ))) ^ 2 *
          descendantsAverage Q j (fun R => cubeBesovPositiveVectorDepthAverage R u n) := by
            congr 1
            exact congrArg (fun x : ℝ => x ^ 2) hshift
    _ =
        (Real.rpow (3 : ℝ) (s * ((j + n : ℕ) : ℝ))) ^ 2 *
          cubeBesovPositiveVectorDepthAverage Q u (j + n) := by
            rw [cubeBesovPositiveVectorDepthAverage_add_eq_descendantsAverage]
    _ = (cubeBesovPositiveVectorDepthSeminorm Q s u (j + n)) ^ 2 := by
          symm
          exact sq_cubeBesovPositiveVectorDepthSeminorm Q s u (j + n)

theorem descendantsAverage_sq_scaled_cubeBesovPositiveVectorPartialSeminormTwo_le {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j N : ℕ) :
    descendantsAverage Q j
      (fun R => (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        cubeBesovPositiveVectorPartialSeminormTwo R s N u) ^ 2) ≤
      (cubeBesovPositiveVectorPartialSeminormTwo Q s (j + N) u) ^ 2 := by
  calc
    descendantsAverage Q j
        (fun R => (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          cubeBesovPositiveVectorPartialSeminormTwo R s N u) ^ 2)
        =
          (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
            descendantsAverage Q j
              (fun R => (cubeBesovPositiveVectorPartialSeminormTwo R s N u) ^ 2) := by
            calc
              descendantsAverage Q j
                  (fun R => (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
                    cubeBesovPositiveVectorPartialSeminormTwo R s N u) ^ 2)
                  =
                    descendantsAverage Q j
                      (fun R =>
                        (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
                          (cubeBesovPositiveVectorPartialSeminormTwo R s N u) ^ 2) := by
                            refine congrArg (descendantsAverage Q j) ?_
                            funext R
                            ring_nf
              _ =
                  (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
                    descendantsAverage Q j
                      (fun R => (cubeBesovPositiveVectorPartialSeminormTwo R s N u) ^ 2) := by
                        rw [descendantsAverage_mul_left Q j
                          ((Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2)
                          (fun R => (cubeBesovPositiveVectorPartialSeminormTwo R s N u) ^ 2)]
    _ =
        (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
          descendantsAverage Q j
            (fun R => Finset.sum (Finset.range (N + 1))
              (fun n => (cubeBesovPositiveVectorDepthSeminorm R s u n) ^ 2)) := by
            congr 1
            refine congrArg (descendantsAverage Q j) ?_
            funext R
            exact sq_cubeBesovPositiveVectorPartialSeminormTwo R s N u
    _ =
        (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
          Finset.sum (Finset.range (N + 1))
            (fun n =>
              descendantsAverage Q j
                (fun R => (cubeBesovPositiveVectorDepthSeminorm R s u n) ^ 2)) := by
            rw [descendantsAverage_sum Q j (Finset.range (N + 1))
              (fun R n => (cubeBesovPositiveVectorDepthSeminorm R s u n) ^ 2)]
    _ =
        Finset.sum (Finset.range (N + 1))
          (fun n =>
            (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
              descendantsAverage Q j
                (fun R => (cubeBesovPositiveVectorDepthSeminorm R s u n) ^ 2)) := by
            rw [Finset.mul_sum]
    _ =
        Finset.sum (Finset.range (N + 1))
          (fun n => (cubeBesovPositiveVectorDepthSeminorm Q s u (j + n)) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            exact descendantsAverage_sq_cubeBesovPositiveVectorDepthSeminorm_eq_shifted
              Q s u j n
    _ = Finset.sum (Finset.Ico j (j + N + 1))
          (fun n => (cubeBesovPositiveVectorDepthSeminorm Q s u n) ^ 2) := by
            simpa [Nat.add_assoc] using
              (Finset.sum_Ico_eq_sum_range
                (f := fun n => (cubeBesovPositiveVectorDepthSeminorm Q s u n) ^ 2)
                (m := j) (n := j + N + 1)).symm
    _ ≤ Finset.sum (Finset.range (j + N + 1))
          (fun n => (cubeBesovPositiveVectorDepthSeminorm Q s u n) ^ 2) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro n hn
              exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
            · intro n hn hnot
              exact sq_nonneg (cubeBesovPositiveVectorDepthSeminorm Q s u n)
    _ = (cubeBesovPositiveVectorPartialSeminormTwo Q s (j + N) u) ^ 2 := by
          symm
          exact sq_cubeBesovPositiveVectorPartialSeminormTwo Q s (j + N) u

theorem descendantsAverage_scaled_cubeBesovPositiveVectorPartialSeminormTwo_le {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (j N : ℕ) :
    (descendantsAverage Q j
      (fun R => (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        cubeBesovPositiveVectorPartialSeminormTwo R s N u) ^ 2)) ^ (1 / 2 : ℝ) ≤
      cubeBesovPositiveVectorPartialSeminormTwo Q s (j + N) u := by
  have hsq :=
    descendantsAverage_sq_scaled_cubeBesovPositiveVectorPartialSeminormTwo_le Q s u j N
  have hleft_nonneg :
      0 ≤ descendantsAverage Q j
        (fun R => (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          cubeBesovPositiveVectorPartialSeminormTwo R s N u) ^ 2) := by
    exact descendantsAverage_nonneg Q j _ fun R hR => sq_nonneg _
  have hroot :
      (descendantsAverage Q j
        (fun R => (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          cubeBesovPositiveVectorPartialSeminormTwo R s N u) ^ 2)) ^ (1 / 2 : ℝ) ≤
        ((cubeBesovPositiveVectorPartialSeminormTwo Q s (j + N) u) ^ 2) ^ (1 / 2 : ℝ) := by
    exact Real.rpow_le_rpow hleft_nonneg hsq (by positivity)
  have hright_nonneg :
      0 ≤ cubeBesovPositiveVectorPartialSeminormTwo Q s (j + N) u :=
    cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s (j + N) u
  calc
    (descendantsAverage Q j
      (fun R => (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
        cubeBesovPositiveVectorPartialSeminormTwo R s N u) ^ 2)) ^ (1 / 2 : ℝ)
        ≤ ((cubeBesovPositiveVectorPartialSeminormTwo Q s (j + N) u) ^ 2) ^ (1 / 2 : ℝ) := hroot
    _ = cubeBesovPositiveVectorPartialSeminormTwo Q s (j + N) u := by
          exact sq_rpow_half_eq_of_nonneg hright_nonneg

theorem cubeBesovPositiveVectorSeminormTwo_le_of_partialBound {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) {B : ℝ}
    (hB : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo Q s N u ≤ B) :
    cubeBesovPositiveVectorSeminormTwo Q s u ≤ B := by
  unfold cubeBesovPositiveVectorSeminormTwo
  refine csSup_le ?_ ?_
  · exact ⟨cubeBesovPositiveVectorPartialSeminormTwo Q s 0 u, ⟨0, rfl⟩⟩
  · rintro x ⟨N, rfl⟩
    exact hB N

theorem cubeBesovPositiveVectorDepthSeminorm_le_of_exponent_le {d : ℕ}
    (Q : TriadicCube d) {s t : ℝ} (u : Vec d → Vec d) (j : ℕ)
    (hst : s ≤ t) :
    cubeBesovPositiveVectorDepthSeminorm Q s u j ≤
      cubeBesovPositiveVectorDepthSeminorm Q t u j := by
  unfold cubeBesovPositiveVectorDepthSeminorm
  have hpow :
      Real.rpow (3 : ℝ) (s * (j : ℝ)) ≤
        Real.rpow (3 : ℝ) (t * (j : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3)
      (mul_le_mul_of_nonneg_right hst (by positivity))
  exact mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg _)

theorem cubeBesovPositiveVectorPartialSeminormTwo_le_of_exponent_le {d : ℕ}
    (Q : TriadicCube d) {s t : ℝ} (u : Vec d → Vec d) (N : ℕ)
    (hst : s ≤ t) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N u ≤
      cubeBesovPositiveVectorPartialSeminormTwo Q t N u := by
  unfold cubeBesovPositiveVectorPartialSeminormTwo
  refine Real.sqrt_le_sqrt ?_
  refine Finset.sum_le_sum ?_
  intro j _hj
  exact pow_le_pow_left₀
    (cubeBesovPositiveVectorDepthSeminorm_nonneg Q s u j)
    (cubeBesovPositiveVectorDepthSeminorm_le_of_exponent_le Q u j hst)
    2

theorem cubeBesovPositiveVectorSeminormTwo_le_of_exponent_le_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) {s t : ℝ} (u : Vec d → Vec d)
    (hst : s ≤ t)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q t N u)) :
    cubeBesovPositiveVectorSeminormTwo Q s u ≤
      cubeBesovPositiveVectorSeminormTwo Q t u := by
  refine cubeBesovPositiveVectorSeminormTwo_le_of_partialBound Q s u ?_
  intro N
  calc
    cubeBesovPositiveVectorPartialSeminormTwo Q s N u
        ≤ cubeBesovPositiveVectorPartialSeminormTwo Q t N u :=
          cubeBesovPositiveVectorPartialSeminormTwo_le_of_exponent_le Q u N hst
    _ ≤ cubeBesovPositiveVectorSeminormTwo Q t u := by
          unfold cubeBesovPositiveVectorSeminormTwo
          exact le_csSup hBdd ⟨N, rfl⟩

theorem cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_exponent_le {d : ℕ}
    (Q : TriadicCube d) {s t : ℝ} (u : Vec d → Vec d)
    (hst : s ≤ t)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q t N u)) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo Q s N u) := by
  rcases hBdd with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  rintro x ⟨N, rfl⟩
  exact
    (cubeBesovPositiveVectorPartialSeminormTwo_le_of_exponent_le
      Q u N hst).trans (hB ⟨N, rfl⟩)

theorem cubeBesovPositiveVectorDepthAverage_sub_const {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (c : Vec d) (j : ℕ)
    (hmem : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeBesovPositiveVectorDepthAverage Q (fun x => u x - c) j =
      cubeBesovPositiveVectorDepthAverage Q u j := by
  unfold cubeBesovPositiveVectorDepthAverage descendantsAverage
  refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro R hR
  congr 1
  apply cubeLpNorm_congr_on_cubeSet_generic R (2 : ℝ≥0∞)
  intro x hx
  simpa using congrFun (cubeFluctuationVec_sub_const R u c (hmem R hR)) x

theorem cubeBesovPositiveVectorDepthSeminorm_sub_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (c : Vec d) (j : ℕ)
    (hmem : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeBesovPositiveVectorDepthSeminorm Q s (fun x => u x - c) j =
      cubeBesovPositiveVectorDepthSeminorm Q s u j := by
  unfold cubeBesovPositiveVectorDepthSeminorm
  rw [cubeBesovPositiveVectorDepthAverage_sub_const Q u c j hmem]

theorem cubeBesovPositiveVectorPartialSeminormTwo_sub_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → Vec d) (c : Vec d)
    (hmem : ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => u x - c) =
      cubeBesovPositiveVectorPartialSeminormTwo Q s N u := by
  unfold cubeBesovPositiveVectorPartialSeminormTwo
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [cubeBesovPositiveVectorDepthSeminorm_sub_const Q s u c j (hmem j hj)]

theorem cubeBesovPositiveVectorSeminormTwo_sub_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (c : Vec d)
    (hmem : ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeBesovPositiveVectorSeminormTwo Q s (fun x => u x - c) =
      cubeBesovPositiveVectorSeminormTwo Q s u := by
  unfold cubeBesovPositiveVectorSeminormTwo
  have hrange :
      Set.range (fun N : ℕ => cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => u x - c)) =
        Set.range (fun N : ℕ => cubeBesovPositiveVectorPartialSeminormTwo Q s N u) := by
    ext x
    constructor
    · rintro ⟨N, rfl⟩
      exact ⟨N, (cubeBesovPositiveVectorPartialSeminormTwo_sub_const Q s N u c
        (fun j _ R hR => hmem j R hR)).symm⟩
    · rintro ⟨N, rfl⟩
      exact ⟨N, cubeBesovPositiveVectorPartialSeminormTwo_sub_const Q s N u c
        (fun j _ R hR => hmem j R hR)⟩
  simp [hrange]

end

end Homogenization
