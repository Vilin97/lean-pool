/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.HarmonicGradient
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube

/-! # Definitions -/

namespace Homogenization

noncomputable section

open MeasureTheory.Measure
open scoped BigOperators ENNReal

noncomputable def cubeL2ScalarDepthAverage {d : ℕ}
    (Q : TriadicCube d) (v : Vec d → ℝ) (j : ℕ) : ℝ :=
  descendantsAverage Q j fun R => (cubeLpNorm R (2 : ℝ≥0∞) v) ^ 2

noncomputable def cubeL2ScalarDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (v : Vec d → ℝ) (j : ℕ) : ℝ :=
  Real.rpow (3 : ℝ) (s * (j : ℝ)) * Real.sqrt (cubeL2ScalarDepthAverage Q v j)

noncomputable def cubeL2ScalarPartialSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (v : Vec d → ℝ) : ℝ :=
  Real.sqrt <|
    Finset.sum (Finset.range (N + 1)) fun j =>
      (cubeL2ScalarDepthSeminorm Q s v j) ^ 2

noncomputable def cubeBesovPositiveScalarDepthAverage {d : ℕ}
    (Q : TriadicCube d) (v : Vec d → ℝ) (j : ℕ) : ℝ :=
  descendantsAverage Q j fun R => (cubeBesovOscillation R (2 : ℝ≥0∞) v) ^ 2

noncomputable def cubeBesovPositiveScalarDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (v : Vec d → ℝ) (j : ℕ) : ℝ :=
  Real.rpow (3 : ℝ) (s * (j : ℝ)) * Real.sqrt (cubeBesovPositiveScalarDepthAverage Q v j)

noncomputable def cubeBesovPositiveScalarPartialSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (v : Vec d → ℝ) : ℝ :=
  Real.sqrt <|
    Finset.sum (Finset.range (N + 1)) fun j =>
      (cubeBesovPositiveScalarDepthSeminorm Q s v j) ^ 2

theorem cubeL2ScalarDepthAverage_nonneg {d : ℕ}
    (Q : TriadicCube d) (v : Vec d → ℝ) (j : ℕ) :
    0 ≤ cubeL2ScalarDepthAverage Q v j := by
  unfold cubeL2ScalarDepthAverage
  exact descendantsAverage_nonneg Q j _ fun R hR => sq_nonneg _

theorem cubeL2ScalarDepthSeminorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (v : Vec d → ℝ) (j : ℕ) :
    0 ≤ cubeL2ScalarDepthSeminorm Q s v j := by
  unfold cubeL2ScalarDepthSeminorm
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (Real.sqrt_nonneg _)

theorem cubeBesovPositiveScalarDepthAverage_nonneg {d : ℕ}
    (Q : TriadicCube d) (v : Vec d → ℝ) (j : ℕ) :
    0 ≤ cubeBesovPositiveScalarDepthAverage Q v j := by
  unfold cubeBesovPositiveScalarDepthAverage
  exact descendantsAverage_nonneg Q j _ fun R hR => sq_nonneg _

theorem cubeBesovPositiveScalarDepthSeminorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (v : Vec d → ℝ) (j : ℕ) :
    0 ≤ cubeBesovPositiveScalarDepthSeminorm Q s v j := by
  unfold cubeBesovPositiveScalarDepthSeminorm
  exact mul_nonneg
    (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    (Real.sqrt_nonneg _)

theorem sq_cubeL2ScalarDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (v : Vec d → ℝ) (j : ℕ) :
    (cubeL2ScalarDepthSeminorm Q s v j) ^ 2 =
      (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 * cubeL2ScalarDepthAverage Q v j := by
  have hA : 0 ≤ cubeL2ScalarDepthAverage Q v j := cubeL2ScalarDepthAverage_nonneg Q v j
  calc
    (cubeL2ScalarDepthSeminorm Q s v j) ^ 2
        =
          (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (cubeL2ScalarDepthAverage Q v j)) ^ 2 := by
              rfl
    _ =
        (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
          (Real.sqrt (cubeL2ScalarDepthAverage Q v j)) ^ 2 := by
            ring
    _ =
        (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
          cubeL2ScalarDepthAverage Q v j := by
            rw [Real.sq_sqrt hA]

theorem sq_cubeL2ScalarPartialSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (v : Vec d → ℝ) :
    (cubeL2ScalarPartialSeminormTwo Q s N v) ^ 2 =
      Finset.sum (Finset.range (N + 1)) fun j =>
        (cubeL2ScalarDepthSeminorm Q s v j) ^ 2 := by
  unfold cubeL2ScalarPartialSeminormTwo
  simpa [pow_two] using
    Real.sq_sqrt
      (Finset.sum_nonneg fun j _ => sq_nonneg (cubeL2ScalarDepthSeminorm Q s v j))

theorem sq_cubeBesovPositiveScalarDepthSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (v : Vec d → ℝ) (j : ℕ) :
    (cubeBesovPositiveScalarDepthSeminorm Q s v j) ^ 2 =
      (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
        cubeBesovPositiveScalarDepthAverage Q v j := by
  have hA : 0 ≤ cubeBesovPositiveScalarDepthAverage Q v j :=
    cubeBesovPositiveScalarDepthAverage_nonneg Q v j
  calc
    (cubeBesovPositiveScalarDepthSeminorm Q s v j) ^ 2
        =
          (Real.rpow (3 : ℝ) (s * (j : ℝ)) *
            Real.sqrt (cubeBesovPositiveScalarDepthAverage Q v j)) ^ 2 := by
              rfl
    _ =
        (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
          (Real.sqrt (cubeBesovPositiveScalarDepthAverage Q v j)) ^ 2 := by
            ring
    _ =
        (Real.rpow (3 : ℝ) (s * (j : ℝ))) ^ 2 *
          cubeBesovPositiveScalarDepthAverage Q v j := by
            rw [Real.sq_sqrt hA]

theorem sq_cubeBesovPositiveScalarPartialSeminormTwo {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (v : Vec d → ℝ) :
    (cubeBesovPositiveScalarPartialSeminormTwo Q s N v) ^ 2 =
      Finset.sum (Finset.range (N + 1)) fun j =>
        (cubeBesovPositiveScalarDepthSeminorm Q s v j) ^ 2 := by
  unfold cubeBesovPositiveScalarPartialSeminormTwo
  simpa [pow_two] using
    Real.sq_sqrt
      (Finset.sum_nonneg fun j _ => sq_nonneg (cubeBesovPositiveScalarDepthSeminorm Q s v j))

theorem cubeBesovPositiveScalarDepthAverage_sub_const {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (c : ℝ) (j : ℕ)
    (hmem : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeBesovPositiveScalarDepthAverage Q (fun x => u x - c) j =
      cubeBesovPositiveScalarDepthAverage Q u j := by
  unfold cubeBesovPositiveScalarDepthAverage descendantsAverage
  refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro R hR
  congr 1
  apply cubeLpNorm_congr_on_cubeSet_generic R (2 : ℝ≥0∞)
  intro x hx
  simpa using congrFun (cubeFluctuation_sub_const R u c (hmem R hR)) x

theorem cubeBesovPositiveScalarDepthSeminorm_sub_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (u : Vec d → ℝ) (c : ℝ) (j : ℕ)
    (hmem : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeBesovPositiveScalarDepthSeminorm Q s (fun x => u x - c) j =
      cubeBesovPositiveScalarDepthSeminorm Q s u j := by
  unfold cubeBesovPositiveScalarDepthSeminorm
  rw [cubeBesovPositiveScalarDepthAverage_sub_const Q u c j hmem]

theorem cubeBesovPositiveScalarPartialSeminormTwo_sub_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ) (c : ℝ)
    (hmem : ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeBesovPositiveScalarPartialSeminormTwo Q s N (fun x => u x - c) =
      cubeBesovPositiveScalarPartialSeminormTwo Q s N u := by
  unfold cubeBesovPositiveScalarPartialSeminormTwo
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [cubeBesovPositiveScalarDepthSeminorm_sub_const Q s u c j (hmem j hj)]

theorem descendantsAverage_sq_const_mul {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (c : ℝ) (F : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => (c * F R) ^ 2) =
      c ^ 2 * descendantsAverage Q j (fun R => (F R) ^ 2) := by
  calc
    descendantsAverage Q j (fun R => (c * F R) ^ 2)
        = descendantsAverage Q j (fun R => c ^ 2 * (F R) ^ 2) := by
            refine congrArg (descendantsAverage Q j) ?_
            funext R
            ring
    _ = c ^ 2 * descendantsAverage Q j (fun R => (F R) ^ 2) := by
          rw [descendantsAverage_mul_left Q j (c ^ 2) (fun R => (F R) ^ 2)]

theorem sqrt_sum_sq_add_le {ι : Type*} (s : Finset ι) (A B : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hB : ∀ i ∈ s, 0 ≤ B i) :
    (∑ i ∈ s, (A i + B i) ^ 2) ^ (1 / 2 : ℝ) ≤
      (∑ i ∈ s, (A i) ^ 2) ^ (1 / 2 : ℝ) +
        (∑ i ∈ s, (B i) ^ 2) ^ (1 / 2 : ℝ) := by
  simpa using
    (Real.Lp_add_le_of_nonneg
      (s := s) (f := A) (g := B) (p := (2 : ℝ))
      (by norm_num) hA hB)

theorem descendantsAverage_L2_add_le {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (A B : TriadicCube d → ℝ)
    (hA : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ A R)
    (hB : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ B R) :
    (descendantsAverage Q j (fun R => (A R + B R) ^ 2)) ^ (1 / 2 : ℝ) ≤
      (descendantsAverage Q j (fun R => (A R) ^ 2)) ^ (1 / 2 : ℝ) +
        (descendantsAverage Q j (fun R => (B R) ^ 2)) ^ (1 / 2 : ℝ) := by
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let c : ℝ := ((D.card : ℝ)⁻¹)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr (by positivity)
  have hsumA_nonneg : 0 ≤ ∑ R ∈ D, (A R) ^ 2 := by
    exact Finset.sum_nonneg fun R hR => sq_nonneg _
  have hsumB_nonneg : 0 ≤ ∑ R ∈ D, (B R) ^ 2 := by
    exact Finset.sum_nonneg fun R hR => sq_nonneg _
  have hsumAB_nonneg : 0 ≤ ∑ R ∈ D, (A R + B R) ^ 2 := by
    exact Finset.sum_nonneg fun R hR => sq_nonneg _
  have hLp :
      (∑ R ∈ D, (A R + B R) ^ 2) ^ (1 / 2 : ℝ) ≤
        (∑ R ∈ D, (A R) ^ 2) ^ (1 / 2 : ℝ) +
          (∑ R ∈ D, (B R) ^ 2) ^ (1 / 2 : ℝ) := by
    simpa using
      (Real.Lp_add_le_of_nonneg
        (s := D) (f := A) (g := B) (p := (2 : ℝ))
        (by norm_num)
        (fun R hR => hA R (by simpa [D] using hR))
        (fun R hR => hB R (by simpa [D] using hR)))
  calc
    (descendantsAverage Q j (fun R => (A R + B R) ^ 2)) ^ (1 / 2 : ℝ)
        = c ^ (1 / 2 : ℝ) * (∑ R ∈ D, (A R + B R) ^ 2) ^ (1 / 2 : ℝ) := by
            have hmul :
                (c * ∑ R ∈ D, (A R + B R) ^ 2) ^ (1 / 2 : ℝ) =
                  c ^ (1 / 2 : ℝ) * (∑ R ∈ D, (A R + B R) ^ 2) ^ (1 / 2 : ℝ) :=
              Real.mul_rpow hc hsumAB_nonneg
            simpa [descendantsAverage, D, c] using hmul
    _ ≤ c ^ (1 / 2 : ℝ) * (∑ R ∈ D, (A R) ^ 2) ^ (1 / 2 : ℝ) +
          c ^ (1 / 2 : ℝ) * (∑ R ∈ D, (B R) ^ 2) ^ (1 / 2 : ℝ) := by
          have hc_rpow : 0 ≤ c ^ (1 / 2 : ℝ) := Real.rpow_nonneg hc _
          have hmul := mul_le_mul_of_nonneg_left hLp hc_rpow
          simpa [mul_add] using hmul
    _ = (descendantsAverage Q j (fun R => (A R) ^ 2)) ^ (1 / 2 : ℝ) +
          c ^ (1 / 2 : ℝ) * (∑ R ∈ D, (B R) ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← Real.mul_rpow hc hsumA_nonneg]
          simp [descendantsAverage, D, c]
    _ = (descendantsAverage Q j (fun R => (A R) ^ 2)) ^ (1 / 2 : ℝ) +
          (descendantsAverage Q j (fun R => (B R) ^ 2)) ^ (1 / 2 : ℝ) := by
          rw [← Real.mul_rpow hc hsumB_nonneg]
          simp [descendantsAverage, D, c]

theorem descendantsAverage_L2_const_mul_eq {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (c : ℝ) (F : TriadicCube d → ℝ) (hc : 0 ≤ c) :
    (descendantsAverage Q j (fun R => (c * F R) ^ 2)) ^ (1 / 2 : ℝ) =
      c * (descendantsAverage Q j (fun R => (F R) ^ 2)) ^ (1 / 2 : ℝ) := by
  have hF_nonneg : 0 ≤ descendantsAverage Q j (fun R => (F R) ^ 2) := by
    exact descendantsAverage_nonneg Q j _ fun R hR => sq_nonneg _
  rw [descendantsAverage_sq_const_mul Q j c F]
  rw [Real.mul_rpow (sq_nonneg c) hF_nonneg]
  rw [sq_rpow_half_eq_of_nonneg hc]

theorem sqrt_sum_sq_const_mul_eq {ι : Type*} (s : Finset ι) (c : ℝ) (F : ι → ℝ)
    (hc : 0 ≤ c) :
    Real.sqrt (∑ i ∈ s, (c * F i) ^ 2) =
      c * Real.sqrt (∑ i ∈ s, (F i) ^ 2) := by
  have hF_nonneg : 0 ≤ ∑ i ∈ s, (F i) ^ 2 := by
    exact Finset.sum_nonneg fun i hi => sq_nonneg _
  calc
    Real.sqrt (∑ i ∈ s, (c * F i) ^ 2)
        = Real.sqrt (c ^ 2 * ∑ i ∈ s, (F i) ^ 2) := by
            congr 1
            calc
              ∑ i ∈ s, (c * F i) ^ 2 = ∑ i ∈ s, c ^ 2 * (F i) ^ 2 := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
              _ = c ^ 2 * ∑ i ∈ s, (F i) ^ 2 := by
                rw [← Finset.mul_sum]
    _ = Real.sqrt (c ^ 2) * Real.sqrt (∑ i ∈ s, (F i) ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg c)]
    _ = c * Real.sqrt (∑ i ∈ s, (F i) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

theorem descendantsAverage_sqrt_const_mul_eq {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (c : ℝ) (F : TriadicCube d → ℝ) (hc : 0 ≤ c) :
    Real.sqrt (descendantsAverage Q j (fun R => (c * F R) ^ 2)) =
      c * Real.sqrt (descendantsAverage Q j (fun R => (F R) ^ 2)) := by
  simpa [Real.sqrt_eq_rpow] using descendantsAverage_L2_const_mul_eq Q j c F hc

theorem descendantsAverage_sqrt_add_le {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (A B : TriadicCube d → ℝ)
    (hA : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ A R)
    (hB : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ B R) :
    Real.sqrt (descendantsAverage Q j (fun R => (A R + B R) ^ 2)) ≤
      Real.sqrt (descendantsAverage Q j (fun R => (A R) ^ 2)) +
        Real.sqrt (descendantsAverage Q j (fun R => (B R) ^ 2)) := by
  simpa [Real.sqrt_eq_rpow] using descendantsAverage_L2_add_le Q j A B hA hB

theorem sqrt_sum_sq_add_le_sqrt {ι : Type*} (s : Finset ι) (A B : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hB : ∀ i ∈ s, 0 ≤ B i) :
    Real.sqrt (∑ i ∈ s, (A i + B i) ^ 2) ≤
      Real.sqrt (∑ i ∈ s, (A i) ^ 2) + Real.sqrt (∑ i ∈ s, (B i) ^ 2) := by
  simpa [Real.sqrt_eq_rpow] using sqrt_sum_sq_add_le s A B hA hB

theorem sqrt_sum_sq_le_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) :
    Real.sqrt (∑ i ∈ s, (A i) ^ 2) ≤ ∑ i ∈ s, A i := by
  have hsq :
      ∑ i ∈ s, (A i) ^ 2 ≤ (∑ i ∈ s, A i) ^ 2 := by
    simpa [pow_two] using Finset.sum_sq_le_sq_sum_of_nonneg hA
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, A i := Finset.sum_nonneg hA
  calc
    Real.sqrt (∑ i ∈ s, (A i) ^ 2)
        ≤ Real.sqrt ((∑ i ∈ s, A i) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ∑ i ∈ s, A i := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsum_nonneg]

theorem sqrt_sum_sq_sum_le_sum_sqrt_sum_sq {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (A : ι → κ → ℝ)
    (hA : ∀ i ∈ s, ∀ k ∈ t, 0 ≤ A i k) :
    Real.sqrt (∑ i ∈ s, (∑ k ∈ t, A i k) ^ 2) ≤
      ∑ k ∈ t, Real.sqrt (∑ i ∈ s, (A i k) ^ 2) := by
  induction t using Finset.induction_on with
  | empty =>
      simp
  | @insert a t ha ih =>
      have hsum_nonneg : ∀ i ∈ s, 0 ≤ ∑ k ∈ t, A i k := by
        intro i hi
        exact Finset.sum_nonneg fun k hk => hA i hi k (Finset.mem_insert_of_mem hk)
      calc
        Real.sqrt (∑ i ∈ s, (∑ k ∈ insert a t, A i k) ^ 2)
            = Real.sqrt (∑ i ∈ s, (A i a + ∑ k ∈ t, A i k) ^ 2) := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [Finset.sum_insert ha]
        _ ≤ Real.sqrt (∑ i ∈ s, (A i a) ^ 2) +
              Real.sqrt (∑ i ∈ s, (∑ k ∈ t, A i k) ^ 2) := by
                exact
                  sqrt_sum_sq_add_le_sqrt s (fun i => A i a) (fun i => ∑ k ∈ t, A i k)
                    (fun i hi => hA i hi a (by simp [ha]))
                    hsum_nonneg
        _ ≤ Real.sqrt (∑ i ∈ s, (A i a) ^ 2) +
              ∑ k ∈ t, Real.sqrt (∑ i ∈ s, (A i k) ^ 2) := by
                exact add_le_add le_rfl <|
                  ih (fun i hi k hk => hA i hi k (Finset.mem_insert_of_mem hk))
        _ = ∑ k ∈ insert a t, Real.sqrt (∑ i ∈ s, (A i k) ^ 2) := by
              simp [ha]

theorem cubeBesovPartialSeminorm_two_two_eq_sqrt_sum_sq {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (N : ℕ) (u : Vec d → ℝ) :
    cubeBesovPartialSeminorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N u =
      Real.sqrt (∑ j ∈ Finset.range (N + 1),
        (cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) u j) ^ 2) := by
  unfold cubeBesovPartialSeminorm
  norm_num [Real.sqrt_eq_rpow]

end

end Homogenization
