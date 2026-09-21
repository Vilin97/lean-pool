/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Duality.Definitions

/-! # Elementary -/

namespace Homogenization

open MeasureTheory.Measure
open scoped BigOperators ENNReal

@[simp] theorem cubeBesovPairing_comm {d : ℕ} (Q : TriadicCube d)
    (f g : Vec d → ℝ) :
    cubeBesovPairing Q f g = cubeBesovPairing Q g f := by
  simp [cubeBesovPairing, mul_comm]

@[simp] theorem cubeBesovPairing_const_left {d : ℕ} (Q : TriadicCube d)
    (c : ℝ) (g : Vec d → ℝ) :
    cubeBesovPairing Q (fun _ => c) g = c * cubeAverage Q g := by
  unfold cubeBesovPairing cubeAverage
  rw [MeasureTheory.integral_const_mul]
  ring

@[simp] theorem cubeBesovPairing_const_right {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) (c : ℝ) :
    cubeBesovPairing Q f (fun _ => c) = c * cubeAverage Q f := by
  rw [cubeBesovPairing_comm, cubeBesovPairing_const_left]

theorem abs_cubeBesovPairing_const_left_le_of_dual_test {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    (c : ℝ) (g : Vec d → ℝ) (hg : CubeBesovDualTest Q s p q N g) :
    |cubeBesovPairing Q (fun _ => c) g| ≤ cubeBesovScaleWeight (-s) Q * ‖c‖ := by
  calc
    |cubeBesovPairing Q (fun _ => c) g|
      = |c * cubeAverage Q g| := by rw [cubeBesovPairing_const_left]
    _ = ‖c‖ * ‖cubeAverage Q g‖ := by
          simp [abs_mul]
    _ = (cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight s Q) *
          (‖c‖ * ‖cubeAverage Q g‖) := by
          rw [cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight, one_mul]
    _ = (cubeBesovScaleWeight (-s) Q * ‖c‖) *
          (cubeBesovScaleWeight s Q * ‖cubeAverage Q g‖) := by ring
    _ ≤ (cubeBesovScaleWeight (-s) Q * ‖c‖) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact hg.scaleWeight_mul_norm_cubeAverage_le_one
          · exact mul_nonneg (cubeBesovScaleWeight_nonneg (-s) Q) (norm_nonneg _)
    _ = cubeBesovScaleWeight (-s) Q * ‖c‖ := by ring

@[simp] theorem cubeBesovPairing_zero_left {d : ℕ} (Q : TriadicCube d)
    (g : Vec d → ℝ) :
    cubeBesovPairing Q (fun _ => (0 : ℝ)) g = 0 := by
  unfold cubeBesovPairing
  simpa using cubeAverage_const Q (0 : ℝ)

@[simp] theorem cubeBesovPairing_zero_right {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    cubeBesovPairing Q f (fun _ => (0 : ℝ)) = 0 := by
  unfold cubeBesovPairing
  simpa using cubeAverage_const Q (0 : ℝ)

@[simp] theorem cubeBesovPairing_neg_left {d : ℕ} (Q : TriadicCube d)
    (f g : Vec d → ℝ) :
    cubeBesovPairing Q (fun x => -f x) g = -cubeBesovPairing Q f g := by
  unfold cubeBesovPairing cubeAverage
  simp_rw [neg_mul]
  rw [MeasureTheory.integral_neg, mul_neg]

@[simp] theorem cubeBesovPairing_neg_right {d : ℕ} (Q : TriadicCube d)
    (f g : Vec d → ℝ) :
    cubeBesovPairing Q f (fun x => -g x) = -cubeBesovPairing Q f g := by
  unfold cubeBesovPairing cubeAverage
  simp_rw [mul_neg]
  rw [MeasureTheory.integral_neg, mul_neg]

theorem cubeBesovDualPartialNormValueSet_nonneg {d : ℕ} {Q : TriadicCube d} {s : ℝ}
    {p q : ℝ≥0∞} {N : ℕ} {f : Vec d → ℝ} {r : ℝ}
    (hr : r ∈ cubeBesovDualPartialNormValueSet Q s p q N f) :
    0 ≤ r := by
  rcases hr with ⟨g, hg, rfl⟩
  exact abs_nonneg _

theorem cubeBesovDualPartialSeminormValueSet_nonneg {d : ℕ} {Q : TriadicCube d} {s : ℝ}
    {p q : ℝ≥0∞} {N : ℕ} {f : Vec d → ℝ} {r : ℝ}
    (hr : r ∈ cubeBesovDualPartialSeminormValueSet Q s p q N f) :
    0 ≤ r := by
  rcases hr with ⟨g, hg, rfl⟩
  exact abs_nonneg _

@[simp] theorem cubeBesovDualTestNorm_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    cubeBesovDualTestNorm Q s p q N (fun _ => (0 : ℝ)) = 0 := by
  unfold cubeBesovDualTestNorm
  by_cases hq : cubeBesovConjExponent q = ∞
  · rw [if_pos hq]
    simpa using cubeBesovPartialNormTop_zero
      (Q := Q) (s := s) (p := cubeBesovConjExponent p) (N := N) hp0 hpTop
  · rw [if_neg hq]
    have hq0 : cubeBesovConjExponent q ≠ 0 := cubeBesovConjExponent_ne_zero q
    simpa using cubeBesovPartialNorm_zero
      (Q := Q) (s := s) (p := cubeBesovConjExponent p) (q := cubeBesovConjExponent q)
      (N := N) hp0 hpTop hq0 hq

@[simp] theorem cubeBesovDualTestSeminorm_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    cubeBesovDualTestSeminorm Q s p q N (fun _ => (0 : ℝ)) = 0 := by
  unfold cubeBesovDualTestSeminorm
  by_cases hq : cubeBesovConjExponent q = ∞
  · rw [if_pos hq]
    simpa using cubeBesovPartialSeminormTop_zero
      (Q := Q) (s := s) (p := cubeBesovConjExponent p) (N := N) hp0 hpTop
  · rw [if_neg hq]
    have hq0 : cubeBesovConjExponent q ≠ 0 := cubeBesovConjExponent_ne_zero q
    simpa using cubeBesovPartialSeminorm_zero
      (Q := Q) (s := s) (p := cubeBesovConjExponent p) (q := cubeBesovConjExponent q)
      (N := N) hp0 hpTop hq0 hq

theorem cubeBesovDualTest_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    CubeBesovDualTest Q s p q N (fun _ => (0 : ℝ)) := by
  unfold CubeBesovDualTest
  rw [cubeBesovDualTestNorm_zero Q s p q N hp0 hpTop]
  refine ⟨by norm_num, ?_⟩
  simpa using cubeBesovDualLocalMemLp_const Q p N (0 : ℝ)

theorem cubeBesovDualMeanZeroTest_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    CubeBesovDualMeanZeroTest Q s p q N (fun _ => (0 : ℝ)) := by
  refine ⟨?_, by simpa using cubeAverage_const Q (0 : ℝ), ?_⟩
  · rw [cubeBesovDualTestSeminorm_zero Q s p q N hp0 hpTop]
    norm_num
  · simpa using cubeBesovDualLocalMemLp_const Q p N (0 : ℝ)

theorem zero_mem_cubeBesovDualPartialNormValueSet {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (f : Vec d → ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    0 ∈ cubeBesovDualPartialNormValueSet Q s p q N f := by
  refine ⟨fun _ => (0 : ℝ), cubeBesovDualTest_zero Q s p q N hp0 hpTop, ?_⟩
  simp

theorem zero_mem_cubeBesovDualPartialSeminormValueSet {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (f : Vec d → ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    0 ∈ cubeBesovDualPartialSeminormValueSet Q s p q N f := by
  refine ⟨fun _ => (0 : ℝ),
    cubeBesovDualMeanZeroTest_zero Q s p q N hp0 hpTop, ?_⟩
  simp

theorem cubeBesovDualPartialNormValueSet_nonempty {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (f : Vec d → ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    (cubeBesovDualPartialNormValueSet Q s p q N f).Nonempty :=
  ⟨0, zero_mem_cubeBesovDualPartialNormValueSet Q s p q N f hp0 hpTop⟩

theorem cubeBesovDualPartialSeminormValueSet_nonempty {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (f : Vec d → ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    (cubeBesovDualPartialSeminormValueSet Q s p q N f).Nonempty :=
  ⟨0, zero_mem_cubeBesovDualPartialSeminormValueSet Q s p q N f hp0 hpTop⟩

theorem cubeBesovDualPartialNorm_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (f : Vec d → ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞)
    (hBdd : BddAbove (cubeBesovDualPartialNormValueSet Q s p q N f)) :
    0 ≤ cubeBesovDualPartialNorm Q s p q N f := by
  unfold cubeBesovDualPartialNorm
  exact le_csSup hBdd
    (zero_mem_cubeBesovDualPartialNormValueSet Q s p q N f hp0 hpTop)

theorem cubeBesovDualPartialSeminorm_nonneg_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (f : Vec d → ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞)
    (hBdd : BddAbove (cubeBesovDualPartialSeminormValueSet Q s p q N f)) :
    0 ≤ cubeBesovDualPartialSeminorm Q s p q N f := by
  unfold cubeBesovDualPartialSeminorm
  exact le_csSup hBdd
    (zero_mem_cubeBesovDualPartialSeminormValueSet Q s p q N f hp0 hpTop)

theorem cubeBesovDualPartialNormValueSet_const_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (c : ℝ) :
    BddAbove (cubeBesovDualPartialNormValueSet Q s p q N (fun _ => c)) := by
  refine ⟨cubeBesovScaleWeight (-s) Q * ‖c‖, ?_⟩
  intro r hr
  rcases hr with ⟨g, hg, rfl⟩
  exact abs_cubeBesovPairing_const_left_le_of_dual_test Q s p q N c g hg

theorem cubeBesovDualPartialNorm_const_le {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (c : ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    cubeBesovDualPartialNorm Q s p q N (fun _ => c) ≤ cubeBesovScaleWeight (-s) Q * ‖c‖ := by
  unfold cubeBesovDualPartialNorm
  refine csSup_le ?_ ?_
  · exact cubeBesovDualPartialNormValueSet_nonempty Q s p q N (fun _ => c) hp0 hpTop
  · intro r hr
    rcases hr with ⟨g, hg, rfl⟩
    exact abs_cubeBesovPairing_const_left_le_of_dual_test Q s p q N c g hg

theorem cubeBesovDualTest_const_scaleWeight_neg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    CubeBesovDualTest Q s p q N (fun _ => cubeBesovScaleWeight (-s) Q) := by
  unfold CubeBesovDualTest
  by_cases hq : cubeBesovConjExponent q = ∞
  · rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s p q N
      (fun _ => cubeBesovScaleWeight (-s) Q) hq]
    rw [cubeBesovPartialNormTop_const (Q := Q) (s := s)
      (p := cubeBesovConjExponent p) (N := N) (u := cubeBesovScaleWeight (-s) Q) hp0 hpTop]
    rw [Real.norm_of_nonneg (cubeBesovScaleWeight_nonneg (-s) Q)]
    have hmul : cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q = 1 := by
      simpa [mul_comm] using cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight Q s
    refine ⟨by simp [hmul], ?_⟩
    exact cubeBesovDualLocalMemLp_const Q p N (cubeBesovScaleWeight (-s) Q)
  · have hq0 : cubeBesovConjExponent q ≠ 0 := cubeBesovConjExponent_ne_zero q
    rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s p q N
      (fun _ => cubeBesovScaleWeight (-s) Q) hq]
    rw [cubeBesovPartialNorm_const (Q := Q) (s := s)
      (p := cubeBesovConjExponent p) (q := cubeBesovConjExponent q) (N := N)
      (u := cubeBesovScaleWeight (-s) Q) hp0 hpTop hq0 hq]
    rw [Real.norm_of_nonneg (cubeBesovScaleWeight_nonneg (-s) Q)]
    have hmul : cubeBesovScaleWeight s Q * cubeBesovScaleWeight (-s) Q = 1 := by
      simpa [mul_comm] using cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight Q s
    refine ⟨by simp [hmul], ?_⟩
    exact cubeBesovDualLocalMemLp_const Q p N (cubeBesovScaleWeight (-s) Q)

@[simp] theorem cubeBesovDualPartialNorm_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (c : ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    cubeBesovDualPartialNorm Q s p q N (fun _ => c) =
      cubeBesovScaleWeight (-s) Q * ‖c‖ := by
  apply le_antisymm
  · exact cubeBesovDualPartialNorm_const_le Q s p q N c hp0 hpTop
  · refine le_csSup
      (cubeBesovDualPartialNormValueSet_const_bddAbove Q s p q N c) ?_
    refine ⟨fun _ => cubeBesovScaleWeight (-s) Q,
      cubeBesovDualTest_const_scaleWeight_neg Q s p q N hp0 hpTop, ?_⟩
    rw [cubeBesovPairing_const_left, cubeAverage_const]
    simp [abs_mul, abs_of_nonneg (cubeBesovScaleWeight_nonneg (-s) Q), mul_comm]

@[simp] theorem cubeBesovDualPartialSeminormValueSet_const {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (c : ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    cubeBesovDualPartialSeminormValueSet Q s p q N (fun _ => c) = {0} := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨g, hg, rfl⟩
    rcases hg with ⟨-, havg, -⟩
    rw [cubeBesovPairing_const_left, havg]
    simp
  · intro hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact zero_mem_cubeBesovDualPartialSeminormValueSet Q s p q N (fun _ => c) hp0 hpTop

@[simp] theorem cubeBesovDualPartialSeminorm_const {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (c : ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    cubeBesovDualPartialSeminorm Q s p q N (fun _ => c) = 0 := by
  rw [cubeBesovDualPartialSeminorm,
    cubeBesovDualPartialSeminormValueSet_const Q s p q N c hp0 hpTop]
  simp

@[simp] theorem cubeBesovDualPartialNormValueSet_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    cubeBesovDualPartialNormValueSet Q s p q N (fun _ => (0 : ℝ)) = {0} := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨g, hg, rfl⟩
    simp
  · intro hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact zero_mem_cubeBesovDualPartialNormValueSet Q s p q N (fun _ => (0 : ℝ)) hp0 hpTop

@[simp] theorem cubeBesovDualPartialSeminormValueSet_zero {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    cubeBesovDualPartialSeminormValueSet Q s p q N (fun _ => (0 : ℝ)) = {0} := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨g, hg, rfl⟩
    simp
  · intro hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact zero_mem_cubeBesovDualPartialSeminormValueSet Q s p q N (fun _ => (0 : ℝ)) hp0 hpTop

@[simp] theorem cubeBesovDualPartialNorm_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    cubeBesovDualPartialNorm Q s p q N (fun _ => (0 : ℝ)) = 0 := by
  rw [cubeBesovDualPartialNorm, cubeBesovDualPartialNormValueSet_zero Q s p q N hp0 hpTop]
  simp

@[simp] theorem cubeBesovDualPartialSeminorm_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    cubeBesovDualPartialSeminorm Q s p q N (fun _ => (0 : ℝ)) = 0 := by
  rw [cubeBesovDualPartialSeminorm, cubeBesovDualPartialSeminormValueSet_zero Q s p q N hp0 hpTop]
  simp


end Homogenization
