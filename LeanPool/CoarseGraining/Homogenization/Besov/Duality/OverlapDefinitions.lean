/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.Definitions
public import LeanPool.CoarseGraining.Homogenization.Besov.Positive.Overlap

/-! # Overlap Definitions -/

@[expose] public section

namespace Homogenization

open MeasureTheory.Measure
open scoped BigOperators ENNReal

/-!
Finite overlap dual-test definitions for cube Besov duality.

This module is the overlap counterpart of `Duality.Definitions`: it keeps
overlap-local measure and `MemLp` facts together with the finite-depth overlap
dual test norms, leaving global `sSup` wrappers to `Duality.OverlapFull`.
-/

namespace ScalarOverlap

theorem normalizedCubeMeasure_eq_smul_restrict_of_mem_centersAtDepth {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} (hS : S ∈ centersAtDepth Q j) :
    normalizedCubeMeasure S =
      ENNReal.ofReal (Homogenization.cubeVolume Q / cubeVolume S) •
        (Homogenization.normalizedCubeMeasure Q).restrict (cubeSet S) := by
  ext t ht
  have hQ : Homogenization.cubeVolume Q ≠ 0 := (Homogenization.cubeVolume_pos Q).ne'
  have hSvol : cubeVolume S ≠ 0 := (cubeVolume_pos S).ne'
  have hsubset : cubeSet S ⊆ Homogenization.cubeSet Q :=
    cubeSet_subset_cubeSet_of_mem_centersAtDepth hS
  have hinter :
      (t ∩ cubeSet S) ∩ Homogenization.cubeSet Q = t ∩ cubeSet S := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, hsubset hx.2⟩
  rw [normalizedCubeMeasure, MeasureTheory.Measure.smul_apply]
  rw [cubeMeasure, MeasureTheory.Measure.restrict_apply ht]
  rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply ht]
  rw [Homogenization.normalizedCubeMeasure, MeasureTheory.Measure.smul_apply]
  change ENNReal.ofReal ((cubeVolume S)⁻¹) * MeasureTheory.volume (t ∩ cubeSet S) =
    ENNReal.ofReal (Homogenization.cubeVolume Q / cubeVolume S) *
      (ENNReal.ofReal ((Homogenization.cubeVolume Q)⁻¹) *
        Homogenization.cubeMeasure Q (t ∩ cubeSet S))
  rw [Homogenization.cubeMeasure,
    MeasureTheory.Measure.restrict_apply (ht.inter (measurableSet_cubeSet S)), hinter]
  have hfactor :
      ENNReal.ofReal ((cubeVolume S)⁻¹) =
        ENNReal.ofReal (Homogenization.cubeVolume Q / cubeVolume S) *
          ENNReal.ofReal ((Homogenization.cubeVolume Q)⁻¹) := by
    have hdiv_nonneg : 0 ≤ Homogenization.cubeVolume Q / cubeVolume S :=
      div_nonneg (Homogenization.cubeVolume_nonneg Q) (cubeVolume_nonneg S)
    rw [← ENNReal.ofReal_mul hdiv_nonneg]
    congr 1
    field_simp [hQ, hSvol]
  rw [hfactor, ← mul_assoc]

theorem memLp_of_mem_centersAtDepth_of_memLp {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {p : ℝ≥0∞} {f : Vec d → ℝ}
    (hS : S ∈ centersAtDepth Q j)
    (hf : MeasureTheory.MemLp f p (Homogenization.normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp f p (normalizedCubeMeasure S) := by
  have hrestrict :
      MeasureTheory.MemLp f p
        ((Homogenization.normalizedCubeMeasure Q).restrict (cubeSet S)) :=
    hf.restrict (cubeSet S)
  have hle :
      normalizedCubeMeasure S ≤
        ENNReal.ofReal (Homogenization.cubeVolume Q / cubeVolume S) •
          ((Homogenization.normalizedCubeMeasure Q).restrict (cubeSet S)) := by
    simp [normalizedCubeMeasure_eq_smul_restrict_of_mem_centersAtDepth hS]
  exact hrestrict.of_measure_le_smul ENNReal.ofReal_ne_top hle

theorem memLp_sub_cubeAverage_of_mem_centersAtDepth_of_memLp {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {p : ℝ≥0∞} {f : Vec d → ℝ}
    (hS : S ∈ centersAtDepth Q j)
    (hf : MeasureTheory.MemLp f p (Homogenization.normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp (fun x => f x - cubeAverage S f) p
      (normalizedCubeMeasure S) := by
  exact
    (memLp_of_mem_centersAtDepth_of_memLp hS hf).sub
      (MeasureTheory.memLp_const (cubeAverage S f))

end ScalarOverlap

noncomputable def cubeBesovOverlapDualTestNorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ) : ℝ :=
  if cubeBesovConjExponent q = ∞ then
    cubeBesovOverlapPartialNormTop Q s (cubeBesovConjExponent p) N g
  else
    cubeBesovOverlapPartialNorm Q s (cubeBesovConjExponent p)
      (cubeBesovConjExponent q) N g

noncomputable def cubeBesovOverlapDualTestSeminorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ) : ℝ :=
  if cubeBesovConjExponent q = ∞ then
    cubeBesovOverlapPartialSeminormTop Q s (cubeBesovConjExponent p) N g
  else
    cubeBesovOverlapPartialSeminorm Q s (cubeBesovConjExponent p)
      (cubeBesovConjExponent q) N g

@[simp] theorem cubeBesovOverlapDualTestNorm_of_conjExponent_eq_top {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ)
    (hq : cubeBesovConjExponent q = ∞) :
    cubeBesovOverlapDualTestNorm Q s p q N g =
      cubeBesovOverlapPartialNormTop Q s (cubeBesovConjExponent p) N g := by
  simp [cubeBesovOverlapDualTestNorm, hq]

@[simp] theorem cubeBesovOverlapDualTestNorm_of_conjExponent_ne_top {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ)
    (hq : cubeBesovConjExponent q ≠ ∞) :
    cubeBesovOverlapDualTestNorm Q s p q N g =
      cubeBesovOverlapPartialNorm Q s (cubeBesovConjExponent p)
        (cubeBesovConjExponent q) N g := by
  simp [cubeBesovOverlapDualTestNorm, hq]

@[simp] theorem cubeBesovOverlapDualTestSeminorm_of_conjExponent_eq_top {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ)
    (hq : cubeBesovConjExponent q = ∞) :
    cubeBesovOverlapDualTestSeminorm Q s p q N g =
      cubeBesovOverlapPartialSeminormTop Q s (cubeBesovConjExponent p) N g := by
  simp [cubeBesovOverlapDualTestSeminorm, hq]

@[simp] theorem cubeBesovOverlapDualTestSeminorm_of_conjExponent_ne_top {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ)
    (hq : cubeBesovConjExponent q ≠ ∞) :
    cubeBesovOverlapDualTestSeminorm Q s p q N g =
      cubeBesovOverlapPartialSeminorm Q s (cubeBesovConjExponent p)
        (cubeBesovConjExponent q) N g := by
  simp [cubeBesovOverlapDualTestSeminorm, hq]

theorem cubeBesovOverlapDualTestNorm_eq_cubeBesovOverlapDualTestSeminorm_of_cubeAverage_eq_zero
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ)
    (g : Vec d → ℝ) (havg : cubeAverage Q g = 0) :
    cubeBesovOverlapDualTestNorm Q s p q N g =
      cubeBesovOverlapDualTestSeminorm Q s p q N g := by
  by_cases hq : cubeBesovConjExponent q = ∞
  · rw [cubeBesovOverlapDualTestNorm_of_conjExponent_eq_top Q s p q N g hq,
      cubeBesovOverlapDualTestSeminorm_of_conjExponent_eq_top Q s p q N g hq]
    unfold cubeBesovOverlapPartialNormTop
    rw [havg]
    simp
  · rw [cubeBesovOverlapDualTestNorm_of_conjExponent_ne_top Q s p q N g hq,
      cubeBesovOverlapDualTestSeminorm_of_conjExponent_ne_top Q s p q N g hq]
    unfold cubeBesovOverlapPartialNorm
    rw [havg]
    simp

def CubeBesovOverlapDualLocalMemLp {d : ℕ} (Q : TriadicCube d)
    (p : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ) : Prop :=
  ∀ j < N + 1, ∀ S ∈ ScalarOverlap.centersAtDepth Q j,
    MeasureTheory.MemLp (fun x => g x - ScalarOverlap.cubeAverage S g)
      (cubeBesovConjExponent p) (ScalarOverlap.normalizedCubeMeasure S)

theorem CubeBesovOverlapDualLocalMemLp.of_memLp_parent {d : ℕ} {Q : TriadicCube d}
    {p : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : MeasureTheory.MemLp g (cubeBesovConjExponent p) (normalizedCubeMeasure Q)) :
    CubeBesovOverlapDualLocalMemLp Q p N g := by
  intro j hj S hS
  exact ScalarOverlap.memLp_sub_cubeAverage_of_mem_centersAtDepth_of_memLp hS hg

def CubeBesovOverlapDualTest {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ) : Prop :=
  cubeBesovOverlapDualTestNorm Q s p q N g ≤ 1 ∧
    CubeBesovOverlapDualLocalMemLp Q p N g

def CubeBesovOverlapDualMeanZeroTest {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (g : Vec d → ℝ) : Prop :=
  cubeBesovOverlapDualTestSeminorm Q s p q N g ≤ 1 ∧
    cubeAverage Q g = 0 ∧
      CubeBesovOverlapDualLocalMemLp Q p N g

theorem CubeBesovOverlapDualTest.norm_le_one {d : ℕ} {Q : TriadicCube d} {s : ℝ}
    {p q : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovOverlapDualTest Q s p q N g) :
    cubeBesovOverlapDualTestNorm Q s p q N g ≤ 1 :=
  hg.1

theorem CubeBesovOverlapDualTest.local_memLp {d : ℕ} {Q : TriadicCube d}
    {p : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovOverlapDualLocalMemLp Q p N g) :
    ∀ j < N + 1, ∀ S ∈ ScalarOverlap.centersAtDepth Q j,
      MeasureTheory.MemLp (fun x => g x - ScalarOverlap.cubeAverage S g)
        (cubeBesovConjExponent p) (ScalarOverlap.normalizedCubeMeasure S) :=
  hg

theorem CubeBesovOverlapDualTest.memLp_admissible {d : ℕ} {Q : TriadicCube d}
    {s : ℝ} {p q : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovOverlapDualTest Q s p q N g) :
    ∀ j < N + 1, ∀ S ∈ ScalarOverlap.centersAtDepth Q j,
      MeasureTheory.MemLp (fun x => g x - ScalarOverlap.cubeAverage S g)
        (cubeBesovConjExponent p) (ScalarOverlap.normalizedCubeMeasure S) :=
  hg.2

theorem CubeBesovOverlapDualMeanZeroTest.seminorm_le_one {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovOverlapDualMeanZeroTest Q s p q N g) :
    cubeBesovOverlapDualTestSeminorm Q s p q N g ≤ 1 :=
  hg.1

theorem CubeBesovOverlapDualMeanZeroTest.cubeAverage_eq_zero {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovOverlapDualMeanZeroTest Q s p q N g) :
    cubeAverage Q g = 0 :=
  hg.2.1

theorem CubeBesovOverlapDualMeanZeroTest.memLp_admissible {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovOverlapDualMeanZeroTest Q s p q N g) :
    ∀ j < N + 1, ∀ S ∈ ScalarOverlap.centersAtDepth Q j,
      MeasureTheory.MemLp (fun x => g x - ScalarOverlap.cubeAverage S g)
        (cubeBesovConjExponent p) (ScalarOverlap.normalizedCubeMeasure S) :=
  hg.2.2

theorem cubeBesovOverlapDualLocalMemLp_const {d : ℕ} (Q : TriadicCube d)
    (p : ℝ≥0∞) (N : ℕ) (c : ℝ) :
    CubeBesovOverlapDualLocalMemLp Q p N (fun _ => c) := by
  intro j hj S hS
  have hzero :
      (fun x : Vec d => c - ScalarOverlap.cubeAverage S (fun _ => c)) =
        fun _ => (0 : ℝ) := by
    funext x
    simp
  rw [hzero]
  exact
    (MeasureTheory.memLp_const (0 : ℝ) :
      MeasureTheory.MemLp (fun _ : Vec d => (0 : ℝ))
        (cubeBesovConjExponent p) (ScalarOverlap.normalizedCubeMeasure S))

theorem CubeBesovOverlapDualMeanZeroTest.to_dual_test {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {N : ℕ} {g : Vec d → ℝ}
    (hg : CubeBesovOverlapDualMeanZeroTest Q s p q N g) :
    CubeBesovOverlapDualTest Q s p q N g := by
  rcases hg with ⟨hseminorm, havg, hmem⟩
  unfold CubeBesovOverlapDualTest
  rw [cubeBesovOverlapDualTestNorm_eq_cubeBesovOverlapDualTestSeminorm_of_cubeAverage_eq_zero
    Q s p q N g havg]
  exact ⟨hseminorm, hmem⟩

end Homogenization
