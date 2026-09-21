/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Duality.Full
import LeanPool.CoarseGraining.Homogenization.Besov.Duality.OverlapDefinitions

/-! # Overlap Full -/

namespace Homogenization

open MeasureTheory.Measure
open scoped BigOperators ENNReal

/-!
Global overlap wrapper layer for the cube Besov duality package.

This module contains the overlap analogues of the global dual-test norm,
mean-zero seminorm, depth-uniform local `MemLp` predicate, and finite-test
accessors. The disjoint full/circ API remains in `Duality.Full`.
-/

noncomputable def cubeBesovOverlapDualFullTestNorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (g : Vec d → ℝ) : ℝ :=
  sSup (Set.range (fun N : ℕ => cubeBesovOverlapDualTestNorm Q s p q N g))

noncomputable def cubeBesovOverlapDualMeanZeroTestSeminorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (g : Vec d → ℝ) : ℝ :=
  sSup (Set.range (fun N : ℕ => cubeBesovOverlapDualTestSeminorm Q s p q N g))

def CubeBesovOverlapDualLocalMemLpGlobal {d : ℕ} (Q : TriadicCube d)
    (p : ℝ≥0∞) (g : Vec d → ℝ) : Prop :=
  ∀ j : ℕ, ∀ S ∈ ScalarOverlap.centersAtDepth Q j,
    MeasureTheory.MemLp (fun x => g x - ScalarOverlap.cubeAverage S g)
      (cubeBesovConjExponent p) (ScalarOverlap.normalizedCubeMeasure S)

def CubeBesovOverlapDualFullTest {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (g : Vec d → ℝ) : Prop :=
  (∀ N : ℕ, cubeBesovOverlapDualTestNorm Q s p q N g ≤ 1) ∧
    CubeBesovOverlapDualLocalMemLpGlobal Q p g

def CubeBesovOverlapDualMeanZeroTestGlobal {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (g : Vec d → ℝ) : Prop :=
  (∀ N : ℕ, cubeBesovOverlapDualTestSeminorm Q s p q N g ≤ 1) ∧
    cubeAverage Q g = 0 ∧ CubeBesovOverlapDualLocalMemLpGlobal Q p g

theorem cubeBesovOverlapDualTestNorm_le_fullTestNorm_of_bddAbove {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (g : Vec d → ℝ)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovOverlapDualTestNorm Q s p q N g))
    (N : ℕ) :
    cubeBesovOverlapDualTestNorm Q s p q N g ≤
      cubeBesovOverlapDualFullTestNorm Q s p q g := by
  unfold cubeBesovOverlapDualFullTestNorm
  exact le_csSup hBdd ⟨N, rfl⟩

theorem cubeBesovOverlapDualTestSeminorm_le_meanZeroTestSeminorm_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞)
    (g : Vec d → ℝ)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovOverlapDualTestSeminorm Q s p q N g))
    (N : ℕ) :
    cubeBesovOverlapDualTestSeminorm Q s p q N g ≤
      cubeBesovOverlapDualMeanZeroTestSeminorm Q s p q g := by
  unfold cubeBesovOverlapDualMeanZeroTestSeminorm
  exact le_csSup hBdd ⟨N, rfl⟩

theorem CubeBesovOverlapDualFullTest.fullTestNorm_le_one {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {g : Vec d → ℝ}
    (hg : CubeBesovOverlapDualFullTest Q s p q g) :
    cubeBesovOverlapDualFullTestNorm Q s p q g ≤ 1 := by
  unfold cubeBesovOverlapDualFullTestNorm
  refine csSup_le ?_ ?_
  · exact ⟨cubeBesovOverlapDualTestNorm Q s p q 0 g, ⟨0, rfl⟩⟩
  · rintro x ⟨N, rfl⟩
    exact hg.1 N

theorem CubeBesovOverlapDualMeanZeroTestGlobal.meanZeroTestSeminorm_le_one
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞}
    {g : Vec d → ℝ}
    (hg : CubeBesovOverlapDualMeanZeroTestGlobal Q s p q g) :
    cubeBesovOverlapDualMeanZeroTestSeminorm Q s p q g ≤ 1 := by
  unfold cubeBesovOverlapDualMeanZeroTestSeminorm
  refine csSup_le ?_ ?_
  · exact ⟨cubeBesovOverlapDualTestSeminorm Q s p q 0 g, ⟨0, rfl⟩⟩
  · rintro x ⟨N, rfl⟩
    exact hg.1 N

theorem CubeBesovOverlapDualFullTest.of_fullTestNorm_le_one_of_bddAbove
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞}
    {g : Vec d → ℝ}
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovOverlapDualTestNorm Q s p q N g))
    (hfull : cubeBesovOverlapDualFullTestNorm Q s p q g ≤ 1)
    (hmem : CubeBesovOverlapDualLocalMemLpGlobal Q p g) :
    CubeBesovOverlapDualFullTest Q s p q g := by
  refine ⟨?_, hmem⟩
  intro N
  exact
    (cubeBesovOverlapDualTestNorm_le_fullTestNorm_of_bddAbove
      Q s p q g hBdd N).trans hfull

theorem CubeBesovOverlapDualMeanZeroTestGlobal.of_meanZeroTestSeminorm_le_one_of_bddAbove
    {d : ℕ} {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞}
    {g : Vec d → ℝ}
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovOverlapDualTestSeminorm Q s p q N g))
    (hfull : cubeBesovOverlapDualMeanZeroTestSeminorm Q s p q g ≤ 1)
    (havg : cubeAverage Q g = 0)
    (hmem : CubeBesovOverlapDualLocalMemLpGlobal Q p g) :
    CubeBesovOverlapDualMeanZeroTestGlobal Q s p q g := by
  refine ⟨?_, havg, hmem⟩
  intro N
  exact
    (cubeBesovOverlapDualTestSeminorm_le_meanZeroTestSeminorm_of_bddAbove
      Q s p q g hBdd N).trans hfull

theorem CubeBesovOverlapDualFullTest.to_dual_test {d : ℕ} {Q : TriadicCube d}
    {s : ℝ} {p q : ℝ≥0∞} {g : Vec d → ℝ}
    (hg : CubeBesovOverlapDualFullTest Q s p q g) :
    ∀ N : ℕ, CubeBesovOverlapDualTest Q s p q N g := by
  intro N
  exact ⟨hg.1 N, fun j hj S hS => hg.2 j S hS⟩

theorem CubeBesovOverlapDualMeanZeroTestGlobal.to_dual_test {d : ℕ}
    {Q : TriadicCube d} {s : ℝ} {p q : ℝ≥0∞} {g : Vec d → ℝ}
    (hg : CubeBesovOverlapDualMeanZeroTestGlobal Q s p q g) :
    ∀ N : ℕ, CubeBesovOverlapDualTest Q s p q N g := by
  intro N
  have hnorm : cubeBesovOverlapDualTestNorm Q s p q N g ≤ 1 := by
    rw [cubeBesovOverlapDualTestNorm_eq_cubeBesovOverlapDualTestSeminorm_of_cubeAverage_eq_zero
      Q s p q N g hg.2.1]
    exact hg.1 N
  exact ⟨hnorm, fun j hj S hS => hg.2.2 j S hS⟩

theorem CubeBesovOverlapDualLocalMemLpGlobal.of_memLp_parent {d : ℕ}
    {Q : TriadicCube d} {p : ℝ≥0∞} {g : Vec d → ℝ}
    (hg : MeasureTheory.MemLp g (cubeBesovConjExponent p) (normalizedCubeMeasure Q)) :
    CubeBesovOverlapDualLocalMemLpGlobal Q p g := by
  intro j S hS
  exact ScalarOverlap.memLp_sub_cubeAverage_of_mem_centersAtDepth_of_memLp hS hg

end Homogenization
