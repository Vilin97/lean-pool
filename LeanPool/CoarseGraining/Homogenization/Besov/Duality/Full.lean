/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Duality.Definitions
import LeanPool.CoarseGraining.Homogenization.Besov.Duality.Elementary

/-! # Full -/

namespace Homogenization

open MeasureTheory.Measure
open scoped BigOperators ENNReal

/-!
Global wrapper layer for the cube Besov duality package.

This file keeps the new global objects deliberately minimal:

* a depth-uniform local `MemLp` predicate for dual tests;
* global dual test predicates, using the finite-depth comparison norms as the
  test data;
* global value sets and `sSup` wrappers for the dual pairing bounds;
* a global circ wrapper built from the finite circ branch.

The comparison theorems themselves are still deferred to the later
projection-limit layer.
-/

noncomputable def CubeBesovDualLocalMemLpGlobal {d : ℕ} (Q : TriadicCube d)
    (p : ℝ≥0∞) (g : Vec d → ℝ) : Prop :=
  ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
    MeasureTheory.MemLp (cubeFluctuation R g) (cubeBesovConjExponent p)
      (normalizedCubeMeasure R)

noncomputable def cubeBesovDualFullTestNorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (g : Vec d → ℝ) : ℝ :=
  sSup (Set.range (fun N : ℕ => cubeBesovDualTestNorm Q s p q N g))

noncomputable def cubeBesovDualMeanZeroTestSeminorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (g : Vec d → ℝ) : ℝ :=
  sSup (Set.range (fun N : ℕ => cubeBesovDualTestSeminorm Q s p q N g))

def CubeBesovDualFullTest {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (g : Vec d → ℝ) : Prop :=
  (∀ N : ℕ, cubeBesovDualTestNorm Q s p q N g ≤ 1) ∧
    CubeBesovDualLocalMemLpGlobal Q p g

def CubeBesovDualMeanZeroTestGlobal {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (g : Vec d → ℝ) : Prop :=
  (∀ N : ℕ, cubeBesovDualTestSeminorm Q s p q N g ≤ 1) ∧
    cubeAverage Q g = 0 ∧ CubeBesovDualLocalMemLpGlobal Q p g

theorem CubeBesovDualFullTest.to_dual_test {d : ℕ} {Q : TriadicCube d} {s : ℝ}
    {p q : ℝ≥0∞} {g : Vec d → ℝ} (hg : CubeBesovDualFullTest Q s p q g) :
    ∀ N : ℕ, CubeBesovDualTest Q s p q N g := by
  intro N
  exact ⟨hg.1 N, fun j hj R hR => hg.2 j R hR⟩

theorem CubeBesovDualMeanZeroTestGlobal.to_dual_test {d : ℕ} {Q : TriadicCube d} {s : ℝ}
    {p q : ℝ≥0∞} {g : Vec d → ℝ} (hg : CubeBesovDualMeanZeroTestGlobal Q s p q g) :
    ∀ N : ℕ, CubeBesovDualTest Q s p q N g := by
  intro N
  have hnorm : cubeBesovDualTestNorm Q s p q N g ≤ 1 := by
    rw [cubeBesovDualTestNorm_eq_cubeBesovDualTestSeminorm_of_cubeAverage_eq_zero
      Q s p q N g hg.2.1]
    exact hg.1 N
  exact ⟨hnorm, fun j hj R hR => hg.2.2 j R hR⟩

noncomputable def cubeBesovDualFullNormValueSet {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (f : Vec d → ℝ) : Set ℝ :=
  {r | ∃ g : Vec d → ℝ, CubeBesovDualFullTest Q s p q g ∧ r = |cubeBesovPairing Q f g|}

noncomputable def cubeBesovDualMeanZeroSeminormValueSet {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (f : Vec d → ℝ) : Set ℝ :=
  {r | ∃ g : Vec d → ℝ, CubeBesovDualMeanZeroTestGlobal Q s p q g ∧
      r = |cubeBesovPairing Q f g|}

noncomputable def cubeBesovDualFullNorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (f : Vec d → ℝ) : ℝ :=
  sSup (cubeBesovDualFullNormValueSet Q s p q f)

noncomputable def cubeBesovDualMeanZeroSeminorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (f : Vec d → ℝ) : ℝ :=
  sSup (cubeBesovDualMeanZeroSeminormValueSet Q s p q f)

noncomputable def cubeBesovCircNormEntry {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) : ℝ :=
  if q = ∞ then
    cubeBesovCircPartialNormTop Q s p (N + 1) u
  else
    cubeBesovCircPartialNorm Q s p q (N + 1) u

noncomputable def cubeBesovCircNormValueSet {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (u : Vec d → ℝ) : Set ℝ :=
  Set.range (fun N : ℕ => cubeBesovCircNormEntry Q s p q N u)

noncomputable def cubeBesovCircNorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (u : Vec d → ℝ) : ℝ :=
  sSup (cubeBesovCircNormValueSet Q s p q u)

theorem CubeBesovDualFullTest_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    CubeBesovDualFullTest Q s p q (fun _ => (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro N
    rw [cubeBesovDualTestNorm_zero Q s p q N hp0 hpTop]
    norm_num
  · intro j R hR
    rw [cubeFluctuation_const]
    exact (MeasureTheory.memLp_const (0 : ℝ) :
      MeasureTheory.MemLp (fun _ : Vec d => (0 : ℝ))
        (cubeBesovConjExponent p) (normalizedCubeMeasure R))

theorem CubeBesovDualMeanZeroTestGlobal_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    CubeBesovDualMeanZeroTestGlobal Q s p q (fun _ => (0 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N
    rw [cubeBesovDualTestSeminorm_zero Q s p q N hp0 hpTop]
    norm_num
  · rw [cubeAverage_const]
  · intro j R hR
    rw [cubeFluctuation_const]
    exact (MeasureTheory.memLp_const (0 : ℝ) :
      MeasureTheory.MemLp (fun _ : Vec d => (0 : ℝ))
        (cubeBesovConjExponent p) (normalizedCubeMeasure R))

theorem cubeBesovDualFullNormValueSet_nonempty {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (f : Vec d → ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    (cubeBesovDualFullNormValueSet Q s p q f).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨fun _ => (0 : ℝ), CubeBesovDualFullTest_zero Q s p q hp0 hpTop, ?_⟩
  simpa [cubeBesovPairing] using (congrArg abs (cubeAverage_const Q (0 : ℝ))).symm

theorem zero_mem_cubeBesovDualFullNormValueSet {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (f : Vec d → ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    0 ∈ cubeBesovDualFullNormValueSet Q s p q f := by
  refine ⟨fun _ => (0 : ℝ), CubeBesovDualFullTest_zero Q s p q hp0 hpTop, ?_⟩
  simp

theorem cubeBesovDualMeanZeroSeminormValueSet_nonempty {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (f : Vec d → ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    (cubeBesovDualMeanZeroSeminormValueSet Q s p q f).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨fun _ => (0 : ℝ), CubeBesovDualMeanZeroTestGlobal_zero Q s p q hp0 hpTop, ?_⟩
  simpa [cubeBesovPairing] using (congrArg abs (cubeAverage_const Q (0 : ℝ))).symm

theorem zero_mem_cubeBesovDualMeanZeroSeminormValueSet {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (f : Vec d → ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    0 ∈ cubeBesovDualMeanZeroSeminormValueSet Q s p q f := by
  refine ⟨fun _ => (0 : ℝ), CubeBesovDualMeanZeroTestGlobal_zero Q s p q hp0 hpTop, ?_⟩
  simp

theorem cubeBesovDualMeanZeroSeminorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (f : Vec d → ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    0 ≤ cubeBesovDualMeanZeroSeminorm Q s p q f := by
  unfold cubeBesovDualMeanZeroSeminorm
  exact Real.sSup_nonneg'
    ⟨0, zero_mem_cubeBesovDualMeanZeroSeminormValueSet Q s p q f hp0 hpTop, le_rfl⟩

theorem cubeBesovDualFullNorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (f : Vec d → ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    0 ≤ cubeBesovDualFullNorm Q s p q f := by
  unfold cubeBesovDualFullNorm
  exact Real.sSup_nonneg'
    ⟨0, zero_mem_cubeBesovDualFullNormValueSet Q s p q f hp0 hpTop, le_rfl⟩

/-- Bound a full dual negative Besov norm by bounding its pairing against all
unit full-dual tests.  This is the formal supremum step used in duality
arguments. -/
theorem cubeBesovDualFullNorm_le_of_forall_fullTest_pairing_le {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (f : Vec d → ℝ) {B : ℝ}
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞)
    (hB :
      ∀ g : Vec d → ℝ,
        CubeBesovDualFullTest Q s p q g →
          |cubeBesovPairing Q f g| ≤ B) :
    cubeBesovDualFullNorm Q s p q f ≤ B := by
  unfold cubeBesovDualFullNorm
  refine csSup_le
    (cubeBesovDualFullNormValueSet_nonempty Q s p q f hp0 hpTop) ?_
  intro r hr
  rcases hr with ⟨g, hg, rfl⟩
  exact hB g hg

@[simp] theorem cubeBesovDualMeanZeroSeminormValueSet_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (c : ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    cubeBesovDualMeanZeroSeminormValueSet Q s p q (fun _ => c) = {0} := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨g, hg, rfl⟩
    rw [cubeBesovPairing_const_left, hg.2.1]
    simp
  · intro hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact zero_mem_cubeBesovDualMeanZeroSeminormValueSet
      Q s p q (fun _ => c) hp0 hpTop

@[simp] theorem cubeBesovDualMeanZeroSeminorm_const {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (c : ℝ)
    (hp0 : cubeBesovConjExponent p ≠ 0) (hpTop : cubeBesovConjExponent p ≠ ∞) :
    cubeBesovDualMeanZeroSeminorm Q s p q (fun _ => c) = 0 := by
  rw [cubeBesovDualMeanZeroSeminorm,
    cubeBesovDualMeanZeroSeminormValueSet_const Q s p q c hp0 hpTop]
  simp

theorem cubeBesovCircNormValueSet_nonempty {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (u : Vec d → ℝ) :
    (cubeBesovCircNormValueSet Q s p q u).Nonempty := by
  exact ⟨cubeBesovCircNormEntry Q s p q 0 u, ⟨0, rfl⟩⟩

theorem abs_cubeBesovPairing_le_cubeBesovDualFullNorm_of_full_test {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (f g : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovDualFullNormValueSet Q s p q f))
    (hg : CubeBesovDualFullTest Q s p q g) :
    |cubeBesovPairing Q f g| ≤ cubeBesovDualFullNorm Q s p q f := by
  unfold cubeBesovDualFullNorm
  exact le_csSup hBdd ⟨g, hg, rfl⟩

theorem abs_cubeBesovPairing_le_cubeBesovDualMeanZeroSeminorm_of_mean_zero_test {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (f g : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovDualMeanZeroSeminormValueSet Q s p q f))
    (hg : CubeBesovDualMeanZeroTestGlobal Q s p q g) :
    |cubeBesovPairing Q f g| ≤ cubeBesovDualMeanZeroSeminorm Q s p q f := by
  unfold cubeBesovDualMeanZeroSeminorm
  exact le_csSup hBdd ⟨g, hg, rfl⟩

theorem cubeBesovCircNormEntry_le_cubeBesovCircNorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (u : Vec d → ℝ)
    (hBdd : BddAbove (cubeBesovCircNormValueSet Q s p q u)) (N : ℕ) :
    cubeBesovCircNormEntry Q s p q N u ≤ cubeBesovCircNorm Q s p q u := by
  unfold cubeBesovCircNorm
  exact le_csSup hBdd ⟨N, rfl⟩

theorem cubeBesovCircPartialNorm_le_cubeBesovCircNorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (u : Vec d → ℝ) (hq : q ≠ ∞)
    (hBdd : BddAbove (cubeBesovCircNormValueSet Q s p q u)) (N : ℕ) :
    cubeBesovCircPartialNorm Q s p q (N + 1) u ≤ cubeBesovCircNorm Q s p q u := by
  simpa [cubeBesovCircNormEntry, hq] using
    cubeBesovCircNormEntry_le_cubeBesovCircNorm Q s p q u hBdd N

theorem cubeBesovCircPartialNormTop_le_cubeBesovCircNorm {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (p q : ℝ≥0∞) (u : Vec d → ℝ) (hq : q = ∞)
    (hBdd : BddAbove (cubeBesovCircNormValueSet Q s p q u)) (N : ℕ) :
    cubeBesovCircPartialNormTop Q s p (N + 1) u ≤ cubeBesovCircNorm Q s p q u := by
  simpa [cubeBesovCircNormEntry, hq] using
    cubeBesovCircNormEntry_le_cubeBesovCircNorm Q s p q u hBdd N

/-- Bound the full circ norm by a uniform bound on all entries in its defining
value set. -/
theorem cubeBesovCircNorm_le_of_forall_entry_le {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) {B : ℝ}
    (hB : ∀ N : ℕ, cubeBesovCircNormEntry Q s p q N u ≤ B) :
    cubeBesovCircNorm Q s p q u ≤ B := by
  unfold cubeBesovCircNorm
  exact csSup_le (cubeBesovCircNormValueSet_nonempty Q s p q u) (by
    intro y hy
    rcases hy with ⟨N, rfl⟩
    exact hB N)

/-- For finite `q`, the full circ norm is bounded by any uniform bound on all
finite partial circ norms. -/
theorem cubeBesovCircNorm_le_of_forall_partialNorm_le {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (u : Vec d → ℝ) {B : ℝ}
    (hq : q ≠ ∞)
    (hB : ∀ N : ℕ, cubeBesovCircPartialNorm Q s p q N u ≤ B) :
    cubeBesovCircNorm Q s p q u ≤ B := by
  exact
    cubeBesovCircNorm_le_of_forall_entry_le Q s p q u (by
      intro N
      simpa [cubeBesovCircNormEntry, hq] using hB (N + 1))

end Homogenization
