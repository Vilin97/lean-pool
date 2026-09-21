/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Order.Partition.Finpartition
import LeanPool.BKARForestFormula.BKAR.ForestGraph
import LeanPool.BKARForestFormula.BKAR.Threshold

/-!
# Threshold components for BKAR interpolation

This file packages the threshold-connected vertices of a BKAR forest as an
actual finite partition.  It is the combinatorial surface needed for
component-form positivity arguments built on the BKAR forest interpolation
formula (see `BKAR.Formula`): at threshold `s`, two
vertices lie in the same partition cell exactly when they are connected by
forest edges whose parameters are at least `s`.
-/

namespace BKAR

open scoped BigOperators

namespace Finpartition

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/--
Summing the indicator of “`z` and `w` lie in the same part” over the parts of a
finite partition leaves exactly the indicator of the part containing `z`.
-/
theorem sum_parts_indicator_pair
    (P : Finpartition (Finset.univ : Finset V)) (r : ℝ) (z w : V) :
    (∑ c : {c : Finset V // c ∈ P.parts},
        if z ∈ c.1 ∧ w ∈ c.1 then r else 0) =
      if w ∈ P.part z then r else 0 := by
  classical
  let cz : {c : Finset V // c ∈ P.parts} :=
    ⟨P.part z, (P.part_mem (a := z)).2 (Finset.mem_univ z)⟩
  by_cases hw : w ∈ P.part z
  · rw [Finset.sum_eq_single cz]
    · simp [cz, hw]
    · intro c _ hc
      have hz_not : z ∉ c.1 := by
        intro hz
        apply hc
        apply Subtype.ext
        exact (P.part_eq_of_mem c.2 hz).symm
      simp [hz_not]
    · intro hcz
      exact False.elim (hcz (Finset.mem_univ cz))
  · rw [if_neg hw]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hz : z ∈ c.1
    · have hpart : P.part z = c.1 := P.part_eq_of_mem c.2 hz
      have hwc : w ∉ c.1 := by
        intro hwc
        exact hw (by rwa [hpart])
      simp [hz, hwc]
    · simp [hz]

end

end Finpartition

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- The `Forest` representative carried by the threshold edge set. -/
def thresholdForest (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ) :
    Forest V :=
  (Classical.choice (F.thresholdIndex u s).acyclic).toForest

@[simp]
theorem thresholdForest_edges (F : Forest V) (u : F.EdgeParam → ℝ)
    (s : ℝ) :
    (F.thresholdForest u s).edges = F.thresholdEdges u s :=
  rfl

/--
Threshold connectivity agrees with the ordinary component relation in the
threshold forest.
-/
theorem thresholdConnected_iff_thresholdForest_inSameComponent
    (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ) (i j : V) :
    F.thresholdConnected u s i j ↔
      (F.thresholdForest u s).inSameComponent i j := by
  constructor
  · rintro ⟨γ, hγ, hall⟩
    refine Forest.inSameComponent_of_isSimplePath
      (F := F.thresholdForest u s) (γ := γ) ?_
    rw [IsSimplePath]
    rw [(F.thresholdForest u s).acyclic.isSimplePath_iff]
    have hγGraph : EdgePath.IsSimplePath F.edges γ i j :=
      F.acyclic.isSimplePath_iff.mp hγ
    have hγThreshold : EdgePath.IsSimplePath (F.thresholdEdges u s) γ i j :=
      hγGraph.mono_of_forall_mem fun e he =>
        (F.mem_thresholdEdges u s e).mpr
          ⟨hγGraph.edge_mem e he, hall e he⟩
    simpa using hγThreshold
  · intro hcomp
    let γ := (F.thresholdForest u s).pathInF i j hcomp
    have hγThresholdSimple :
        IsSimplePath (F.thresholdForest u s) γ i j :=
      (F.thresholdForest u s).pathInF_isSimple hcomp
    have hγThresholdGraph :
        EdgePath.IsSimplePath (F.thresholdEdges u s) γ i j := by
      rw [IsSimplePath] at hγThresholdSimple
      exact (F.thresholdForest u s).acyclic.isSimplePath_iff.mp
        hγThresholdSimple
    refine ⟨γ, ?_, ?_⟩
    · rw [IsSimplePath]
      rw [F.acyclic.isSimplePath_iff]
      exact hγThresholdGraph.mono fun e he =>
        (F.mem_thresholdEdges u s e).mp he |>.1
    · intro e he
      exact (F.mem_thresholdEdges u s e).mp
        (hγThresholdGraph.edge_mem e he) |>.2

theorem thresholdConnected_refl
    (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ) (i : V) :
    F.thresholdConnected u s i i := by
  rw [F.thresholdConnected_iff_thresholdForest_inSameComponent u s]
  exact (F.thresholdForest u s).acyclic.inSameComponent_refl i

theorem thresholdConnected_symm
    (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ)
    {i j : V} (h : F.thresholdConnected u s i j) :
    F.thresholdConnected u s j i := by
  rw [F.thresholdConnected_iff_thresholdForest_inSameComponent u s] at h ⊢
  exact (F.thresholdForest u s).acyclic.inSameComponent_symm h

theorem thresholdConnected_trans
    (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ)
    {i j k : V} (hij : F.thresholdConnected u s i j)
    (hjk : F.thresholdConnected u s j k) :
    F.thresholdConnected u s i k := by
  rw [F.thresholdConnected_iff_thresholdForest_inSameComponent u s] at hij hjk ⊢
  exact (F.thresholdForest u s).inSameComponent_trans hij hjk

/-- Threshold connectivity as a finite setoid on vertices. -/
def thresholdSetoid (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ) :
    Setoid V where
  r := F.thresholdConnected u s
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact F.thresholdConnected_refl u s i
    · intro i j hij
      exact F.thresholdConnected_symm u s hij
    · intro i j k hij hjk
      exact F.thresholdConnected_trans u s hij hjk

/--
The finite partition of vertices into threshold-connected components.
-/
def thresholdPartition (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ) :
    Finpartition (Finset.univ : Finset V) := by
  classical
  exact Finpartition.ofSetoid (F.thresholdSetoid u s)

/-- The threshold component containing a given vertex. -/
def thresholdComponent (F : Forest V) (u : F.EdgeParam → ℝ) (s : ℝ)
    (i : V) : Finset V :=
  (F.thresholdPartition u s).part i

@[simp]
theorem mem_thresholdComponent (F : Forest V) (u : F.EdgeParam → ℝ)
    (s : ℝ) (i j : V) :
    j ∈ F.thresholdComponent u s i ↔
      F.thresholdConnected u s i j := by
  classical
  simpa [thresholdComponent, thresholdPartition, thresholdSetoid] using!
    (Finpartition.mem_part_ofSetoid_iff_rel
      (s := F.thresholdSetoid u s) (a := i) (b := j))

@[simp]
theorem self_mem_thresholdComponent (F : Forest V) (u : F.EdgeParam → ℝ)
    (s : ℝ) (i : V) :
    i ∈ F.thresholdComponent u s i := by
  rw [F.mem_thresholdComponent u s]
  exact F.thresholdConnected_refl u s i

/--
Positive-threshold layer-set form of the BKAR interpolation value: the edge
value is above `s` exactly when the endpoints lie in the same threshold
component.
-/
theorem le_standardInterp_iff_mem_thresholdComponent
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (e : Edge V) :
    s ≤ F.standardInterp u e ↔
      e.right ∈ F.thresholdComponent u s e.left := by
  rw [F.mem_thresholdComponent u s]
  exact F.le_standardInterp_iff_thresholdConnected u hs0 hs1 e

/--
At a fixed threshold, summing over threshold partition cells gives the
component indicator of the threshold component containing `z`.
-/
theorem sum_thresholdPartition_parts_indicator_pair
    (F : Forest V) (u : F.EdgeParam → ℝ) (s r : ℝ) (z w : V) :
    (∑ c : {c : Finset V // c ∈ (F.thresholdPartition u s).parts},
        if z ∈ c.1 ∧ w ∈ c.1 then r else 0) =
      if w ∈ F.thresholdComponent u s z then r else 0 := by
  simpa [thresholdComponent] using!
    (Finpartition.sum_parts_indicator_pair
      (P := F.thresholdPartition u s) (r := r) (z := z) (w := w))

end

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
